use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};

use crate::expander::{expand_tag, field_int};
use crate::expander::{
    Data, EnumData, Expander, ExpanderWithMode, ExpansionMode, FieldData, StructData, VariantData,
};
use crate::internals::attr::{DefaultTag, Packing};
use crate::internals::symbol::*;

pub(crate) fn expand_encode_entry(
    e: &Expander,
    expansion: ExpansionMode<'_>,
) -> Option<TokenStream> {
    let e = ExpanderWithMode {
        input: e.input,
        cx: &e.cx,
        type_attr: &e.type_attr,
        type_name: &e.type_name,
        data: &e.data,
        tokens: &e.tokens,
        mode: expansion.as_mode(&e.tokens),
    };

    expand_encode_moded(e, expansion)
}

/// Entrypoint for expanding an `Encode` implementation.
fn expand_encode_moded(
    e: ExpanderWithMode<'_>,
    expansion: ExpansionMode<'_>,
) -> Option<TokenStream> {
    let span = e.input.ident.span();

    let type_ident = &e.input.ident;

    let var = syn::Ident::new("encoder", span);

    let body = match &e.data {
        Data::Struct(data) => encode_struct(e, &var, data)?,
        Data::Enum(data) => encode_tagged_enum(e, &var, data)?,
        Data::Union => {
            e.cx.error_span(span, "musli: unions are not supported");
            return None;
        }
    };

    if e.cx.has_errors() {
        return None;
    }

    let encode_t = &e.tokens.encode_t;
    let encoder_t = &e.tokens.encoder_t;

    let (impl_generics, mode_ident, where_clause) =
        expansion.as_impl_generics(e.input.generics.clone(), &e.tokens);

    let type_generics = &e.input.generics;

    Some(quote_spanned! {
        span =>
        #[automatically_derived]
        impl #impl_generics #encode_t<#mode_ident> for #type_ident #type_generics #where_clause {
            #[inline]
            fn encode<E>(&self, #var: E) -> Result<E::Ok, E::Error>
            where
                E: #encoder_t
            {
                #body
            }
        }
    })
}

/// Encode a transparent element.
fn encode_transparent(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    span: Span,
    fields: &[FieldData],
) -> Option<TokenStream> {
    let f = match fields {
        [f] => f,
        _ => {
            e.transparent_diagnostics(span, fields);
            return None;
        }
    };

    let accessor = match &f.ident {
        Some(ident) => quote_spanned!(f.span => &self.#ident),
        None => quote_spanned!(f.span => &self.0),
    };

    let (span, encode_path) = f.attr.encode_path(e.mode, span);

    Some(quote_spanned! {
        span => #encode_path(#accessor, #var)
    })
}

/// Encode a struct.
fn encode_struct(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    st: &StructData,
) -> Option<TokenStream> {
    let mut field_tests = Vec::with_capacity(st.fields.len());
    let mut encoders = Vec::with_capacity(st.fields.len());
    let mut test_variables = Vec::with_capacity(st.fields.len());
    let packing = e.type_attr.packing(e.mode).cloned().unwrap_or_default();

    let default_field_tag = e.type_attr.default_field_tag(e.mode);

    for f in &st.fields {
        let access = match &f.ident {
            Some(ident) => quote!(&self.#ident),
            None => {
                let n = field_int(f.index, f.span);
                quote!(&self.#n)
            }
        };

        let mut encode = encode_field(e, var, f, &access, &packing, default_field_tag)?;

        if let Some((decl, test)) = do_field_test(e, &access, f) {
            encode = quote_spanned! {
                f.span =>
                if #test {
                    #encode
                }
            };

            field_tests.push(decl);
            test_variables.push(test);
        }

        encoders.push(encode);
    }

    let encode = match packing {
        Packing::Transparent => encode_transparent(e, var, e.input.ident.span(), &st.fields)?,
        Packing::Tagged(..) => {
            let encode = quote! { #(#encoders)* };
            encode_field_tag(e, var, &st.fields, encode, &field_tests, &test_variables)
        }
        Packing::Packed => {
            let encoder_t = &e.tokens.encoder_t;
            let sequence_encoder_t = &e.tokens.sequence_encoder_t;

            quote! {{
                let mut pack = #encoder_t::encode_pack(#var)?;
                #(#field_tests)*
                #(#encoders)*
                #sequence_encoder_t::end(pack)
            }}
        }
    };

    Some(encode)
}

/// Encode an internally tagged enum.
fn encode_tagged_enum(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    data: &EnumData,
) -> Option<TokenStream> {
    if let Some(&(span, Packing::Transparent)) = e.type_attr.packing_span(e.mode) {
        e.cx.error_span(
            span,
            format!("#[{}({})] cannot be used on enums", ATTR, TRANSPARENT),
        );
        return None;
    }

    let mut variants = Vec::with_capacity(data.variants.len());

    for variant in &data.variants {
        if let Some((pattern, encode)) = encode_variant(e, var, variant) {
            variants.push(quote!(#pattern => { #encode }));
        }
    }

    // Special case: uninhabitable types.
    Some(if variants.is_empty() {
        quote! {
            match *self {}
        }
    } else {
        quote! {
            match self {
                #(#variants),*
            }
        }
    })
}

fn encode_field_tag(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    fields: &[FieldData],
    encode: TokenStream,
    field_tests: &[TokenStream],
    test_variables: &[syn::Ident],
) -> TokenStream {
    let encoder_t = &e.tokens.encoder_t;
    let pairs_encoder_t = &e.tokens.pairs_encoder_t;

    let len = calculate_tests(fields.len(), test_variables);

    quote! {
        #(#field_tests)*
        let mut #var = #encoder_t::encode_struct(#var, #len)?;
        #encode
        #pairs_encoder_t::end(#var)
    }
}

/// Setup encoding for a single variant. that is externally tagged.
fn encode_variant(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    v: &VariantData,
) -> Option<(TokenStream, TokenStream)> {
    let span = v.span;

    let variant_packing = v
        .attr
        .packing(e.mode)
        .or_else(|| e.type_attr.packing(e.mode))
        .cloned()
        .unwrap_or_default();

    let default_field_tag = v
        .attr
        .default_field_tag(e.mode)
        .unwrap_or_else(|| e.type_attr.default_field_tag(e.mode));

    let (mut encode, patterns) = match &variant_packing {
        Packing::Tagged(..) => {
            let (encode, patterns, tests) =
                encode_variant_fields(e, v, var, &variant_packing, default_field_tag)?;

            // Special stuff needed to encode the field if its tagged.
            let encode = encode_field_tag(e, var, &v.fields, encode, &[], &tests);
            (encode, patterns)
        }
        Packing::Packed => {
            let (encode, patterns, _) =
                encode_variant_fields(e, v, var, &variant_packing, default_field_tag)?;
            (encode, patterns)
        }
        Packing::Transparent => encode_transparent_variant(e, var, span, &v.fields)?,
    };

    if let Packing::Tagged(..) = e.type_attr.packing(e.mode).cloned().unwrap_or_default() {
        let encoder_t = &e.tokens.encoder_t;
        let variant_encoder_t = &e.tokens.variant_encoder_t;

        let (tag, _) = expand_tag(
            &e.cx,
            v.span,
            v.attr.rename(e.mode),
            e.type_attr.default_variant_tag(e.mode),
            v.index,
            Some(&v.name),
        )?;

        let encode_t_encode = e.mode.encode_t_encode();

        encode = quote! {
            let mut variant_encoder = #encoder_t::encode_variant(#var)?;

            {
                let tag_encoder = #variant_encoder_t::tag(&mut variant_encoder)?;
                #encode_t_encode(&#tag, tag_encoder)?;
            }

            {
                let #var = #variant_encoder_t::variant(&mut variant_encoder)?;
                #encode?;
            }

            #variant_encoder_t::end(variant_encoder)
        };
    }

    let mut path = syn::Path::from(syn::Ident::new("Self", span));
    path.segments.push(v.ident.clone().into());

    let pattern = quote!(#path { #(#patterns),* });
    Some((pattern, encode))
}

fn encode_variant_fields(
    e: ExpanderWithMode<'_>,
    v: &VariantData,
    var: &syn::Ident,
    packing: &Packing,
    default_field_tag: DefaultTag,
) -> Option<(TokenStream, Vec<TokenStream>, Vec<syn::Ident>)> {
    let mut field_tests = Vec::with_capacity(v.fields.len());
    let mut encoders = Vec::with_capacity(v.fields.len());
    let mut patterns = Vec::with_capacity(v.fields.len());
    let mut test_variables = Vec::with_capacity(v.fields.len());

    for f in &v.fields {
        let access = match &f.ident {
            Some(ident) => {
                patterns.push(quote!(#ident));
                quote!(#ident)
            }
            None => {
                let index = field_int(f.index, f.span);
                let var = syn::Ident::new(&format!("v{}", f.index), f.span);
                patterns.push(quote!(#index: #var));
                quote!(#var)
            }
        };

        let mut encode = encode_field(e, var, f, &access, packing, default_field_tag)?;

        if let Some((decl, test)) = do_field_test(e, &access, f) {
            encode = quote_spanned! {
                f.span =>
                if #test {
                    #encode
                }
            };

            field_tests.push(decl);
            test_variables.push(test);
        }

        encoders.push(encode);
    }

    let encode = match packing {
        Packing::Tagged(..) => {
            quote_spanned! {
                v.span =>
                #(#field_tests)*
                #(#encoders)*
            }
        }
        Packing::Packed => {
            let encoder_t = &e.tokens.encoder_t;
            let sequence_encoder_t = &e.tokens.sequence_encoder_t;

            quote_spanned! {
                v.span =>
                let mut pack = #encoder_t::encode_pack(#var)?;
                #(#field_tests)*
                #(#encoders)*
                #sequence_encoder_t::end(pack)
            }
        }
        _ => quote!(),
    };

    Some((encode, patterns, test_variables))
}

fn do_field_test(
    e: ExpanderWithMode<'_>,
    access: &TokenStream,
    f: &FieldData,
) -> Option<(TokenStream, syn::Ident)> {
    let (skip_span, skip_encoding_if_path) = f.attr.skip_encoding_if(e.mode)?;
    let test = syn::Ident::new(&format!("t{}", f.index), f.span);

    let decl = quote_spanned! {
        skip_span =>
        let #test = !#skip_encoding_if_path(#access);
    };

    Some((decl, test))
}

/// Encode a field.
fn encode_field(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    f: &FieldData,
    access: &TokenStream,
    packing: &Packing,
    default_field_tag: DefaultTag,
) -> Option<TokenStream> {
    let (span, encode_path) = f.attr.encode_path(e.mode, f.span);

    match packing {
        Packing::Tagged(..) | Packing::Transparent => {
            let (tag, _) = expand_tag(
                &e.cx,
                f.span,
                f.attr.rename(e.mode),
                default_field_tag,
                f.index,
                f.name.as_ref(),
            )?;

            let pair_encoder_t = &e.tokens.pair_encoder_t;
            let pairs_encoder_t = &e.tokens.pairs_encoder_t;

            let encode_t_encode = e.mode.encode_t_encode();

            Some(quote_spanned! {
                span => {
                    let mut pair_encoder = #pairs_encoder_t::next(&mut #var)?;
                    let field_encoder = #pair_encoder_t::first(&mut pair_encoder)?;
                    #encode_t_encode(&#tag, field_encoder)?;
                    let value_encoder = #pair_encoder_t::second(&mut pair_encoder)?;
                    #encode_path(#access, value_encoder)?;
                    #pair_encoder_t::end(pair_encoder)?;
                }
            })
        }
        Packing::Packed => {
            let sequence_encoder_t = &e.tokens.sequence_encoder_t;

            Some(quote_spanned! {
                span =>
                #encode_path(#access, #sequence_encoder_t::next(&mut pack)?)?;
            })
        }
    }
}

/// Encode a transparent element.
fn encode_transparent_variant(
    e: ExpanderWithMode<'_>,
    var: &syn::Ident,
    span: Span,
    fields: &[FieldData],
) -> Option<(TokenStream, Vec<TokenStream>)> {
    let f = match fields {
        [f] => f,
        _ => {
            e.transparent_diagnostics(span, fields);
            return None;
        }
    };

    let (span, encode_path) = f.attr.encode_path(e.mode, span);

    let encode = quote_spanned! {
        span => #encode_path(this, #var)
    };

    let accessor = match &f.ident {
        Some(ident) => quote_spanned!(f.span => #ident: this),
        None => quote_spanned!(f.span => 0: this),
    };

    Some((encode, vec![accessor]))
}

fn calculate_tests(count: usize, tests: &[syn::Ident]) -> TokenStream {
    if tests.is_empty() {
        quote!(#count)
    } else {
        let count = count.saturating_sub(tests.len());
        let tests = tests.iter().map(|v| quote!(if #v { 1 } else { 0 }));
        quote!(#count + #(#tests)+*)
    }
}

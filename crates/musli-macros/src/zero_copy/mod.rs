use self::num::{Enumerator, NumericalRepr};
mod num;

use std::cell::RefCell;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::meta::ParseNestedMeta;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parenthesized, Token};

#[derive(Default)]
struct Ctxt {
    errors: RefCell<Vec<syn::Error>>,
}

impl Ctxt {
    fn error(&self, error: syn::Error) {
        self.errors.borrow_mut().push(error);
    }
}

pub struct Expander {
    input: syn::DeriveInput,
}

impl Expander {
    pub fn new(input: syn::DeriveInput) -> Self {
        Self { input }
    }
}

impl Expander {
    pub fn expand(self) -> Result<TokenStream, Vec<syn::Error>> {
        let cx = Ctxt::default();

        let Ok(output) = expand(&cx, self.input) else {
            return Err(cx.errors.into_inner());
        };

        let errors = cx.errors.into_inner();

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(output)
    }
}

fn expand(cx: &Ctxt, input: syn::DeriveInput) -> Result<TokenStream, ()> {
    let (attrs, name, mut generics, data) = (input.attrs, input.ident, input.generics, input.data);

    let mut r = ReprAttr::default();
    let mut krate: syn::Path = syn::parse_quote!(musli_zerocopy);

    for attr in &attrs {
        if attr.path().is_ident("repr") {
            r.parse_attr(cx, attr);
        }

        if attr.path().is_ident("zero_copy") {
            let result = attr.parse_nested_meta(|meta: ParseNestedMeta| {
                if meta.path.is_ident("bounds") {
                    meta.input.parse::<Token![=]>()?;
                    let content;
                    syn::braced!(content in meta.input);

                    let predicates =
                        Punctuated::<syn::WherePredicate, Token![,]>::parse_terminated(&content)?;

                    generics.make_where_clause().predicates.extend(predicates);
                    return Ok(());
                }

                if meta.path.is_ident("crate") {
                    if meta.input.parse::<Option<Token![=]>>()?.is_some() {
                        krate = meta.input.parse()?;
                    } else {
                        krate = syn::parse_quote!(crate);
                    }

                    return Ok(());
                }

                Err(syn::Error::new(
                    meta.input.span(),
                    "ZeroCopy: Unsupported attribute",
                ))
            });

            if let Err(error) = result {
                cx.error(error);
            }
        }
    }

    let Some((repr_span, repr)) = r.repr else {
        cx.error(syn::Error::new(
            Span::call_site(),
            "ZeroCopy: struct must be marked with repr(C), repr(transparent), repr(u*), or repr(i*)",
        ));
        return Err(());
    };

    let error: syn::Path = syn::parse_quote!(#krate::Error);
    let mem: syn::Path = syn::parse_quote!(#krate::__private::mem);
    let padder: syn::Path = syn::parse_quote!(#krate::buf::Padder);
    let result: syn::Path = syn::parse_quote!(#krate::__private::result::Result);
    let unknown_discriminant: syn::Path =
        syn::parse_quote!(#krate::__private::unknown_discriminant);
    let validator: syn::Path = syn::parse_quote!(#krate::buf::Validator);
    let zero_copy: syn::Path = syn::parse_quote!(#krate::traits::ZeroCopy);
    let zero_sized: syn::Path = syn::parse_quote!(#krate::traits::ZeroSized);

    let pad;
    let validate;
    let impl_zero_sized;
    let any_bits;
    let padded;
    // Expands to an expression which is not executed, but ensures that the type
    // expands only to the fields visible to the proc macro or causes a compile
    // error.
    let check_fields;
    let mut check_zero_sized = Vec::new();

    match &data {
        syn::Data::Struct(st) => {
            // Field types.
            let mut output = process_fields(cx, &st.fields);
            check_zero_sized.append(&mut output.check_zero_sized);

            match (repr, &output.first_field) {
                (Repr::Transparent, Some(ty)) => {
                    pad = quote! {
                        <#ty as #zero_copy>::pad(#padder::transparent::<#ty>(padder));
                    };

                    validate = quote! {
                        <#ty as #zero_copy>::validate(#validator::transparent::<#ty>(validator))?;
                    };
                }
                _ => {
                    let types = &output.types;

                    match r.repr_packed {
                        Some((_, align)) => {
                            pad = quote! {
                                #(#padder::pad_with::<#types>(padder, #align);)*
                            };

                            validate = quote! {
                                // SAFETY: We've systematically ensured that we're
                                // only validating over fields within the size of
                                // this type.
                                #(#validator::validate_with::<#types>(validator, #align)?;)*
                            };
                        }
                        _ => {
                            pad = quote! {
                                #(#padder::pad::<#types>(padder);)*
                            };

                            validate = quote! {
                                // SAFETY: We've systematically ensured that we're
                                // only validating over fields within the size of
                                // this type.
                                #(#validator::validate::<#types>(validator)?;)*
                            };
                        }
                    }
                }
            }

            let mut field_sizes = Vec::new();
            let mut field_padded = Vec::new();

            for ty in output.types.iter() {
                field_sizes.push(quote!(#mem::size_of::<#ty>()));
                field_padded.push(quote!(<#ty as #zero_copy>::PADDED));
            }

            // ZSTs are padded if their alignment is not 1, any other type is
            // padded if the sum of all their field sizes does not match the
            // size of the type itself.
            padded = quote!(#mem::size_of::<Self>() > (0 #(+ #field_sizes)*) #(|| #field_padded)*);

            let types = &output.types;

            impl_zero_sized = types.is_empty().then(|| {
                let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

                quote! {
                    // SAFETY: Type has no fields and has the necessary `repr`.
                    #[automatically_derived]
                    unsafe impl #impl_generics #zero_sized for #name #ty_generics #where_clause {}
                }
            });

            any_bits = quote!(true #(&& <#types as #zero_copy>::ANY_BITS)*);

            let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

            // NB: We go through a pointer here to allow for padded structs.
            check_fields = {
                let pat = build_field_exhaustive_pattern([name.clone()], &output, &st.fields);

                quote!(
                    const _: () = {
                        #[allow(unused)]
                        fn check_struct_fields #impl_generics(this: #name #ty_generics) #where_clause {
                            match this {
                                #pat => {}
                            }
                        }
                    };
                )
            };
        }
        syn::Data::Enum(en) => {
            if let Some((span, _)) = r.repr_packed {
                cx.error(syn::Error::new(
                    span,
                    "ZeroCopy: repr(packed) is only supported on structs",
                ));

                return Err(());
            }

            let Some((span, num)) = repr.as_numerical_repr() else {
                cx.error(syn::Error::new(
                    repr_span,
                    "ZeroCopy: only supported for repr(i*) or repr(u*) enums",
                ));

                return Err(());
            };

            let ty = syn::Ident::new(num.as_ty(), span);

            let mut validate_variants = Vec::new();
            let mut pad_variants = Vec::new();
            let mut padded_variants = Vec::new();
            let mut variant_fields = Vec::new();

            let mut enumerator = Enumerator::new(num, ty.span());

            for variant in &en.variants {
                let mut output = process_fields(cx, &variant.fields);
                check_zero_sized.append(&mut output.check_zero_sized);

                let discriminant =
                    match enumerator.next(variant.discriminant.as_ref().map(|(_, expr)| expr)) {
                        Ok(discriminant) => discriminant,
                        Err(error) => {
                            cx.error(error);
                            break;
                        }
                    };

                let types = &output.types;

                validate_variants.push(quote! {
                    #discriminant => {
                        #(#validator::validate::<#types>(validator)?;)*
                    }
                });

                pad_variants.push(quote! {
                    #discriminant => {
                        #(#padder::pad::<#types>(padder);)*
                    }
                });

                let mut field_sizes = Vec::new();
                let mut field_padded = Vec::new();

                for ty in output.types.iter() {
                    field_sizes.push(quote!(#mem::size_of::<#ty>()));
                    field_padded.push(quote!(<#ty as #zero_copy>::PADDED));
                }

                let base_size = num.size(&mem);

                // Struct does not need to be padded if all elements are the
                // same size and alignment.
                padded_variants.push(quote!((#mem::size_of::<Self>() > (#base_size #(+ #field_sizes)*) #(|| #field_padded)*)));

                variant_fields.push({
                    let pat = build_field_exhaustive_pattern(
                        [name.clone(), variant.ident.clone()],
                        &output,
                        &variant.fields,
                    );
                    quote!(#pat => ())
                });
            }

            pad = quote! {
                // NOTE: this is assumed to be properly, since enums cannot be
                // packed.
                match #padder::pad_discriminant::<#ty>(padder) {
                    #(#pad_variants,)*
                    discriminant => #unknown_discriminant(discriminant),
                }
            };

            let illegal_enum = quote::format_ident!("__illegal_enum_{}", num.as_ty());

            validate = quote! {
                // SAFETY: We've systematically ensured that we're only
                // validating over fields within the size of this type.
                let discriminant = *#validator::field::<#ty>(validator)?;

                match discriminant {
                    #(#validate_variants,)*
                    value => return #result::Err(#error::#illegal_enum::<Self>(value)),
                }
            };

            impl_zero_sized = None;
            any_bits = quote!(false);
            padded = quote!(false #(|| #padded_variants)*);

            let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

            // NB: Since enums can't be packed we can use a reference.
            check_fields = quote!(
                const _: () = {
                    #[allow(unused)]
                    fn check_variant_fields #impl_generics(this: &#name #ty_generics) #where_clause {
                        match this {
                            #(#variant_fields,)*
                        }
                    }
                };
            );
        }
        syn::Data::Union(data) => {
            cx.error(syn::Error::new_spanned(
                data.union_token,
                "ZeroCopy: not supported for unions",
            ));
            return Err(());
        }
    };

    let check_zero_sized = (!check_zero_sized.is_empty()).then(|| {
        let (impl_generics, _, where_clause) = generics.split_for_impl();

        quote! {
            const _: () = {
                fn ensure_zero_sized<T: #zero_sized>() {}

                fn ensure_fields #impl_generics() #where_clause {
                    #(ensure_zero_sized::<#check_zero_sized>();)*
                }
            };
        }
    });

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        #check_zero_sized

        #check_fields

        #impl_zero_sized

        #[automatically_derived]
        unsafe impl #impl_generics #zero_copy for #name #ty_generics #where_clause {
            const ANY_BITS: bool = #any_bits;
            const PADDED: bool = #padded;

            #[inline]
            unsafe fn pad(padder: &mut #padder<'_, Self>) {
                #pad
            }

            #[inline]
            unsafe fn validate(validator: &mut #validator<'_, Self>) -> #result<(), #error> {
                #validate
                #result::Ok(())
            }
        }
    })
}

/// Construct a match pattern with carefully assigned spans to improve
/// diagnostics as much as possible.
fn build_field_exhaustive_pattern<const N: usize>(
    steps: [syn::Ident; N],
    output: &Fields<'_>,
    fields: &syn::Fields,
) -> syn::Pat {
    let mut path = syn::Path {
        leading_colon: None,
        segments: syn::punctuated::Punctuated::default(),
    };

    for step in steps {
        path.segments.push(syn::PathSegment::from(step));
    }

    match fields {
        syn::Fields::Named(named) => {
            let mut fields = syn::punctuated::Punctuated::new();

            for member in &output.exhaustive {
                fields.push(syn::FieldPat {
                    attrs: Vec::new(),
                    member: member.clone(),
                    colon_token: None,
                    pat: Box::new(syn::Pat::Verbatim(quote!(#member))),
                });
            }

            syn::Pat::Struct(syn::PatStruct {
                attrs: Vec::new(),
                qself: None,
                path: path.clone(),
                brace_token: named.brace_token,
                fields,
                rest: None,
            })
        }
        syn::Fields::Unnamed(unnamed) => {
            let mut elems = syn::punctuated::Punctuated::new();

            for _ in &output.exhaustive {
                elems.push(syn::Pat::Wild(syn::PatWild {
                    attrs: Vec::new(),
                    underscore_token: <syn::Token![_]>::default(),
                }));
            }

            syn::Pat::TupleStruct(syn::PatTupleStruct {
                attrs: Vec::new(),
                qself: None,
                path: path.clone(),
                paren_token: unnamed.paren_token,
                elems,
            })
        }
        syn::Fields::Unit => syn::Pat::Path(syn::ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: path.clone(),
        }),
    }
}

#[derive(Default)]
struct Fields<'a> {
    types: Vec<&'a syn::Type>,
    exhaustive: Vec<syn::Member>,
    first_field: Option<&'a syn::Type>,
    check_zero_sized: Vec<&'a syn::Type>,
}

fn process_fields<'a>(cx: &Ctxt, fields: &'a syn::Fields) -> Fields<'a> {
    let mut output = Fields::default();

    for (index, field) in fields.iter().enumerate() {
        let mut ignore = None;

        for attr in &field.attrs {
            if attr.path().is_ident("zero_copy") {
                let result = attr.parse_nested_meta(|meta: ParseNestedMeta| {
                    if meta.path.is_ident("ignore") {
                        ignore = Some(meta.path.span());
                        return Ok(());
                    }

                    Err(syn::Error::new(
                        meta.input.span(),
                        "ZeroCopy: Unsupported attribute",
                    ))
                });

                if let Err(error) = result {
                    cx.error(error);
                }
            }
        }

        let ty = &field.ty;

        let member = match &field.ident {
            Some(ident) => syn::Member::Named(ident.clone()),
            None => syn::Member::Unnamed(syn::Index::from(index)),
        };

        // Ignored fields are ignored in bindings.
        output.exhaustive.push(member.clone());

        if ignore.is_some() {
            output.check_zero_sized.push(ty);
            continue;
        }

        output.types.push(ty);

        if output.first_field.is_none() {
            output.first_field = Some(ty);
        }
    }

    output
}

#[derive(Default)]
struct ReprAttr {
    repr: Option<(Span, Repr)>,
    repr_align: Option<usize>,
    repr_packed: Option<(Span, usize)>,
}

impl ReprAttr {
    fn parse_attr(&mut self, cx: &Ctxt, attr: &syn::Attribute) {
        let result = attr.parse_nested_meta(|meta| {
            macro_rules! repr {
                ($ident:ident, $variant:expr) => {
                    if meta.path.is_ident(stringify!($ident)) {
                        if self.repr.is_some() {
                            return Err(syn::Error::new_spanned(
                                meta.path,
                                "ZeroCopy: only one kind of repr is supported",
                            ));
                        }

                        self.repr = Some((meta.path.span(), $variant));
                        return Ok(());
                    }
                };
            }

            repr!(C, Repr::C);
            repr!(transparent, Repr::Transparent);
            repr!(u8, Repr::Num(meta.path.span(), NumericalRepr::U8));
            repr!(u16, Repr::Num(meta.path.span(), NumericalRepr::U16));
            repr!(u32, Repr::Num(meta.path.span(), NumericalRepr::U32));
            repr!(u64, Repr::Num(meta.path.span(), NumericalRepr::U64));
            repr!(u128, Repr::Num(meta.path.span(), NumericalRepr::U128));
            repr!(i8, Repr::Num(meta.path.span(), NumericalRepr::I8));
            repr!(i16, Repr::Num(meta.path.span(), NumericalRepr::I16));
            repr!(i32, Repr::Num(meta.path.span(), NumericalRepr::I32));
            repr!(i64, Repr::Num(meta.path.span(), NumericalRepr::I64));
            repr!(i128, Repr::Num(meta.path.span(), NumericalRepr::I128));
            repr!(isize, Repr::Num(meta.path.span(), NumericalRepr::Isize));
            repr!(Usize, Repr::Num(meta.path.span(), NumericalRepr::Usize));

            // #[repr(align(N))]
            if meta.path.is_ident("align") {
                let content;
                parenthesized!(content in meta.input);
                let lit: syn::LitInt = content.parse()?;
                let n: usize = lit.base10_parse()?;
                self.repr_align = Some(n);
                return Ok(());
            }

            // #[repr(packed)] or #[repr(packed(N))], omitted N means 1
            if meta.path.is_ident("packed") {
                if meta.input.peek(syn::token::Paren) {
                    let content;
                    parenthesized!(content in meta.input);
                    let lit: syn::LitInt = content.parse()?;
                    let n: usize = lit.base10_parse()?;
                    self.repr_packed = Some((meta.input.span(), n));
                } else {
                    self.repr_packed = Some((meta.input.span(), 1));
                }
                return Ok(());
            }

            Err(syn::Error::new_spanned(
                meta.path,
                "ZeroCopy: unsupported #[repr(..)]",
            ))
        });

        if let Err(error) = result {
            cx.error(error);
        }
    }
}

#[derive(Clone, Copy)]
enum Repr {
    C,
    Transparent,
    Num(Span, NumericalRepr),
}

impl Repr {
    fn as_numerical_repr(self) -> Option<(Span, NumericalRepr)> {
        match self {
            Repr::C => None,
            Repr::Transparent => None,
            Repr::Num(span, num) => Some((span, num)),
        }
    }
}
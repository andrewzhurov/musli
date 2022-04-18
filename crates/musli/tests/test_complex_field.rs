use musli::{Decode, Encode};

#[derive(Debug, Encode, Decode, PartialEq, Eq)]
struct FieldVariantTag<'a> {
    name: &'a str,
}

#[derive(Debug, PartialEq, Eq, Encode, Decode)]
#[musli(transparent)]
struct BytesTag<'a>(&'a [u8]);

#[derive(Debug, PartialEq, Eq, Encode, Decode)]
#[musli(transparent)]
struct BytesTagVec(Vec<u8>);

/// A custom tag.
const CUSTOM_TAG1: FieldVariantTag = FieldVariantTag { name: "field1" };
const CUSTOM_TAG2: FieldVariantTag = FieldVariantTag { name: "field2" };

#[derive(Debug, PartialEq, Encode, Decode)]
pub struct StructCustomFieldAsStruct {
    #[musli(tag = CUSTOM_TAG1)]
    field1: u32,
    #[musli(tag = CUSTOM_TAG2)]
    field2: u32,
}

#[test]
fn test_bytes_tag_vec() {
    musli_wire::test::rt(BytesTagVec(b"hello world".to_vec()));
}

#[test]
fn test_custom_struct_tag() {
    musli_wire::test::rt(StructCustomFieldAsStruct {
        field1: 42,
        field2: 84,
    });
}

#[derive(Debug, PartialEq, Encode, Decode)]
#[musli(tag_type = [u8; 4])]
pub struct StructCustomTag {
    #[musli(tag = [1, 2, 3, 4])]
    field1: u32,
    #[musli(tag = [2, 3, 4, 5])]
    field2: u32,
}

#[test]
fn test_custom_tag() {
    musli_wire::test::rt(StructCustomTag {
        field1: 42,
        field2: 84,
    });
}

#[derive(Debug, PartialEq, Encode, Decode)]
#[musli(tag_type = BytesTag)]
struct StructWithBytesTag {
    #[musli(tag = BytesTag(b"name in bytes"))]
    string: String,
}

#[test]
fn test_struct_with_bytes_tag() {
    musli_wire::test::rt(StructWithBytesTag {
        string: String::from("Some String"),
    });
}

#[derive(Debug, PartialEq, Encode, Decode)]
#[musli(tag_type = BytesTag)]
enum EnumWithBytesTag {
    #[musli(tag = BytesTag(b"a"))]
    Variant1 { string: String },
    #[musli(tag = BytesTag(b"b"), tag_type = BytesTag)]
    Variant2 {
        #[musli(tag = BytesTag(b"c"))]
        string: String,
    },
}

#[test]
fn test_bytes_tag_in_enum() {
    musli_wire::test::rt(EnumWithBytesTag::Variant1 {
        string: String::from("st"),
    });

    musli_wire::test::rt(EnumWithBytesTag::Variant2 {
        string: String::from("st"),
    });
}
#![allow(dead_code)]

use bstr::BStr;
use musli::{Decode, Encode};

#[derive(Encode, Decode)]
#[musli(name_type = &str)]
struct StructStr {
    #[musli(name = "field1")]
    field1: u32,
    #[musli(name = "field2")]
    field2: u32,
}

#[derive(Encode, Decode)]
#[musli(name_type = [u8], name_format_with = BStr::new)]
struct StructBytes {
    #[musli(name = &[b'f', b'i', b'e', b'l', b'd', b'1'])]
    field1: u32,
    #[musli(name = &[b'f', b'i', b'e', b'l', b'd', b'2'])]
    field2: u32,
}

#[derive(Encode, Decode)]
#[musli(name_type = [u8], name_format_with = BStr::new)]
struct StructBytesArray {
    #[musli(name = b"field1")]
    field1: u32,
    #[musli(name = b"field2")]
    field2: u32,
}

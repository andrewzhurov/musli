#[cfg(not(feature = "no-map"))]
use std::collections::HashMap;
use std::collections::HashSet;

#[cfg(not(feature = "no-btree"))]
use std::collections::{BTreeMap, BTreeSet};

use core::ops::Range;

#[cfg(not(feature = "no-cstring"))]
use alloc::ffi::CString;
use alloc::string::String;
use alloc::vec::Vec;

#[cfg(feature = "musli-zerocopy")]
use musli_zerocopy::ZeroCopy;

#[cfg(feature = "zerocopy")]
use zerocopy::{AsBytes, FromBytes, FromZeroes};

#[cfg(feature = "musli")]
use musli::{Decode, Encode};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "musli")]
use crate::mode::Packed;

use crate::generate::Generate;
pub use rand::prelude::*;

miri! {
    pub const PRIMITIVES_RANGE: Range<usize> = 10..100, 1..3;
    pub const MEDIUM_RANGE: Range<usize> = 10..100, 1..3;
    pub const SMALL_FIELDS: Range<usize> = 1..3, 1..2;
}

#[derive(Debug, Clone, Copy, PartialEq, Generate)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "musli", derive(Encode, Decode))]
#[cfg_attr(feature = "musli-zerocopy", derive(ZeroCopy))]
#[cfg_attr(feature = "bitcode-derive", derive(bitcode::Encode, bitcode::Decode))]
#[cfg_attr(feature = "zerocopy", derive(AsBytes, FromBytes, FromZeroes))]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize),
    archive(compare(PartialEq), check_bytes),
    archive_attr(derive(Debug))
)]
#[cfg_attr(any(feature = "musli-zerocopy", feature = "zerocopy"), repr(C))]
pub struct PrimitivesPacked {
    unsigned8: u8,
    #[cfg_attr(feature = "musli", musli(bytes))]
    _pad0: [u8; 1],
    unsigned16: u16,
    unsigned32: u32,
    unsigned64: u64,
    #[cfg(not(feature = "no-128"))]
    unsigned128: u128,
    signed8: i8,
    #[cfg_attr(feature = "musli", musli(bytes))]
    _pad1: [u8; 1],
    signed16: i16,
    signed32: i32,
    signed64: i64,
    #[cfg(not(feature = "no-128"))]
    signed128: i128,
    #[cfg(not(feature = "no-usize"))]
    unsignedsize: usize,
    #[cfg(not(feature = "no-usize"))]
    signedsize: isize,
    float32: f32,
    #[cfg_attr(feature = "musli", musli(bytes))]
    _pad3: [u8; 4],
    float64: f64,
}

#[cfg(feature = "rkyv")]
impl PartialEq<PrimitivesPacked> for &ArchivedPrimitivesPacked {
    #[inline]
    fn eq(&self, other: &PrimitivesPacked) -> bool {
        *other == **self
    }
}

impl PartialEq<PrimitivesPacked> for &PrimitivesPacked {
    #[inline]
    fn eq(&self, other: &PrimitivesPacked) -> bool {
        *other == **self
    }
}

#[derive(Debug, Clone, PartialEq, Generate)]
#[cfg_attr(feature = "musli-zerocopy", derive(ZeroCopy))]
#[cfg_attr(feature = "musli", derive(Encode, Decode))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "bitcode-derive", derive(bitcode::Encode, bitcode::Decode))]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize),
    archive(compare(PartialEq), check_bytes),
    archive_attr(derive(Debug))
)]
#[cfg_attr(feature = "musli", musli(mode = Packed, packed))]
#[cfg_attr(feature = "musli-zerocopy", repr(C))]
pub struct Primitives {
    boolean: bool,
    character: char,
    unsigned8: u8,
    unsigned16: u16,
    unsigned32: u32,
    unsigned64: u64,
    #[cfg(not(feature = "no-128"))]
    unsigned128: u128,
    signed8: i8,
    signed16: i16,
    signed32: i32,
    signed64: i64,
    #[cfg(not(feature = "no-128"))]
    signed128: i128,
    #[cfg(not(feature = "no-usize"))]
    unsignedsize: usize,
    #[cfg(not(feature = "no-usize"))]
    signedsize: isize,
    #[cfg(not(feature = "no-float"))]
    float32: f32,
    #[cfg(not(feature = "no-float"))]
    float64: f64,
}

#[cfg(feature = "rkyv")]
impl PartialEq<Primitives> for &ArchivedPrimitives {
    #[inline]
    fn eq(&self, other: &Primitives) -> bool {
        *other == **self
    }
}

impl PartialEq<Primitives> for &Primitives {
    #[inline]
    fn eq(&self, other: &Primitives) -> bool {
        *other == **self
    }
}

#[derive(Debug, Clone, PartialEq, Generate)]
#[cfg_attr(feature = "musli", derive(Encode, Decode))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "bitcode-derive", derive(bitcode::Encode, bitcode::Decode))]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize),
    archive(compare(PartialEq), check_bytes),
    archive_attr(derive(Debug))
)]
#[cfg_attr(feature = "musli", musli(mode = Packed, packed))]
pub struct Allocated {
    string: String,
    #[cfg_attr(feature = "musli", musli(bytes))]
    #[generate(range = SMALL_FIELDS)]
    bytes: Vec<u8>,
    #[cfg(all(not(feature = "no-map"), not(feature = "no-number-key")))]
    #[generate(range = SMALL_FIELDS)]
    number_map: HashMap<u32, u64>,
    #[cfg(all(not(feature = "no-map"), not(feature = "no-string-key")))]
    #[generate(range = SMALL_FIELDS)]
    string_map: HashMap<String, u64>,
    #[generate(range = SMALL_FIELDS)]
    number_set: HashSet<u32>,
    #[generate(range = SMALL_FIELDS)]
    #[cfg(not(feature = "no-string-set"))]
    string_set: HashSet<String>,
    #[cfg(all(not(feature = "no-btree"), not(feature = "no-number-key")))]
    #[generate(range = SMALL_FIELDS)]
    number_btree: BTreeMap<u32, u64>,
    #[cfg(not(feature = "no-btree"))]
    #[generate(range = SMALL_FIELDS)]
    string_btree: BTreeMap<String, u64>,
    #[cfg(not(feature = "no-btree"))]
    #[generate(range = SMALL_FIELDS)]
    number_btree_set: BTreeSet<u32>,
    #[cfg(not(feature = "no-btree"))]
    #[generate(range = SMALL_FIELDS)]
    string_btree_set: BTreeSet<String>,
    #[cfg(not(feature = "no-cstring"))]
    c_string: CString,
}

#[cfg(feature = "rkyv")]
impl PartialEq<Allocated> for &ArchivedAllocated {
    #[inline]
    fn eq(&self, other: &Allocated) -> bool {
        *other == **self
    }
}

impl PartialEq<Allocated> for &Allocated {
    #[inline]
    fn eq(&self, other: &Allocated) -> bool {
        *other == **self
    }
}

#[derive(Debug, Clone, PartialEq, Generate)]
#[cfg_attr(feature = "musli", derive(Encode, Decode))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "bitcode-derive", derive(bitcode::Encode, bitcode::Decode))]
#[cfg_attr(feature = "musli", musli(mode = Packed, packed))]
pub struct Tuples {
    u0: (),
    u1: (bool,),
    u2: (bool, u8),
    u3: (bool, u8, u32),
    u4: (bool, u8, u32, u64),
    #[cfg(not(feature = "no-float"))]
    u5: (bool, u8, u32, u64, f32),
    #[cfg(not(feature = "no-float"))]
    u6: (bool, u8, u32, u64, f32, f64),
    i0: (),
    i1: (bool,),
    i2: (bool, i8),
    i3: (bool, i8, i32),
    i4: (bool, i8, i32, i64),
    #[cfg(not(feature = "no-float"))]
    i5: (bool, i8, i32, i64, f32),
    #[cfg(not(feature = "no-float"))]
    i6: (bool, i8, i32, i64, f32, f64),
}

impl PartialEq<Tuples> for &Tuples {
    #[inline]
    fn eq(&self, other: &Tuples) -> bool {
        *other == **self
    }
}

#[derive(Debug, Clone, PartialEq, Generate)]
#[cfg_attr(feature = "musli", derive(Encode, Decode))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "bitcode-derive", derive(bitcode::Encode, bitcode::Decode))]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize),
    archive(compare(PartialEq), check_bytes),
    archive_attr(derive(Debug))
)]
#[cfg_attr(feature = "musli", musli(mode = Packed))]
pub enum MediumEnum {
    #[cfg(not(feature = "no-empty"))]
    Empty,
    EmptyTuple(),
    #[cfg_attr(feature = "musli", musli(transparent))]
    #[cfg(not(feature = "no-newtype"))]
    NewType(u64),
    Tuple(u64, u64),
    #[cfg_attr(feature = "musli", musli(transparent))]
    #[cfg(not(feature = "no-newtype"))]
    NewTypeString(String),
    TupleString(String, Vec<u8>),
    Struct {
        a: u32,
        primitives: Primitives,
        b: u64,
    },
    EmptyStruct {},
}

#[cfg(feature = "rkyv")]
impl PartialEq<MediumEnum> for &ArchivedMediumEnum {
    #[inline]
    fn eq(&self, other: &MediumEnum) -> bool {
        *other == **self
    }
}

impl PartialEq<MediumEnum> for &MediumEnum {
    #[inline]
    fn eq(&self, other: &MediumEnum) -> bool {
        *other == **self
    }
}

#[derive(Debug, Clone, PartialEq, Generate)]
#[cfg_attr(feature = "musli", derive(Encode, Decode))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "bitcode-derive", derive(bitcode::Encode, bitcode::Decode))]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize),
    archive(compare(PartialEq), check_bytes),
    archive_attr(derive(Debug))
)]
#[cfg_attr(feature = "musli", musli(mode = Packed, packed))]
pub struct LargeStruct {
    #[generate(range = PRIMITIVES_RANGE)]
    primitives: Vec<Primitives>,
    #[cfg(not(any(feature = "no-vec", feature = "no-tuple")))]
    #[generate(range = PRIMITIVES_RANGE)]
    tuples: Vec<(Tuples, Tuples)>,
    #[generate(range = MEDIUM_RANGE)]
    medium_vec: Vec<MediumEnum>,
    #[cfg(all(not(feature = "no-map"), not(feature = "no-string-key")))]
    #[generate(range = MEDIUM_RANGE)]
    medium_map: HashMap<String, MediumEnum>,
    #[cfg(all(not(feature = "no-map"), not(feature = "no-string-key")))]
    string_keys: HashMap<String, u64>,
    #[cfg(all(not(feature = "no-map"), not(feature = "no-number-key")))]
    number_map: HashMap<u32, u64>,
    #[cfg(not(feature = "no-tuple"))]
    number_vec: Vec<(u32, u64)>,
}

#[cfg(feature = "rkyv")]
impl PartialEq<LargeStruct> for &ArchivedLargeStruct {
    #[inline]
    fn eq(&self, other: &LargeStruct) -> bool {
        *other == **self
    }
}

impl PartialEq<LargeStruct> for &LargeStruct {
    #[inline]
    fn eq(&self, other: &LargeStruct) -> bool {
        *other == **self
    }
}

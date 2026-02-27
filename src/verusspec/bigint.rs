// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::float_cmp,
    clippy::unwrap_used,
    clippy::unreachable,
    clippy::option_if_let_else,
    clippy::unseparated_literal_suffix,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use num_bigint::BigInt;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExNumBigInt(num_bigint::BigInt);

pub assume_specification[ <BigInt as Clone>::clone ](n: &BigInt) -> (res: BigInt)
    ensures
        res == n,
;

pub trait BigIntAdditionalSpecFns {
    spec fn view(&self) -> int;
}

impl BigIntAdditionalSpecFns for BigInt {
    uninterp spec fn view(&self) -> int;
}

// Conditions

pub assume_specification[ <BigInt as num_traits::Zero>::is_zero ](x: &BigInt) -> (res: bool)
    ensures
        res == (x@ == 0),
;

pub assume_specification[ <BigInt as num_traits::Signed>::is_negative ](x: &BigInt) -> (res: bool)
    ensures
        res == (x@ < 0),
;

// From

pub assume_specification[ <BigInt as core::convert::From<i64>>::from ](i: i64) -> (res: BigInt)
    ensures
        res@ == i,
;

pub assume_specification[ <BigInt as core::convert::From<i128>>::from ](i: i128) -> (res: BigInt)
    ensures
        res@ == i,
;

pub assume_specification[ <BigInt as core::convert::From<u64>>::from ](u: u64) -> (res: BigInt)
    ensures
        res@ == u,
;

pub assume_specification[ <BigInt as core::convert::From<u128>>::from ](u: u128) -> (res: BigInt)
    ensures
        res@ == u,
;

// ToPrimitive

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(ToPrimitiveSpec via ToPrimitiveSpecImpl)]
pub trait ExToPrimitive {
    type ExternalTraitSpecificationFor: num_traits::ToPrimitive;

    spec fn obeys_to_primitive_spec() -> bool;

    spec fn spec_to_int(&self) -> Option<int>;

    fn to_isize(&self) -> (res: Option<isize>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(isize::MIN <= n <= isize::MAX),
                },
        default_ensures
            true,
    ;

    fn to_i8(&self) -> (res: Option<i8>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(i8::MIN <= n <= i8::MAX),
                },
        default_ensures
            true,
    ;

    fn to_i16(&self) -> (res: Option<i16>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(i16::MIN <= n <= i16::MAX),
                },
        default_ensures
            true,
    ;

    fn to_i32(&self) -> (res: Option<i32>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(i32::MIN <= n <= i32::MAX),
                },
        default_ensures
            true,
    ;

    fn to_i64(&self) -> (res: Option<i64>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(i64::MIN <= n <= i64::MAX),
                },
    ;

    fn to_i128(&self) -> (res: Option<i128>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(i128::MIN <= n <= i128::MAX),
                },
        default_ensures
            true,
    ;

    fn to_usize(&self) -> (res: Option<usize>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(usize::MIN <= n <= usize::MAX),
                },
        default_ensures
            true,
    ;

    fn to_u8(&self) -> (res: Option<u8>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(u8::MIN <= n <= u8::MAX),
                },
        default_ensures
            true,
    ;

    fn to_u16(&self) -> (res: Option<u16>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(u16::MIN <= n <= u16::MAX),
                },
        default_ensures
            true,
    ;

    fn to_u32(&self) -> (res: Option<u32>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(u32::MIN <= n <= u32::MAX),
                },
        default_ensures
            true,
    ;

    fn to_u64(&self) -> (res: Option<u64>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(u64::MIN <= n <= u64::MAX),
                },
    ;

    fn to_u128(&self) -> (res: Option<u128>)
        ensures
            Self::obeys_to_primitive_spec() ==>
                match (self.spec_to_int(), res) {
                    (None, None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 == n2,
                    (Some(n), None) => !(u128::MIN <= n <= u128::MAX),
                },
        default_ensures
            true,
    ;

    spec fn spec_to_f32(&self) -> Option<f32>;

    fn to_f32(&self) -> (res: Option<f32>)
        ensures
            Self::obeys_to_primitive_spec() ==> res == self.spec_to_f32(),
        default_ensures
            true,
    ;

    spec fn spec_to_f64(&self) -> Option<f64>;

    fn to_f64(&self) -> (res: Option<f64>)
        ensures
            Self::obeys_to_primitive_spec() ==> res == self.spec_to_f64(),
        default_ensures
            true,
    ;
}

impl ToPrimitiveSpecImpl for num_bigint::BigInt
{
    open spec fn obeys_to_primitive_spec() -> bool
    {
        true
    }

    open spec fn spec_to_int(&self) -> Option<int>
    {
        Some(self@)
    }

    uninterp spec fn spec_to_f32(&self) -> Option<f32>;

    uninterp spec fn spec_to_f64(&self) -> Option<f64>;
}

// These are the methods of ToPrimitive that BigInt implements because there is no default in ToPrimitive
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_i64 ](x: &BigInt) -> (res: Option<i64>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_u64 ](x: &BigInt) -> (res: Option<u64>);

// These are the methods of ToPrimitive that BigInt overrides the defaults for because they'd otherwise be wrong
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_i128 ](x: &BigInt) -> (res: Option<i128>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_u128 ](x: &BigInt) -> (res: Option<u128>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_f32 ](x: &BigInt) -> (res: Option<f32>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_f64 ](x: &BigInt) -> (res: Option<f64>);

// Negation

pub assume_specification[ <BigInt as core::ops::Neg>::neg ](x: BigInt) -> (y: BigInt)
    ensures
        y@ == -x@,
;

// Addition

pub assume_specification[ <BigInt as core::ops::Add>::add ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ + y@,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&BigInt>>::add ](x: BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == x@ + (*y)@,
;

pub assume_specification<'a, 'b>[ <&BigInt as core::ops::Add<&BigInt>>::add ](x: &'b BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == (*x)@ + (*y)@,
;

pub assume_specification[ <BigInt as core::ops::Add<u8>>::add ](x: BigInt, y: u8) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<u16>>::add ](x: BigInt, y: u16) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<u32>>::add ](x: BigInt, y: u32) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<u64>>::add ](x: BigInt, y: u64) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<u128>>::add ](x: BigInt, y: u128) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<i8>>::add ](x: BigInt, y: i8) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<i16>>::add ](x: BigInt, y: i16) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<i32>>::add ](x: BigInt, y: i32) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<i64>>::add ](x: BigInt, y: i64) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification[ <BigInt as core::ops::Add<i128>>::add ](x: BigInt, y: i128) -> (o: BigInt)
    ensures
        o@ == x@ + y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&u8>>::add ](x: BigInt, y: &u8) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&u16>>::add ](x: BigInt, y: &u16) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&u32>>::add ](x: BigInt, y: &u32) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&u64>>::add ](x: BigInt, y: &u64) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&u128>>::add ](x: BigInt, y: &u128) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&i8>>::add ](x: BigInt, y: &i8) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&i16>>::add ](x: BigInt, y: &i16) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&i32>>::add ](x: BigInt, y: &i32) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&i64>>::add ](x: BigInt, y: &i64) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Add<&i128>>::add ](x: BigInt, y: &i128) -> (o: BigInt)
    ensures
        o@ == x@ + *y,
;

// Subtraction

pub assume_specification[ <BigInt as core::ops::Sub>::sub ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ - y@,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&BigInt>>::sub ](x: BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == x@ - (*y)@,
;

pub assume_specification<'a, 'b>[ <&BigInt as core::ops::Sub<&BigInt>>::sub ](x: &'b BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == (*x)@ - (*y)@,
;

pub assume_specification[ <BigInt as core::ops::Sub<u8>>::sub ](x: BigInt, y: u8) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<u16>>::sub ](x: BigInt, y: u16) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<u32>>::sub ](x: BigInt, y: u32) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<u64>>::sub ](x: BigInt, y: u64) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<u128>>::sub ](x: BigInt, y: u128) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<i8>>::sub ](x: BigInt, y: i8) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<i16>>::sub ](x: BigInt, y: i16) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<i32>>::sub ](x: BigInt, y: i32) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<i64>>::sub ](x: BigInt, y: i64) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification[ <BigInt as core::ops::Sub<i128>>::sub ](x: BigInt, y: i128) -> (o: BigInt)
    ensures
        o@ == x@ - y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&u8>>::sub ](x: BigInt, y: &u8) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&u16>>::sub ](x: BigInt, y: &u16) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&u32>>::sub ](x: BigInt, y: &u32) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&u64>>::sub ](x: BigInt, y: &u64) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&u128>>::sub ](x: BigInt, y: &u128) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&i8>>::sub ](x: BigInt, y: &i8) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&i16>>::sub ](x: BigInt, y: &i16) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&i32>>::sub ](x: BigInt, y: &i32) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&i64>>::sub ](x: BigInt, y: &i64) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Sub<&i128>>::sub ](x: BigInt, y: &i128) -> (o: BigInt)
    ensures
        o@ == x@ - *y,
;

// Multiplication

pub assume_specification[ <BigInt as core::ops::Mul>::mul ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ * y@,
;

pub assume_specification<'a>[ <BigInt as core::ops::Mul<&BigInt>>::mul ](x: BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == x@ * (*y)@,
;

pub assume_specification<'a, 'b>[ <&BigInt as core::ops::Mul<&BigInt>>::mul ](x: &'b BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == (*x)@ * (*y)@,
;

pub assume_specification[ <BigInt as core::ops::Mul<u8>>::mul ](x: BigInt, y: u8) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<u16>>::mul ](x: BigInt, y: u16) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<u32>>::mul ](x: BigInt, y: u32) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<u64>>::mul ](x: BigInt, y: u64) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<u128>>::mul ](x: BigInt, y: u128) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<i8>>::mul ](x: BigInt, y: i8) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<i16>>::mul ](x: BigInt, y: i16) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<i32>>::mul ](x: BigInt, y: i32) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<i64>>::mul ](x: BigInt, y: i64) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification[ <BigInt as core::ops::Mul<i128>>::mul ](x: BigInt, y: i128) -> (o: BigInt)
    ensures
        o@ == x@ * y,
;

pub assume_specification<'a>[ <BigInt as core::ops::Mul<&u8>>::mul ](x: BigInt, y: &u8) -> (o: BigInt)
    ensures
        o@ == x@ * *y,
;

// Division

pub assume_specification[ <BigInt as core::ops::Div>::div ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ / y@,
;

pub assume_specification<'a>[ <BigInt as core::ops::Div<&BigInt>>::div ](x: BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == x@ / (*y)@,
;

pub assume_specification<'a, 'b>[ <&BigInt as core::ops::Div<&BigInt>>::div ](x: &'b BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        o@ == (*x)@ / (*y)@,
;

pub assume_specification[ <BigInt as core::ops::Div<u8>>::div ](x: BigInt, y: u8) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u16>>::div ](x: BigInt, y: u16) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u32>>::div ](x: BigInt, y: u32) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u64>>::div ](x: BigInt, y: u64) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u128>>::div ](x: BigInt, y: u128) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i8>>::div ](x: BigInt, y: i8) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i16>>::div ](x: BigInt, y: i16) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i32>>::div ](x: BigInt, y: i32) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i64>>::div ](x: BigInt, y: i64) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i128>>::div ](x: BigInt, y: i128) -> (o: BigInt)
    ensures
        o@ == x@ / (y as int),
;

pub assume_specification<'a>[ <BigInt as core::ops::Div<&u8>>::div ](x: BigInt, y: &u8) -> (o: BigInt)
    ensures
        o@ == x@ / (*y as int),
;

} // end verus!

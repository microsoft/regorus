// This file contains assumptions about the BigInt library, encoded
// in Verus.
//
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

use vstd::prelude::*;

verus! {

use core::cmp::Ordering;
use num_bigint::BigInt;
use vstd::arithmetic::div_mod::{rust_div, rust_rem};
use vstd::arithmetic::power2::pow2;
use vstd::std_specs::cmp::OrdSpec;

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

// BitAnd

pub open spec fn spec_bigint_bitand(lhs: int, rhs: int) -> int
    decreases
        if lhs >= 0 { lhs } else { -(lhs + 1) },
        if rhs >= 0 { rhs } else { -(rhs + 1) }
{
    let lsb: int = if (lhs % 2 == 1) && (rhs % 2 == 1) { 1int } else { 0int };
    if (lhs == 0 || lhs == -1) && (rhs == 0 || rhs == -1) {
        -lsb
    }
    else {
        spec_bigint_bitand(lhs / 2, rhs / 2) * 2 + lsb
    }
}

// To help demonstrate that the spec for `spec_bigint_bitand` is
// valid, prove that it's equivalent to `&` for arbitrary `i16`
// values. (Using 16 bits is enough for high confidence, and doesn't
// tax the bit-vector solver.)
proof fn lemma_test_spec_bigint_bitand_for_i16(lhs: i16, rhs: i16)
    ensures
        spec_bigint_bitand(lhs as int, rhs as int) == (lhs & rhs) as int,
    decreases
        if lhs >= 0 { lhs as int } else { -(lhs + 1) },
        if rhs >= 0 { rhs as int } else { -(rhs + 1) }
{
    let lsb: i16 = if (lhs % 2 == 1) && (rhs % 2 == 1) { 1i16 } else { 0i16 };
    if (lhs == 0 || lhs == -1) && (rhs == 0 || rhs == -1) {
        assert(-lsb == lhs & rhs) by (bit_vector)
            requires
                lhs == 0 || lhs == -1,
                rhs == 0 || rhs == -1,
                lsb == if (lhs % 2 == 1) && (rhs % 2 == 1) { 1i16 } else { 0i16 },
        ;
    }
    else {
        lemma_test_spec_bigint_bitand_for_i16((lhs / 2) as i16, (rhs / 2) as i16);
        assert(((lhs / 2) as i16 & (rhs / 2) as i16) * 2 + lsb == lhs & rhs) by (bit_vector)
            requires
                lsb == if (lhs % 2 == 1) && (rhs % 2 == 1) { 1i16 } else { 0i16 },
        ;
    }
}

// To help demonstrate that the spec for `spec_bigint_bitand`
// corresponds to what's implemented by the BigInt library, prove that
// its results match examples given in comments at:
// https://docs.rs/num-bigint/latest/src/num_bigint/bigint/bits.rs.html
proof fn lemma_test_spec_bigint_bitand_with_examples()
    ensures
        // From documentation for bitand_pos_neg:
        spec_bigint_bitand(1, -0xff) == 1,
        spec_bigint_bitand(0xff, -1) == 0xff,
        // From documentation for bitand_neg_pos:
        spec_bigint_bitand(-1, 0xff) == 0xff,
        spec_bigint_bitand(-0xff, 1) == 1,
        // From documentation for bitand_neg_neg:
        spec_bigint_bitand(-1, -0xff) == -0xff,
        spec_bigint_bitand(-0xff, -1) == -0xff,
        spec_bigint_bitand(-0xff, -0xfe) == -0x100,
{
    assert(spec_bigint_bitand(1, -0xff) == 1) by (compute);
    assert(spec_bigint_bitand(0xff, -1) == 0xff) by (compute);

    assert(spec_bigint_bitand(-1, 0xff) == 0xff) by (compute);
    assert(spec_bigint_bitand(-0xff, 1) == 1) by (compute);

    assert(spec_bigint_bitand(-1, -0xff) == -0xff) by (compute);
    assert(spec_bigint_bitand(-0xff, -1) == -0xff) by (compute);
    assert(spec_bigint_bitand(-0xff, -0xfe) == -0x100) by (compute);
}

pub axiom fn axiom_bigint_obeys_bitand_spec()
    ensures
        <BigInt as vstd::std_specs::ops::BitAndSpec>::obeys_bitand_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitAndSpec>::bitand_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitAndSpec>::bitand_spec(lhs, rhs)@
                == spec_bigint_bitand(lhs@, rhs@),
;

// BitOr

pub open spec fn spec_bigint_bitor(lhs: int, rhs: int) -> int
    decreases
        if lhs >= 0 { lhs } else { -(lhs + 1) },
        if rhs >= 0 { rhs } else { -(rhs + 1) }
{
    let lsb: int = if (lhs % 2 == 1) || (rhs % 2 == 1) { 1int } else { 0int };
    if (lhs == 0 || lhs == -1) && (rhs == 0 || rhs == -1) {
        -lsb
    }
    else {
        spec_bigint_bitor(lhs / 2, rhs / 2) * 2 + lsb
    }
}

// To help demonstrate that the spec for `spec_bigint_bitor` is
// valid, prove that it's equivalent to `|` for arbitrary `i16`
// values. (Using 16 bits is enough for high confidence, and doesn't
// tax the bit-vector solver.)
proof fn lemma_test_spec_bigint_bitor_for_i16(lhs: i16, rhs: i16)
    ensures
        spec_bigint_bitor(lhs as int, rhs as int) == (lhs | rhs) as int,
    decreases
        if lhs >= 0 { lhs as int } else { -(lhs + 1) },
        if rhs >= 0 { rhs as int } else { -(rhs + 1) }
{
    let lsb: i16 = if (lhs % 2 == 1) || (rhs % 2 == 1) { 1i16 } else { 0i16 };
    if (lhs == 0 || lhs == -1) && (rhs == 0 || rhs == -1) {
        assert(-lsb == lhs | rhs) by (bit_vector)
            requires
                lhs == 0 || lhs == -1,
                rhs == 0 || rhs == -1,
                lsb == if (lhs % 2 == 1) || (rhs % 2 == 1) { 1i16 } else { 0i16 },
        ;
    }
    else {
        lemma_test_spec_bigint_bitor_for_i16((lhs / 2) as i16, (rhs / 2) as i16);
        assert(((lhs / 2) as i16 | (rhs / 2) as i16) * 2 + lsb == lhs | rhs) by (bit_vector)
            requires
                lsb == if (lhs % 2 == 1) || (rhs % 2 == 1) { 1i16 } else { 0i16 },
        ;
    }
}

// To help demonstrate that the spec for `spec_bigint_bitor`
// corresponds to what's implemented by the BigInt library, prove that
// its results match examples given in comments at:
// https://docs.rs/num-bigint/latest/src/num_bigint/bigint/bits.rs.html
proof fn lemma_test_spec_bigint_bitor_with_examples()
    ensures
        // From documentation for bitor_pos_neg:
        spec_bigint_bitor(1, -0xff) == -0xff,
        spec_bigint_bitor(0xff, -1) == -1,

        // From documentation for bitor_neg_pos:
        spec_bigint_bitor(-1, 0xff) == -1,
        spec_bigint_bitor(-0xff, 1) == -0xff,

        // From documentation for bitor_neg_neg:
        spec_bigint_bitor(-1, -0xff) == -1,
        spec_bigint_bitor(-0xff, -1) == -1,
{
    assert(spec_bigint_bitor(1, -0xff) == -0xff) by (compute);
    assert(spec_bigint_bitor(0xff, -1) == -1) by (compute);

    assert(spec_bigint_bitor(-1, 0xff) == -1) by (compute);
    assert(spec_bigint_bitor(-0xff, 1) == -0xff) by (compute);

    assert(spec_bigint_bitor(-1, -0xff) == -1) by (compute);
    assert(spec_bigint_bitor(-0xff, -1) == -1) by (compute);
}

pub axiom fn axiom_bigint_obeys_bitor_spec()
    ensures
        <BigInt as vstd::std_specs::ops::BitOrSpec>::obeys_bitor_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitOrSpec>::bitor_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitOrSpec>::bitor_spec(lhs, rhs)@
                == spec_bigint_bitor(lhs@, rhs@),
;

// BitXor

pub open spec fn spec_bigint_bitxor(lhs: int, rhs: int) -> int
    decreases
        if lhs >= 0 { lhs } else { -(lhs + 1) },
        if rhs >= 0 { rhs } else { -(rhs + 1) }
{
    let lsb: int = if (lhs % 2 == 1) != (rhs % 2 == 1) { 1int } else { 0int };
    if (lhs == 0 || lhs == -1) && (rhs == 0 || rhs == -1) {
        -lsb
    }
    else {
        spec_bigint_bitxor(lhs / 2, rhs / 2) * 2 + lsb
    }
}

// To help demonstrate that the spec for `spec_bigint_bitxor` is
// valid, prove that it's equivalent to `^` for arbitrary `i16`
// values. (Using 16 bits is enough for high confidence, and doesn't
// tax the bit-vector solver.)
proof fn lemma_test_spec_bigint_bitxor_for_i16(lhs: i16, rhs: i16)
    ensures
        spec_bigint_bitxor(lhs as int, rhs as int) == (lhs ^ rhs) as int,
    decreases
        if lhs >= 0 { lhs as int } else { -(lhs + 1) },
        if rhs >= 0 { rhs as int } else { -(rhs + 1) }
{
    let lsb: i16 = if (lhs % 2 == 1) != (rhs % 2 == 1) { 1i16 } else { 0i16 };
    if (lhs == 0 || lhs == -1) && (rhs == 0 || rhs == -1) {
        assert(-lsb == lhs ^ rhs) by (bit_vector)
            requires
                lhs == 0 || lhs == -1,
                rhs == 0 || rhs == -1,
                lsb == if (lhs % 2 == 1) != (rhs % 2 == 1) { 1i16 } else { 0i16 },
        ;
    }
    else {
        lemma_test_spec_bigint_bitxor_for_i16((lhs / 2) as i16, (rhs / 2) as i16);
        assert(((lhs / 2) as i16 ^ (rhs / 2) as i16) * 2 + lsb == lhs ^ rhs) by (bit_vector)
            requires
                lsb == if (lhs % 2 == 1) != (rhs % 2 == 1) { 1i16 } else { 0i16 },
        ;
    }
}

// To help demonstrate that the spec for `spec_bigint_bitxor`
// corresponds to what's implemented by the BigInt library, prove that
// its results match examples given in comments at:
// https://docs.rs/num-bigint/latest/src/num_bigint/bigint/bits.rs.html
proof fn lemma_test_spec_bigint_bitxor_with_examples()
    ensures
        // From documentation for bitxor_pos_neg:
        spec_bigint_bitxor(1, -0xff) == -0x100,
        spec_bigint_bitxor(0xff, -1) == -0x100,

        // From documentation for bitxor_neg_pos:
        spec_bigint_bitxor(-1, 0xff) == -0x100,
        spec_bigint_bitxor(-0xff, 1) == -0x100,

        // From documentation for bitxor_neg_neg:
        spec_bigint_bitxor(-1, -0xff) == 0xfe,
        spec_bigint_bitxor(-0xff, -1) == 0xfe,
{
    assert(spec_bigint_bitxor(1, -0xff) == -0x100) by (compute);
    assert(spec_bigint_bitxor(0xff, -1) == -0x100) by (compute);

    assert(spec_bigint_bitxor(-1, 0xff) == -0x100) by (compute);
    assert(spec_bigint_bitxor(-0xff, 1) == -0x100) by (compute);

    assert(spec_bigint_bitxor(-1, -0xff) == 0xfe) by (compute);
    assert(spec_bigint_bitxor(-0xff, -1) == 0xfe) by (compute);
}

pub axiom fn axiom_bigint_obeys_bitxor_spec()
    ensures
        <BigInt as vstd::std_specs::ops::BitXorSpec>::obeys_bitxor_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitXorSpec>::bitxor_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitXorSpec>::bitxor_spec(lhs, rhs)@
                == spec_bigint_bitxor(lhs@, rhs@),
;

// Shift

pub assume_specification[ <BigInt as core::ops::ShrAssign<usize>>::shr_assign ](
    value: &mut BigInt,
    shift: usize,
)
    ensures
        (*final(value))@ == (*old(value))@ / (pow2(shift as nat) as int),
;

pub assume_specification[ <BigInt as core::ops::ShlAssign<usize>>::shl_assign ](
    value: &mut BigInt,
    shift: usize,
)
    ensures
        (*final(value))@ == (*old(value))@ * (pow2(shift as nat) as int),
;

// vstd's op-assignment traits carry an uninterpreted precondition that each
// implementation is free to choose. `num_bigint` imposes no preconditions on
// its op-assignment operators, so they always hold.
pub axiom fn axiom_bigint_shr_assign_req()
    ensures
        forall|value: BigInt, shift: usize| #[trigger]
            <BigInt as vstd::std_specs::ops::ShrAssignSpec<usize>>::shr_assign_req(&value, shift),
;

pub axiom fn axiom_bigint_shl_assign_req()
    ensures
        forall|value: BigInt, shift: usize| #[trigger]
            <BigInt as vstd::std_specs::ops::ShlAssignSpec<usize>>::shl_assign_req(&value, shift),
;

pub axiom fn axiom_bigint_add_assign_req()
    ensures
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddAssignSpec<BigInt>>::add_assign_req(&value, rhs),
;

pub axiom fn axiom_bigint_sub_assign_req()
    ensures
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubAssignSpec<BigInt>>::sub_assign_req(&value, rhs),
;

pub axiom fn axiom_bigint_mul_assign_ref_req()
    ensures
        forall|value: BigInt, rhs: &BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulAssignSpec<&BigInt>>::mul_assign_req(&value, rhs),
;

pub axiom fn axiom_bigint_not_spec(value: BigInt)
    ensures
        <BigInt as vstd::std_specs::ops::NotSpec>::obeys_not_spec(),
        <BigInt as vstd::std_specs::ops::NotSpec>::not_req(value),
        <BigInt as vstd::std_specs::ops::NotSpec>::not_spec(value)@ == -(value@) - 1,
;

// Conditions

pub open spec fn bigint_bits_ensures(value: int, bits: nat) -> bool
{
    &&& -(pow2(bits) as int) < value < pow2(bits)
    &&& forall|n: nat| #![trigger pow2(n)] n < bits ==>
        !( -(pow2(n) as int) < value < pow2(n) )
}

pub assume_specification[ BigInt::bits ](x: &BigInt) -> (res: u64)
    ensures
        bigint_bits_ensures(x@, res as nat),
;

pub assume_specification[ <BigInt as num_traits::Zero>::is_zero ](x: &BigInt) -> (res: bool)
    ensures
        res == (x@ == 0),
;

pub assume_specification[ <BigInt as num_traits::Signed>::is_negative ](x: &BigInt) -> (res: bool)
    ensures
        res == (x@ < 0),
;

pub assume_specification[ <BigInt as num_traits::Signed>::abs ](x: &BigInt) -> (res: BigInt)
    ensures
        res@ == if x@ < 0 { -x@ } else { x@ },
;

// Formatting

// Nothing is promised about the rendered digits; callers only need this to be
// callable from verified code.
pub assume_specification[ BigInt::to_str_radix ](x: &BigInt, radix: u32) -> (res:
    alloc::string::String);

// PartialEq

pub axiom fn axiom_bigint_obeys_eq_spec()
    ensures
        <BigInt as vstd::std_specs::cmp::PartialEqSpec>::obeys_eq_spec(),
;

pub axiom fn axiom_bigint_obeys_partial_cmp_spec()
    ensures
        <BigInt as vstd::std_specs::cmp::PartialOrdSpec>::obeys_partial_cmp_spec(),
;

pub assume_specification[ <BigInt as core::cmp::PartialEq>::eq ](x: &BigInt, y: &BigInt) -> (res: bool)
    ensures
        res == (x@ == y@),
;

// Ord

pub axiom fn axiom_bigint_obeys_cmp_spec()
    ensures
        <BigInt as vstd::std_specs::cmp::OrdSpec>::obeys_cmp_spec(),
        forall|b1: &BigInt, b2: &BigInt| match #[trigger] b1.cmp_spec(b2) {
            Ordering::Less => b1@ < b2@,
            Ordering::Greater => b1@ > b2@,
            Ordering::Equal => b1@ == b2@,
        },
;

pub assume_specification[ <BigInt as core::cmp::Ord>::cmp ](x: &BigInt, y: &BigInt) -> (res: Ordering)
    ensures
        match res {
            Ordering::Less => x@ < y@,
            Ordering::Greater => x@ > y@,
            Ordering::Equal => x@ == y@,
        },
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

pub assume_specification[ <BigInt as core::convert::From<u8>>::from ](u: u8) -> (res: BigInt)
    ensures
        res@ == u,
;

// One

pub assume_specification[ <BigInt as num_traits::One>::one ]() -> (res: BigInt)
    ensures
        res@ == 1,
;

// Negation

pub assume_specification[ <BigInt as core::ops::Neg>::neg ](x: BigInt) -> (y: BigInt)
    ensures
        y@ == -x@,
;

// Addition

pub axiom fn axiom_bigint_obeys_add_spec()
    ensures
        <BigInt as vstd::std_specs::ops::AddSpec>::obeys_add_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddSpec>::add_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddSpec>::add_spec(lhs, rhs)@
                == lhs@ + rhs@,
;

pub assume_specification[ <BigInt as core::ops::Add>::add ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ + y@,
;

pub assume_specification[ <BigInt as core::ops::AddAssign>::add_assign ](
    value: &mut BigInt,
    rhs: BigInt,
)
    ensures
        (*final(value))@ == (*old(value))@ + rhs@,
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

pub axiom fn axiom_bigint_obeys_sub_spec()
    ensures
        <BigInt as vstd::std_specs::ops::SubSpec>::obeys_sub_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubSpec>::sub_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubSpec>::sub_spec(lhs, rhs)@
                == lhs@ - rhs@,
;

pub assume_specification[ <BigInt as core::ops::Sub>::sub ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ - y@,
;

pub assume_specification[ <BigInt as core::ops::SubAssign>::sub_assign ](
    value: &mut BigInt,
    rhs: BigInt,
)
    ensures
        (*final(value))@ == (*old(value))@ - rhs@,
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

pub axiom fn axiom_bigint_obeys_mul_spec()
    ensures
        <BigInt as vstd::std_specs::ops::MulSpec>::obeys_mul_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulSpec>::mul_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulSpec>::mul_spec(lhs, rhs)@
                == lhs@ * rhs@,
;

pub assume_specification[ <BigInt as core::ops::Mul>::mul ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        o@ == x@ * y@,
;

pub assume_specification<'a>[ <BigInt as core::ops::MulAssign<&'a BigInt>>::mul_assign ](
    value: &mut BigInt,
    rhs: &BigInt,
)
    ensures
        (*final(value))@ == (*old(value))@ * rhs@,
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

pub axiom fn axiom_bigint_obeys_div_rem_spec()
    ensures
        <BigInt as vstd::std_specs::ops::DivSpec>::obeys_div_spec(),
        <BigInt as vstd::std_specs::ops::RemSpec>::obeys_rem_spec(),
        forall|lhs: BigInt, rhs: BigInt| rhs@ != 0 ==> #[trigger]
            <BigInt as vstd::std_specs::ops::DivSpec>::div_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| rhs@ != 0 ==> #[trigger]
            <BigInt as vstd::std_specs::ops::RemSpec>::rem_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| rhs@ != 0 ==> #[trigger]
            <BigInt as vstd::std_specs::ops::DivSpec>::div_spec(lhs, rhs)@
                == rust_div(lhs@, rhs@),
        forall|lhs: BigInt, rhs: BigInt| rhs@ != 0 ==> #[trigger]
            <BigInt as vstd::std_specs::ops::RemSpec>::rem_spec(lhs, rhs)@
                == rust_rem(lhs@, rhs@),
;

pub assume_specification[ <BigInt as core::ops::Div>::div ](x: BigInt, y: BigInt) -> (o: BigInt)
    ensures
        y@ != 0 ==> o@ == rust_div(x@, y@),
;

pub assume_specification<'a>[ <BigInt as core::ops::Div<&BigInt>>::div ](x: BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        y@ != 0 ==> o@ == rust_div(x@, (*y)@),
;

pub assume_specification<'a, 'b>[ <&BigInt as core::ops::Div<&BigInt>>::div ](x: &'b BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        y@ != 0 ==> o@ == rust_div((*x)@, (*y)@),
;

pub assume_specification<'a, 'b>[ <&BigInt as core::ops::Rem<&BigInt>>::rem ](x: &'b BigInt, y: &BigInt) -> (o: BigInt)
    ensures
        y@ != 0 ==> o@ == rust_rem((*x)@, (*y)@),
;

pub assume_specification[ <BigInt as core::ops::Div<u8>>::div ](x: BigInt, y: u8) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u16>>::div ](x: BigInt, y: u16) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u32>>::div ](x: BigInt, y: u32) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u64>>::div ](x: BigInt, y: u64) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<u128>>::div ](x: BigInt, y: u128) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i8>>::div ](x: BigInt, y: i8) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i16>>::div ](x: BigInt, y: i16) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i32>>::div ](x: BigInt, y: i32) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i64>>::div ](x: BigInt, y: i64) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification[ <BigInt as core::ops::Div<i128>>::div ](x: BigInt, y: i128) -> (o: BigInt)
    ensures
        y != 0 ==> o@ == rust_div(x@, y as int),
;

pub assume_specification<'a>[ <BigInt as core::ops::Div<&u8>>::div ](x: BigInt, y: &u8) -> (o: BigInt)
    ensures
        *y != 0 ==> o@ == rust_div(x@, *y as int),
;

// Verus's encoding of ToPrimitive relies on an unstable feature
// `sized_hierarchy`, so we can only talk about it when verifying.

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

pub axiom fn axiom_safe_bigints_to_f64()
    ensures
        forall|x: &BigInt| {
            -9_007_199_254_740_992 < x@ < 9_007_199_254_740_992 ==>
                <BigInt as ToPrimitiveSpec>::spec_to_f64(x) is Some
        },
;

// These are the methods of ToPrimitive that BigInt implements because there is no default in ToPrimitive
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_i64 ](x: &BigInt) -> (res: Option<i64>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_u64 ](x: &BigInt) -> (res: Option<u64>);

// These are the methods of ToPrimitive that BigInt overrides the defaults for because they'd otherwise be wrong
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_i128 ](x: &BigInt) -> (res: Option<i128>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_u128 ](x: &BigInt) -> (res: Option<u128>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_f32 ](x: &BigInt) -> (res: Option<f32>);
pub assume_specification[ <num_bigint::BigInt as num_traits::ToPrimitive>::to_f64 ](x: &BigInt) -> (res: Option<f64>);

} // end verus!

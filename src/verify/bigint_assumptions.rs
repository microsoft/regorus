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

/// A `BigInt` is abstracted as an `int`.

pub trait BigIntAdditionalSpecFns {
    spec fn view(&self) -> int;
}

impl BigIntAdditionalSpecFns for BigInt {
    uninterp spec fn view(&self) -> int;
}

/// Semantics for BigInt::Clone

// We assume that `a.clone()` has the same view as `BigInt` `a`.
pub assume_specification[ <BigInt as Clone>::clone ](n: &BigInt) -> (res: BigInt)
    ensures
        res == n,
;

/// Addition

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `(a + b)@ == a@ + b@.
pub axiom fn axiom_bigint_obeys_add_spec()
    ensures
        <BigInt as vstd::std_specs::ops::AddSpec>::obeys_add_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddSpec>::add_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddSpec>::add_spec(lhs, rhs)@
                == lhs@ + rhs@,
;

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `a += b` causes the resulting `a@` to be the old value of `a@` plus `b@`.
pub axiom fn axiom_bigint_obeys_add_assign_spec()
    ensures
        <BigInt as vstd::std_specs::ops::AddAssignSpec<BigInt>>::obeys_add_assign_spec(),
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddAssignSpec<BigInt>>::add_assign_req(&value, rhs),
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::AddAssignSpec<BigInt>>::add_assign_spec(&value, rhs)@ ==
            value@ + rhs@,
;

/// Subtraction

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `(a - b)@ == a@ - b@.
pub axiom fn axiom_bigint_obeys_sub_spec()
    ensures
        <BigInt as vstd::std_specs::ops::SubSpec>::obeys_sub_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubSpec>::sub_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubSpec>::sub_spec(lhs, rhs)@
                == lhs@ - rhs@,
;

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `a -= b` causes the resulting `a@` to be the old value of `a@` minus `b@`.
pub axiom fn axiom_bigint_obeys_sub_assign_spec()
    ensures
        <BigInt as vstd::std_specs::ops::SubAssignSpec<BigInt>>::obeys_sub_assign_spec(),
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubAssignSpec<BigInt>>::sub_assign_req(&value, rhs),
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::SubAssignSpec<BigInt>>::sub_assign_spec(&value, rhs)@ ==
            value@ - rhs@,
;

/// Multiplication

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `(a * b)@ == a@ * b@.
pub axiom fn axiom_bigint_obeys_mul_spec()
    ensures
        <BigInt as vstd::std_specs::ops::MulSpec>::obeys_mul_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulSpec>::mul_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulSpec>::mul_spec(lhs, rhs)@
                == lhs@ * rhs@,
;

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `a *= b` causes the resulting `a@` to be the old value of `a@` times `b@`.
pub axiom fn axiom_bigint_obeys_mul_assign_spec()
    ensures
        <BigInt as vstd::std_specs::ops::MulAssignSpec<BigInt>>::obeys_mul_assign_spec(),
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulAssignSpec<BigInt>>::mul_assign_req(&value, rhs),
        forall|value: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulAssignSpec<BigInt>>::mul_assign_spec(&value, rhs)@ ==
            value@ * rhs@,
;

pub axiom fn axiom_bigint_obeys_mul_assign_ref_spec()
    ensures
        <BigInt as vstd::std_specs::ops::MulAssignSpec<&BigInt>>::obeys_mul_assign_spec(),
        forall|value: BigInt, rhs: &BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulAssignSpec<&BigInt>>::mul_assign_req(&value, rhs),
        forall|value: BigInt, rhs: &BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::MulAssignSpec<&BigInt>>::mul_assign_spec(&value, rhs)@ ==
            value@ * (*rhs)@,
;

/// Division

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// `(a / b)@ == rust_div(a@, b@), and `(a % b)@ == rust_rem(a@, b@)`.
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

/// Bitwise AND

// This function describes the result of performing a bitwise AND
// operation on two unbounded-precision integers.
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

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// (a & b)@ == spec_bigint_bitand(a@, b@). It's justified by the
// lemmas above named `lemma_test_spec_bigint_bitand_for_i16`
// and `lemma_test_spec_bigint_bitand_with_examples`.
pub axiom fn axiom_bigint_obeys_bitand_spec()
    ensures
        <BigInt as vstd::std_specs::ops::BitAndSpec>::obeys_bitand_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitAndSpec>::bitand_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitAndSpec>::bitand_spec(lhs, rhs)@
                == spec_bigint_bitand(lhs@, rhs@),
;

/// Bitwise OR

// This function describes the result of performing a bitwise OR
// operation on two unbounded-precision integers.
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

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// (a | b)@ == spec_bigint_bitor(a@, b@). It's justified by the
// lemmas above named `lemma_test_spec_bigint_bitor_for_i16`
// and `lemma_test_spec_bigint_bitor_with_examples`.
pub axiom fn axiom_bigint_obeys_bitor_spec()
    ensures
        <BigInt as vstd::std_specs::ops::BitOrSpec>::obeys_bitor_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitOrSpec>::bitor_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitOrSpec>::bitor_spec(lhs, rhs)@
                == spec_bigint_bitor(lhs@, rhs@),
;

/// Bitwise XOR

// This function describes the result of performing a bitwise XOR
// operation on two unbounded-precision integers.
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

// This axiom says that, for any pair of `BigInt`s `a` and `b`,
// (a | b)@ == spec_bigint_bitxor(a@, b@). It's justified by the
// lemmas above named `lemma_test_spec_bigint_bitxor_for_i16`
// and `lemma_test_spec_bigint_bitxor_with_examples`.
pub axiom fn axiom_bigint_obeys_bitxor_spec()
    ensures
        <BigInt as vstd::std_specs::ops::BitXorSpec>::obeys_bitxor_spec(),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitXorSpec>::bitxor_req(lhs, rhs),
        forall|lhs: BigInt, rhs: BigInt| #[trigger]
            <BigInt as vstd::std_specs::ops::BitXorSpec>::bitxor_spec(lhs, rhs)@
                == spec_bigint_bitxor(lhs@, rhs@),
;

/// Bitwise NOT

// This axiom says that, for `BigInt` `a`, `(~a)@ == -a@ - 1`.
// This corresponds to twos-complement bitwise negation.
pub axiom fn axiom_bigint_not_spec(value: BigInt)
    ensures
        <BigInt as vstd::std_specs::ops::NotSpec>::obeys_not_spec(),
        <BigInt as vstd::std_specs::ops::NotSpec>::not_req(value),
        <BigInt as vstd::std_specs::ops::NotSpec>::not_spec(value)@ == -(value@) - 1,
;

/// Bitwise shifting

// This axiom says that BigInt supports the expected semantics for
// core::ops::ShrAssign, i.e., `>>=`. That is, for any BigInt 'a' and
// any shift amount `u: usize`, `a >>= u` causes the resulting `a@` to
// be the old `a@` shifted right by `u` bits.
pub axiom fn axiom_bigint_obeys_shr_assign_spec()
    ensures
        <BigInt as vstd::std_specs::ops::ShrAssignSpec<usize>>::obeys_shr_assign_spec(),
        forall|value: BigInt, shift: usize| #[trigger]
            <BigInt as vstd::std_specs::ops::ShrAssignSpec<usize>>::shr_assign_req(&value, shift),
        forall|value: BigInt, shift: usize| #[trigger]
            <BigInt as vstd::std_specs::ops::ShrAssignSpec<usize>>::shr_assign_spec(&value, shift)@ ==
            value@ / pow2(shift as nat) as int,
;

// This axiom says that BigInt supports the expected semantics for
// core::ops::ShlAssign, i.e., `<<=`. That is, for any BigInt 'a' and
// any shift amount `u: usize`, `a <<= u` causes the resulting `a@` to
// be the old `a@` shifted left by `u` bits.
pub axiom fn axiom_bigint_obeys_shl_assign_spec()
    ensures
        <BigInt as vstd::std_specs::ops::ShlAssignSpec<usize>>::obeys_shl_assign_spec(),
        forall|value: BigInt, shift: usize| #[trigger]
            <BigInt as vstd::std_specs::ops::ShlAssignSpec<usize>>::shl_assign_req(&value, shift),
        forall|value: BigInt, shift: usize| #[trigger]
            <BigInt as vstd::std_specs::ops::ShlAssignSpec<usize>>::shl_assign_spec(&value, shift)@ ==
            value@ * pow2(shift as nat) as int,
;

/// Unary operations

// We assume that `x.is_zero()` gives the same result as `x@ == 0`.
pub assume_specification[ <BigInt as num_traits::Zero>::is_zero ](x: &BigInt) -> (res: bool)
    ensures
        res == (x@ == 0),
;

// We assume that `x.is_negative()` gives the same result as `x@ < 0`.
pub assume_specification[ <BigInt as num_traits::Signed>::is_negative ](x: &BigInt) -> (res: bool)
    ensures
        res == (x@ < 0),
;

// We assume that `x.abs()` produces a `BigInt` `y` such that `y@ == abs(x@)`.
pub assume_specification[ <BigInt as num_traits::Signed>::abs ](x: &BigInt) -> (res: BigInt)
    ensures
        res@ == if x@ < 0 { -x@ } else { x@ },
;

// This is the specification for what `BigInt::bits` produces.
// According to the documentation
// (https://docs.rs/num-bigint/latest/num_bigint/struct.BigInt.html#method.bits),
// it's the fewest bits necessary to express its value, not including the sign.
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

/// Negation

// This axiom says that, for `BigInt` `a`, `(-a)@ == -a@`.
pub axiom fn axiom_bigint_neg_spec(value: BigInt)
    ensures
        <BigInt as vstd::std_specs::ops::NegSpec>::obeys_neg_spec(),
        <BigInt as vstd::std_specs::ops::NegSpec>::neg_req(value),
        <BigInt as vstd::std_specs::ops::NegSpec>::neg_spec(value)@ == -value@,
;

/// Formatting

// Nothing is promised about the rendered digits; callers only need this to be
// callable from verified code.
pub assume_specification[ BigInt::to_str_radix ](x: &BigInt, radix: u32) -> (res:
    alloc::string::String);

/// Equality

// This axiom says that if we execute `a == b` for two `BigInt`s `a` and `b`,
// the result is equal to `a@ == b@`.
pub axiom fn axiom_bigint_obeys_eq_spec()
    ensures
        <BigInt as vstd::std_specs::cmp::PartialEqSpec>::obeys_eq_spec(),
        forall|a: BigInt, b: BigInt| #[trigger]
            <BigInt as vstd::std_specs::cmp::PartialEqSpec>::eq_spec(&a, &b) == (a@ == b@),
;

/// Comparison

// This axiom says that comparison operators on `BigInt`s return what would
// result from comparing their views.
pub axiom fn axiom_bigint_obeys_cmp_spec()
    ensures
        <BigInt as vstd::std_specs::cmp::OrdSpec>::obeys_cmp_spec(),
        forall|b1: &BigInt, b2: &BigInt| match #[trigger] b1.cmp_spec(b2) {
            Ordering::Less => b1@ < b2@,
            Ordering::Greater => b1@ > b2@,
            Ordering::Equal => b1@ == b2@,
        },
;

/// From<T>

// We assume that `BigInt::from(i)` where `i` has type `i64` produces a `BigInt`
// whose view equals `i`.
pub assume_specification[ <BigInt as core::convert::From<i64>>::from ](i: i64) -> (res: BigInt)
    ensures
        res@ == i,
;

// We assume that `BigInt::from(i)` where `i` has type `i128` produces a `BigInt`
// whose view equals `i`.
pub assume_specification[ <BigInt as core::convert::From<i128>>::from ](i: i128) -> (res: BigInt)
    ensures
        res@ == i,
;

// We assume that `BigInt::from(u)` where `u` has type `u64` produces a `BigInt`
// whose view equals `u`.
pub assume_specification[ <BigInt as core::convert::From<u64>>::from ](u: u64) -> (res: BigInt)
    ensures
        res@ == u,
;

// We assume that `BigInt::from(u)` where `u` has type `u128` produces a `BigInt`
// whose view equals `u`.
pub assume_specification[ <BigInt as core::convert::From<u128>>::from ](u: u128) -> (res: BigInt)
    ensures
        res@ == u,
;

// We assume that `BigInt::from(u)` where `u` has type `u8` produces a `BigInt`
// whose view equals `u`.
pub assume_specification[ <BigInt as core::convert::From<u8>>::from ](u: u8) -> (res: BigInt)
    ensures
        res@ == u,
;

/// BigInt::one

// We assume that `BigInt::one` produces a value whose view is 1.
pub assume_specification[ <BigInt as num_traits::One>::one ]() -> (res: BigInt)
    ensures
        res@ == 1,
;

// ToPrimitive

// Verus does not support `assume_specification` for provided trait methods, so
// `to_u32` needs a minimal external trait specification. BigInt's overridden
// conversion methods are specified directly below.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(ToPrimitiveSpec via ToPrimitiveSpecImpl)]
pub trait ExToPrimitive {
    type ExternalTraitSpecificationFor: num_traits::ToPrimitive;

    spec fn obeys_to_primitive_spec() -> bool;

    spec fn spec_to_int(&self) -> Option<int>;

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
}

impl ToPrimitiveSpecImpl for BigInt {
    open spec fn obeys_to_primitive_spec() -> bool
    {
        true
    }

    open spec fn spec_to_int(&self) -> Option<int>
    {
        Some(self@)
    }
}

// We assume that `b.to_i64()` where `b` is of type `BigInt` produces `Some(i)`
// if its view `i` is in the range of an `i64` and `None` otherwise.
pub assume_specification[ <BigInt as num_traits::ToPrimitive>::to_i64 ](x: &BigInt) -> (res: Option<i64>)
    ensures
        match res {
            Some(value) => x@ == value,
            None => !(i64::MIN <= x@ <= i64::MAX),
        },
;

// We assume that `b.to_i128()` where `b` is of type `BigInt` produces `Some(i)`
// if its view `i` is in the range of an `i128` and `None` otherwise.
pub assume_specification[ <BigInt as num_traits::ToPrimitive>::to_i128 ](x: &BigInt) -> (res: Option<i128>)
    ensures
        match res {
            Some(value) => x@ == value,
            None => !(i128::MIN <= x@ <= i128::MAX),
        },
;

// We assume that `b.to_u64()` where `b` is of type `BigInt` produces `Some(u)`
// if its view `u` is in the range of a `u64` and `None` otherwise.
pub assume_specification[ <BigInt as num_traits::ToPrimitive>::to_u64 ](x: &BigInt) -> (res: Option<u64>)
    ensures
        match res {
            Some(value) => x@ == value,
            None => !(u64::MIN <= x@ <= u64::MAX),
        },
;

// We assume that `b.to_u128()` where `b` is of type `BigInt` produces `Some(u)`
// if its view `u` is in the range of a `u128` and `None` otherwise.
pub assume_specification[ <BigInt as num_traits::ToPrimitive>::to_u128 ](x: &BigInt) -> (res: Option<u128>)
    ensures
        match res {
            Some(value) => x@ == value,
            None => !(u128::MIN <= x@ <= u128::MAX),
        },
;

pub uninterp spec fn spec_bigint_to_f64(x: &BigInt) -> Option<f64>;

// We define the value returned by `b.to_f64()` as `spec_bigint_to_f64(&b)`.
// We assume that this is `Some` if `b` is in the range -2^53 to 2^53 inclusive.
// (It may be `Some` elsewhere; we don't assume either way.)
pub assume_specification[ <BigInt as num_traits::ToPrimitive>::to_f64 ](x: &BigInt) -> (res: Option<f64>)
    ensures
        res == spec_bigint_to_f64(x),
        -9_007_199_254_740_992 <= x@ <= 9_007_199_254_740_992 ==> res is Some,
;

} // end verus!

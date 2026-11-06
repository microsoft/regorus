// This file contains assumptions about `f64`, encoded in Verus.
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

use vstd::arithmetic::power2::pow2;
use vstd::float::*;
use vstd::std_specs::cmp::PartialEqIs;
use vstd::std_specs::cmp::PartialOrdIs;

// Exponent field of an f64 magnitude (bits 52..=62). `to_bits_abs_spec` has already cleared
// the sign bit.
pub open spec fn f64_biased_exponent(f: f64) -> int
{
    (f.to_bits_abs_spec() >> 52) as int
}

// Fraction field of an f64 magnitude (bits 0..=51).
pub open spec fn f64_fraction(f: f64) -> int
{
    (f.to_bits_abs_spec() & 0x000f_ffff_ffff_ffff) as int
}

// Integer significand scaled by 2^52 for a finite binary64 value.
pub open spec fn f64_finite_significand(f: f64) -> int
{
    if f64_biased_exponent(f) == 0 {
        f64_fraction(f)
    } else {
        f64_fraction(f) + pow2(52)
    }
}

// Exponent paired with `f64_finite_significand`. For a finite value,
// `|f| == f64_finite_significand(f) * 2^f64_finite_exponent(f)`. The normal-value
// offset is 1023 + 52 = 1075 because the significand is scaled by 2^52.
pub open spec fn f64_finite_exponent(f: f64) -> int
{
    if f64_biased_exponent(f) == 0 {
        -1074
    } else {
        f64_biased_exponent(f) - 1075
    }
}

// Signed value in units of 2^exponent, truncating toward zero at coarser scales.
// This is exact when exponent is no larger than the decoded exponent.
pub open spec fn f64_scaled_value(f: f64, exponent: int) -> int
{
    let shift = f64_finite_exponent(f) - exponent;
    let magnitude = if shift >= 0 {
        f64_finite_significand(f) * pow2(shift as nat)
    } else {
        f64_finite_significand(f) / (pow2((-shift) as nat) as int)
    };
    if f.is_sign_negative_spec() { -magnitude } else { magnitude }
}

pub open spec fn f64_has_fraction(f: f64) -> bool
{
    f64_finite_exponent(f) < 0
        && f64_finite_significand(f) % (pow2((-f64_finite_exponent(f)) as nat) as int) != 0
}

// Specify the mantissa only for normal finite values; exponent and sign apply to all values.
pub open spec fn f64_integer_decode_ensures(f: f64, decoded: (u64, i16, i8)) -> bool
{
    &&& 0 < f64_biased_exponent(f) < 2047 ==>
        decoded.0 as int == f64_finite_significand(f)
    &&& decoded.1 as int == f64_biased_exponent(f) - 1075
    &&& decoded.2 == if f.is_sign_negative_spec() { -1i8 } else { 1i8 }
}

pub assume_specification[ <f64 as num_traits::float::FloatCore>::integer_decode ](f: f64)
    -> (decoded: (u64, i16, i8))
    ensures
        f64_integer_decode_ensures(f, decoded),
;

pub assume_specification[ f64::is_sign_negative ](f: f64) -> (negative: bool)
    ensures
        negative == f.is_sign_negative_spec(),
;

pub axiom fn axiom_f64_order_zero(f: f64, exponent: int)
    requires
        !f.is_nan_spec(),
        exponent <= f64_finite_exponent(f),
    ensures
        f.ieee_lt(0.0f64) == if f.is_finite_spec() {
            f64_scaled_value(f, exponent) < 0
        } else {
            f.is_sign_negative_spec()
        },
;

pub axiom fn axiom_f64_finite_order(f: f64, g: f64, exponent: int)
    requires
        f.is_finite_spec(),
        g.is_finite_spec(),
        exponent <= f64_finite_exponent(f),
        exponent <= f64_finite_exponent(g),
    ensures
        f.ieee_lt(g) == (f64_scaled_value(f, exponent) < f64_scaled_value(g, exponent)),
        f.ieee_gt(g) == (f64_scaled_value(f, exponent) > f64_scaled_value(g, exponent)),
        f.ieee_ge(g) == (f64_scaled_value(f, exponent) >= f64_scaled_value(g, exponent)),
;

// Non-NaN values lie between the infinities; equal infinities compare equal.
pub axiom fn axiom_f64_infinite_order(f: f64, infinity: f64)
    requires
        !f.is_nan_spec(),
        infinity.is_infinite_spec(),
    ensures
        f.ieee_lt(infinity) == (!infinity.is_sign_negative_spec()
            && (f.is_finite_spec() || f.is_sign_negative_spec())),
        infinity.ieee_lt(f) == (infinity.is_sign_negative_spec()
            && (f.is_finite_spec() || !f.is_sign_negative_spec())),
        f.ieee_gt(infinity) == infinity.ieee_lt(f),
        infinity.ieee_gt(f) == f.ieee_lt(infinity),
;

// Round-to-nearest, ties-to-even maps u64::MAX to exactly 2^64.
pub axiom fn axiom_f64_u64_max_cast(exponent: int)
    requires
        exponent <= 0,
    ensures
        ieee_float_cast::<u64, f64>(u64::MAX).is_finite_spec(),
        !ieee_float_cast::<u64, f64>(u64::MAX).is_sign_negative_spec(),
        f64_biased_exponent(ieee_float_cast::<u64, f64>(u64::MAX)) == 1087,
        f64_fraction(ieee_float_cast::<u64, f64>(u64::MAX)) == 0,
;

// A negative unbiased exponent means |f| < 1, including subnormals and signed zero.
pub axiom fn axiom_f64_to_u64_below_one(f: f64)
    requires
        f.is_finite_spec(),
        f64_biased_exponent(f) < 1023,
    ensures
        ieee_float_cast::<f64, u64>(f) == 0,
;

// For nonnegative, in-range values with unbiased exponent >= 0, the cast rounds down.
pub axiom fn axiom_f64_to_u64_in_range(f: f64)
    requires
        f.is_finite_spec(),
        f64_biased_exponent(f) >= 1023,
        0 <= f64_scaled_value(f, 0) <= u64::MAX,
    ensures
        ieee_float_cast::<f64, u64>(f) as int == f64_scaled_value(f, 0),
;

// The truncated integer is exactly representable, so its back-cast is smaller
// than f precisely when f has a fractional part.
pub axiom fn axiom_f64_to_u64_backcast(f: f64)
    requires
        f.is_finite_spec(),
        !f.ieee_lt(0.0f64),
        0 <= f64_scaled_value(f, 0) <= u64::MAX,
    ensures
        f.ieee_gt(ieee_float_cast::<u64, f64>(ieee_float_cast::<f64, u64>(f)))
            == f64_has_fraction(f),
;

// i64::MIN is exactly -2^63; round-to-nearest, ties-to-even maps i64::MAX to +2^63.
pub axiom fn axiom_f64_i64_limit_casts()
    ensures
        ieee_float_cast::<i64, f64>(i64::MIN).is_finite_spec(),
        ieee_float_cast::<i64, f64>(i64::MIN).is_sign_negative_spec(),
        f64_biased_exponent(ieee_float_cast::<i64, f64>(i64::MIN)) == 1086,
        f64_fraction(ieee_float_cast::<i64, f64>(i64::MIN)) == 0,
        ieee_float_cast::<i64, f64>(i64::MAX).is_finite_spec(),
        !ieee_float_cast::<i64, f64>(i64::MAX).is_sign_negative_spec(),
        f64_biased_exponent(ieee_float_cast::<i64, f64>(i64::MAX)) == 1086,
        f64_fraction(ieee_float_cast::<i64, f64>(i64::MAX)) == 0,
;

// Both signs of |f| < 1 truncate to zero, including subnormals and signed zero.
pub axiom fn axiom_f64_to_i64_below_one(f: f64)
    requires
        f.is_finite_spec(),
        f64_biased_exponent(f) < 1023,
    ensures
        ieee_float_cast::<f64, i64>(f) == 0,
;

// At larger magnitudes, an in-range cast truncates toward zero (not toward -infinity).
pub axiom fn axiom_f64_to_i64_in_range(f: f64)
    requires
        f.is_finite_spec(),
        f64_biased_exponent(f) >= 1023,
        i64::MIN <= f64_scaled_value(f, 0) <= i64::MAX,
    ensures
        ieee_float_cast::<f64, i64>(f) as int == f64_scaled_value(f, 0),
;

// The truncated integer is exactly representable; its back-cast lies toward zero.
pub axiom fn axiom_f64_to_i64_backcast(f: f64)
    requires
        f.is_finite_spec(),
        i64::MIN <= f64_scaled_value(f, 0) <= i64::MAX,
    ensures
        f.ieee_lt(ieee_float_cast::<i64, f64>(ieee_float_cast::<f64, i64>(f)))
            == (f.is_sign_negative_spec() && f64_has_fraction(f)),
        f.ieee_gt(ieee_float_cast::<i64, f64>(ieee_float_cast::<f64, i64>(f)))
            == (!f.is_sign_negative_spec() && f64_has_fraction(f)),
;

pub axiom fn axiom_f64_obeys_eq_spec()
    ensures
        <f64 as vstd::std_specs::cmp::PartialEqSpec>::obeys_eq_spec(),
;

pub axiom fn axiom_f64_obeys_partial_cmp_spec()
    ensures
        <f64 as vstd::std_specs::cmp::PartialOrdSpec>::obeys_partial_cmp_spec(),
;

pub axiom fn axiom_f64_comparisons_match_ieee()
    ensures
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_lt(f2) <==> f1.is_lt(&f2),
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_le(f2) <==> f1.is_le(&f2),
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_gt(f2) <==> f1.is_gt(&f2),
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_ge(f2) <==> f1.is_ge(&f2),
;

pub axiom fn axiom_f64_ops_deterministic()
    ensures
        <f64 as vstd::std_specs::ops::NegSpec>::obeys_neg_spec(),
        <f64 as vstd::std_specs::ops::AddSpec>::obeys_add_spec(),
        <f64 as vstd::std_specs::ops::SubSpec>::obeys_sub_spec(),
        <f64 as vstd::std_specs::ops::MulSpec>::obeys_mul_spec(),
        <f64 as vstd::std_specs::ops::DivSpec>::obeys_div_spec(),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::AddSpec>::add_req(lhs, rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::AddSpec>::add_spec(lhs, rhs)
                == lhs.ieee_add(rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::SubSpec>::sub_req(lhs, rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::SubSpec>::sub_spec(lhs, rhs)
                == lhs.ieee_sub(rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::MulSpec>::mul_req(lhs, rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::MulSpec>::mul_spec(lhs, rhs)
                == lhs.ieee_mul(rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::DivSpec>::div_req(lhs, rhs),
        forall|lhs: f64, rhs: f64| #[trigger]
            <f64 as vstd::std_specs::ops::DivSpec>::div_spec(lhs, rhs)
                == lhs.ieee_div(rhs),
        forall|n: i8, f: f64| float_cast_spec::<i8, f64>(n, f) ==> f == ieee_float_cast::<i8, f64>(n),
        forall|n: u8, f: f64| float_cast_spec::<u8, f64>(n, f) ==> f == ieee_float_cast::<u8, f64>(n),
        forall|n: i8, f: f64| float_cast_spec::<f64, i8>(f, n) ==> n == ieee_float_cast::<f64, i8>(f),
        forall|n: u8, f: f64| float_cast_spec::<f64, u8>(f, n) ==> n == ieee_float_cast::<f64, u8>(f),
        forall|n: i16, f: f64| float_cast_spec::<i16, f64>(n, f) ==> f == ieee_float_cast::<i16, f64>(n),
        forall|n: u16, f: f64| float_cast_spec::<u16, f64>(n, f) ==> f == ieee_float_cast::<u16, f64>(n),
        forall|n: i16, f: f64| float_cast_spec::<f64, i16>(f, n) ==> n == ieee_float_cast::<f64, i16>(f),
        forall|n: u16, f: f64| float_cast_spec::<f64, u16>(f, n) ==> n == ieee_float_cast::<f64, u16>(f),
        forall|n: i32, f: f64| float_cast_spec::<i32, f64>(n, f) ==> f == ieee_float_cast::<i32, f64>(n),
        forall|n: u32, f: f64| float_cast_spec::<u32, f64>(n, f) ==> f == ieee_float_cast::<u32, f64>(n),
        forall|n: i32, f: f64| float_cast_spec::<f64, i32>(f, n) ==> n == ieee_float_cast::<f64, i32>(f),
        forall|n: u32, f: f64| float_cast_spec::<f64, u32>(f, n) ==> n == ieee_float_cast::<f64, u32>(f),
        forall|n: i64, f: f64| float_cast_spec::<i64, f64>(n, f) ==> f == ieee_float_cast::<i64, f64>(n),
        forall|n: u64, f: f64| float_cast_spec::<u64, f64>(n, f) ==> f == ieee_float_cast::<u64, f64>(n),
        forall|n: i64, f: f64| float_cast_spec::<f64, i64>(f, n) ==> n == ieee_float_cast::<f64, i64>(f),
        forall|n: u64, f: f64| float_cast_spec::<f64, u64>(f, n) ==> n == ieee_float_cast::<f64, u64>(f),
        forall|n: i128, f: f64| float_cast_spec::<i128, f64>(n, f) ==> f == ieee_float_cast::<i128, f64>(n),
        forall|n: u128, f: f64| float_cast_spec::<u128, f64>(n, f) ==> f == ieee_float_cast::<u128, f64>(n),
        forall|n: i128, f: f64| float_cast_spec::<f64, i128>(f, n) ==> n == ieee_float_cast::<f64, i128>(f),
        forall|n: u128, f: f64| float_cast_spec::<f64, u128>(f, n) ==> n == ieee_float_cast::<f64, u128>(f),
;

// The executable test in `f64_tests.rs` validates these casts and justifies
// this axiom.
pub axiom fn axiom_f64_safe_integer_casts()
    ensures
        ieee_float_cast::<f64, u64>(9_007_199_254_740_992.0f64) == 9_007_199_254_740_992u64,
        ieee_float_cast::<f64, i128>(9_007_199_254_740_992.0f64) == 9_007_199_254_740_992i128,
;

pub assume_specification [ f64::is_finite ](f: f64) -> (res: bool)
    ensures
        res == f.is_finite_spec(),
;

pub uninterp spec fn spec_f64_fract(f: f64) -> f64;

pub assume_specification [ f64::fract ](f: f64) -> (res: f64)
    requires
        f.is_finite_spec(),
    ensures
        res == spec_f64_fract(f),
;

pub uninterp spec fn spec_f64_abs(f: f64) -> f64;

pub assume_specification [ f64::abs ](f: f64) -> (res: f64)
    ensures
        res == spec_f64_abs(f),
;

pub assume_specification [ <f64 as num_traits::Signed>::abs ](f: &f64) -> (res: f64)
    ensures
        res == spec_f64_abs(*f),
;

pub uninterp spec fn spec_f64_floor(f: f64) -> f64;

pub assume_specification [ f64::floor ](f: f64) -> (res: f64)
    ensures
        res == spec_f64_floor(f),
;

pub uninterp spec fn spec_f64_ceil(f: f64) -> f64;

pub assume_specification [ f64::ceil ](f: f64) -> (res: f64)
    ensures
        res == spec_f64_ceil(f),
;

pub uninterp spec fn spec_f64_round(f: f64) -> f64;

pub assume_specification [ f64::round ](f: f64) -> (res: f64)
    ensures
        res == spec_f64_round(f),
;

pub assume_specification [ f64::is_nan ](f: f64) -> (res: bool)
    ensures
        res == f.is_nan_spec(),
;

pub uninterp spec fn spec_f64_is_sign_positive(f: f64) -> bool;

pub assume_specification [ f64::is_sign_positive ](f: f64) -> (res: bool)
    ensures
        res == spec_f64_is_sign_positive(f),
;

pub uninterp spec fn spec_f64_neg_infinity() -> f64;

pub uninterp spec fn spec_f64_infinity() -> f64;

pub assume_specification[ f64::NEG_INFINITY ] -> (res: f64)
    ensures
        res == spec_f64_neg_infinity(),
;

pub assume_specification[ f64::INFINITY ] -> (res: f64)
    ensures
        res == spec_f64_infinity(),
;

} // end verus!

// This file contains specifications for `Number` and its methods.
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

use crate::number::*;
use core::cmp::Ordering;
use super::bigint_assumptions::*;
use super::f64_assumptions::*;
use vstd::arithmetic::power2::pow2;
use vstd::float::*;
use vstd::std_specs::cmp::PartialEqSpec;

pub assume_specification[ <Number as Clone>::clone ](n: &Number) -> (res: Number)
    ensures
        res@ == n@,
;

pub enum NumberView {
    Integer(int),
    Float(f64),
}

pub open spec fn float_to_small_int(value: f64) -> Option<int>
{
    if !value.is_finite_spec() ||
       !spec_f64_fract(value).eq_spec(&0.0f64) ||
       spec_f64_abs(value) > 9_007_199_254_740_992.0 {
        None
    }
    else if value >= 0.0 {
        let value_as_u64 = ieee_float_cast::<f64, u64>(value);
        if ieee_float_cast::<u64, f64>(value_as_u64).eq_spec(&value) {
            Some(value_as_u64 as int)
        }
        else {
            None
        }
    }
    else {
        let value_as_i64 = ieee_float_cast::<f64, i64>(value);
        if ieee_float_cast::<i64, f64>(value_as_i64).eq_spec(&value) {
            Some(ieee_float_cast::<f64, i64>(value) as int)
        }
        else {
            None
        }
    }
}

pub open spec fn normalize_float(value: f64) -> NumberView
{
    match float_to_small_int(value) {
        Some(n) => NumberView::Integer(n),
        None => NumberView::Float(value),
    }
}

// ---- exact comparison ----------------------------------------------------------------------
//
// `Number::cmp`/`Number::eq` must be exact and total, so they are specified in the integers
// instead of through `to_f64_lossy`, which rounded away differences (2^63 == 2^63+1) and mapped
// every out-of-range BigInt to +/-Inf (so `Float(INFINITY) == <huge BigInt>` was true).
//
// A binary64 value is exactly `sign * significand * 2^exponent`, read straight out of its bit
// pattern, so every `NumberView` has a scaled-integer form and the comparison never leaves the
// integers.

// Exponent field of an f64 magnitude (bits 52..=62).
pub open spec fn f64_biased_exponent(f: f64) -> int
{
    (f.to_bits_abs_spec() >> 52) as int
}

// Fraction field of an f64 magnitude (bits 0..=51).
pub open spec fn f64_fraction(f: f64) -> int
{
    (f.to_bits_abs_spec() & 0x000f_ffff_ffff_ffff) as int
}

// binary64 significand: the implicit leading 1 is present only for normal values.
pub open spec fn f64_significand(f: f64) -> int
{
    if f64_biased_exponent(f) == 0 {
        f64_fraction(f)
    } else {
        f64_fraction(f) + pow2(52)
    }
}

// binary64 exponent, i.e. `|f| == f64_significand(f) * pow2(f64_exponent(f))` for a finite `f`.
pub open spec fn f64_exponent(f: f64) -> int
{
    if f64_biased_exponent(f) == 0 {
        -1074
    } else {
        f64_biased_exponent(f) - 1075
    }
}

// Compare `l_sign * l_magnitude * 2^l_exponent` with `r_sign * r_magnitude * 2^r_exponent`.
// Scaling both sides up to the larger exponent keeps the comparison integral and exact.
pub open spec fn cmp_scaled_values(
    l_sign: bool, l_magnitude: int, l_exponent: int,
    r_sign: bool, r_magnitude: int, r_exponent: int) -> Ordering
{
    if l_magnitude == 0 && r_magnitude == 0 {
        // Numeric equality treats -0.0, 0.0 and integer zero as one value.
        Ordering::Equal
    }
    else {
        let l_value = if l_exponent >= r_exponent { l_magnitude * pow2((l_exponent - r_exponent) as nat) } else { l_magnitude };
        let r_value = if r_exponent >= l_exponent { r_magnitude * pow2((r_exponent - l_exponent) as nat) } else { r_magnitude };
        if l_sign != r_sign {
            // Both magnitudes are non-zero, so the signs decide.
            if l_sign { Ordering::Less } else { Ordering::Greater }
        }
        else if l_value < r_value {
            if l_sign { Ordering::Greater } else { Ordering::Less }
        }
        else if l_value > r_value {
            if l_sign { Ordering::Less } else { Ordering::Greater }
        }
        else {
            Ordering::Equal
        }
    }
}

impl NumberView {
    pub open spec fn is_finite(self: Self) -> bool
    {
        match self {
            Self::Integer(_) => true,
            Self::Float(f) => f.is_finite_spec(),
        }
    }

    pub open spec fn is_zero(&self) -> bool
    {
        match *self {
            Self::Integer(n) => n == 0,
            Self::Float(f) => f.eq_spec(&0.0f64),
        }
    }

    pub open spec fn to_int(&self) -> Option<int>
    {
        match *self {
            Self::Integer(n) => Some(n),
            Self::Float(f) => float_to_small_int(f),
        }
    }

    // The complete order is:
    //
    // negative NaNs < -Inf < negative finite numbers
    //     < (-0.0 == +0.0 == integer 0)
    //     < positive finite numbers < +Inf < positive NaNs
    //
    // Finite comparison merges signed zero with integer zero. The scaled fields below distinguish
    // NaN payloads within each sign consistently with `f64::total_cmp`.
    pub open spec fn cmp_rank(self) -> int
    {
        match self {
            Self::Integer(_) => 0,
            Self::Float(f) =>
                if f.is_nan_spec() {
                    if f.is_sign_negative_spec() { -2 } else { 2 }
                }
                else if f.is_finite_spec() { 0 }
                else if f.is_sign_negative_spec() { -1 } else { 1 },
        }
    }

    // Exact scaled form of a ranked (finite, or non-finite-but-never-compared) value:
    // `value == (if scaled_sign then -1 else 1) * scaled_magnitude * pow2(scaled_exponent)`.
    pub open spec fn scaled_sign(self) -> bool
    {
        match self {
            Self::Integer(n) => n < 0,
            Self::Float(f) => f.is_sign_negative_spec(),
        }
    }

    pub open spec fn scaled_magnitude(self) -> int
    {
        match self {
            Self::Integer(n) => if n < 0 { -n } else { n },
            Self::Float(f) => f64_significand(f),
        }
    }

    pub open spec fn scaled_exponent(self) -> int
    {
        match self {
            Self::Integer(_) => 0,
            Self::Float(f) => f64_exponent(f),
        }
    }

    // The exact total order: rank first (so the non-finite tail is ordered and never collapses
    // onto a finite value), then the scaled integer values.
    pub open spec fn cmp_values(self: Self, other: Self) -> Ordering
    {
        if self.cmp_rank() != other.cmp_rank() {
            if self.cmp_rank() < other.cmp_rank() { Ordering::Less } else { Ordering::Greater }
        }
        else {
            cmp_scaled_values(
                self.scaled_sign(), self.scaled_magnitude(), self.scaled_exponent(),
                other.scaled_sign(), other.scaled_magnitude(), other.scaled_exponent())
        }
    }

    pub open spec fn cmp_ensures(self: Self, other: Self, result: Ordering) -> bool
    {
        result == self.cmp_values(other)
    }

    // `PartialEq` is defined as `cmp == Equal`, which is what keeps `Ord`-backed containers
    // (Set, object keys) in agreement with `==`.
    pub open spec fn eq_ensures(self: Self, other: Self, result: bool) -> bool
    {
        result == (self.cmp_values(other) == Ordering::Equal)
    }

    pub open spec fn to_f64_lossy_ensures(self: Self, f: f64) -> bool
    {
        match self {
            NumberView::Integer(v) =>
            {
                ||| 0 <= v <= u64::MAX && f == ieee_float_cast::<u64, f64>(v as u64)
                ||| i64::MIN <= v <= i64::MAX && f == ieee_float_cast::<i64, f64>(v as i64)
                ||| exists|bi: BigInt| {
                    &&& bi@ == v
                    &&& match #[trigger] super::bigint_assumptions::spec_bigint_to_f64(&bi) {
                        Some(x) => f == x,
                        None => f == if v < 0 { spec_f64_neg_infinity() } else { spec_f64_infinity() }
                    }
                }
            },
            NumberView::Float(v) => f == v,
        }
    }

    pub open spec fn add_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        &&& result.is_finite()
        &&& match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                result matches NumberView::Integer(sum) && sum == lhs + rhs,
            _ => exists|a: f64, b: f64| {
                &&& self.to_f64_lossy_ensures(a)
                &&& rhs.to_f64_lossy_ensures(b)
                &&& match float_to_small_int(a + b) {
                    Some(sum) => result == NumberView::Integer(sum),
                    None => result == NumberView::Float(a + b),
                }
            },
        }
    }

    pub open spec fn sub_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        &&& result.is_finite()
        &&& match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                result matches NumberView::Integer(diff) && diff == lhs - rhs,
            _ => exists|a: f64, b: f64| {
                &&& self.to_f64_lossy_ensures(a)
                &&& rhs.to_f64_lossy_ensures(b)
                &&& match float_to_small_int(a - b) {
                    Some(diff) => result == NumberView::Integer(diff),
                    None => result == NumberView::Float(a - b)
                }
            },
        }
    }

    pub open spec fn mul_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        &&& result.is_finite()
        &&& match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                result matches NumberView::Integer(product) && product == lhs * rhs,
            _ => exists|a: f64, b: f64| {
                &&& self.to_f64_lossy_ensures(a)
                &&& rhs.to_f64_lossy_ensures(b)
                &&& match float_to_small_int(a * b) {
                    Some(product) => result == NumberView::Integer(product),
                    None => result == NumberView::Float(a * b)
                }
            },
        }
    }

    pub open spec fn div_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        &&& result.is_finite()
        &&& match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(divisor)) => {
                &&& divisor != 0
                &&& if vstd::arithmetic::div_mod::rust_rem(lhs, divisor) == 0 {
                    result == NumberView::Integer(
                        vstd::arithmetic::div_mod::rust_div(lhs, divisor),
                    )
                } else {
                    exists|a: f64, b: f64| {
                        &&& self.to_f64_lossy_ensures(a)
                        &&& rhs.to_f64_lossy_ensures(b)
                        &&& result == NumberView::Float(a / b)
                    }
                }
            },
            _ => {
                &&& !rhs.is_zero()
                &&& exists|a: f64, b: f64| {
                    &&& self.to_f64_lossy_ensures(a)
                    &&& rhs.to_f64_lossy_ensures(b)
                    &&& result == NumberView::Float(a / b)
                }
            },
        }
    }

    // The float-promoting paths of add/sub/mul/divide report an error instead of returning
    // the +/-Inf or NaN that an f64 promotion can produce, since Rego has no non-finite
    // numbers. These describe when such an error is allowed.
    pub open spec fn add_overflows(self: Self, rhs: Self) -> bool
    {
        exists|a: f64, b: f64| {
            &&& self.to_f64_lossy_ensures(a)
            &&& rhs.to_f64_lossy_ensures(b)
            &&& !(a + b).is_finite_spec()
        }
    }

    pub open spec fn sub_overflows(self: Self, rhs: Self) -> bool
    {
        exists|a: f64, b: f64| {
            &&& self.to_f64_lossy_ensures(a)
            &&& rhs.to_f64_lossy_ensures(b)
            &&& !(a - b).is_finite_spec()
        }
    }

    pub open spec fn mul_overflows(self: Self, rhs: Self) -> bool
    {
        exists|a: f64, b: f64| {
            &&& self.to_f64_lossy_ensures(a)
            &&& rhs.to_f64_lossy_ensures(b)
            &&& !(a * b).is_finite_spec()
        }
    }

    pub open spec fn div_overflows(self: Self, rhs: Self) -> bool
    {
        exists|a: f64, b: f64| {
            &&& self.to_f64_lossy_ensures(a)
            &&& rhs.to_f64_lossy_ensures(b)
            &&& !(a / b).is_finite_spec()
        }
    }

}

// `spec_bigint_to_f64` deliberately leaves conversions outside the exactly represented range
// uninterpreted. This captures the narrower fact required by negative powers: converting a
// positive integer divisor and taking `1.0 / divisor` cannot produce NaN or infinity.
pub axiom fn axiom_positive_integer_reciprocal_is_finite(divisor: int)
    requires
        divisor > 0,
    ensures
        !NumberView::Integer(1).div_overflows(NumberView::Integer(divisor)),
;

} // end verus!

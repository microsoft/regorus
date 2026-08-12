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

use core::cmp::Ordering;
use crate::number::*;
use super::bigint_assumptions::*;
use super::f64_assumptions::*;
use vstd::float::*;
use vstd::std_specs::cmp::*;
use vstd::std_specs::convert::*;

pub assume_specification[ <Number as Clone>::clone ](n: &Number) -> (res: Number)
    ensures
        res@ == n@,
;

pub enum NumberView {
    Integer(int),
    Float(f64),
}

impl View for Number
{
    type V = NumberView;

    open(crate) spec fn view(&self) -> NumberView
    {
        match self {
            Number::UInt(n) => NumberView::Integer(n as int),
            Number::Int(n) => NumberView::Integer(n as int),
            Number::Float(f) => NumberView::Float(*f),
            Number::BigInt(b) => NumberView::Integer(b@),
        }
    }
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

impl NumberView {
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
        match (self, rhs) {
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
        match (self, rhs) {
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
        match (self, rhs) {
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
        match (self, rhs) {
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

}

impl FromSpecImpl<BigInt> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: BigInt) -> Number;
}

impl FromSpecImpl<u64> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: u64) -> Number;
}

impl FromSpecImpl<usize> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: usize) -> Number;
}

impl FromSpecImpl<u128> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: u128) -> Number;
}

impl FromSpecImpl<i64> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: i64) -> Number;
}

impl FromSpecImpl<i128> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: i128) -> Number;
}

impl FromSpecImpl<f64> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: f64) -> Number;
}

impl PartialEqSpecImpl for Number {
    open spec fn obeys_eq_spec() -> bool
    {
        false
    }

    open spec fn eq_spec(&self, other: &Self) -> bool
    {
        *self == *other
    }
}

impl OrdSpecImpl for Number {
    // `Number::cmp` is specified directly in terms of `NumberView`, so there's
    // no need for a `cmp_spec` that would expose the internal representation.
    open spec fn obeys_cmp_spec() -> bool
    {
        false
    }

    uninterp spec fn cmp_spec(&self, other: &Self) -> Ordering;
}

} // end verus!

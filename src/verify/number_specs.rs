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

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
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
        res == n,
;

pub enum NumberView {
    Integer(int),
    Float(f64),
}

impl View for Number
{
    type V = NumberView;

    open spec fn view(&self) -> NumberView
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
        if ieee_float_cast::<u64, f64>(ieee_float_cast::<f64, u64>(value)).eq_spec(&value) {
            Some(ieee_float_cast::<f64, u64>(value) as int)
        }
        else {
            None
        }
    }
    else {
        if ieee_float_cast::<i64, f64>(ieee_float_cast::<f64, i64>(value)).eq_spec(&value) {
            Some(ieee_float_cast::<f64, i64>(value) as int)
        }
        else {
            None
        }
    }
}

impl NumberView {
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
                    &&& match #[trigger] super::bigint_assumptions::ToPrimitiveSpec::spec_to_f64(&bi) {
                        Some(x) => f == x,
                        None => f == if v < 0 { spec_f64_neg_infinity() } else { spec_f64_infinity() }
                    }
                }
            },
            NumberView::Float(v) => f == v,
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

impl Number {
    pub open spec fn spec_to_f64_lossy(&self) -> f64
    {
        match *self {
            Number::UInt(v) => ieee_float_cast::<u64, f64>(v),
            Number::Int(v) => ieee_float_cast::<i64, f64>(v),
            Number::Float(v) => v,
            Number::BigInt(v) => {
                if let Some(f) = <BigInt as ToPrimitiveSpec>::spec_to_f64(&v) {
                    f
                } else if v@ < 0 {
                    spec_f64_neg_infinity()
                } else {
                    spec_f64_infinity()
                }
            },
        }
    }
}

impl OrdSpecImpl for Number {
    open spec fn obeys_cmp_spec() -> bool
    {
        true
    }

    open spec fn cmp_spec(&self, other: &Self) -> Ordering
    {
         match (self@.to_int(), other@.to_int()) {
             (Some(n1), Some(n2)) => n1.cmp_spec(&n2),
             _ => {
                 let f1 = self.spec_to_f64_lossy();
                 let f2 = other.spec_to_f64_lossy();
                 f1.partial_cmp_spec(&f2).unwrap_or(Ordering::Equal)
            },
        }
    }
}

} // end verus!

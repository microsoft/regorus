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

use alloc::format;
use alloc::string::{String, ToString};
use core::cmp::Ordering;
use core::fmt::{Debug, Display, Formatter};
use core::str::FromStr;

use anyhow::{anyhow, bail, Result};
use num_bigint::BigInt as NumBigInt;
#[allow(unused)]
use num_traits::float::FloatCore;
use num_traits::{One, Signed, ToPrimitive, Zero};

use serde::ser::Serializer;
use serde::Serialize;

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verify::bigint_assumptions::*;
#[cfg(verus_keep_ghost)]
use crate::verify::bigint_proofs::*;
#[cfg(verus_keep_ghost)]
use crate::verify::f64_assumptions::*;
#[cfg(verus_keep_ghost)]
use crate::verify::number_proofs::*;
#[cfg(verus_keep_ghost)]
use crate::verify::number_specs::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_keep_ghost)]
use vstd::float::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::*;

use crate::*;

pub type BigInt = NumBigInt;

#[derive(Debug)]
pub struct NumericOverflowError {
    operation: &'static str,
}

impl NumericOverflowError {
    #[cfg(feature = "rvm")]
    pub const fn operation(&self) -> &'static str {
        self.operation
    }
}

impl Display for NumericOverflowError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "numeric overflow in {}", self.operation)
    }
}

impl core::error::Error for NumericOverflowError {}

#[verus_verify]
const F64_SAFE_INTEGER: f64 = 9_007_199_254_740_992.0; // 2^53

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone)]
pub enum Number {
    UInt(u64),
    Int(i64),
    Float(f64),
    BigInt(Rc<BigInt>),
}

#[verus_verify]
impl Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value@),
    )]
    fn from_bigint_owned(value: BigInt) -> Self {
        if value.is_zero() {
            return Number::Int(0);
        }

        if value.is_negative() {
            if let Some(i) = value.to_i64() {
                return Number::Int(i);
            }
        } else if let Some(u) = value.to_u64() {
            return Number::UInt(u);
        } else if let Some(i) = value.to_i64() {
            return Number::Int(i);
        }

        Number::BigInt(Rc::new(value))
    }

    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value as int),
    )]
    fn from_i128(value: i128) -> Self {
        if value >= 0 {
            if let Ok(u) = u64::try_from(value) {
                return Number::UInt(u);
            }
        }

        if let Ok(i) = i64::try_from(value) {
            Number::Int(i)
        } else {
            Number::BigInt(Rc::new(BigInt::from(value)))
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => result matches Some(bi) && bi@ == n,
                NumberView::Float(f) =>
                {
                    match result {
                        Some(bi) => float_to_small_int(f) == Some(bi@),
                        None => float_to_small_int(f) is None,
                    }
                },
            },
    )]
    fn to_bigint_owned(&self) -> Option<BigInt> {
        match self {
            Number::UInt(v) => Some(BigInt::from(*v)),
            Number::Int(v) => Some(BigInt::from(*v)),
            Number::BigInt(v) => Some((**v).clone()),
            Number::Float(f) => Self::float_to_small_bigint(*f),
        }
    }

    #[verus_spec(result =>
        ensures
            match result {
                Some(bi) => float_to_small_int(value) == Some(bi@),
                None => float_to_small_int(value) is None,
            },
    )]
    fn float_to_small_bigint(value: f64) -> Option<BigInt> {
        proof! {
            axiom_f64_obeys_eq_spec();
            axiom_f64_obeys_partial_cmp_spec();
            axiom_f64_ops_deterministic();
            axiom_f64_comparisons_match_ieee();
        }

        if !value.is_finite() || value.fract() != 0.0 {
            return None;
        }

        if value.abs() > F64_SAFE_INTEGER {
            return None;
        }

        if value >= 0.0 {
            let u = value as u64;
            if (u as f64) == value {
                return Some(BigInt::from(u));
            }
        } else {
            let i = value as i64;
            if (i as f64) == value {
                return Some(BigInt::from(i));
            }
        }

        None
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => result matches Some(bi) && bi@ == n,
                NumberView::Float(f) =>
                    match float_to_small_int(f) {
                        Some(i) => result matches Some(bi) && bi@ == i,
                        None => result is None,
                    },
            },
    )]
    fn to_bigint_rc(&self) -> Option<Rc<BigInt>> {
        match self {
            Number::BigInt(v) => Some(v.clone()),
            _ => self.to_bigint_owned().map(Rc::new),
        }
    }

    #[verus_spec(result =>
        ensures
            self@.to_f64_lossy_ensures(result),
    )]
    fn to_f64_lossy(&self) -> f64 {
        proof! { axiom_f64_ops_deterministic(); }
        match self {
            Number::UInt(v) => *v as f64,
            Number::Int(v) => *v as f64,
            Number::Float(v) => *v,
            Number::BigInt(v) => {
                if let Some(f) = v.to_f64() {
                    f
                } else if v.is_negative() {
                    f64::NEG_INFINITY
                } else {
                    f64::INFINITY
                }
            }
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => result == (n == 0),
                NumberView::Float(f) => result == f.eq_spec(&0.0f64),
            },
    )]
    fn is_zero(&self) -> bool {
        proof! { axiom_f64_obeys_eq_spec(); }
        match self {
            Number::UInt(0) | Number::Int(0) => true,
            Number::Float(f) => *f == 0.0,
            Number::BigInt(v) => v.is_zero(),
            _ => false,
        }
    }

    #[verus_spec(result =>
        ensures
            result@ == normalize_float(value),
    )]
    fn normalize_float(value: f64) -> Number {
        if let Some(i) = Self::float_to_small_bigint(value) {
            return Self::from_bigint_owned(i);
        }
        Number::Float(value)
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(v) => if 0 <= v <= u32::MAX { result == Some(v as u32) } else { result is None },
                NumberView::Float(_) => result is None,
            },
    )]
    fn as_u32(&self) -> Option<u32> {
        match self {
            Number::UInt(v) if *v <= u32::MAX as u64 => Some(*v as u32),
            Number::Int(v) if *v >= 0 && *v <= u32::MAX as i64 => Some(*v as u32),
            Number::BigInt(v) => v.to_u32(),
            _ => None,
        }
    }
}

impl Debug for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.format_decimal())
    }
}

impl Serialize for Number {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = self.format_decimal();
        let v = serde_json::Number::from_str(&s)
            .map_err(|_| serde::ser::Error::custom("could not serialize number"))?;
        v.serialize(serializer)
    }
}

#[verus_verify]
impl From<BigInt> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value@),
    )]
    fn from(value: BigInt) -> Self {
        Number::from_bigint_owned(value)
    }
}

#[verus_verify]
impl From<u64> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value as int),
    )]
    fn from(value: u64) -> Self {
        Number::UInt(value)
    }
}

#[verus_verify]
impl From<usize> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value as int),
    )]
    fn from(value: usize) -> Self {
        Number::UInt(value as u64)
    }
}

#[verus_verify]
impl From<u128> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value as int),
    )]
    fn from(value: u128) -> Self {
        if let Ok(n) = u64::try_from(value) {
            Number::UInt(n)
        } else {
            Number::from_bigint_owned(BigInt::from(value))
        }
    }
}

#[verus_verify]
impl From<i64> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value as int),
    )]
    fn from(value: i64) -> Self {
        Number::Int(value)
    }
}

#[verus_verify]
impl From<i128> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Integer(value as int),
    )]
    fn from(value: i128) -> Self {
        Number::from_i128(value)
    }
}

#[verus_verify]
impl From<f64> for Number {
    #[verus_spec(result =>
        ensures
            result@ == NumberView::Float(value),
    )]
    fn from(value: f64) -> Self {
        Number::Float(value)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseNumberError;

impl FromStr for Number {
    type Err = ParseNumberError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed = s.trim();
        if trimmed.is_empty() {
            return Err(ParseNumberError);
        }

        let canonical = trimmed.replace('_', "");
        if canonical.is_empty() {
            return Err(ParseNumberError);
        }

        let normalized = if let Some(rest) = canonical.strip_prefix("-.") {
            format!("-0.{rest}")
        } else if let Some(rest) = canonical.strip_prefix("+.") {
            format!("+0.{rest}")
        } else if let Some(rest) = canonical.strip_prefix('.') {
            format!("0.{rest}")
        } else {
            canonical
        };

        let normalized_ref = normalized.as_str();
        let is_integer_literal = !normalized_ref.contains('.')
            && !normalized_ref.contains('e')
            && !normalized_ref.contains('E');

        if is_integer_literal {
            let (sign, digits) = if let Some(rest) = normalized_ref.strip_prefix('-') {
                (-1, rest)
            } else if let Some(rest) = normalized_ref.strip_prefix('+') {
                (1, rest)
            } else {
                (1, normalized_ref)
            };

            if !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()) {
                if let Some(mut value) = BigInt::parse_bytes(digits.as_bytes(), 10) {
                    if sign < 0 {
                        value = -value;
                    }
                    return Ok(Number::from_bigint_owned(value));
                }
            }
        }

        if let Some(value) = parse_scientific_bigint(normalized_ref) {
            return Ok(Number::from_bigint_owned(value));
        }

        match normalized_ref.parse::<f64>() {
            Ok(value) if value.is_finite() => Ok(Number::Float(value)),
            _ => Err(ParseNumberError),
        }
    }
}

#[verus_verify]
impl Number {
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            NumberView::Float(f).cmp_ensures(NumberView::Integer(n as int), result),
    )]
    fn cmp_float_uint(f: f64, n: u64) -> Ordering {
        if !f.is_finite() {
            return if f.is_sign_negative() {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        if f < 0.0 {
            return Ordering::Less;
        }
        // `u64::MAX as f64` rounds up to 2^64, strictly above every u64.
        if f >= u64::MAX as f64 {
            return Ordering::Greater;
        }

        let truncated = f as u64;
        match truncated.cmp(&n) {
            Ordering::Equal if f < truncated as f64 => Ordering::Less,
            Ordering::Equal if f > truncated as f64 => Ordering::Greater,
            ordering => ordering,
        }
    }

    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            NumberView::Float(f).cmp_ensures(NumberView::Integer(n as int), result),
    )]
    fn cmp_float_sint(f: f64, n: i64) -> Ordering {
        if !f.is_finite() {
            return if f.is_sign_negative() {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        if f < i64::MIN as f64 {
            return Ordering::Less;
        }
        // `i64::MAX as f64` rounds up to 2^63, strictly above every i64.
        if f >= i64::MAX as f64 {
            return Ordering::Greater;
        }

        let truncated = f as i64;
        match truncated.cmp(&n) {
            Ordering::Equal if f < truncated as f64 => Ordering::Less,
            Ordering::Equal if f > truncated as f64 => Ordering::Greater,
            ordering => ordering,
        }
    }

    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            NumberView::Integer(n@).cmp_ensures(NumberView::Integer(value as int), result),
    )]
    fn cmp_bigint_uint(n: &BigInt, value: u64) -> Ordering {
        if n.is_negative() {
            Ordering::Less
        } else {
            n.to_u64().map_or(Ordering::Greater, |n| n.cmp(&value))
        }
    }

    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            NumberView::Integer(n@).cmp_ensures(NumberView::Integer(value as int), result),
    )]
    fn cmp_bigint_sint(n: &BigInt, value: i64) -> Ordering {
        n.to_i64().map_or_else(
            || {
                if n.is_negative() {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            },
            |n| n.cmp(&value),
        )
    }

    // Exact comparison of a finite float against an exact integer. `FloatCore::integer_decode`
    // splits a finite float into `sign * mantissa * 2^exp`. Integral values scale the bounded
    // mantissa and compare it with the borrowed BigInt; fractional values compare their bounded
    // integer part first and use the fraction only as a tie-break. Neither operand is rounded
    // through f64, and the stored BigInt is never cloned or shifted. The previous
    // `to_f64_lossy()` path merged distinct values (`2^63 == 2^63 + 1`) and mapped every
    // out-of-range BigInt to +/-Inf.
    //
    // Verus cannot translate `FloatCore::integer_decode`, BigInt shifts, or
    // `f64::is_sign_negative`, so this exact comparison is the narrow trusted boundary.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            NumberView::Float(f).cmp_ensures(NumberView::Integer(n@), result),
    )]
    fn cmp_float_int(f: f64, n: &BigInt) -> Ordering {
        if !f.is_finite() {
            // The tail ranks -NaN/-Inf below every exact integer and +Inf/+NaN above every one,
            // consistent with the `total_cmp` ranking in `cmp_float` below.
            return if f.is_sign_negative() {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }

        let (mantissa, exp, _) = f.integer_decode();

        if exp < 0 {
            // A negative decoded exponent bounds the magnitude below 2^53. Compare the truncated
            // integer parts without allocating, then use the fractional remainder as the tie-break.
            let truncated = f as i64;
            match Self::cmp_bigint_sint(n, truncated).reverse() {
                Ordering::Equal if f < truncated as f64 => Ordering::Less,
                Ordering::Equal if f > truncated as f64 => Ordering::Greater,
                ordering => ordering,
            }
        } else {
            // The temporary is bounded by binary64 itself (at most 1024 bits); the potentially
            // arbitrarily large stored BigInt is only borrowed, never cloned or shifted.
            let mantissa = if f.is_sign_negative() {
                -BigInt::from(mantissa)
            } else {
                BigInt::from(mantissa)
            };
            (mantissa << (exp as usize)).cmp(n)
        }
    }

    // A total order over `f64` values.
    //
    // Finite floats use exact numeric comparison, with `-0.0 == 0.0`. The complete order is:
    //
    // negative NaNs < -Inf < negative finite numbers
    //     < (-0.0 == +0.0 == integer 0)
    //     < positive finite numbers < +Inf < positive NaNs
    //
    // NaNs of the same sign follow `f64::total_cmp`'s bit-pattern order. No pair is treated as
    // Equal merely because `partial_cmp` returned None.
    //
    // Verus cannot translate `f64::total_cmp`; the contract exactly models both the finite
    // comparison and non-finite total-order branches.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            NumberView::Float(a).cmp_ensures(NumberView::Float(b), result),
    )]
    fn cmp_float(a: f64, b: f64) -> Ordering {
        if a.is_finite() && b.is_finite() {
            if a < b {
                Ordering::Less
            } else if a > b {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        } else {
            a.total_cmp(&b)
        }
    }
}

#[verus_verify]
impl PartialEq for Number {
    // `Ordering`'s standard-library `PartialEq` implementation has no Verus specification.
    // The contract pins equality to the exact comparison model used by `Ord`.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            self@.eq_ensures(other@, result),
    )]
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Number {}

#[verus_verify]
impl Ord for Number {
    // Verus cannot currently translate the float decoding, standard ordering, and BigInt
    // operations used by the helpers, or prove the mixed-direction reversal through `Ordering`.
    // Keep the executable boundary external with an exact public contract.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            self@.cmp_ensures(other@, result),
    )]
    fn cmp(&self, other: &Self) -> Ordering {
        proof! {
            axiom_f64_obeys_partial_cmp_spec();
            axiom_bigint_obeys_cmp_spec();
        }
        match (self, other) {
            (Number::Float(a), Number::Float(b)) => Self::cmp_float(*a, *b),
            (Number::Float(a), Number::UInt(b)) => Self::cmp_float_uint(*a, *b),
            (Number::Float(a), Number::Int(b)) => Self::cmp_float_sint(*a, *b),
            (Number::Float(a), Number::BigInt(b)) => Self::cmp_float_int(*a, b),
            (Number::UInt(a), Number::Float(b)) => Self::cmp_float_uint(*b, *a).reverse(),
            (Number::Int(a), Number::Float(b)) => Self::cmp_float_sint(*b, *a).reverse(),
            (Number::BigInt(a), Number::Float(b)) => Self::cmp_float_int(*b, a).reverse(),
            (Number::UInt(a), Number::UInt(b)) => a.cmp(b),
            (Number::Int(a), Number::Int(b)) => a.cmp(b),
            (Number::UInt(a), Number::Int(b)) => {
                if *b < 0 {
                    Ordering::Greater
                } else {
                    a.cmp(&(*b as u64))
                }
            }
            (Number::Int(a), Number::UInt(b)) => {
                if *a < 0 {
                    Ordering::Less
                } else {
                    (*a as u64).cmp(b)
                }
            }
            (Number::BigInt(a), Number::BigInt(b)) => a.cmp(b),
            (Number::BigInt(a), Number::UInt(b)) => Self::cmp_bigint_uint(a, *b),
            (Number::UInt(a), Number::BigInt(b)) => Self::cmp_bigint_uint(b, *a).reverse(),
            (Number::BigInt(a), Number::Int(b)) => Self::cmp_bigint_sint(a, *b),
            (Number::Int(a), Number::BigInt(b)) => Self::cmp_bigint_sint(b, *a).reverse(),
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[verus_verify]
impl Number {
    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => {
                    if 0 <= n <= u128::MAX {
                        result matches Some(value) && value as int == n
                    } else {
                        result is None
                    }
                },
                NumberView::Float(f) => {
                    if f.is_finite_spec()
                       && f.ieee_ge(0.0f64)
                       && spec_f64_fract(f).eq_spec(&0.0f64)
                       && ieee_float_cast::<u128, f64>(ieee_float_cast::<f64, u128>(f)).eq_spec(&f) {
                        result matches Some(value) && value == ieee_float_cast::<f64, u128>(f)
                    }
                    else {
                        result is None
                    }
                },
            },
    )]
    pub fn as_u128(&self) -> Option<u128> {
        proof! {
            axiom_f64_obeys_eq_spec();
            axiom_f64_obeys_partial_cmp_spec();
            axiom_f64_ops_deterministic();
            axiom_f64_comparisons_match_ieee();
        }
        match self {
            Number::UInt(v) => Some(*v as u128),
            Number::Int(v) if *v >= 0 => Some(*v as u128),
            Number::BigInt(v) => v.to_u128(),
            Number::Float(f) => {
                if f.is_finite() && *f >= 0.0 && f.fract() == 0.0 {
                    let candidate = *f as u128;
                    if (candidate as f64) == *f {
                        return Some(candidate);
                    }
                }
                None
            }
            _ => None,
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => {
                    if i128::MIN <= n <= i128::MAX {
                        result matches Some(value) && value as int == n
                    } else {
                        result is None
                    }
                },
                NumberView::Float(f) => {
                    if f.is_finite_spec()
                       && spec_f64_fract(f).eq_spec(&0.0f64)
                       && ieee_float_cast::<i128, f64>(ieee_float_cast::<f64, i128>(f)).eq_spec(&f) {
                        result matches Some(value) && value == ieee_float_cast::<f64, i128>(f)
                    }
                    else {
                        result is None
                    }
                },
            },
    )]
    pub fn as_i128(&self) -> Option<i128> {
        proof! {
            axiom_f64_obeys_eq_spec();
            axiom_f64_ops_deterministic();
        }
        match self {
            Number::UInt(v) => Some(*v as i128),
            Number::Int(v) => Some(*v as i128),
            Number::BigInt(v) => v.to_i128(),
            Number::Float(f) => {
                if f.is_finite() && f.fract() == 0.0 {
                    let candidate = *f as i128;
                    if (candidate as f64) == *f {
                        return Some(candidate);
                    }
                }
                None
            }
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => {
                    if 0 <= n <= u64::MAX {
                        result matches Some(value) && value as int == n
                    } else {
                        result is None
                    }
                },
                NumberView::Float(f) => {
                    if f.is_finite_spec()
                       && f.ieee_ge(0.0f64)
                       && spec_f64_fract(f).eq_spec(&0.0f64)
                       && f.ieee_le(ieee_float_cast::<u64, f64>(u64::MAX))
                       && ieee_float_cast::<u64, f64>(ieee_float_cast::<f64, u64>(f)).eq_spec(&f) {
                        result matches Some(value) && value == ieee_float_cast::<f64, u64>(f)
                    }
                    else {
                        result is None
                    }
                },
            },
    )]
    pub fn as_u64(&self) -> Option<u64> {
        proof! {
            axiom_f64_obeys_eq_spec();
            axiom_f64_obeys_partial_cmp_spec();
            axiom_f64_ops_deterministic();
            axiom_f64_comparisons_match_ieee();
        }
        match self {
            Number::UInt(v) => Some(*v),
            Number::Int(v) if *v >= 0 => Some(*v as u64),
            Number::BigInt(v) => v.to_u64(),
            Number::Float(f) => {
                if f.is_finite() && *f >= 0.0 && f.fract() == 0.0 && *f <= u64::MAX as f64 {
                    let candidate = *f as u64;
                    if (candidate as f64) == *f {
                        return Some(candidate);
                    }
                }
                None
            }
            _ => None,
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => {
                    if i64::MIN <= n <= i64::MAX {
                        result matches Some(value) && value as int == n
                    } else {
                        result is None
                    }
                },
                NumberView::Float(f) => {
                    if f.is_finite_spec()
                       && spec_f64_fract(f).eq_spec(&0.0f64)
                       && f.ieee_ge(ieee_float_cast::<i64, f64>(i64::MIN))
                       && f.ieee_le(ieee_float_cast::<i64, f64>(i64::MAX))
                       && ieee_float_cast::<i64, f64>(ieee_float_cast::<f64, i64>(f)).eq_spec(&f) {
                        result matches Some(value) && value == ieee_float_cast::<f64, i64>(f)
                    }
                    else {
                        result is None
                    }
                },
            },
    )]
    pub fn as_i64(&self) -> Option<i64> {
        proof! {
            axiom_f64_obeys_eq_spec();
            axiom_f64_obeys_partial_cmp_spec();
            axiom_f64_ops_deterministic();
            axiom_f64_comparisons_match_ieee();
        }
        match self {
            Number::UInt(v) if *v <= i64::MAX as u64 => Some(*v as i64),
            Number::Int(v) => Some(*v),
            Number::BigInt(v) => v.to_i64(),
            Number::Float(f) => {
                if f.is_finite()
                    && f.fract() == 0.0
                    && *f >= i64::MIN as f64
                    && *f <= i64::MAX as f64
                {
                    let candidate = *f as i64;
                    if (candidate as f64) == *f {
                        return Some(candidate);
                    }
                }
                None
            }
            _ => None,
        }
    }

    #[verus_spec(result =>
        ensures
            match (self@, result) {
                (NumberView::Float(f), Some(value)) => f.is_finite_spec() && value == f,
                (NumberView::Float(f), None) => !f.is_finite_spec(),
                (NumberView::Integer(n), Some(value)) => {
                    &&& -9_007_199_254_740_992 <= n <= 9_007_199_254_740_992
                    &&& self@.to_f64_lossy_ensures(value)
                },
                // The bounds intentionally overlap at +/-2^53: primitive variants return
                // Some there, while a BigInt variant with the same NumberView returns None.
                (NumberView::Integer(n), None) => {
                    n <= -9_007_199_254_740_992 || 9_007_199_254_740_992 <= n
                },
            },
    )]
    pub fn as_f64(&self) -> Option<f64> {
        proof! {
            axiom_f64_ops_deterministic();
            axiom_f64_safe_integer_casts();
            lemma_bigint_bits_le_53();
        }
        match self {
            Number::Float(f) if f.is_finite() => Some(*f),
            Number::UInt(v) if *v <= F64_SAFE_INTEGER as u64 => Some(*v as f64),
            Number::Int(v) if (*v as i128).abs() <= F64_SAFE_INTEGER as i128 => Some(*v as f64),
            Number::BigInt(v) => {
                if v.bits() <= 53 {
                    v.to_f64()
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => result matches Some(bi) && bi@ == n,
                NumberView::Float(f) => {
                    match float_to_small_int(f) {
                        Some(i) => result matches Some(bi) && bi@ == i,
                        None => result is None,
                    }
                },
            },
    )]
    pub fn as_big(&self) -> Option<Rc<BigInt>> {
        self.to_bigint_rc()
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => result matches Ok(bi) && bi@ == n,
                NumberView::Float(f) => {
                    match float_to_small_int(f) {
                        Some(i) => result matches Ok(bi) && bi@ == i,
                        None => result is Err,
                    }
                },
            },
    )]
    pub fn to_big(&self) -> Result<Rc<BigInt>> {
        self.as_big()
            .ok_or_else(|| anyhow!("Number::to_big failed"))
    }

    // The float paths below promote their operands to f64, which can overflow when an
    // operand is a BigInt outside f64 range. Rego's number domain excludes Inf and NaN,
    // so report an error instead of returning a fabricated non-finite value.
    // Verus cannot translate construction of the external anyhow payload; keep that
    // unsupported detail behind a helper while verifying the branch that returns it.
    #[verus_verify(external_body)]
    fn numeric_overflow_error(operation: &'static str) -> anyhow::Error {
        NumericOverflowError { operation }.into()
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(result) => result == value && value.is_finite_spec(),
                Err(_) => !value.is_finite_spec(),
            },
    )]
    fn checked_float(value: f64, operation: &'static str) -> Result<f64> {
        if value.is_finite() {
            Ok(value)
        } else {
            Err(Self::numeric_overflow_error(operation))
        }
    }

    // Non-exact division promotes to f64 like add/sub/mul, but the quotient is not
    // normalized back to an integer.
    #[verus_spec(result =>
        requires
            !rhs@.is_zero(),
            match (self@, rhs@) {
                (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                    vstd::arithmetic::div_mod::rust_rem(lhs, rhs) != 0,
                _ => true,
            },
        ensures
            match result {
                Ok(value) => self@.div_ensures(rhs@, value@),
                Err(_) => self@.div_overflows(rhs@),
            },
    )]
    fn float_quotient(&self, rhs: &Self) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            lemma_div_ensures_cases(self@, rhs@);
        }
        let quotient = Self::checked_float(self.to_f64_lossy() / rhs.to_f64_lossy(), "division")?;
        Ok(Number::Float(quotient))
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(()) => old(self)@.add_ensures(rhs@, final(self)@),
                Err(_) => old(self)@.add_overflows(rhs@),
            },
    )]
    pub fn add_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.add(rhs)?;
        Ok(())
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(value) => self@.add_ensures(rhs@, value@),
                Err(_) => self@.add_overflows(rhs@),
            },
    )]
    pub fn add(&self, rhs: &Self) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            axiom_bigint_obeys_add_spec();
            axiom_bigint_obeys_add_assign_spec();
        }

        match (self, rhs) {
            (Number::Float(_), _) | (_, Number::Float(_)) => {
                let sum =
                    Self::checked_float(self.to_f64_lossy() + rhs.to_f64_lossy(), "addition")?;
                Ok(Number::normalize_float(sum))
            }
            (Number::UInt(a), Number::UInt(b)) => {
                if let Some(sum) = a.checked_add(*b) {
                    Ok(Number::UInt(sum))
                } else {
                    Ok(Number::from_bigint_owned(
                        BigInt::from(*a) + BigInt::from(*b),
                    ))
                }
            }
            (Number::Int(a), Number::Int(b)) => {
                if let Some(sum) = a.checked_add(*b) {
                    Ok(Number::Int(sum))
                } else {
                    Ok(Number::from_bigint_owned(
                        BigInt::from(*a) + BigInt::from(*b),
                    ))
                }
            }
            (Number::Int(a), Number::UInt(b)) | (Number::UInt(b), Number::Int(a)) => {
                Ok(Number::from_i128(*a as i128 + *b as i128))
            }
            (Number::BigInt(a), Number::BigInt(b)) => {
                Ok(Number::from_bigint_owned((**a).clone() + (**b).clone()))
            }
            (Number::BigInt(a), other) | (other, Number::BigInt(a)) => {
                let mut sum = (**a).clone();
                sum += other.to_bigint_owned().unwrap();
                Ok(Number::from_bigint_owned(sum))
            }
        }
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(()) => old(self)@.sub_ensures(rhs@, final(self)@),
                Err(_) => old(self)@.sub_overflows(rhs@),
            },
    )]
    pub fn sub_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.sub(rhs)?;
        Ok(())
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(value) => self@.sub_ensures(rhs@, value@),
                Err(_) => self@.sub_overflows(rhs@),
            },
    )]
    pub fn sub(&self, rhs: &Self) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            axiom_bigint_obeys_sub_spec();
            axiom_bigint_obeys_sub_assign_spec();
        }

        match (self, rhs) {
            (Number::Float(_), _) | (_, Number::Float(_)) => {
                let diff =
                    Self::checked_float(self.to_f64_lossy() - rhs.to_f64_lossy(), "subtraction")?;
                Ok(Number::normalize_float(diff))
            }
            (Number::UInt(a), Number::UInt(b)) => {
                if a >= b {
                    Ok(Number::UInt(a - b))
                } else {
                    Ok(Number::from_i128(*a as i128 - *b as i128))
                }
            }
            (Number::Int(a), Number::Int(b)) => {
                if let Some(diff) = a.checked_sub(*b) {
                    Ok(Number::Int(diff))
                } else {
                    Ok(Number::from_bigint_owned(
                        BigInt::from(*a) - BigInt::from(*b),
                    ))
                }
            }
            (Number::Int(a), Number::UInt(b)) => Ok(Number::from_i128(*a as i128 - *b as i128)),
            (Number::UInt(a), Number::Int(b)) => Ok(Number::from_i128(*a as i128 - *b as i128)),
            (Number::BigInt(a), Number::BigInt(b)) => {
                Ok(Number::from_bigint_owned((**a).clone() - (**b).clone()))
            }
            (Number::BigInt(a), other) => {
                let mut diff = (**a).clone();
                diff -= other.to_bigint_owned().unwrap();
                Ok(Number::from_bigint_owned(diff))
            }
            (other, Number::BigInt(b)) => {
                let mut diff = other.to_bigint_owned().unwrap();
                diff -= (**b).clone();
                Ok(Number::from_bigint_owned(diff))
            }
        }
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(()) => old(self)@.mul_ensures(rhs@, final(self)@),
                Err(_) => old(self)@.mul_overflows(rhs@),
            },
    )]
    pub fn mul_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.mul(rhs)?;
        Ok(())
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(value) => self@.mul_ensures(rhs@, value@),
                Err(_) => self@.mul_overflows(rhs@),
            },
    )]
    pub fn mul(&self, rhs: &Self) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            axiom_bigint_obeys_mul_spec();
            if let (Number::UInt(lhs), Number::UInt(rhs_value)) = (self, rhs) {
                assert((*lhs as int) * (*rhs_value as int) <= u128::MAX as int)
                    by(nonlinear_arith);
            }
            // Some cases are handled by an or-pattern that computes the product
            // with the operands swapped.
            if self@ is Integer && rhs@ is Integer {
                assert(self@->Integer_0 * rhs@->Integer_0 == rhs@->Integer_0
                    * self@->Integer_0) by(nonlinear_arith);
            }
        }

        match (self, rhs) {
            (Number::Float(_), _) | (_, Number::Float(_)) => {
                let product = Self::checked_float(
                    self.to_f64_lossy() * rhs.to_f64_lossy(),
                    "multiplication",
                )?;
                Ok(Number::normalize_float(product))
            }
            (Number::UInt(a), Number::UInt(b)) => {
                let product = (*a as u128) * (*b as u128);
                if let Ok(v) = u64::try_from(product) {
                    Ok(Number::UInt(v))
                } else {
                    Ok(Number::from_bigint_owned(BigInt::from(product)))
                }
            }
            (Number::Int(a), Number::Int(b)) => {
                if let Some(prod) = a.checked_mul(*b) {
                    Ok(Number::Int(prod))
                } else {
                    Ok(Number::from_bigint_owned(
                        BigInt::from(*a) * BigInt::from(*b),
                    ))
                }
            }
            (Number::Int(a), Number::UInt(b)) | (Number::UInt(b), Number::Int(a)) => {
                let lhs = *a as i128;
                let rhs_val = *b as i128;
                if let Some(prod) = lhs.checked_mul(rhs_val) {
                    Ok(Number::from_i128(prod))
                } else {
                    Ok(Number::from_bigint_owned(
                        BigInt::from(*a) * BigInt::from(*b),
                    ))
                }
            }
            (Number::BigInt(a), Number::BigInt(b)) => {
                Ok(Number::from_bigint_owned((**a).clone() * (**b).clone()))
            }
            (Number::BigInt(a), other) | (other, Number::BigInt(a)) => {
                let product = (**a).clone() * other.to_bigint_owned().unwrap();
                Ok(Number::from_bigint_owned(product))
            }
        }
    }

    #[verus_spec(result =>
        ensures
            match result {
                Ok(value) => self@.div_ensures(rhs@, value@),
                Err(_) => rhs@.is_zero() || self@.div_overflows(rhs@),
            },
    )]
    pub fn divide(self, rhs: &Self) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            axiom_bigint_obeys_div_rem_spec();
            lemma_div_ensures_cases(self@, rhs@);
            lemma_number_primitive_division_facts(&self, rhs);
        }

        if rhs.is_zero() {
            bail!("division by zero");
        }

        if matches!(self, Number::Float(_)) || matches!(rhs, Number::Float(_)) {
            return self.float_quotient(rhs);
        }

        match (&self, rhs) {
            (Number::UInt(a), Number::UInt(b)) => {
                if *a % *b == 0 {
                    Ok(Number::UInt(*a / *b))
                } else {
                    self.float_quotient(rhs)
                }
            }
            (Number::Int(a), Number::Int(b)) => {
                if *a == i64::MIN && *b == -1 {
                    // Rust panics on i64::MIN % -1i64, so handle it specially
                    let quotient = BigInt::from(*a) / BigInt::from(*b);
                    Ok(Number::from_bigint_owned(quotient))
                } else if *a % *b == 0 {
                    if let Some(q) = a.checked_div(*b) {
                        proof! {
                            lemma_checked_div_matches_rust_i64(*a, *b, q);
                        }
                        Ok(Number::Int(q))
                    } else {
                        let quotient = BigInt::from(*a) / BigInt::from(*b);
                        Ok(Number::from_bigint_owned(quotient))
                    }
                } else {
                    self.float_quotient(rhs)
                }
            }
            (Number::Int(a), Number::UInt(b)) => {
                let lhs = *a as i128;
                let rhs_i = *b as i128;
                if lhs % rhs_i == 0 {
                    Ok(Number::from_i128(lhs / rhs_i))
                } else {
                    self.float_quotient(rhs)
                }
            }
            (Number::UInt(a), Number::Int(b)) => {
                let lhs = *a as i128;
                let rhs_i = *b as i128;
                if lhs % rhs_i == 0 {
                    Ok(Number::from_i128(lhs / rhs_i))
                } else {
                    self.float_quotient(rhs)
                }
            }
            (Number::BigInt(a), Number::BigInt(b)) => {
                let remainder = (&**a) % (&**b);
                if remainder.is_zero() {
                    let quotient = (&**a) / (&**b);
                    Ok(Number::from_bigint_owned(quotient))
                } else {
                    self.float_quotient(rhs)
                }
            }
            (Number::BigInt(a), _) => {
                if let Some(b_big) = rhs.to_bigint_owned() {
                    let remainder = (&**a) % &b_big;
                    if remainder.is_zero() {
                        let quotient = (&**a) / &b_big;
                        Ok(Number::from_bigint_owned(quotient))
                    } else {
                        self.float_quotient(rhs)
                    }
                } else {
                    self.float_quotient(rhs)
                }
            }
            (_, Number::BigInt(b)) => {
                if let Some(a_big) = self.to_bigint_owned() {
                    let remainder = (&a_big) % (&**b);
                    if remainder.is_zero() {
                        let quotient = (&a_big) / (&**b);
                        Ok(Number::from_bigint_owned(quotient))
                    } else {
                        self.float_quotient(rhs)
                    }
                } else {
                    self.float_quotient(rhs)
                }
            }
            _ => self.float_quotient(rhs),
        }
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@.to_int()) {
                (Some(a), Some(b)) =>
                    if b == 0 {
                        result is Err
                    } else {
                        result matches Ok(value)
                            && value@ == NumberView::Integer(
                            vstd::arithmetic::div_mod::rust_rem(a, b),
                        )
                    },
                _ => result is Err,
            },
    )]
    pub fn modulo(self, rhs: &Self) -> Result<Number> {
        proof! {
            axiom_bigint_obeys_div_rem_spec();
        }

        // Conversion fails for a non-integral float, and also for an integral
        // one whose magnitude exceeds 2^53, which cannot be represented exactly.
        let (a, b) = match (self.to_bigint_owned(), rhs.to_bigint_owned()) {
            (Some(a), Some(b)) => (a, b),
            _ => bail!("modulo on floating-point number"),
        };

        if b.is_zero() {
            bail!("modulo by zero");
        }

        let rem = a % &b;
        Ok(Number::from_bigint_owned(rem))
    }

    #[verus_spec(result =>
        ensures
            result == match self@ {
                NumberView::Integer(_) => true,
                NumberView::Float(f) => f.is_finite_spec() && spec_f64_fract(f).eq_spec(&0.0f64),
            },
    )]
    pub fn is_integer(&self) -> bool {
        proof! { axiom_f64_obeys_eq_spec(); }
        match self {
            Number::Float(f) => f.is_finite() && f.fract() == 0.0,
            _ => true,
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(n) => result == (n >= 0),
                NumberView::Float(f) => result == spec_f64_is_sign_positive(f),
            },
    )]
    pub fn is_positive(&self) -> bool {
        match self {
            Number::UInt(_) => true,
            Number::Int(v) => *v >= 0,
            Number::BigInt(v) => !v.is_negative(),
            Number::Float(f) => f.is_sign_positive(),
        }
    }

    #[verus_spec(result =>
        ensures
            match (a@.to_int(), b@.to_int()) {
                (Some(lhs), Some(rhs)) =>
                    result matches Some((a, b)) && a@ == lhs && b@ == rhs,
                _ => result is None,
            }
    )]
    #[allow(clippy::if_then_some_else_none)]
    fn ensure_integers(a: &Number, b: &Number) -> Option<(BigInt, BigInt)> {
        if a.is_integer() && b.is_integer() {
            Some((a.to_bigint_owned()?, b.to_bigint_owned()?))
        } else {
            None
        }
    }

    #[verus_spec(result =>
        ensures
            match self@.to_int() {
                Some(value) => result matches Some(big) && big@ == value,
                None => result is None,
            },
    )]
    fn ensure_integer(&self) -> Option<BigInt> {
        if self.is_integer() {
            self.to_bigint_owned()
        } else {
            None
        }
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@.to_int()) {
                (Some(a), Some(b)) =>
                    result matches Some(value) &&
                    value@ == NumberView::Integer(spec_bigint_bitand(a, b)),
                _ => result is None,
            },
    )]
    pub fn and(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_bitand_spec(); }
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a & b))
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@.to_int()) {
                (Some(a), Some(b)) =>
                    result matches Some(value)
                    && value@ == NumberView::Integer(spec_bigint_bitor(a, b)),
                _ => result is None,
            },
    )]
    pub fn or(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_bitor_spec(); }
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a | b))
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@.to_int()) {
                (Some(a), Some(b)) =>
                    result matches Some(value)
                    && value@ == NumberView::Integer(spec_bigint_bitxor(a, b)),
                _ => result is None,
            },
    )]
    pub fn xor(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_bitxor_spec(); }
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a ^ b))
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@) {
                (Some(value), NumberView::Integer(shift)) => {
                    if 0 <= shift <= u32::MAX {
                        result matches Some(r)
                         && r@ == NumberView::Integer(value * pow2(shift as nat) as int)
                    }
                    else {
                        result is None
                    }
                },
                _ => result is None,
            },
    )]
    pub fn lsh(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_shl_assign_spec(); }
        let shift = rhs.as_u32()? as usize;
        let mut value = self.ensure_integer()?;
        value <<= shift;
        Some(Number::from_bigint_owned(value))
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@) {
                (Some(value), NumberView::Integer(shift)) => {
                    if 0 <= shift <= u32::MAX {
                        result matches Some(r)
                         && r@ == NumberView::Integer(value / pow2(shift as nat) as int)
                    }
                    else {
                        result is None
                    }
                },
                _ => result is None,
            },
    )]
    pub fn rsh(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_shr_assign_spec(); }
        let shift = rhs.as_u32()? as usize;
        let mut value = self.ensure_integer()?;
        value >>= shift;
        Some(Number::from_bigint_owned(value))
    }

    #[verus_spec(result =>
        ensures
            match self@.to_int() {
                Some(value) => {
                    result matches Some(r)
                    && r@ == NumberView::Integer(-value - 1)
                },
                None => result is None,
            },
    )]
    pub fn neg(&self) -> Option<Number> {
        let mut value = self.ensure_integer()?;
        proof! { axiom_bigint_not_spec(value); }
        value = !value;
        Some(Number::from_bigint_owned(value))
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(value) => {
                    result@ matches NumberView::Integer(abs) && abs == if value < 0 { -value } else { value }
                },
                NumberView::Float(value) => result@ == NumberView::Float(spec_f64_abs(value)),
            },
    )]
    pub fn abs(&self) -> Number {
        match self {
            Number::UInt(_) => self.clone(),
            Number::Int(v) => {
                if let Some(abs) = v.checked_abs() {
                    Number::Int(abs)
                } else {
                    Number::from_bigint_owned(BigInt::from(*v).abs())
                }
            }
            Number::BigInt(v) => Number::from_bigint_owned((**v).clone().abs()),
            Number::Float(f) => Number::Float(f.abs()),
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(_) => result@ == self@,
                NumberView::Float(value) => result@ == normalize_float(spec_f64_floor(value)),
            },
    )]
    pub fn floor(&self) -> Number {
        match self {
            Number::Float(f) => Number::normalize_float(f.floor()),
            _ => self.clone(),
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(_) => result@ == self@,
                NumberView::Float(value) => result@ == normalize_float(spec_f64_ceil(value)),
            },
    )]
    pub fn ceil(&self) -> Number {
        match self {
            Number::Float(f) => Number::normalize_float(f.ceil()),
            _ => self.clone(),
        }
    }

    #[verus_spec(result =>
        ensures
            match self@ {
                NumberView::Integer(_) => result@ == self@,
                NumberView::Float(value) => result@ == normalize_float(spec_f64_round(value)),
            },
    )]
    pub fn round(&self) -> Number {
        match self {
            Number::Float(f) => Number::normalize_float(f.round()),
            _ => self.clone(),
        }
    }

    #[verus_spec(result =>
        ensures
            result matches Ok(value) && if e >= 0 {
                value@ == NumberView::Integer(pow2(e as nat) as int)
            } else {
                NumberView::Integer(1).div_ensures(
                    NumberView::Integer(pow2((-(e as int)) as nat) as int),
                    value@,
                )
            },
    )]
    pub fn two_pow(e: i32) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            if e >= 0 {
                assert((e as u32) as nat == e as nat);
            } else {
                let exp = (-(e as i64)) as u32;
                assert(exp > 0);
                vstd::arithmetic::power2::lemma2_to64();
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, exp as nat);
                assert(1 < pow2(exp as nat));
                vstd::arithmetic::div_mod::lemma_small_mod(1, pow2(exp as nat));
                assert(vstd::arithmetic::div_mod::rust_rem(1, pow2(exp as nat) as int) == 1);
                axiom_positive_integer_reciprocal_is_finite(pow2(exp as nat) as int);
            }
        }
        if e >= 0 {
            Ok(two_pow_positive(e as u32))
        } else {
            // Must cast to i64 before negating in case it's i32::MIN
            let denom = two_pow_positive((-(e as i64)) as u32);
            Number::from(1u64).divide(&denom)
        }
    }

    #[verus_spec(result =>
        ensures
            result matches Ok(value) && if e >= 0 {
                value@ == NumberView::Integer(vstd::arithmetic::power::pow(10, e as nat))
            } else {
                NumberView::Integer(1).div_ensures(
                    NumberView::Integer(
                        vstd::arithmetic::power::pow(10, (-(e as int)) as nat)
                    ),
                    value@,
                )
            },
    )]
    pub fn ten_pow(e: i32) -> Result<Number> {
        proof! {
            axiom_f64_ops_deterministic();
            if e < 0 {
                let exp = (-(e as i64)) as u32;
                assert(exp > 0);
                vstd::arithmetic::power::lemma_pow0(10);
                vstd::arithmetic::power::lemma_pow_strictly_increases(10, 0, exp as nat);
                assert(1 < vstd::arithmetic::power::pow(10, exp as nat));
                vstd::arithmetic::div_mod::lemma_small_mod(
                    1,
                    vstd::arithmetic::power::pow(10, exp as nat) as nat,
                );
                axiom_positive_integer_reciprocal_is_finite(
                    vstd::arithmetic::power::pow(10, exp as nat) as int,
                );
            } else {
                assert((e as u32) as nat == e as nat);
                vstd::arithmetic::power::lemma_pow_positive(10, (e as u32) as nat);
            }
        }
        if e >= 0 {
            Ok(ten_pow_positive(e as u32))
        } else {
            // Must cast to i64 before negating in case it's i32::MIN
            let denom = ten_pow_positive((-(e as i64)) as u32);
            Number::from(1u64).divide(&denom)
        }
    }

    pub fn format_bin(&self) -> String {
        self.ensure_integer()
            .map(|v| v.to_str_radix(2))
            .unwrap_or_default()
    }

    pub fn format_octal(&self) -> String {
        self.ensure_integer()
            .map(|v| v.to_str_radix(8))
            .unwrap_or_default()
    }

    // Verus doesn't support format!
    #[verus_verify(external_body)]
    #[verus_spec(ensures true)]
    pub fn format_scientific(&self) -> String {
        match self {
            Number::Float(f) => format!("{:e}", f),
            _ => self
                .ensure_integer()
                .map(|v| bigint_to_scientific(&v))
                .unwrap_or_else(|| format!("{:e}", self.to_f64_lossy())),
        }
    }

    pub fn format_decimal(&self) -> String {
        match self {
            Number::UInt(v) => v.to_string(),
            Number::Int(v) => v.to_string(),
            Number::BigInt(v) => v.to_string(),
            Number::Float(f) => {
                if f.is_nan() {
                    "NaN".to_string()
                } else {
                    f.to_string()
                }
            }
        }
    }

    // Verus doesn't support format!
    #[verus_verify(external_body)]
    #[verus_spec(ensures true)]
    pub fn format_decimal_with_width(&self, d: u32) -> String {
        match self {
            Number::Float(f) => {
                let factor = 10f64.powi(d as i32);
                let rounded = (f * factor).round() / factor;
                format!("{:.*}", d as usize, rounded)
            }
            _ => self.format_decimal(),
        }
    }

    pub fn format_hex(&self) -> String {
        self.ensure_integer()
            .map(|v| v.to_str_radix(16))
            .unwrap_or_default()
    }

    pub fn format_big_hex(&self) -> String {
        self.ensure_integer()
            .map(|v| v.to_str_radix(16).to_ascii_uppercase())
            .unwrap_or_default()
    }
}

#[verus_spec(result =>
    ensures
        result@ == NumberView::Integer(pow2(exp as nat) as int),
)]
fn two_pow_positive(exp: u32) -> Number {
    if exp < 64 {
        proof! {
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(exp as nat, 64);
            vstd::bits::lemma_u64_shl_is_mul(1u64, exp as u64);
        }
        Number::UInt(1u64 << exp)
    } else {
        let mut value = BigInt::one();
        proof! { axiom_bigint_obeys_shl_assign_spec(); }
        value <<= exp as usize;
        Number::from_bigint_owned(value)
    }
}

#[verus_spec(result =>
    ensures
        result@ == vstd::arithmetic::power::pow(10, exp as nat),
)]
fn pow10_bigint(exp: u32) -> BigInt {
    proof! {
        vstd::arithmetic::power::lemma_pow0(10);
    }

    if exp == 0 {
        return BigInt::one();
    }

    let mut result = BigInt::one();
    let mut base = BigInt::from(10u8);
    let mut e = exp;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            result@ * vstd::arithmetic::power::pow(base@, e as nat)
                == vstd::arithmetic::power::pow(10, exp as nat),
        decreases e,
    ))]
    while e > 0 {
        proof! {
            axiom_bigint_obeys_mul_spec();
            axiom_bigint_obeys_mul_assign_ref_spec();
            assert(e & 1 == e % 2) by (bit_vector);
            assert(e >> 1 == e / 2) by (bit_vector);
            // `pow(base, 2) == base * base`, so squaring `base` halves `e`.
            vstd::arithmetic::power::lemma_pow0(base@);
            vstd::arithmetic::power::lemma_pow1(base@);
            vstd::arithmetic::power::lemma_pow_adds(base@, 1, 1);
            vstd::arithmetic::power::lemma_pow_multiplies(base@, 2, (e / 2) as nat);
            // Peeling one factor off when `e` is odd.
            vstd::arithmetic::power::lemma_pow_adds(base@, 1, (e - e % 2) as nat);
            vstd::arithmetic::mul::lemma_mul_is_associative(
                result@,
                base@,
                vstd::arithmetic::power::pow(base@, (e - e % 2) as nat),
            );
        }
        if e & 1 == 1 {
            result *= &base;
        }
        if e > 1 {
            base = &base * &base;
        }
        e >>= 1;
    }

    proof! { vstd::arithmetic::power::lemma_pow0(base@); }

    result
}

#[verus_spec(result =>
    ensures
        result@ == NumberView::Integer(vstd::arithmetic::power::pow(10, exp as nat)),
)]
fn ten_pow_positive(exp: u32) -> Number {
    if let Some(value) = 10u64.checked_pow(exp) {
        Number::UInt(value)
    } else {
        Number::from_bigint_owned(pow10_bigint(exp))
    }
}

fn bigint_to_scientific(value: &BigInt) -> String {
    let s = value.to_string();
    let (sign, digits) = if let Some(rest) = s.strip_prefix('-') {
        ("-", rest)
    } else {
        ("", s.as_str())
    };

    if digits.len() <= 1 {
        return format!("{}{}e0", sign, digits);
    }

    let exponent = digits.len() - 1;
    format!("{}{}.{}e{}", sign, &digits[0..1], &digits[1..], exponent)
}

fn parse_scientific_bigint(input: &str) -> Option<BigInt> {
    let (mantissa, exponent_part) = split_scientific_parts(input)?;
    let exponent = exponent_part.parse::<i32>().ok()?;
    scientific_parts_to_bigint(mantissa, exponent)
}

fn split_scientific_parts(input: &str) -> Option<(&str, &str)> {
    let idx = input.find(['e', 'E'])?;
    let mantissa = &input[..idx];
    let exponent = &input[idx + 1..];
    if exponent.is_empty() {
        None
    } else {
        Some((mantissa, exponent))
    }
}

fn scientific_parts_to_bigint(mantissa: &str, exponent: i32) -> Option<BigInt> {
    let (sign, unsigned) = if let Some(rest) = mantissa.strip_prefix('-') {
        (-1, rest)
    } else if let Some(rest) = mantissa.strip_prefix('+') {
        (1, rest)
    } else {
        (1, mantissa)
    };

    if unsigned.is_empty() {
        return None;
    }

    let mut digits = String::new();
    let mut fractional_len: i32 = 0;
    let mut seen_dot = false;
    for ch in unsigned.chars() {
        match ch {
            '.' => {
                if seen_dot {
                    return None;
                }
                seen_dot = true;
            }
            '0'..='9' => {
                digits.push(ch);
                if seen_dot {
                    fractional_len += 1;
                }
            }
            _ => return None,
        }
    }

    if digits.is_empty() {
        return Some(BigInt::zero());
    }

    while fractional_len > 0 && digits.ends_with('0') {
        digits.pop();
        fractional_len -= 1;
    }

    let adjusted_exponent = exponent.checked_sub(fractional_len)?;
    if adjusted_exponent < 0 {
        return None;
    }

    let mut value = BigInt::parse_bytes(digits.as_bytes(), 10)?;
    if adjusted_exponent > 0 {
        let factor = pow10_bigint(u32::try_from(adjusted_exponent).ok()?);
        value *= factor;
    }

    if sign < 0 {
        value = -value;
    }

    Some(value)
}

#[cfg(test)]
mod tests {
    #![allow(clippy::expect_used)] // tests expect() to assert arithmetic results

    use super::*;
    use alloc::string::ToString;

    /// `Ord` and `Eq` must agree, and must form a total order over every `Number` the engine can
    /// hold: integers of any width (`UInt`, `Int`, `BigInt`), floats inside the exact integer
    /// range, and `Float`s above 2^53 - an integer division with a remainder produces one, e.g.
    /// `(2*2^63+1)/2` is a `Float` holding exactly 2^63. The non-finite tail is included because
    /// `cmp`/`eq` must remain total even if a non-finite value reaches this internal type.
    ///
    /// Converting mixed operands through `f64` makes `Float(2^63)` and `BigInt(2^63 + 1)` compare
    /// Equal even though the integers differ. Mapping an out-of-range `BigInt` to infinity creates
    /// the same collision with `Float(INFINITY)`.
    #[test]
    fn ordering_is_total_and_agrees_with_equality() {
        let big_int = |digits: &[u8]| Number::from(BigInt::parse_bytes(digits, 10).unwrap());
        let beyond_f64 = BigInt::from(1u8) << 2048usize;
        let universe: Vec<Number> = vec![
            Number::UInt(0),
            Number::UInt(1),
            Number::UInt(2),
            Number::UInt(u64::MAX),
            Number::Int(-1),
            Number::Int(i64::MIN),
            Number::Float(0.0),
            Number::Float(-0.0),
            Number::Float(1.0),
            Number::Float(2.5),
            Number::Float(-1.5),
            Number::Float(9_007_199_254_740_992.0), // 2^53
            Number::Float(-9_007_199_254_740_992.0),
            Number::Float(1e-300),
            Number::Float(f64::MIN),
            Number::Float(f64::MAX),
            Number::from(BigInt::from(9_007_199_254_740_993i64)), // 2^53 + 1
            // A `Float` holding exactly 2^63 next to its exact neighbours: the lossy comparison
            // flattened all three onto one f64.
            Number::Float(9_223_372_036_854_775_808.0),
            Number::Float(-9_223_372_036_854_775_808.0),
            big_int(b"9223372036854775808"), // 2^63
            big_int(b"9223372036854775809"), // 2^63 + 1
            Number::from(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap()),
            Number::from(BigInt::parse_bytes(b"18446744073709551617", 10).unwrap()),
            Number::from(BigInt::parse_bytes(b"-18446744073709551617", 10).unwrap()),
            Number::from(beyond_f64.clone()),
            Number::from(-beyond_f64),
            Number::from(
                BigInt::parse_bytes(
                    b"100000000000000000000000000000000000000000000000000000000000000000000000\
                      0000000000000000000000000000000000000000000000000000000000000000000000000\
                      00000000000000000000000000000000000000000000000000000000000000000000000000\
                      000000000000000000000000000000",
                    10,
                )
                .unwrap(),
            ),
            // Non-finite tail: ranked below/above every finite value, and `NaN` Equal only to
            // itself. `Ord`-backed containers must not collapse one into a finite number.
            Number::Float(f64::NEG_INFINITY),
            Number::Float(f64::INFINITY),
            Number::Float(f64::NAN),
            Number::Float(-f64::NAN),
        ];
        let name = |n: &Number| format!("{n:?}");
        let mut failures: Vec<String> = vec![];

        for a in &universe {
            if a.cmp(a) != Ordering::Equal || !a.eq(a) {
                failures.push(format!("reflexivity: {}", name(a)));
            }
            for b in &universe {
                if a.cmp(b) != b.cmp(a).reverse() {
                    failures.push(format!("antisymmetry: {} {:?}", name(a), a.cmp(b)));
                }
                if a.eq(b) != b.eq(a) || (a.cmp(b) == Ordering::Equal) != a.eq(b) {
                    failures.push(format!("cmp/eq disagree: {} {}", name(a), name(b)));
                }
            }
        }
        for a in &universe {
            for b in &universe {
                for c in &universe {
                    if a.cmp(b) != Ordering::Greater
                        && b.cmp(c) != Ordering::Greater
                        && a.cmp(c) == Ordering::Greater
                    {
                        failures.push(format!("ordering: {} {} {}", name(a), name(b), name(c)));
                    }
                    if a.eq(b) && b.eq(c) && !a.eq(c) {
                        failures.push(format!("equality: {} {} {}", name(a), name(b), name(c)));
                    }
                }
            }
        }

        assert!(failures.is_empty(), "{:#?}", failures);
    }

    /// The `Float(2^63)` that integer division produces must stay distinct from the exact
    /// integers either side of it. This directly covers the private `Number` representation while
    /// `tests/gate_cmp_exactness.rs` covers the public evaluation boundary.
    ///
    /// With the old `to_f64_lossy()` comparison all four assertions below were `true`.
    #[test]
    fn float_holding_two_pow_63_is_exact_against_its_neighbours() {
        let two_pow_63 = Number::Float(9_223_372_036_854_775_808.0);
        let exact = |digits: &[u8]| Number::from(BigInt::parse_bytes(digits, 10).unwrap());
        let lower = exact(b"9223372036854775807");
        let same = exact(b"9223372036854775808");
        let upper = exact(b"9223372036854775809");

        assert_eq!(
            two_pow_63, same,
            "the Float is exactly 2^63, so it must be equal"
        );
        assert_ne!(two_pow_63, upper, "2^63 must not be equal to 2^63 + 1");
        assert_eq!(two_pow_63.cmp(&upper), Ordering::Less);
        assert_eq!(two_pow_63.cmp(&lower), Ordering::Greater);

        // A `BigInt` outside f64 range used to be mapped to +Inf, so it compared Equal to
        // `Float(INFINITY)`.
        let huge = Number::from(BigInt::from(1u8) << 2048usize);
        let negative_huge = Number::from(-(BigInt::from(1u8) << 2048usize));
        assert_ne!(Number::Float(f64::INFINITY), huge);
        assert_eq!(Number::Float(f64::INFINITY).cmp(&huge), Ordering::Greater);
        assert_ne!(Number::Float(f64::NEG_INFINITY), negative_huge);
        assert_eq!(
            Number::Float(f64::NEG_INFINITY).cmp(&negative_huge),
            Ordering::Less,
            "-Inf must rank below every exact integer, however large"
        );
    }

    #[test]
    fn primitive_mixed_comparison_boundaries_are_exact() {
        let two_pow_64 = u64::MAX as f64;
        let below_two_pow_64 = f64::from_bits(two_pow_64.to_bits() - 1);
        assert_eq!(
            Number::Float(two_pow_64).cmp(&Number::UInt(u64::MAX)),
            Ordering::Greater
        );
        assert_eq!(
            Number::Float(below_two_pow_64).cmp(&Number::UInt(u64::MAX)),
            Ordering::Less
        );

        let two_pow_63 = i64::MAX as f64;
        assert_eq!(
            Number::Float(two_pow_63).cmp(&Number::Int(i64::MAX)),
            Ordering::Greater
        );
        assert_eq!(
            Number::Float(i64::MIN as f64).cmp(&Number::Int(i64::MIN)),
            Ordering::Equal
        );

        assert_eq!(Number::Float(-0.0).cmp(&Number::UInt(0)), Ordering::Equal);
        assert_eq!(Number::Float(0.5).cmp(&Number::UInt(0)), Ordering::Greater);
        assert_eq!(Number::Float(-0.5).cmp(&Number::Int(0)), Ordering::Less);
        assert_eq!(
            Number::Float(9_007_199_254_740_992.0).cmp(&Number::UInt(9_007_199_254_740_993)),
            Ordering::Less
        );
    }

    /// Non-finite numbers use `f64::total_cmp` rather than
    /// `partial_cmp(..).unwrap_or(Ordering::Equal)`, which reported every unordered pair as Equal.
    ///
    /// Returning the `unwrap_or(Ordering::Equal)` fallback makes the `+NaN`/`+Inf`,
    /// `-NaN`/`-Inf` and `NaN`/finite assertions below fail.
    #[test]
    fn non_finite_numbers_are_ranked_by_a_total_order() {
        let nan = Number::Float(f64::NAN);
        let neg_nan = Number::Float(-f64::NAN);
        let inf = Number::Float(f64::INFINITY);
        let neg_inf = Number::Float(f64::NEG_INFINITY);

        assert_eq!(inf.cmp(&Number::Float(f64::MAX)), Ordering::Greater);
        assert_eq!(neg_inf.cmp(&Number::Float(f64::MIN)), Ordering::Less);
        assert_eq!(nan.cmp(&inf), Ordering::Greater, "+NaN ranks above +Inf");
        assert_eq!(
            neg_nan.cmp(&neg_inf),
            Ordering::Less,
            "-NaN ranks below -Inf"
        );
        assert_eq!(neg_inf.cmp(&Number::Int(i64::MIN)), Ordering::Less);
        assert_eq!(inf.cmp(&Number::UInt(u64::MAX)), Ordering::Greater);

        // A NaN is Equal only to itself, and never Equal to a finite value or an infinity.
        assert_eq!(nan.cmp(&nan), Ordering::Equal);
        assert!(nan.eq(&nan), "a NaN is equal only to itself");
        assert_eq!(nan.cmp(&neg_nan), Ordering::Greater);
        assert!(!nan.eq(&neg_nan));
        assert!(!nan.eq(&inf));
        for finite in [
            Number::UInt(0),
            Number::Int(-1),
            Number::Float(0.0),
            Number::Float(-0.0),
            Number::Float(f64::MAX),
            Number::Float(f64::MIN),
            Number::Float(1e-300),
        ] {
            assert_eq!(nan.cmp(&finite), Ordering::Greater);
            assert_eq!(neg_nan.cmp(&finite), Ordering::Less);
            assert!(!nan.eq(&finite), "NaN compared Equal to {finite:?}");
        }

        assert_eq!(neg_nan.cmp(&inf), Ordering::Less);
        assert_eq!(Number::Float(-2.5).cmp(&neg_inf), Ordering::Greater);
    }

    /// `Ord`-backed containers must keep every one of those values apart. `Number::eq` is defined
    /// as `cmp == Equal`, so a `BTreeSet` (and the `Object` keys behind a Rego object) can no
    /// longer merge a `Float` with a distinct exact integer.
    ///
    /// With the lossy comparison the set collapsed `Float(2^63)`, `2^63`, `2^63 + 1`,
    /// `Float(INFINITY)` and the out-of-range `BigInt` into fewer elements, and `NaN`/`-NaN`
    /// together.
    #[test]
    fn non_finite_and_large_numbers_stay_distinct_in_ord_backed_containers() {
        use crate::value::Object;
        // Pairwise unequal on purpose; signed zero is covered separately below.
        let pool: Vec<Number> = vec![
            Number::Float(0.0),
            Number::Float(2.5),
            Number::Float(9_007_199_254_740_992.0),
            Number::from(BigInt::from(9_007_199_254_740_993i64)),
            Number::Float(9_223_372_036_854_775_808.0),
            Number::from(BigInt::parse_bytes(b"9223372036854775809", 10).unwrap()),
            Number::from(
                BigInt::parse_bytes(b"100000000000000000000000000000000000000000", 10).unwrap(),
            ),
            Number::Float(f64::NEG_INFINITY),
            Number::Float(f64::INFINITY),
            Number::Float(f64::NAN),
            Number::Float(-f64::NAN),
        ];

        let set: alloc::collections::BTreeSet<Number> = pool.iter().cloned().collect();
        assert_eq!(
            set.len(),
            pool.len(),
            "a set merged values that are not equal"
        );

        let mut object = Object::new();
        for n in &pool {
            object.insert(Value::Number(n.clone()), Value::from(1u64));
        }
        assert_eq!(object.len(), pool.len(), "object keys were merged");

        // Signed zero stays one value with integer zero.
        let mut zeros = alloc::collections::BTreeSet::new();
        zeros.insert(Number::Float(-0.0));
        zeros.insert(Number::Float(0.0));
        zeros.insert(Number::UInt(0));
        assert_eq!(zeros.len(), 1, "-0.0 must stay equal to 0");
    }

    /// Regression test: `i64::MIN / -1` overflows `i64` and panics in Rust's
    /// native integer division/remainder. `divide` must promote the result
    /// instead of panicking.
    #[test]
    fn i64_min_by_negative_one() {
        let quotient = Number::Int(i64::MIN)
            .divide(&Number::Int(-1))
            .expect("division should succeed");

        // 2^63 does not fit in i64, but does fit in u64.
        assert_eq!(quotient.as_u64(), Some(9_223_372_036_854_775_808));
        assert_eq!(quotient.as_i64(), None);
        assert_eq!(quotient.as_i128(), Some(9_223_372_036_854_775_808));
        assert_eq!(
            *quotient.to_big().expect("to_big should succeed"),
            -BigInt::from(i64::MIN)
        );

        // The same overflow case reached via the mixed `Int`/`BigInt` path.
        let big_quotient = Number::Int(i64::MIN)
            .divide(&Number::BigInt(Rc::new(BigInt::from(-1))))
            .expect("division should succeed");
        assert_eq!(big_quotient.as_u64(), Some(9_223_372_036_854_775_808));

        // `i64::MIN % -1` also panics natively; the result must be zero.
        let remainder = Number::Int(i64::MIN)
            .modulo(&Number::Int(-1))
            .expect("modulo should succeed");
        assert_eq!(remainder.as_i64(), Some(0));
    }

    #[test]
    fn modulo_handles_floats_that_are_really_integers() {
        // An integral float is a valid operand.
        assert!(matches!(
            Number::Float(4.0).modulo(&Number::Int(3)),
            Ok(Number::UInt(1))
        ));
        // `1e300` has no fractional part, but it is too large to convert to an
        // integer exactly. This must report an error, not panic.
        assert_eq!(
            Number::Float(1e300)
                .modulo(&Number::Int(3))
                .err()
                .map(|e| e.to_string()),
            Some("modulo on floating-point number".to_string())
        );
        assert_eq!(
            Number::Int(3)
                .modulo(&Number::Float(1e300))
                .err()
                .map(|e| e.to_string()),
            Some("modulo on floating-point number".to_string())
        );
    }

    #[test]
    fn ten_pow_computes_negative_exponent() {
        assert!(matches!(
            Number::ten_pow(-3),
            Ok(Number::Float(value)) if value == 0.001
        ));
    }

    #[test]
    fn divide_handles_minimum_i64_by_negative_one() {
        assert!(matches!(
            Number::Int(i64::MIN).divide(&Number::Int(-1)),
            Ok(Number::UInt(value)) if value == 1u64 << 63
        ));
    }
    /// Mixed BigInt/Float operands and non-exact division promote to `f64`. Results outside
    /// the finite `f64` range report an error, while exact integer paths keep every digit.
    ///
    /// OPA uses `big.Int` for integer-valued operands and a wide-exponent `big.Float` for
    /// fractional arithmetic. Rejecting these finite OPA results is an intentional,
    /// fail-closed compatibility break until Regorus has an equivalent representation.
    #[test]
    fn arithmetic_rejects_overflowing_promotion() {
        let big = Number::from_str("1e300")
            .unwrap()
            .mul(&Number::from_str("1e300").unwrap())
            .unwrap();
        let negative_big = Number::from_str("-1e300")
            .unwrap()
            .mul(&Number::from_str("1e300").unwrap())
            .unwrap();
        assert_eq!(big.format_decimal().len(), 601);

        for (result, expected) in [
            (
                big.clone().divide(&Number::from(7u64)),
                "numeric overflow in division",
            ),
            (
                big.clone().add(&Number::from(0.5f64)),
                "numeric overflow in addition",
            ),
            (
                big.clone().sub(&Number::from(0.5f64)),
                "numeric overflow in subtraction",
            ),
            (
                big.clone().mul(&Number::from(1.5f64)),
                "numeric overflow in multiplication",
            ),
            (
                big.clone().mul(&Number::from(0.0f64)),
                "numeric overflow in multiplication",
            ),
            (
                negative_big.mul(&Number::from(1.0f64)),
                "numeric overflow in multiplication",
            ),
            (
                Number::from(1.5f64).divide(&Number::from_str("1e-320").unwrap()),
                "numeric overflow in division",
            ),
        ] {
            assert_eq!(
                result.unwrap_err().to_string(),
                expected,
                "unexpected overflow diagnostic"
            );
        }

        // Binary64 underflow remains finite and therefore is not rejected.
        assert_eq!(
            Number::from_str("1e-320")
                .unwrap()
                .mul(&Number::from_str("1e-320").unwrap())
                .unwrap()
                .format_decimal(),
            "0"
        );

        // Controls: the promoted result is finite, so these keep their old answers.
        assert!(matches!(
            Number::from(7u64).divide(&Number::from(2u64)),
            Ok(Number::Float(value)) if value == 3.5
        ));
        assert_eq!(
            Number::from_str("1e400")
                .unwrap()
                .divide(&Number::from_str("1e400").unwrap())
                .unwrap()
                .format_decimal(),
            "1"
        );
    }
}

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
use core::fmt::{Debug, Formatter};
use core::str::FromStr;

use anyhow::{anyhow, bail, Result};
use num_bigint::BigInt as NumBigInt;
#[allow(unused)]
use num_traits::float::FloatCore;
use num_traits::{One, Signed, ToPrimitive, Zero};

use serde::ser::Serializer;
use serde::Serialize;

#[cfg(not(feature = "verus"))]
use regorus_verus_shim::{proof, verus_spec, verus_verify};
#[cfg(feature = "verus")]
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
                    match result {
                        Some(bi) => float_to_small_int(f) == Some(bi@),
                        None => float_to_small_int(f) is None,
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

        normalized_ref
            .parse::<f64>()
            .map(Number::Float)
            .map_err(|_| ParseNumberError)
    }
}

#[verus_verify]
impl PartialEq for Number {
    #[verus_spec(result =>
        ensures
            match (self@.to_int(), other@.to_int()) {
                (Some(n1), Some(n2)) => result == (n1 == n2),
                _ => exists|f1: f64, f2: f64| #![trigger self@.to_f64_lossy_ensures(f1), other@.to_f64_lossy_ensures(f2)] {
                    &&& self@.to_f64_lossy_ensures(f1)
                    &&& other@.to_f64_lossy_ensures(f2)
                    &&& result == (!f1.is_nan_spec() && !f2.is_nan_spec() && f1.eq_spec(&f2))
                },
            },
    )]
    fn eq(&self, other: &Self) -> bool {
        proof! {
            axiom_bigint_obeys_eq_spec();
            axiom_f64_obeys_eq_spec();
        }

        if let (Some(a), Some(b)) = (self.to_bigint_owned(), other.to_bigint_owned()) {
            return a == b;
        }

        let a = self.to_f64_lossy();
        let b = other.to_f64_lossy();
        if a.is_nan() || b.is_nan() {
            return false;
        }
        a == b
    }
}

impl Eq for Number {}

#[verus_verify]
impl Ord for Number {
    #[verus_spec(result =>
         ensures
             match (self@.to_int(), other@.to_int()) {
                 (Some(n1), Some(n2)) => result == n1.cmp_spec(&n2),
                 _ => exists|f1: f64, f2: f64| #![trigger self@.to_f64_lossy_ensures(f1), other@.to_f64_lossy_ensures(f2)] {
                     &&& self@.to_f64_lossy_ensures(f1)
                     &&& other@.to_f64_lossy_ensures(f2)
                     &&& result == f1.partial_cmp_spec(&f2).unwrap_or(Ordering::Equal)
                },
            },
    )]
    fn cmp(&self, other: &Self) -> Ordering {
        proof! {
            axiom_f64_obeys_partial_cmp_spec();
            axiom_bigint_obeys_cmp_spec();
        }
        if let (Some(a), Some(b)) = (self.to_bigint_owned(), other.to_bigint_owned()) {
            return a.cmp(&b);
        }

        self.to_f64_lossy()
            .partial_cmp(&other.to_f64_lossy())
            .unwrap_or(Ordering::Equal)
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
                    let convertible = f.is_finite_spec()
                        && f.ieee_ge(0.0f64)
                        && spec_f64_fract(f).eq_spec(&0.0f64)
                        && ieee_float_cast::<u128, f64>(ieee_float_cast::<f64, u128>(f)).eq_spec(&f);
                    match result {
                        Some(value) => convertible && value == ieee_float_cast::<f64, u128>(f),
                        None => !convertible,
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
                    let convertible = f.is_finite_spec()
                        && spec_f64_fract(f).eq_spec(&0.0f64)
                        && ieee_float_cast::<i128, f64>(ieee_float_cast::<f64, i128>(f)).eq_spec(&f);
                    match result {
                        Some(value) => convertible && value == ieee_float_cast::<f64, i128>(f),
                        None => !convertible,
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
                    let convertible = f.is_finite_spec()
                        && f.ieee_ge(0.0f64)
                        && spec_f64_fract(f).eq_spec(&0.0f64)
                        && f.ieee_le(ieee_float_cast::<u64, f64>(u64::MAX))
                        && ieee_float_cast::<u64, f64>(ieee_float_cast::<f64, u64>(f)).eq_spec(&f);
                    match result {
                        Some(value) => convertible && value == ieee_float_cast::<f64, u64>(f),
                        None => !convertible,
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
                    let convertible = f.is_finite_spec()
                        && spec_f64_fract(f).eq_spec(&0.0f64)
                        && f.ieee_ge(ieee_float_cast::<i64, f64>(i64::MIN))
                        && f.ieee_le(ieee_float_cast::<i64, f64>(i64::MAX))
                        && ieee_float_cast::<i64, f64>(ieee_float_cast::<f64, i64>(f)).eq_spec(&f);
                    match result {
                        Some(value) => convertible && value == ieee_float_cast::<f64, i64>(f),
                        None => !convertible,
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
            axiom_safe_bigints_to_f64();
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
                    match result {
                        Some(bi) => float_to_small_int(f) == Some(bi@),
                        None => float_to_small_int(f) is None,
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
                    match result {
                        Ok(bi) => float_to_small_int(f) == Some(bi@),
                        Err(_) => float_to_small_int(f) is None,
                    }
                },
            },
    )]
    pub fn to_big(&self) -> Result<Rc<BigInt>> {
        self.as_big()
            .ok_or_else(|| anyhow!("Number::to_big failed"))
    }

    #[verus_spec(result =>
        ensures
            result is Ok,
            old(self)@.add_ensures(rhs@, final(self)@),
    )]
    pub fn add_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.add(rhs)?;
        Ok(())
    }

    // Verus does not yet support overloaded op-assignment operators like `+=`.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            result matches Ok(value) && self@.add_ensures(rhs@, value@),
    )]
    pub fn add(&self, rhs: &Self) -> Result<Number> {
        if matches!(self, Number::Float(_)) || matches!(rhs, Number::Float(_)) {
            return Ok(Number::normalize_float(
                self.to_f64_lossy() + rhs.to_f64_lossy(),
            ));
        }

        match (self, rhs) {
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
            _ => unreachable!(),
        }
    }

    #[verus_spec(result =>
        ensures
            result is Ok,
            old(self)@.sub_ensures(rhs@, final(self)@),
    )]
    pub fn sub_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.sub(rhs)?;
        Ok(())
    }

    // Verus does not yet support overloaded op-assignment operators like `-=`.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            result matches Ok(value) && self@.sub_ensures(rhs@, value@),
    )]
    pub fn sub(&self, rhs: &Self) -> Result<Number> {
        if matches!(self, Number::Float(_)) || matches!(rhs, Number::Float(_)) {
            return Ok(Number::normalize_float(
                self.to_f64_lossy() - rhs.to_f64_lossy(),
            ));
        }

        match (self, rhs) {
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
            _ => unreachable!(),
        }
    }

    #[verus_spec(result =>
        ensures
            result is Ok,
            old(self)@.mul_ensures(rhs@, final(self)@),
    )]
    pub fn mul_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.mul(rhs)?;
        Ok(())
    }

    #[verus_spec(result =>
        ensures
            result matches Ok(value) && self@.mul_ensures(rhs@, value@),
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
            (Number::Float(_), _) | (_, Number::Float(_)) => Ok(Number::normalize_float(
                self.to_f64_lossy() * rhs.to_f64_lossy(),
            )),
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
                Err(_) => rhs@.is_zero(),
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
            return Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()));
        }

        match (&self, rhs) {
            (Number::UInt(a), Number::UInt(b)) => {
                if *a % *b == 0 {
                    Ok(Number::UInt(*a / *b))
                } else {
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
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
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                }
            }
            (Number::Int(a), Number::UInt(b)) => {
                let lhs = *a as i128;
                let rhs_i = *b as i128;
                if lhs % rhs_i == 0 {
                    Ok(Number::from_i128(lhs / rhs_i))
                } else {
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                }
            }
            (Number::UInt(a), Number::Int(b)) => {
                let lhs = *a as i128;
                let rhs_i = *b as i128;
                if lhs % rhs_i == 0 {
                    Ok(Number::from_i128(lhs / rhs_i))
                } else {
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                }
            }
            (Number::BigInt(a), Number::BigInt(b)) => {
                let remainder = (&**a) % (&**b);
                if remainder.is_zero() {
                    let quotient = (&**a) / (&**b);
                    Ok(Number::from_bigint_owned(quotient))
                } else {
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                }
            }
            (Number::BigInt(a), _) => {
                if let Some(b_big) = rhs.to_bigint_owned() {
                    let remainder = (&**a) % &b_big;
                    if remainder.is_zero() {
                        let quotient = (&**a) / &b_big;
                        Ok(Number::from_bigint_owned(quotient))
                    } else {
                        Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                    }
                } else {
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                }
            }
            (_, Number::BigInt(b)) => {
                if let Some(a_big) = self.to_bigint_owned() {
                    let remainder = (&a_big) % (&**b);
                    if remainder.is_zero() {
                        let quotient = (&a_big) / (&**b);
                        Ok(Number::from_bigint_owned(quotient))
                    } else {
                        Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                    }
                } else {
                    Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy()))
                }
            }
            _ => Ok(Number::Float(self.to_f64_lossy() / rhs.to_f64_lossy())),
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
<<<<<<< HEAD
        // Conversion fails for a non-integral float, and also for an integral
        // one whose magnitude exceeds 2^53, which cannot be represented exactly.
        let (a, b) = match (self.to_bigint_owned(), rhs.to_bigint_owned()) {
            (Some(a), Some(b)) => (a, b),
            _ => bail!("modulo on floating-point number"),
        };

        if b.is_zero() {
            bail!("modulo by zero");
        }

=======
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

>>>>>>> efd56bf (Fix bug in Number::modulo)
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
            match (a@.to_int(), b@.to_int(), result) {
                (Some(lhs), Some(rhs), Some((lhs_big, rhs_big))) => {
                    lhs_big@ == lhs && rhs_big@ == rhs
                },
                (Some(_), Some(_), None) => false,
                (_, _, Some(_)) => false,
                (_, _, None) => true,
            },
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
            match (self@.to_int(), rhs@.to_int(), result) {
                (Some(lhs), Some(rhs), Some(value)) => {
                    value@ == NumberView::Integer(spec_bigint_bitand(lhs, rhs))
                },
                (Some(_), Some(_), None) => false,
                (_, _, Some(_)) => false,
                (_, _, None) => true,
            },
    )]
    pub fn and(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_bitand_spec(); }
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a & b))
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@.to_int(), result) {
                (Some(lhs), Some(rhs), Some(value)) => {
                    value@ == NumberView::Integer(spec_bigint_bitor(lhs, rhs))
                },
                (Some(_), Some(_), None) => false,
                (_, _, Some(_)) => false,
                (_, _, None) => true,
            },
    )]
    pub fn or(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_bitor_spec(); }
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a | b))
    }

    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@.to_int(), result) {
                (Some(lhs), Some(rhs), Some(value)) => {
                    value@ == NumberView::Integer(spec_bigint_bitxor(lhs, rhs))
                },
                (Some(_), Some(_), None) => false,
                (_, _, Some(_)) => false,
                (_, _, None) => true,
            },
    )]
    pub fn xor(&self, rhs: &Self) -> Option<Number> {
        proof! { axiom_bigint_obeys_bitxor_spec(); }
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a ^ b))
    }

    // Verus does not yet support overloaded assigment operators like `<<=`.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@, result) {
                (Some(value), NumberView::Integer(shift), Some(result)) => {
                    &&& 0 <= shift <= u32::MAX
                    &&& result@ == NumberView::Integer(value * pow2(shift as nat) as int)
                },
                (Some(_), NumberView::Integer(shift), None) => {
                    !(0 <= shift <= u32::MAX)
                },
                (_, _, Some(_)) => false,
                (_, _, None) => true,
            },
    )]
    pub fn lsh(&self, rhs: &Self) -> Option<Number> {
        let shift = rhs.as_u32()? as usize;
        let mut value = self.ensure_integer()?;
        value <<= shift;
        Some(Number::from_bigint_owned(value))
    }

    // Verus does not yet support overloaded op-assignment operators such as `>>=`.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            match (self@.to_int(), rhs@, result) {
                (Some(value), NumberView::Integer(shift), Some(result)) => {
                    &&& 0 <= shift <= u32::MAX
                    &&& result@ == NumberView::Integer(value / (pow2(shift as nat) as int))
                },
                (Some(_), NumberView::Integer(shift), None) => {
                    !(0 <= shift <= u32::MAX)
                },
                (_, _, Some(_)) => false,
                (_, _, None) => true,
            },
    )]
    pub fn rsh(&self, rhs: &Self) -> Option<Number> {
        let shift = rhs.as_u32()? as usize;
        let mut value = self.ensure_integer()?;
        value >>= shift;
        Some(Number::from_bigint_owned(value))
    }

    // Verus panics while translating overloaded `!` on an external `BigInt`.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            match (self@.to_int(), result) {
                (Some(value), Some(result)) => {
                    result@ == NumberView::Integer(-value - 1)
                },
                (Some(_), None) => false,
                (None, Some(_)) => false,
                (None, None) => true,
            },
    )]
    pub fn neg(&self) -> Option<Number> {
        let mut value = self.ensure_integer()?;
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
            match result {
                Ok(value) => if e >= 0 {
                    value@ == NumberView::Integer(pow2(e as nat) as int)
                } else {
                    NumberView::Integer(1).div_ensures(
                        NumberView::Integer(pow2((-(e as int)) as nat) as int),
                        value@,
                    )
                },
                Err(_) => false,
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
            match result {
                Ok(value) => if e >= 0 {
                    value@ == NumberView::Integer(vstd::arithmetic::power::pow(10, e as nat))
                } else {
                    NumberView::Integer(1).div_ensures(
                        NumberView::Integer(
                            vstd::arithmetic::power::pow(10, (-(e as int)) as nat)
                        ),
                        value@,
                    )
                },
                Err(_) => false,
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

// Verus does not yet support overloaded op-assignment operators such as `<<=`.
#[verus_verify(external_body)]
#[verus_spec(result =>
    ensures
        result@ == NumberView::Integer(pow2(exp as nat) as int),
)]
fn two_pow_positive(exp: u32) -> Number {
    if exp < 64 {
        Number::UInt(1u64 << exp)
    } else {
        let mut value = BigInt::one();
        value <<= exp as usize;
        Number::from_bigint_owned(value)
    }
}

// Verus does not yet support overloaded op-assignment operators such as `*=`.
#[verus_verify(external_body)]
#[verus_spec(result =>
    ensures
        result@ == vstd::arithmetic::power::pow(10, exp as nat),
)]
fn pow10_bigint(exp: u32) -> BigInt {
    if exp == 0 {
        return BigInt::one();
    }

    let mut result = BigInt::one();
    let mut base = BigInt::from(10u8);
    let mut e = exp;

    while e > 0 {
        if e & 1 == 1 {
            result *= &base;
        }
        if e > 1 {
            base = &base * &base;
        }
        e >>= 1;
    }

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

// Verus does not support format!
#[verus_verify(external_body)]
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

    let exponent = digits.len() as i32 - 1;
    format!("{}{}.{}e{}", sign, &digits[0..1], &digits[1..], exponent)
}

#[verus_verify(external_body)]
fn parse_scientific_bigint(input: &str) -> Option<BigInt> {
    let (mantissa, exponent_part) = split_scientific_parts(input)?;
    let exponent = exponent_part.parse::<i32>().ok()?;
    scientific_parts_to_bigint(mantissa, exponent)
}

#[verus_verify(external_body)]
#[verus_spec(result =>
    ensures
        result matches Some((_, exponent)) ==> exponent@.len() > 0,
)]
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

#[verus_verify(external_body)]
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
    fn two_pow_computes_minimum_exponent() {
        assert!(matches!(
            Number::two_pow(i32::MIN),
            Ok(Number::Float(value)) if value == 0.0
        ));
    }

    #[test]
    fn ten_pow_uses_unsigned_minimum_exponent_magnitude() {
        assert_eq!((-(i32::MIN as i64)) as u32, 1u32 << 31);
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
}

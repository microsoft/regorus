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

use crate::*;

pub type BigInt = NumBigInt;

const F64_SAFE_INTEGER: f64 = 9_007_199_254_740_992.0; // 2^53

#[derive(Clone)]
pub enum Number {
    UInt(u64),
    Int(i64),
    Float(f64),
    BigInt(Rc<BigInt>),
}

impl Number {
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

    fn to_bigint_owned(&self) -> Option<BigInt> {
        match self {
            Number::UInt(v) => Some(BigInt::from(*v)),
            Number::Int(v) => Some(BigInt::from(*v)),
            Number::BigInt(v) => Some((**v).clone()),
            Number::Float(f) => Self::float_to_small_bigint(*f),
        }
    }

    fn float_to_small_bigint(value: f64) -> Option<BigInt> {
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

    fn to_bigint_rc(&self) -> Option<Rc<BigInt>> {
        match self {
            Number::BigInt(v) => Some(v.clone()),
            _ => self.to_bigint_owned().map(Rc::new),
        }
    }

    fn to_f64_lossy(&self) -> f64 {
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

    fn is_zero(&self) -> bool {
        match self {
            Number::UInt(0) | Number::Int(0) => true,
            Number::Float(f) => *f == 0.0,
            Number::BigInt(v) => v.is_zero(),
            _ => false,
        }
    }

    fn ints_to_bigint(a: &Number, b: &Number) -> (BigInt, BigInt) {
        (a.to_bigint_owned().unwrap(), b.to_bigint_owned().unwrap())
    }

    fn normalize_float(value: f64) -> Number {
        if let Some(int) = Self::float_to_small_bigint(value) {
            return Self::from_bigint_owned(int);
        }
        Number::Float(value)
    }

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

impl From<BigInt> for Number {
    fn from(value: BigInt) -> Self {
        Number::from_bigint_owned(value)
    }
}

impl From<u64> for Number {
    fn from(value: u64) -> Self {
        Number::UInt(value)
    }
}

impl From<usize> for Number {
    fn from(value: usize) -> Self {
        Number::UInt(value as u64)
    }
}

impl From<u128> for Number {
    fn from(value: u128) -> Self {
        if let Ok(n) = u64::try_from(value) {
            Number::UInt(n)
        } else {
            Number::from_bigint_owned(BigInt::from(value))
        }
    }
}

impl From<i64> for Number {
    fn from(value: i64) -> Self {
        Number::Int(value)
    }
}

impl From<i128> for Number {
    fn from(value: i128) -> Self {
        Number::from_i128(value)
    }
}

impl From<f64> for Number {
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

impl PartialEq for Number {
    fn eq(&self, other: &Self) -> bool {
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

impl Ord for Number {
    fn cmp(&self, other: &Self) -> Ordering {
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

impl Number {
    pub fn as_u128(&self) -> Option<u128> {
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

    pub fn as_i128(&self) -> Option<i128> {
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

    pub fn as_u64(&self) -> Option<u64> {
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

    pub fn as_i64(&self) -> Option<i64> {
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

    pub fn as_f64(&self) -> Option<f64> {
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

    pub fn as_big(&self) -> Option<Rc<BigInt>> {
        self.to_bigint_rc()
    }

    pub fn to_big(&self) -> Result<Rc<BigInt>> {
        self.as_big()
            .ok_or_else(|| anyhow!("Number::to_big failed"))
    }

    pub fn add_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.add(rhs)?;
        Ok(())
    }

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

    pub fn sub_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.sub(rhs)?;
        Ok(())
    }

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

    pub fn mul_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.mul(rhs)?;
        Ok(())
    }

    pub fn mul(&self, rhs: &Self) -> Result<Number> {
        if matches!(self, Number::Float(_)) || matches!(rhs, Number::Float(_)) {
            return Ok(Number::normalize_float(
                self.to_f64_lossy() * rhs.to_f64_lossy(),
            ));
        }

        match (self, rhs) {
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
            _ => unreachable!(),
        }
    }

    pub fn divide(self, rhs: &Self) -> Result<Number> {
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
                if *a % *b == 0 {
                    if let Some(q) = a.checked_div(*b) {
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

    pub fn modulo(self, rhs: &Self) -> Result<Number> {
        if rhs.is_zero() {
            bail!("modulo by zero");
        }

        if !self.is_integer() || !rhs.is_integer() {
            bail!("modulo on floating-point number");
        }

        let (a, b) = Number::ints_to_bigint(&self, rhs);
        let rem = a % &b;
        Ok(Number::from_bigint_owned(rem))
    }

    pub fn is_integer(&self) -> bool {
        match self {
            Number::Float(f) => f.is_finite() && f.fract() == 0.0,
            _ => true,
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            Number::UInt(_) => true,
            Number::Int(v) => *v >= 0,
            Number::BigInt(v) => !v.is_negative(),
            Number::Float(f) => f.is_sign_positive(),
        }
    }

    fn ensure_integers(a: &Number, b: &Number) -> Option<(BigInt, BigInt)> {
        if a.is_integer() && b.is_integer() {
            Some((a.to_bigint_owned()?, b.to_bigint_owned()?))
        } else {
            None
        }
    }

    fn ensure_integer(&self) -> Option<BigInt> {
        if self.is_integer() {
            self.to_bigint_owned()
        } else {
            None
        }
    }

    pub fn and(&self, rhs: &Self) -> Option<Number> {
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a & b))
    }

    pub fn or(&self, rhs: &Self) -> Option<Number> {
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a | b))
    }

    pub fn xor(&self, rhs: &Self) -> Option<Number> {
        let (a, b) = Self::ensure_integers(self, rhs)?;
        Some(Number::from_bigint_owned(a ^ b))
    }

    pub fn lsh(&self, rhs: &Self) -> Option<Number> {
        let shift = rhs.as_u32()? as usize;
        let mut value = self.ensure_integer()?;
        value <<= shift;
        Some(Number::from_bigint_owned(value))
    }

    pub fn rsh(&self, rhs: &Self) -> Option<Number> {
        let shift = rhs.as_u32()? as usize;
        let mut value = self.ensure_integer()?;
        value >>= shift;
        Some(Number::from_bigint_owned(value))
    }

    pub fn neg(&self) -> Option<Number> {
        let mut value = self.ensure_integer()?;
        value = !value;
        Some(Number::from_bigint_owned(value))
    }

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

    pub fn floor(&self) -> Number {
        match self {
            Number::Float(f) => Number::normalize_float(f.floor()),
            _ => self.clone(),
        }
    }

    pub fn ceil(&self) -> Number {
        match self {
            Number::Float(f) => Number::normalize_float(f.ceil()),
            _ => self.clone(),
        }
    }

    pub fn round(&self) -> Number {
        match self {
            Number::Float(f) => Number::normalize_float(f.round()),
            _ => self.clone(),
        }
    }

    pub fn two_pow(e: i32) -> Result<Number> {
        if e >= 0 {
            Ok(two_pow_positive(e as u32))
        } else {
            let denom = two_pow_positive((-e) as u32);
            Number::from(1u64).divide(&denom)
        }
    }

    pub fn ten_pow(e: i32) -> Result<Number> {
        if e >= 0 {
            Ok(ten_pow_positive(e as u32))
        } else {
            let denom = ten_pow_positive((-e) as u32);
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

fn two_pow_positive(exp: u32) -> Number {
    if exp < 64 {
        Number::UInt(1u64 << exp)
    } else {
        let mut value = BigInt::one();
        value <<= exp as usize;
        Number::from_bigint_owned(value)
    }
}

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

    let exponent = digits.len() as i32 - 1;
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

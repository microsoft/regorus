// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::fmt::{Debug, Formatter};
use std::cmp::{Ord, Ordering};
use std::str::FromStr;

use anyhow::{anyhow, bail, Result};

use serde::ser::Serializer;
use serde::Serialize;

use crate::Rc;

pub type BigInt = i128;

type BigFloat = scientific::Scientific;
const PRECISION: scientific::Precision = scientific::Precision::Digits(100);

#[derive(Clone, Debug, PartialEq)]
pub struct BigDecimal {
    d: BigFloat,
}

impl AsRef<BigFloat> for BigDecimal {
    fn as_ref(&self) -> &BigFloat {
        &self.d
    }
}

impl AsMut<BigFloat> for BigDecimal {
    fn as_mut(&mut self) -> &mut BigFloat {
        &mut self.d
    }
}

impl From<BigFloat> for BigDecimal {
    fn from(value: BigFloat) -> Self {
        BigDecimal { d: value }
    }
}

impl From<i128> for BigDecimal {
    fn from(value: i128) -> Self {
        BigDecimal {
            d: Into::<BigFloat>::into(value),
        }
    }
}

impl BigDecimal {
    fn is_integer(&self) -> bool {
        self.d.decimals() <= 0
    }
}

#[derive(Clone)]
pub enum Number {
    // TODO: maybe specialize for u64, i64, f64
    Big(Rc<BigDecimal>),
}

impl Debug for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Number::Big(b) => b.d.fmt(f),
        }
    }
}

impl Serialize for Number {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Big(_) => {
                let s = self.format_decimal();
                let v = serde_json::Number::from_str(&s)
                    .map_err(|_| serde::ser::Error::custom("could not serialize big number"))?;
                v.serialize(serializer)
            }
        }
    }
}

use Number::*;

impl From<BigFloat> for Number {
    fn from(n: BigFloat) -> Self {
        Self::Big(BigDecimal::from(n).into())
    }
}

impl From<u64> for Number {
    fn from(n: u64) -> Self {
        BigFloat::from(n).into()
    }
}

impl From<usize> for Number {
    fn from(n: usize) -> Self {
        BigFloat::from(n).into()
    }
}

impl From<u128> for Number {
    fn from(n: u128) -> Self {
        BigFloat::from(n).into()
    }
}

impl From<i128> for Number {
    fn from(n: i128) -> Self {
        BigFloat::from(n).into()
    }
}

impl From<i64> for Number {
    fn from(n: i64) -> Self {
        BigFloat::from(n).into()
    }
}

impl From<f64> for Number {
    fn from(n: f64) -> Self {
        // Reading from float is not precise. Therefore, serialize to string and read.
        match Self::from_str(&format!("{n}")) {
            Ok(v) => v,
            _ => BigFloat::ZERO.into(),
        }
    }
}

impl Number {
    pub fn as_u128(&self) -> Option<u128> {
        match self {
            Big(b) if b.is_integer() => match u128::try_from(&b.d) {
                Ok(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn as_i128(&self) -> Option<i128> {
        match self {
            Big(b) if b.is_integer() => match i128::try_from(&b.d) {
                Ok(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Big(b) if b.is_integer() => match u64::try_from(&b.d) {
                Ok(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Big(b) if b.is_integer() => match i64::try_from(&b.d) {
                Ok(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Big(b) => {
                let f = f64::from(&b.d);
                match BigFloat::try_from(f) {
                    Ok(bf) if bf == b.d => Some(f),
                    _ => None,
                }
            }
        }
    }

    pub fn as_big(&self) -> Option<Rc<BigDecimal>> {
        Some(match self {
            Big(b) => b.clone(),
        })
    }

    pub fn to_big(&self) -> Result<Rc<BigDecimal>> {
        match self.as_big() {
            Some(b) => Ok(b),
            _ => bail!("Number::to_big failed"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseNumberError;

impl FromStr for Number {
    type Err = ParseNumberError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Ok(v) = BigFloat::from_str(s) {
            return Ok(v.into());
        }
        Ok(f64::from_str(s).map_err(|_| ParseNumberError)?.into())
    }
}

impl Eq for Number {}

impl PartialEq for Number {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Big(a), Big(b)) => a.d == b.d,
        }
    }
}

impl Ord for Number {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Big(a), Big(b)) => a.d.cmp(&b.d),
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Number {
    pub fn add_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.add(rhs)?;
        Ok(())
    }

    pub fn add(&self, rhs: &Self) -> Result<Number> {
        match (self, rhs) {
            (Big(a), Big(b)) => Ok(Big(BigDecimal::from(&a.d + &b.d).into())),
        }
    }

    pub fn sub_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.sub(rhs)?;
        Ok(())
    }

    pub fn sub(&self, rhs: &Self) -> Result<Number> {
        match (self, rhs) {
            (Big(a), Big(b)) => Ok(Big(BigDecimal::from(&a.d - &b.d).into())),
        }
    }

    pub fn mul_assign(&mut self, rhs: &Self) -> Result<()> {
        *self = self.mul(rhs)?;
        Ok(())
    }

    pub fn mul(&self, rhs: &Self) -> Result<Number> {
        match (self, rhs) {
            (Big(a), Big(b)) => Ok(Big(BigDecimal::from(&a.d * &b.d).into())),
        }
    }

    pub fn divide(self, rhs: &Self) -> Result<Number> {
        match (self, rhs) {
            (Big(a), Big(b)) => {
                let c =
                    a.d.div_truncate(&b.d, PRECISION)
                        .map_err(|e| anyhow!("{e}"))?;
                Ok(Big(BigDecimal::from(c).into()))
            }
        }
    }

    pub fn modulo(self, rhs: &Self) -> Result<Number> {
        match (self, rhs) {
            (Big(a), Big(b)) => {
                let (_, c) = a.d.div_rem(&b.d).map_err(|e| anyhow!("{e}"))?;
                Ok(Big(BigDecimal::from(c).into()))
            }
        }
    }

    pub fn is_integer(&self) -> bool {
        match self {
            Big(b) => b.is_integer(),
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            Big(b) => b.d.is_sign_positive(),
        }
    }

    fn ensure_integers(a: &Number, b: &Number) -> Option<(BigInt, BigInt)> {
        match (a, b) {
            (Big(a), Big(b)) if a.is_integer() && b.is_integer() => {
                match (BigInt::try_from(&a.d), BigInt::try_from(&b.d)) {
                    (Ok(a), Ok(b)) => Some((a, b)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn ensure_integer(&self) -> Option<BigInt> {
        match self {
            Big(a) if a.is_integer() => match BigInt::try_from(&a.d) {
                Ok(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn and(&self, rhs: &Self) -> Option<Number> {
        match Self::ensure_integers(self, rhs) {
            Some((a, b)) => Some((a & b).into()),
            _ => None,
        }
    }

    pub fn or(&self, rhs: &Self) -> Option<Number> {
        match Self::ensure_integers(self, rhs) {
            Some((a, b)) => Some((a | b).into()),
            _ => None,
        }
    }

    pub fn xor(&self, rhs: &Self) -> Option<Number> {
        match Self::ensure_integers(self, rhs) {
            Some((a, b)) => Some((a ^ b).into()),
            _ => None,
        }
    }

    pub fn lsh(&self, rhs: &Self) -> Option<Number> {
        match Self::ensure_integers(self, rhs) {
            Some((a, b)) => a.checked_shl(b as u32).map(|v| v.into()),
            _ => None,
        }
    }

    pub fn rsh(&self, rhs: &Self) -> Option<Number> {
        match Self::ensure_integers(self, rhs) {
            Some((a, b)) => a.checked_shr(b as u32).map(|v| v.into()),
            _ => None,
        }
    }

    pub fn neg(&self) -> Option<Number> {
        self.ensure_integer().map(|a| (!a).into())
    }

    pub fn abs(&self) -> Number {
        match self {
            Big(b) => b.d.clone().abs().into(),
        }
    }

    pub fn floor(&self) -> Number {
        match self {
            Big(b) => Big(BigDecimal::from(b.d.round(
                scientific::Precision::Decimals(0),
                scientific::Rounding::RoundDown,
            ))
            .into()),
        }
    }

    pub fn ceil(&self) -> Number {
        match self {
            Big(b) => Big(BigDecimal::from(b.d.round(
                scientific::Precision::Decimals(0),
                scientific::Rounding::RoundUp,
            ))
            .into()),
        }
    }

    pub fn round(&self) -> Number {
        match self {
            Big(b) => Big(BigDecimal::from(b.d.round(
                scientific::Precision::Decimals(0),
                scientific::Rounding::RoundHalfAwayFromZero,
            ))
            .into()),
        }
    }

    pub fn two_pow(e: i32) -> Result<Number> {
        if e >= 0 {
            Ok(BigFloat::from(2).powi(e as usize).into())
        } else {
            Number::from(1u64).divide(&BigFloat::from(2).powi(-e as usize).into())
        }
    }

    pub fn ten_pow(e: i32) -> Result<Number> {
        if e >= 0 {
            Ok(BigFloat::from(10).powi(e as usize).into())
        } else {
            Number::from(1u64).divide(&BigFloat::from(10).powi(-e as usize).into())
        }
    }

    pub fn format_bin(&self) -> String {
        self.ensure_integer()
            .map(|a| format!("{:b}", a))
            .unwrap_or("".to_string())
    }

    pub fn format_octal(&self) -> String {
        self.ensure_integer()
            .map(|a| format!("{:o}", a))
            .unwrap_or("".to_string())
    }

    pub fn format_scientific(&self) -> String {
        match self {
            Big(b) => format!("{}", b.d),
        }
    }

    pub fn format_decimal(&self) -> String {
        if let Some(u) = self.as_u64() {
            u.to_string()
        } else if let Some(i) = self.as_i64() {
            i.to_string()
        } else if let Some(f) = self.as_f64() {
            f.to_string()
        } else {
            let s = match self {
                Big(b) => format!("{}", b.d),
            };

            // Remove trailing e0
            if s.ends_with("e0") {
                return s[..s.len() - 2].to_string();
            }

            // Avoid e notation if full mantissa is written out.
            let parts: Vec<&str> = s.split('e').collect();
            match self {
                Big(b) => {
                    if b.d.is_sign_positive() {
                        if parts[0].len() == b.d.exponent1() as usize + 2 {
                            return parts[0].replace('.', "");
                        }
                    } else if parts[0].len() == b.d.exponent1() as usize + 3 {
                        return parts[0].replace('.', "");
                    }
                }
            }

            s
        }
    }

    pub fn format_decimal_with_width(&self, d: u32) -> String {
        match self {
            Big(b) => {
                let n = Big(BigDecimal::from(b.d.round(
                    scientific::Precision::Decimals(d as isize),
                    scientific::Rounding::RoundHalfAwayFromZero,
                ))
                .into());
                n.format_decimal()
            }
        }
    }

    pub fn format_hex(&self) -> String {
        self.ensure_integer()
            .map(|a| format!("{:x}", a))
            .unwrap_or("".to_string())
    }

    pub fn format_big_hex(&self) -> String {
        self.ensure_integer()
            .map(|a| format!("{:X}", a))
            .unwrap_or("".to_string())
    }
}

#[cfg(test)]
mod test {
    use crate::number::*;

    #[test]
    fn display_number() {
        let n = Number::from(123456f64);
        assert_eq!(format!("{}", n.format_decimal()), "123456");
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::fmt::{Debug, Formatter};
use std::cmp::{Ord, Ordering};
use std::ops::{AddAssign, Div, MulAssign, SubAssign};
use std::rc::Rc;
use std::str::FromStr;

use anyhow::{bail, Result};
use dashu_float;
use num_traits::cast::ToPrimitive;

use serde::ser::Serializer;
use serde::Serialize;

pub type BigInt = i128;

type BigFloat = dashu_float::DBig;
const PRECISION: usize = 100;

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
            d: Into::<BigFloat>::into(value)
                .with_precision(PRECISION)
                .value(),
        }
    }
}

impl Serialize for BigDecimal {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = self.d.to_string();
        let v = serde_json::Number::from_str(&s)
            .map_err(|_| serde::ser::Error::custom("could not serialize big number"))?;
        v.serialize(serializer)
    }
}

impl BigDecimal {
    fn is_integer(&self) -> bool {
        self.d.floor() == self.d
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
            Big(b) => {
                if let Some(n) = self.as_u64() {
                    n.serialize(serializer)
                } else if let Some(n) = self.as_i64() {
                    n.serialize(serializer)
                } else {
                    if let Some(f) = self.as_f64() {
                        if b.d.digits() <= 15 {
                            return f.serialize(serializer);
                        }
                    }
                    let s = b.d.to_string();
                    let v = serde_json::Number::from_str(&s)
                        .map_err(|_| serde::ser::Error::custom("could not serialize big number"))?;
                    v.serialize(serializer)
                }
            }
        }
    }
}

use Number::*;

impl From<BigFloat> for Number {
    fn from(n: BigFloat) -> Self {
        Self::Big(BigDecimal::from(n.with_precision(PRECISION).value()).into())
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
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Big(b) if b.is_integer() => b.d.to_u64(),
            _ => None,
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Big(b) if b.is_integer() => b.d.to_i64(),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Big(b) => Some(b.d.to_binary().value().to_f64().value()),
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
        match (self, rhs) {
            (Big(ref mut a), Big(b)) => {
                Rc::make_mut(a).d.add_assign(&b.d);
            }
        }
        Ok(())
    }

    pub fn add(&self, rhs: &Self) -> Result<Number> {
        let mut c = self.clone();
        c.add_assign(rhs)?;
        Ok(c)
    }

    pub fn sub_assign(&mut self, rhs: &Self) -> Result<()> {
        match (self, rhs) {
            (Big(ref mut a), Big(b)) => {
                Rc::make_mut(a).d.sub_assign(&b.d);
            }
        }
        Ok(())
    }

    pub fn sub(&self, rhs: &Self) -> Result<Number> {
        let mut c = self.clone();
        c.sub_assign(rhs)?;
        Ok(c)
    }

    pub fn mul_assign(&mut self, rhs: &Self) -> Result<()> {
        match (self, rhs) {
            (Big(ref mut a), Big(b)) => {
                Rc::make_mut(a).d.mul_assign(&b.d);
            }
        }
        Ok(())
    }

    pub fn mul(&self, rhs: &Self) -> Result<Number> {
        let mut c = self.clone();
        c.mul_assign(rhs)?;
        Ok(c)
    }

    pub fn divide(self, rhs: &Self) -> Result<Number> {
        Ok(match (self, rhs) {
            (Big(a), Big(b)) => a.d.clone().div(&b.d).into(),
        })
    }

    pub fn modulo(self, rhs: &Self) -> Result<Number> {
        use dashu_base::RemEuclid;
        Ok(match (self, rhs) {
            (Big(a), Big(b)) => a.d.clone().rem_euclid(&b.d).into(),
        })
    }

    pub fn is_integer(&self) -> bool {
        match self {
            Big(b) => b.is_integer(),
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            Big(b) => b.d.sign() == dashu_base::Sign::Positive,
        }
    }

    fn ensure_integers(a: &Number, b: &Number) -> Option<(BigInt, BigInt)> {
        match (a, b) {
            (Big(a), Big(b)) if a.is_integer() && b.is_integer() => {
                match (a.d.to_i128(), b.d.to_i128()) {
                    (Some(a), Some(b)) => Some((a, b)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn ensure_integer(&self) -> Option<BigInt> {
        match self {
            Big(a) if a.is_integer() => a.d.to_i128(),
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
        use dashu_base::Abs;
        match self {
            Big(b) => b.d.clone().abs().into(),
        }
    }

    pub fn floor(&self) -> Number {
        match self {
            Big(b) => b.d.floor().into(),
        }
    }

    pub fn ceil(&self) -> Number {
        match self {
            Big(b) => b.d.ceil().into(),
        }
    }

    pub fn round(&self) -> Number {
        match self {
            Big(b) => b.d.round().into(),
        }
    }

    pub fn two_pow(e: i32) -> Number {
        use num_traits::Pow;
        BigFloat::from(2)
            .with_precision(80)
            .value()
            .pow(&BigFloat::from(e))
            .into()
    }

    pub fn ten_pow(e: i32) -> Number {
        use num_traits::Pow;
        BigFloat::from(10)
            .with_precision(80)
            .value()
            .pow(&BigFloat::from(e))
            .into()
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

    pub fn format_decimal(&self) -> String {
        self.ensure_integer()
            .map(|a| format!("{}", a))
            .unwrap_or("".to_string())
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

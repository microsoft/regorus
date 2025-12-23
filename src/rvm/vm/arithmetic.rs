#![allow(
    clippy::unused_self,
    clippy::missing_const_for_fn,
    clippy::unseparated_literal_suffix,
    clippy::pattern_type_mismatch
)]
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;

use crate::number::Number;
use crate::value::Value;

use super::errors::{Result, VmError};
use super::machine::RegoVM;

impl RegoVM {
    /// Add two values using interpreter's arithmetic logic
    pub(super) fn add_values(&self, a: &Value, b: &Value) -> Result<Value> {
        match (a, b) {
            (Value::Number(x), Value::Number(y)) => Ok(Value::from(x.add(y)?)),
            _ => Err(VmError::InvalidAddition {
                left: a.clone(),
                right: b.clone(),
            }),
        }
    }

    /// Subtract two values using interpreter's arithmetic logic
    pub(super) fn sub_values(&self, a: &Value, b: &Value) -> Result<Value> {
        match (a, b) {
            (Value::Number(x), Value::Number(y)) => Ok(Value::from(x.sub(y)?)),
            (Value::Set(left), Value::Set(right)) => {
                let diff: BTreeSet<Value> = left.difference(right).cloned().collect();
                Ok(Value::from_set(diff))
            }
            _ => Err(VmError::InvalidSubtraction {
                left: a.clone(),
                right: b.clone(),
            }),
        }
    }

    /// Multiply two values using interpreter's arithmetic logic
    pub(super) fn mul_values(&self, a: &Value, b: &Value) -> Result<Value> {
        match (a, b) {
            (Value::Number(x), Value::Number(y)) => Ok(Value::from(x.mul(y)?)),
            _ => Err(VmError::InvalidMultiplication {
                left: a.clone(),
                right: b.clone(),
            }),
        }
    }

    /// Divide two values using interpreter's arithmetic logic
    pub(super) fn div_values(&self, a: &Value, b: &Value) -> Result<Value> {
        match (a, b) {
            (Value::Number(x), Value::Number(y)) => {
                if *y == Number::from(0u64) {
                    if self.strict_builtin_errors {
                        return Err(VmError::InvalidDivision {
                            left: a.clone(),
                            right: b.clone(),
                        });
                    }
                    return Ok(Value::Undefined);
                }

                Ok(Value::from(x.clone().divide(y)?))
            }
            _ => Err(VmError::InvalidDivision {
                left: a.clone(),
                right: b.clone(),
            }),
        }
    }

    /// Modulo two values using interpreter's arithmetic logic
    pub(super) fn mod_values(&self, a: &Value, b: &Value) -> Result<Value> {
        match (a, b) {
            (Value::Number(x), Value::Number(y)) => {
                if *y == Number::from(0u64) {
                    if self.strict_builtin_errors {
                        return Err(VmError::InvalidModulo {
                            left: a.clone(),
                            right: b.clone(),
                        });
                    }
                    return Ok(Value::Undefined);
                }

                if !x.is_integer() || !y.is_integer() {
                    return Err(VmError::ModuloOnFloat);
                }

                Ok(Value::from(x.clone().modulo(y)?))
            }
            _ => Err(VmError::InvalidModulo {
                left: a.clone(),
                right: b.clone(),
            }),
        }
    }

    pub(super) fn to_bool(&self, value: &Value) -> Option<bool> {
        match value {
            Value::Bool(b) => Some(*b),
            Value::Null if !self.strict_builtin_errors => Some(true),
            _ => None,
        }
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template numeric function builtins for Azure Policy expressions.
//!
//! Implements: min, max, float.
//!
//! Note: `sub`, `mul`, `div`, `mod` are compiled directly to native RVM
//! instructions (`Sub`, `Mul`, `Div`, `Mod`) and do not need builtins.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;

use anyhow::Result;

use super::helpers::try_coerce_to_number;

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.min", (fn_min, 0));
    m.insert("azure.policy.fn.max", (fn_max, 0));
    m.insert("azure.policy.fn.float", (fn_float, 1));
    m.insert("azure.policy.fn.int_div", (fn_int_div, 2));
    m.insert("azure.policy.fn.int_mod", (fn_int_mod, 2));
}

/// `min(arg1, arg2, ...)` or `min(intArray)` → smallest integer/number.
///
/// Accepts either:
/// - Multiple integer arguments: `min(1, 2, 3)` → `1`
/// - A single array argument: `min([1, 2, 3])` → `1`
fn fn_min(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let values = if args.len() == 1 {
        args.first().map_or(args, |first| match *first {
            Value::Array(ref arr) => arr.as_ref().as_slice(),
            _ => args,
        })
    } else {
        args
    };

    if values.is_empty() {
        return Ok(Value::Undefined);
    }

    let mut result: Option<&Value> = None;
    for v in values {
        match *v {
            Value::Number(_) => {
                result = Some(match result {
                    Some(current) if v >= current => current,
                    _ => v,
                });
            }
            _ => return Ok(Value::Undefined),
        }
    }

    Ok(result.cloned().unwrap_or(Value::Undefined))
}

/// `max(arg1, arg2, ...)` or `max(intArray)` → largest integer/number.
///
/// Same overloading as `min`.
fn fn_max(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let values = if args.len() == 1 {
        args.first().map_or(args, |first| match *first {
            Value::Array(ref arr) => arr.as_ref().as_slice(),
            _ => args,
        })
    } else {
        args
    };

    if values.is_empty() {
        return Ok(Value::Undefined);
    }

    let mut result: Option<&Value> = None;
    for v in values {
        match *v {
            Value::Number(_) => {
                result = Some(match result {
                    Some(current) if v <= current => current,
                    _ => v,
                });
            }
            _ => return Ok(Value::Undefined),
        }
    }

    Ok(result.cloned().unwrap_or(Value::Undefined))
}

/// `float(value)` → floating-point number.
fn fn_float(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    match *arg {
        Value::Number(ref n) => n
            .as_f64()
            .map_or_else(|| Ok(arg.clone()), |f| Ok(Value::from(f))),
        Value::String(ref s) => Ok(try_coerce_to_number(s)
            .and_then(|n| n.as_f64())
            .map_or(Value::Undefined, Value::from)),
        _ => Ok(Value::Undefined),
    }
}

/// `div(operand1, operand2)` → integer division (truncating).
///
/// ARM template `div()` performs integer division, unlike the RVM `Div`
/// instruction which may produce floats for non-evenly-divisible operands.
fn fn_int_div(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [a, b] = args
    else {
        return Ok(Value::Undefined);
    };
    let (a, b) = (extract_i64(a), extract_i64(b));
    match (a, b) {
        (Some(a), Some(b)) => a
            .checked_div(b)
            .map_or(Ok(Value::Undefined), |r| Ok(Value::from(r))),
        _ => Ok(Value::Undefined),
    }
}

/// `mod(operand1, operand2)` → integer modulo.
fn fn_int_mod(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [a, b] = args
    else {
        return Ok(Value::Undefined);
    };
    let (a, b) = (extract_i64(a), extract_i64(b));
    match (a, b) {
        (Some(a), Some(b)) => a
            .checked_rem(b)
            .map_or(Ok(Value::Undefined), |r| Ok(Value::from(r))),
        _ => Ok(Value::Undefined),
    }
}

fn extract_i64(v: &Value) -> Option<i64> {
    match *v {
        Value::Number(ref n) => n.as_i64().or_else(|| n.as_f64().map(f64_to_i64)),
        _ => None,
    }
}

#[expect(clippy::as_conversions)]
const fn f64_to_i64(x: f64) -> i64 {
    x as i64
}

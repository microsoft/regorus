// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};
use crate::lexer::Span;
use crate::number::Number;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("count", (count, 1));
    m.insert("max", (max, 1));
    m.insert("min", (min, 1));
    m.insert("product", (product, 1));
    m.insert("sort", (sort, 1));
    m.insert("sum", (sum, 1));
}

fn count(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    ensure_args_count(span, "count", params, args, 1)?;

    Ok(Value::from(Number::from(match &args[0] {
        Value::Array(a) => a.len(),
        Value::Set(a) => a.len(),
        Value::Object(a) => a.len(),
        Value::String(a) => a.encode_utf16().count(),
        a if strict => {
            let span = params[0].span();
            bail!(span.error(
                format!("`count` requires array/object/set/string argument. Got `{a}`.").as_str()
            ))
        }
        _ => return Ok(Value::Undefined),
    })))
}

fn max(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "max", params, args, 1)?;

    Ok(match &args[0] {
        Value::Array(a) if a.is_empty() => Value::Undefined,
        Value::Array(a) => a.iter().max().unwrap().clone(),
        Value::Set(a) if a.is_empty() => Value::Undefined,
        Value::Set(a) => a.iter().max().unwrap().clone(),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`max` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

fn min(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "min", params, args, 1)?;

    Ok(match &args[0] {
        Value::Array(a) if a.is_empty() => Value::Undefined,
        Value::Array(a) => a.iter().min().unwrap().clone(),
        Value::Set(a) if a.is_empty() => Value::Undefined,
        Value::Set(a) => a.iter().min().unwrap().clone(),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`min` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

fn product(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "product", params, args, 1)?;

    let mut v = Number::from(1_u64);
    Ok(Value::from(match &args[0] {
        Value::Array(a) => {
            for e in a.iter() {
                v.mul_assign(&ensure_numeric("product", &params[0], e)?)?;
            }
            v
        }

        Value::Set(a) => {
            for e in a.iter() {
                v.mul_assign(&ensure_numeric("product", &params[0], e)?)?;
            }
            v
        }
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`product` requires array/set argument. Got `{a}`.").as_str()))
        }
    }))
}

fn sort(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "sort", params, args, 1)?;
    Ok(match &args[0] {
        Value::Array(a) => {
            let mut ac = (**a).clone();
            ac.sort();
            Value::from(ac)
        }
        // Sorting a set produces array.
        Value::Set(a) => Value::from(a.iter().cloned().collect::<Vec<Value>>()),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`sort` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

fn sum(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "sum", params, args, 1)?;

    let mut v = Number::from(0_u64);
    Ok(Value::from(match &args[0] {
        Value::Array(a) => {
            for e in a.iter() {
                v.add_assign(&ensure_numeric("sum", &params[0], e)?)?;
            }
            v
        }

        Value::Set(a) => {
            for e in a.iter() {
                v.add_assign(&ensure_numeric("sum", &params[0], e)?)?;
            }
            v
        }
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`sum` requires array/set argument. Got `{a}`.").as_str()))
        }
    }))
}

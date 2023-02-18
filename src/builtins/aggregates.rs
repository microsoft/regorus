// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};
use crate::lexer::Span;
use crate::value::{Float, Value};

use anyhow::{bail, Result};

pub fn count(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "count", params, args, 1)?;

    Ok(Value::from_float(match &args[0] {
        Value::Array(a) => a.len() as Float,
        Value::Set(a) => a.len() as Float,
        Value::Object(a) => a.len() as Float,
        Value::String(a) => a.len() as Float,
        a => {
            let span = params[0].span();
            bail!(span.error(
                format!("`count` requires array/object/set/string argument. Got `{a}`.").as_str()
            ))
        }
    }))
}

pub fn max(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
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

pub fn min(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "min", params, args, 1)?;

    Ok(match &args[0] {
        Value::Array(a) if a.is_empty() => Value::Undefined,
        Value::Array(a) => a.iter().max().unwrap().clone(),
        Value::Set(a) if a.is_empty() => Value::Undefined,
        Value::Set(a) => a.iter().max().unwrap().clone(),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`min` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

pub fn product(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "min", params, args, 1)?;

    let mut v = 1 as Float;
    Ok(match &args[0] {
        Value::Array(a) => {
            for e in a.iter() {
                v *= ensure_numeric("product", &params[0], e)?;
            }
            Value::from_float(v)
        }

        Value::Set(a) => {
            for e in a.iter() {
                v *= ensure_numeric("product", &params[0], e)?;
            }
            Value::from_float(v)
        }
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`product` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

pub fn sort(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "sort", params, args, 1)?;
    Ok(match &args[0] {
        Value::Array(a) => {
            let mut ac = (**a).clone();
            ac.sort();
            Value::from_array(ac)
        }
        Value::Set(a) => Value::from_set(a.iter().cloned().collect()),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`sort` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

pub fn sum(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "sum", params, args, 1)?;

    let mut v = 0 as Float;
    Ok(match &args[0] {
        Value::Array(a) => {
            for e in a.iter() {
                v += ensure_numeric("sum", &params[0], e)?;
            }
            Value::from_float(v)
        }

        Value::Set(a) => {
            for e in a.iter() {
                v += ensure_numeric("sum", &params[0], e)?;
            }
            Value::from_float(v)
        }
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`sum` requires array/set argument. Got `{a}`.").as_str()))
        }
    })
}

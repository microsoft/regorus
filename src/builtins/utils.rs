// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]
use crate::ast::{Expr, Ref};
use crate::lexer::Span;
use crate::number::Number;
use crate::Rc;
use crate::Value;
use crate::*;

use alloc::collections::{BTreeMap, BTreeSet};

use anyhow::{bail, Result};

#[inline]
pub fn enforce_limit() -> Result<()> {
    crate::utils::limits::check_memory_limit_if_needed().map_err(anyhow::Error::new)
}

pub fn ensure_args_count(
    span: &Span,
    fcn: &'static str,
    params: &[Ref<Expr>],
    args: &[Value],
    expected: usize,
) -> Result<()> {
    if args.len() != expected {
        let span = match args.len() > expected {
            false => span,
            true => params[args.len() - 1].span(),
        };
        if expected == 1 {
            bail!(span.error(format!("`{fcn}` expects 1 argument").as_str()))
        } else {
            bail!(span.error(format!("`{fcn}` expects {expected} arguments").as_str()))
        }
    }
    Ok(())
}

pub fn ensure_numeric(fcn: &str, arg: &Expr, v: &Value) -> Result<Number> {
    Ok(match &v {
        Value::Number(n) => n.clone(),
        _ => {
            let span = arg.span();
            bail!(
                span.error(format!("`{fcn}` expects numeric argument. Got `{v}` instead").as_str())
            )
        }
    })
}

pub fn validate_integer_arg(
    fcn: &str,
    param: &Ref<Expr>,
    original_value: &Value,
    numeric_value: &Number,
    strict: bool,
    allow_negative: bool,
) -> Result<bool> {
    if !numeric_value.is_integer() {
        if strict {
            bail!(param.span().error(
                format!("`{fcn}` expects integer arguments. Got `{original_value}`").as_str()
            ));
        }
        return Ok(false);
    }

    if !allow_negative {
        if let Some(int_value) = numeric_value.as_i128() {
            if int_value < 0 {
                if strict {
                    bail!(param.span().error(
                        format!("`{fcn}` expects non-negative integer arguments. Got `{original_value}`")
                            .as_str(),
                    ));
                }
                return Ok(false);
            }
        } else if !numeric_value.is_positive() {
            if strict {
                bail!(param.span().error(
                    format!(
                        "`{fcn}` expects non-negative integer arguments. Got `{original_value}`"
                    )
                    .as_str(),
                ));
            }
            return Ok(false);
        }
    }

    Ok(true)
}

pub fn ensure_string(fcn: &str, arg: &Expr, v: &Value) -> Result<Rc<str>> {
    Ok(match &v {
        Value::String(s) => s.clone(),
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects string argument. Got `{v}` instead").as_str()))
        }
    })
}

pub fn ensure_string_element<'a>(
    fcn: &str,
    arg: &Expr,
    v: &'a Value,
    idx: usize,
) -> Result<&'a str> {
    Ok(match &v {
        Value::String(s) => s.as_ref(),
        _ => {
            let span = arg.span();
            bail!(span.error(
                format!("`{fcn}` expects string collection. Element {idx} is not a string.")
                    .as_str()
            ))
        }
    })
}

pub fn ensure_string_collection<'a>(fcn: &str, arg: &Expr, v: &'a Value) -> Result<Vec<&'a str>> {
    let mut collection = vec![];
    match &v {
        Value::Array(a) => {
            for (idx, elem) in a.iter().enumerate() {
                collection.push(ensure_string_element(fcn, arg, elem, idx)?);
                // Enforce allocator limit while materializing the string collection.
                enforce_limit()?;
            }
        }
        Value::Set(s) => {
            for (idx, elem) in s.iter().enumerate() {
                collection.push(ensure_string_element(fcn, arg, elem, idx)?);
                // Enforce allocator limit while materializing the string collection.
                enforce_limit()?;
            }
        }
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects array/set of strings.").as_str()))
        }
    }
    Ok(collection)
}

pub fn ensure_array(fcn: &str, arg: &Expr, v: Value) -> Result<Rc<Vec<Value>>> {
    Ok(match v {
        Value::Array(a) => a,
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects array argument. Got `{v}` instead").as_str()))
        }
    })
}

pub fn ensure_set(fcn: &str, arg: &Expr, v: Value) -> Result<Rc<BTreeSet<Value>>> {
    Ok(match v {
        Value::Set(s) => s,
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects set argument. Got `{v}` instead").as_str()))
        }
    })
}

pub fn ensure_object(fcn: &str, arg: &Expr, v: Value) -> Result<Rc<BTreeMap<Value, Value>>> {
    Ok(match v {
        Value::Object(o) => o,
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects object argument. Got `{v}` instead").as_str()))
        }
    })
}

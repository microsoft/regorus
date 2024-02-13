// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_array, ensure_numeric};
use crate::lexer::Span;
use crate::Rc;
use crate::Value;

use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("array.concat", (concat, 2));
    m.insert("array.reverse", (reverse, 1));
    m.insert("array.slice", (slice, 3));
}

fn concat(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "array.concat";
    ensure_args_count(span, name, params, args, 2)?;
    let mut v1 = ensure_array(name, &params[0], args[0].clone())?;
    let mut v2 = ensure_array(name, &params[1], args[1].clone())?;

    Rc::make_mut(&mut v1).append(Rc::make_mut(&mut v2));
    Ok(Value::Array(v1))
}

fn reverse(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "array.reverse";
    ensure_args_count(span, name, params, args, 1)?;

    let mut v1 = ensure_array(name, &params[0], args[0].clone())?;
    Rc::make_mut(&mut v1).reverse();
    Ok(Value::Array(v1))
}

fn slice(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "array.slice";
    ensure_args_count(span, name, params, args, 3)?;

    let array = ensure_array(name, &params[0], args[0].clone())?;
    let start = ensure_numeric(name, &params[1], &args[1].clone())?;
    let stop = ensure_numeric(name, &params[2], &args[2].clone())?;

    if !start.is_integer() || !stop.is_integer() {
        return Ok(Value::Undefined);
    }

    let start = match start.as_i64() {
        Some(n) if n < 0 => 0,
        Some(n) => n as usize,
        _ => return Ok(Value::Undefined),
    };

    let stop = match stop.as_i64() {
        Some(n) if n < 0 => 0,
        Some(n) if n as usize > array.len() => array.len(),
        Some(n) => n as usize,
        _ => return Ok(Value::Undefined),
    };

    if start >= stop {
        return Ok(Value::new_array());
    }

    let slice = &array[start..stop];
    Ok(Value::from(slice.to_vec()))
}

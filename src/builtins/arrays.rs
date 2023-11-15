// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_array, ensure_numeric};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;
use std::rc::Rc;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("array.concat", (concat, 2));
    m.insert("array.reverse", (reverse, 1));
    m.insert("array.slice", (slice, 3));
}

fn concat(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "array.concat";
    ensure_args_count(span, name, params, args, 2)?;
    let mut v1 = ensure_array(name, &params[0], args[0].clone())?;
    let mut v2 = ensure_array(name, &params[1], args[1].clone())?;

    Rc::make_mut(&mut v1).append(Rc::make_mut(&mut v2));
    Ok(Value::Array(v1))
}

fn reverse(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "array.reverse";
    ensure_args_count(span, name, params, args, 1)?;

    let mut v1 = ensure_array(name, &params[0], args[0].clone())?;
    Rc::make_mut(&mut v1).reverse();
    Ok(Value::Array(v1))
}

fn slice(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "array.slice";
    ensure_args_count(span, name, params, args, 3)?;

    let array = ensure_array(name, &params[0], args[0].clone())?;
    let start = ensure_numeric(name, &params[1], &args[1].clone())?;
    let stop = ensure_numeric(name, &params[2], &args[2].clone())?;

    if start != start.floor() || stop != stop.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: usize conversion checks.
    let start = start as usize;
    let stop = match stop as usize {
        s if s > array.len() => array.len(),
        s => s,
    };

    if start >= stop {
        return Ok(Value::new_array());
    }

    let slice = &array[start..stop];
    Ok(Value::from_array(slice.to_vec()))
}

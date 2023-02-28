// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string, ensure_string_collection};
use crate::lexer::Span;
use crate::value::{Float, Value};

use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("concat", concat);
    m.insert("contains", contains);
    m.insert("endswith", endswith);
    m.insert("indexof", indexof);
    m.insert("indexof_n", indexof_n);
    m.insert("lower", lower);
    m.insert("startswith", startswith);
    m.insert("upper", upper);
}

fn concat(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "concat";
    ensure_args_count(span, name, params, args, 2)?;
    let delimiter = ensure_string(name, &params[0], &args[0])?;
    let collection = ensure_string_collection(name, &params[1], &args[1])?;
    Ok(Value::String(collection.join(&delimiter)))
}

fn contains(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "contains";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.contains(&s2)))
}

fn endswith(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "endswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.ends_with(&s2)))
}

fn indexof(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "indexof";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::from_float(match s1.find(&s2) {
        Some(pos) => pos as i64,
        _ => -1,
    } as Float))
}

fn indexof_n(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "indexof_n";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;

    let mut positions = vec![];
    let mut idx = 0;
    while idx < s1.len() {
        if let Some(pos) = s1.find(&s2) {
            positions.push(Value::from_float(pos as Float));
            idx = pos + 1;
        } else {
            break;
        }
    }
    Ok(Value::from_array(positions))
}

fn lower(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "lower";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_lowercase()))
}

fn startswith(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "startswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.starts_with(&s2)))
}

fn upper(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "upper";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_uppercase()))
}

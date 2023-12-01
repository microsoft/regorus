// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
use regex::Regex;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("regex.is_valid", (is_valid, 1));
    m.insert("regex.match", (regex_match, 2));
    m.insert("regex.split", (regex_split, 2));
}

fn is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "regex.is_valid";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(ensure_string(name, &params[0], &args[0])
        .map_or(Value::Bool(false), |p| Value::Bool(Regex::new(&p).is_ok())))
}

pub fn regex_match(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "regex.match";
    ensure_args_count(span, name, params, args, 2)?;
    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let pattern = Regex::new(&pattern).or_else(|_| bail!(span.error("invalid regex")))?;
    Ok(Value::Bool(pattern.is_match(&value)))
}

pub fn regex_split(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "regex.split";
    ensure_args_count(span, name, params, args, 2)?;
    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let pattern = Regex::new(&pattern).or_else(|_| bail!(span.error("invalid regex")))?;
    Ok(Value::from_array(
        pattern
            .split(&value)
            .map(|s| Value::String(s.into()))
            .collect::<Vec<Value>>(),
    ))
}

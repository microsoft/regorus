// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins::utils::{ensure_args_count, ensure_set};
use crate::builtins::BuiltinFcn;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
use lazy_static::lazy_static;

#[cfg(feature = "regex")]
use crate::builtins::regex::regex_match;

#[rustfmt::skip]
lazy_static! {
    pub static ref DEPRECATED: HashMap<&'static str, BuiltinFcn> = {
	let mut m : HashMap<&'static str, BuiltinFcn>  = HashMap::new();
	
	m.insert("all", (all, 1));
	m.insert("any", (any, 1));
	m.insert("cast_array", (cast_array, 1));
	m.insert("cast_boolean", (cast_boolean, 1));
	m.insert("cast_null", (cast_null, 1));
	m.insert("cast_object", (cast_object, 1));
	m.insert("cast_set", (cast_set, 1));
	m.insert("cast_string", (cast_string, 1));
	m.insert("set_diff", (set_diff, 2));

	#[cfg(feature = "regex")]
	m.insert("re_match", (regex_match, 2));
	m
    };
}

fn all(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "all", params, args, 1)?;

    Ok(Value::Bool(match &args[0] {
        Value::Array(a) => a.iter().all(|i| i == &Value::Bool(true)),
        Value::Set(a) => a.iter().all(|i| i == &Value::Bool(true)),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`all` requires array/set argument. Got `{a}`.").as_str()))
        }
    }))
}

fn any(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "any", params, args, 1)?;

    Ok(Value::Bool(match &args[0] {
        Value::Array(a) => a.iter().any(|i| i == &Value::Bool(true)),
        Value::Set(a) => a.iter().any(|i| i == &Value::Bool(true)),
        a => {
            let span = params[0].span();
            bail!(span.error(format!("`any` requires array/set argument. Got `{a}`.").as_str()))
        }
    }))
}

fn set_diff(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "set_diff";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_set(name, &params[0], args[0].clone())?;
    let s2 = ensure_set(name, &params[1], args[1].clone())?;
    Ok(Value::from_set(s1.difference(&s2).cloned().collect()))
}

fn cast_array(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "cast_array";
    ensure_args_count(span, name, params, args, 1)?;
    match &args[0] {
        Value::Array(_) => Ok(args[0].clone()),
        Value::Set(s) => Ok(Value::from_array(s.iter().cloned().collect())),
        _ if strict => bail!(params[0].span().error("array required")),
        _ => Ok(Value::Undefined),
    }
}

fn cast_boolean(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "cast_boolean";
    ensure_args_count(span, name, params, args, 1)?;
    match &args[0] {
        Value::Bool(_) => Ok(args[0].clone()),
        _ if strict => bail!(params[0].span().error("boolean required")),
        _ => Ok(Value::Undefined),
    }
}

fn cast_null(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "cast_null";
    ensure_args_count(span, name, params, args, 1)?;
    match &args[0] {
        Value::Null => Ok(Value::Null),
        _ if strict => bail!(params[0].span().error("null required")),
        _ => Ok(Value::Undefined),
    }
}

fn cast_object(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "cast_object";
    ensure_args_count(span, name, params, args, 1)?;
    match &args[0] {
        Value::Object(_) => Ok(args[0].clone()),
        _ if strict => bail!(params[0].span().error("object required")),
        _ => Ok(Value::Undefined),
    }
}

fn cast_set(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "cast_set";
    ensure_args_count(span, name, params, args, 1)?;
    match &args[0] {
        Value::Set(_) => Ok(args[0].clone()),
        Value::Array(a) => Ok(Value::from_set(a.iter().cloned().collect())),
        _ if strict => bail!(params[0].span().error("set required")),
        _ => Ok(Value::Undefined),
    }
}

fn cast_string(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "cast_string";
    ensure_args_count(span, name, params, args, 1)?;
    match &args[0] {
        Value::String(_) => Ok(args[0].clone()),
        _ if strict => bail!(params[0].span().error("string required")),
        _ => Ok(Value::Undefined),
    }
}

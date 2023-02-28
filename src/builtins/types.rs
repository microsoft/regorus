// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::ensure_args_count;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("is_array", is_array);
    m.insert("is_boolean", is_boolean);
    m.insert("is_null", is_null);
    m.insert("is_number", is_number);
    m.insert("is_object", is_object);
    m.insert("is_set", is_set);
    m.insert("is_string", is_string);
    m.insert("type_name", type_name);
}

fn is_array(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_array", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::Array(_))))
}

fn is_boolean(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_boolean", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::Bool(_))))
}

fn is_null(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_null", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::Null)))
}

fn is_number(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_number", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::Number(_))))
}

fn is_object(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_object", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::Object(_))))
}

fn is_set(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_set", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::Set(_))))
}

fn is_string(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "is_string", params, args, 1)?;
    Ok(Value::Bool(matches!(&args[0], Value::String(_))))
}

pub fn get_type(value: &Value) -> &str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
        Value::Set(_) => "set",
        Value::Undefined => "undefined",
    }
}

pub fn type_name(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "type_name", params, args, 1)?;
    Ok(Value::String(get_type(&args[0]).to_string()))
}

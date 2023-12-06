// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{Context, Result};
use data_encoding::BASE64;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("base64.decode", (base64_decode, 1));
    m.insert("json.is_valid", (json_is_valid, 1));
    m.insert("json.marshal", (json_marshal, 1));
    m.insert("jsonunmarshal", (json_unmarshal, 1));

    #[cfg(feature = "yaml")]
    {
        m.insert("yaml.is_valid", (yaml_is_valid, 1));
        m.insert("yaml.marshal", (yaml_marshal, 1));
        m.insert("yaml.unmarshal", (yaml_unmarshal, 1));
    }
}

fn base64_decode(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "base64.decode";
    ensure_args_count(span, name, params, args, 1)?;

    let encoded_str = ensure_string(name, &params[0], &args[0])?;
    let decoded_bytes = BASE64.decode(encoded_str.as_bytes())?;
    Ok(Value::String(
        String::from_utf8_lossy(&decoded_bytes).into(),
    ))
}

#[cfg(feature = "yaml")]
fn yaml_is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "yaml.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let yaml_str = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::Bool(Value::from_yaml_str(&yaml_str).is_ok()))
}

#[cfg(feature = "yaml")]
fn yaml_marshal(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "yaml.marshal";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(Value::String(
        serde_yaml::to_string(&args[0])
            .with_context(|| span.error("could not serialize to yaml"))?
            .into(),
    ))
}

#[cfg(feature = "yaml")]
fn yaml_unmarshal(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "yaml.unmarshal";
    ensure_args_count(span, name, params, args, 1)?;
    let yaml_str = ensure_string(name, &params[0], &args[0])?;
    Value::from_yaml_str(&yaml_str).with_context(|| span.error("could not deserialize yaml."))
}

fn json_is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "json.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let json_str = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::Bool(Value::from_json_str(&json_str).is_ok()))
}

fn json_marshal(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "json.marshal";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(Value::String(
        serde_json::to_string(&args[0])
            .with_context(|| span.error("could not serialize to json"))?
            .into(),
    ))
}

fn json_unmarshal(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "json.unmarshal";
    ensure_args_count(span, name, params, args, 1)?;
    let json_str = ensure_string(name, &params[0], &args[0])?;
    Value::from_json_str(&json_str).with_context(|| span.error("could not deserialize json."))
}

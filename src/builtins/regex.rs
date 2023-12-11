// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
use regex::Regex;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert(
        "regex.find_all_string_submatch_n",
        (find_all_string_submatch_n, 3),
    );
    m.insert("regex.find_n", (find_n, 3));
    // TODO: m.insert("regex.globs_match", (globs_match, 2));
    m.insert("regex.is_valid", (is_valid, 1));
    m.insert("regex.match", (regex_match, 2));
    m.insert("regex.replace", (regex_replace, 3));
    m.insert("regex.split", (regex_split, 2));
    m.insert("regex.template_match", (regex_template_match, 4));
}

fn find_all_string_submatch_n(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.find_all_string_submatch_n";
    ensure_args_count(span, name, params, args, 3)?;

    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;
    let n = ensure_numeric(name, &params[2], &args[2])?;

    let pattern =
        Regex::new(&pattern).or_else(|_| bail!(params[0].span().error("invalid regex")))?;

    if !n.is_integer() {
        bail!(params[2].span().error("n must be an integer"));
    }

    let n = match n.as_i64() {
        Some(n) if n < 0 => usize::MAX,
        Some(n) => n as usize,
        None => usize::MAX,
    };

    Ok(Value::from_array(
        pattern
            .captures_iter(&value)
            .map(|capture| {
                Value::from_array(
                    capture
                        .iter()
                        .map(|group| {
                            Value::String(match group {
                                Some(s) => s.as_str().into(),
                                _ => "".into(),
                            })
                        })
                        .collect(),
                )
            })
            .take(n)
            .collect(),
    ))
}

fn find_n(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "regex.find_n";
    ensure_args_count(span, name, params, args, 3)?;

    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;
    let n = ensure_numeric(name, &params[2], &args[2])?;

    let pattern =
        Regex::new(&pattern).or_else(|_| bail!(params[0].span().error("invalid regex")))?;

    if !n.is_integer() {
        bail!(params[2].span().error("n must be an integer"));
    }

    let n = match n.as_i64() {
        Some(n) if n < 0 => usize::MAX,
        Some(n) => n as usize,
        None => usize::MAX,
    };

    Ok(Value::from_array(
        pattern
            .find_iter(&value)
            .map(|m| Value::String(m.as_str().into()))
            .take(n)
            .collect(),
    ))
}

fn is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "regex.is_valid";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(ensure_string(name, &params[0], &args[0])
        .map_or(Value::Bool(false), |p| Value::Bool(Regex::new(&p).is_ok())))
}

pub fn regex_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.match";
    ensure_args_count(span, name, params, args, 2)?;
    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let pattern =
        Regex::new(&pattern).or_else(|_| bail!(params[0].span().error("invalid regex")))?;
    Ok(Value::Bool(pattern.is_match(&value)))
}

fn regex_replace(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.replace";
    ensure_args_count(span, name, params, args, 3)?;

    let s = ensure_string(name, &params[0], &args[0])?;
    let pattern = ensure_string(name, &params[1], &args[1])?;
    let value = ensure_string(name, &params[2], &args[2])?;

    let pattern = match Regex::new(&pattern) {
        Ok(p) => p,
        // TODO: This behavior is due to OPA test not raising error. Should we raise error?
        _ => return Ok(Value::Undefined),
    };

    Ok(Value::String(
        pattern.replace_all(&s, value.as_ref()).into(),
    ))
}

fn regex_split(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "regex.split";
    ensure_args_count(span, name, params, args, 2)?;
    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let pattern =
        Regex::new(&pattern).or_else(|_| bail!(params[0].span().error("invalid regex")))?;
    Ok(Value::from_array(
        pattern
            .split(&value)
            .map(|s| Value::String(s.into()))
            .collect::<Vec<Value>>(),
    ))
}

fn regex_template_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.template_match";
    ensure_args_count(span, name, params, args, 4)?;
    let template = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;
    let delimiter_start = ensure_string(name, &params[2], &args[2])?;
    let delimiter_end = ensure_string(name, &params[3], &args[3])?;

    let delimiter_start = delimiter_start.as_ref();
    let delimiter_end = delimiter_end.as_ref();
    let mut template = template.as_ref();
    let mut value = value.as_ref();

    while let (Some(start), Some(end)) =
        (template.find(delimiter_start), template.find(delimiter_end))
    {
        if start >= end {
            return Ok(Value::Undefined);
        }
        // Match precesing literal (if any)
        if template[0..start] != value[0..start] {
            return Ok(Value::Bool(false));
        }

        // Fetch pattern, excluding delimiters.
        let pattern = Regex::new(&template[start + delimiter_start.len()..end])
            .or_else(|_| bail!(params[0].span().error("invalid regex")))?;

        // Skip preceding literal in value.
        value = &value[start..];

        let m = match pattern.find(value) {
            Some(m) if m.start() == 0 => m,
            _ => return Ok(Value::Bool(false)),
        };
        // Skip match in string.
        value = &value[m.len()..];

        // Skip regex and delimiter in template.
        template = &template[end + delimiter_end.len()..];
    }

    // Ensure that ending literal matches.
    Ok(Value::Bool(template == value))
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::{
    ensure_args_count, ensure_numeric, ensure_object, ensure_string, ensure_string_collection,
};
use crate::lexer::Span;
use crate::value::{Float, Value};

use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("concat", concat);
    m.insert("contains", contains);
    m.insert("endswith", endswith);
    m.insert("format_int", format_int);
    m.insert("indexof", indexof);
    m.insert("indexof_n", indexof_n);
    m.insert("lower", lower);
    m.insert("replace", replace);
    m.insert("split", split);
    //    m.insert("sprintf", sprintf);
    m.insert("startswith", startswith);
    m.insert("strings.any_prefix_match", any_prefix_match);
    m.insert("strings.any_suffix_match", any_suffix_match);
    m.insert("strings.replace_n", replace_n);
    m.insert("strings.reverse", reverse);
    m.insert("strings.substring", substring);
    m.insert("trim", trim);
    m.insert("trim_left", trim_left);
    m.insert("trim_prefix", trim_prefix);
    m.insert("trim_right", trim_right);
    m.insert("trim_space", trim_space);
    m.insert("trim_suffix", trim_suffix);
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

fn format_int(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "endswith";
    ensure_args_count(span, name, params, args, 2)?;
    let mut n = ensure_numeric(name, &params[0], &args[0])?;
    let mut sign = "";
    if n < 0.0 {
        n = n.abs();
        sign = "-";
    }
    let n = n.floor() as u64;

    Ok(Value::String(
        sign.to_owned()
            + &match ensure_numeric(name, &params[1], &args[1])? as u64 {
                2 => format!("{:b}", n),
                8 => format!("{:o}", n),
                10 => format!("{}", n),
                16 => format!("{:x}", n),
                _ => return Ok(Value::Undefined),
            },
    ))
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

fn replace(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "replace";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let old = ensure_string(name, &params[1], &args[1])?;
    let new = ensure_string(name, &params[2], &args[2])?;
    Ok(Value::String(s.replace(&old, &new)))
}

fn split(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "replace";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let delimiter = ensure_string(name, &params[1], &args[1])?;

    Ok(Value::from_array(
        s.split(&delimiter)
            .map(|s| Value::String(s.to_string()))
            .collect(),
    ))
}

fn any_prefix_match(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "strings.any_prefix_match";
    ensure_args_count(span, name, params, args, 2)?;

    let search = match &args[0] {
        Value::String(s) => vec![s.as_str()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[0], &args[0])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    let base = match &args[1] {
        Value::String(s) => vec![s.as_str()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[1], &args[1])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    Ok(Value::Bool(
        search.iter().any(|s| base.iter().any(|b| s.starts_with(b))),
    ))
}

fn any_suffix_match(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "strings.any_suffix_match";
    ensure_args_count(span, name, params, args, 2)?;

    let search = match &args[0] {
        Value::String(s) => vec![s.as_str()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[0], &args[0])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    let base = match &args[1] {
        Value::String(s) => vec![s.as_str()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[1], &args[1])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    Ok(Value::Bool(
        search.iter().any(|s| base.iter().any(|b| s.ends_with(b))),
    ))
}

fn startswith(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "startswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.starts_with(&s2)))
}

fn replace_n(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim";
    ensure_args_count(span, name, params, args, 2)?;
    let obj = ensure_object(name, &params[0], args[0].clone())?;
    let mut s = ensure_string(name, &params[1], &args[1])?;

    let span = params[0].span();
    for item in obj.as_ref().iter() {
        match item {
            (Value::String(k), Value::String(v)) => {
                s = s.replace(k, v);
            }
            _ => {
                bail!(span.error(
                    format!("`{name}` expects string keys and values in pattern object.").as_str()
                ))
            }
        }
    }

    Ok(Value::String(s))
}

fn reverse(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "reverse";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.chars().rev().collect()))
}

fn substring(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "substring";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let offset = ensure_numeric(name, &params[1], &args[1])?;
    let length = ensure_numeric(name, &params[2], &args[2])?;

    if offset.floor() != offset || length.floor() != length {
        return Ok(Value::Undefined);
    }

    if offset < 0.0 || length < 0.0 {
        return Ok(Value::Undefined);
    }

    let offset = offset as usize;
    let length = length as usize;

    // TODO: distinguish between 20.0 and 20
    // Also: behavior of
    // x = substring("hello", 20 + 0.0, 25)
    if offset > s.len() || length <= offset {
        return Ok(Value::String("".to_string()));
    }

    Ok(Value::String(s[offset..offset + length].to_string()))
}

fn trim(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_matches(|c| s2.contains(c)).to_string(),
    ))
}

fn trim_left(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim_left";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_start_matches(|c| s2.contains(c)).to_string(),
    ))
}

fn trim_prefix(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim_prefix";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(match s1.strip_prefix(&s2) {
        Some(s) => s.to_string(),
        _ => s1,
    }))
}

fn trim_right(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim_right";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_end_matches(|c| s2.contains(c)).to_string(),
    ))
}

fn trim_space(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim_space";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.trim().to_string()))
}

fn trim_suffix(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "trim_suffix";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(match s1.strip_suffix(&s2) {
        Some(s) => s.to_string(),
        _ => s1,
    }))
}

fn upper(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "upper";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_uppercase()))
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use semver::Version;

use std::cmp::Ordering;
use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("semver.compare", (compare, 2));
    m.insert("semver.is_valid", (is_valid, 1));
}

fn compare(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "semver.compare";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_string(name, &params[0], &args[0])?;
    let v2 = ensure_string(name, &params[1], &args[1])?;
    let version1 = Version::parse(&v1)?;
    let version2 = Version::parse(&v2)?;
    let result = match version1.cmp_precedence(&version2) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    Ok(Value::from(result as i64))
}

fn is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "semver.is_valid";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(Value::Bool(
        Version::parse(&if strict {
            ensure_string(name, &params[0], &args[0])?
        } else {
            match &args[0] {
                Value::String(s) => s.clone(),
                _ => return Ok(Value::Bool(false)),
            }
        })
        .is_ok(),
    ))
}

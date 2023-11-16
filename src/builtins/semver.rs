// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use semver::Version;

use std::cmp::Ordering;
use std::collections::HashMap;

use anyhow::{Ok, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("semver.compare", (compare, 2));
    m.insert("semver.is_valid", (is_valid, 1));
}

fn compare(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "semver.compare";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_string(name, &params[0], &args[0])?;
    let v2 = ensure_string(name, &params[1], &args[1])?;

    // TODO: Implement function as described at
    // https://www.openpolicyagent.org/docs/latest/policy-reference/#semver
    let version1 = Version::parse(&v1)?;
    let version2 = Version::parse(&v2)?;

    let result = match version1.cmp_precedence(&version2) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };

    Ok(Value::from_float(result as f64))
}

fn is_valid(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "semver.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let v = ensure_string(name, &params[0], &args[0])?;

    // TODO: Implement function as described at
    // https://www.openpolicyagent.org/docs/latest/policy-reference/#semver

    Ok(Value::Bool(Version::parse(&v).is_ok()))
}

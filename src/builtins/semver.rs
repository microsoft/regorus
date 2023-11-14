// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("semver.compare", (compare, 2));
    m.insert("semver.is_valid", (is_valid, 1));
}

fn compare(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "semver.compare";
    ensure_args_count(span, name, params, args, 2)?;

    let _v1 = ensure_string(name, &params[0], &args[0])?;
    let _v2 = ensure_string(name, &params[1], &args[1])?;

    // TODO: Implement function as described at
    // https://www.openpolicyagent.org/docs/latest/policy-reference/#semver

    bail!(span.error(format!("{name} is not implemented").as_str()))
}

fn is_valid(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "semver.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let _v = ensure_string(name, &params[0], &args[0])?;

    // TODO: Implement function as described at
    // https://www.openpolicyagent.org/docs/latest/policy-reference/#semver

    bail!(span.error(format!("{name} is not implemented").as_str()))
}

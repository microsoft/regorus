// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::value::Value;

use std::collections::BTreeSet;
use std::rc::Rc;

use anyhow::{bail, Result};

fn ensure_set(fcn: &str, arg: &Expr, v: Value) -> Result<Rc<BTreeSet<Value>>> {
    Ok(match v {
        Value::Set(s) => s,
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects set argument. Got `{v}` instead").as_str()))
        }
    })
}

pub fn difference(expr1: &Expr, expr2: &Expr, v1: Value, v2: Value) -> Result<Value> {
    let s1 = ensure_set("difference", expr1, v1)?;
    let s2 = ensure_set("difference", expr2, v2)?;
    Ok(Value::from_set(s1.difference(&s2).cloned().collect()))
}

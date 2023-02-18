// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::lexer::Span;
use crate::value::{Float, Value};

use std::collections::BTreeSet;
use std::rc::Rc;

use anyhow::{bail, Result};

pub fn ensure_args_count(
    span: &Span,
    fcn: &'static str,
    params: &[Expr],
    args: &[Value],
    expected: usize,
) -> Result<()> {
    if args.len() != expected {
        let span = match args.len() > expected {
            false => span,
            true => params[args.len() - 1].span(),
        };
        if expected == 1 {
            bail!(span.error(format!("`{fcn}` expects 1 argument").as_str()))
        } else {
            bail!(span.error(format!("`{fcn}` expects {expected} arguments").as_str()))
        }
    }
    Ok(())
}

pub fn ensure_numeric(fcn: &str, arg: &Expr, v: &Value) -> Result<Float> {
    Ok(match &v {
        Value::Number(n) => n.0 .0,
        _ => {
            let span = arg.span();
            bail!(
                span.error(format!("`{fcn}` expects numeric argument. Got `{v}` instead").as_str())
            )
        }
    })
}

pub fn ensure_string(fcn: &str, arg: &Expr, v: &Value) -> Result<String> {
    Ok(match &v {
        Value::String(s) => s.clone(),
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects string argument. Got `{v}` instead").as_str()))
        }
    })
}

pub fn ensure_set(fcn: &str, arg: &Expr, v: Value) -> Result<Rc<BTreeSet<Value>>> {
    Ok(match v {
        Value::Set(s) => s,
        _ => {
            let span = arg.span();
            bail!(span.error(format!("`{fcn}` expects set argument. Got `{v}` instead").as_str()))
        }
    })
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins::utils::ensure_args_count;
use crate::builtins::BuiltinFcn;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
use lazy_static::lazy_static;

#[rustfmt::skip]
lazy_static! {
    pub static ref DEPRECATED: HashMap<&'static str, BuiltinFcn> = {
	let mut m : HashMap<&'static str, BuiltinFcn>  = HashMap::new();
	
	m.insert("all", (all, 1));
	m.insert("any", (any, 1));	
	
	m
    };
}

fn all(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
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

fn any(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
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

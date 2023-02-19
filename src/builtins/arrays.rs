// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_array};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;
use std::rc::Rc;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("array.concat", concat);
    m.insert("array.reverse", reverse);
}

fn concat(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "array.concat";
    ensure_args_count(span, name, params, args, 2)?;
    let mut v1 = ensure_array(name, &params[0], args[0].clone())?;
    let mut v2 = ensure_array(name, &params[1], args[1].clone())?;

    Rc::make_mut(&mut v1).append(Rc::make_mut(&mut v2));
    Ok(Value::Array(v1))
}

fn reverse(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "array.reverse";
    ensure_args_count(span, name, params, args, 2)?;

    let mut v1 = ensure_array(name, &params[0], args[0].clone())?;
    Rc::make_mut(&mut v1).reverse();
    Ok(Value::Array(v1))
}

/*
fn slice(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
*/

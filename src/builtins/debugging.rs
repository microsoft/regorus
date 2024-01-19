// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};

// TODO: Should we avoid this limit?
const MAX_ARGS: u8 = std::u8::MAX;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("print", (print, MAX_ARGS));
}

// Symbol analyzer must ensure that vars used by print are defined before
// the print statement. Scheduler must ensure the above constraint.
// Additionally interpreter must allow undefined inputs to print.
fn print(span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    if args.len() > MAX_ARGS as usize {
        bail!(span.error("print supports up to 100 arguments"));
    }

    let mut msg = String::default();
    for a in args {
        match a {
            Value::Undefined => msg += " <undefined>",
            Value::String(s) => msg += &format!(" {s}"),
            _ => msg += &format!(" {a}"),
        };
    }

    if !msg.is_empty() {
        println!("{}", &msg[1..]);
    }
    Ok(Value::Bool(true))
}

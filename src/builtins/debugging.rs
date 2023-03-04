// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("print", print);
}

// Symbol analyzer must ensure that vars used by print are defined before
// the print statement. Scheduler must ensure the above constraint.
// Additionally interpreter must allow undefined inputs to print.
fn print(span: &Span, _params: &[Expr], args: &[Value]) -> Result<Value> {
    let mut msg = String::default();
    for a in args {
        match a {
            Value::Undefined => msg += "<undefined>",
            _ => msg += format!("{a}").as_str(),
        };
    }

    span.message("print", msg.as_str());
    Ok(Value::Bool(true))
}

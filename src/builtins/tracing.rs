// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("trace", (trace, 1));
}

// Symbol analyzer must ensure that vars used by trace are defined before
// the trace statement. Scheduler must ensure the above constraint.
fn trace(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trace";
    ensure_args_count(span, name, params, args, 1)?;
    let msg = ensure_string(name, &params[0], &args[0])?;

    // Unlike rego, trace returns a string instead of bool.
    // The interpreter accumulates the traces.
    // TODO: Stateful bultins can pass in a state that would allow capturing
    // the traces in the state.
    Ok(Value::String(msg))
}

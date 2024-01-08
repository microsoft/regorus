// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::time;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;
use std::thread;

use anyhow::{Ok, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("test.sleep", (sleep, 1));
}

fn sleep(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "test.sleep";
    ensure_args_count(span, name, params, args, 1)?;

    let val = ensure_string(name, &params[0], &args[0])?;
    let dur = time::compat::parse_duration(val.as_ref())?;

    thread::sleep(dur.to_std()?);

    Ok(Value::Null)
}

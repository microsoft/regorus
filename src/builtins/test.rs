// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::indexing_slicing)]

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::time;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;
use crate::*;

use std::thread;

use anyhow::{Ok, Result};

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("test.sleep", (sleep, 1));
}

fn sleep(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "test.sleep";
    ensure_args_count(span, name, params, args, 1)?;

    let val = ensure_string(name, &params[0], &args[0])?;
    let dur = time::compat::parse_duration(val.as_ref())
        .map_err(|e| params[0].span().error(&format!("{e}")))?;

    let std_dur = dur
        .to_std()
        .map_err(|err| anyhow::anyhow!("Failed to convert to std::time::Duration: {err}"))?;

    thread::sleep(std_dur);

    Ok(Value::Null)
}

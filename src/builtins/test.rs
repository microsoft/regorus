// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;
use std::thread;
use std::time::Duration;

use anyhow::{bail, Ok, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("test.sleep", (sleep, 1));
}

fn sleep(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "test.sleep";
    ensure_args_count(span, name, params, args, 1)?;

    let val = ensure_string(name, &params[0], &args[0])?;

    let duration = if let Some(millis) = val.strip_suffix("ms").and_then(|v| v.parse().ok()) {
        Duration::from_millis(millis)
    } else if let Some(secs) = val.strip_suffix("s").and_then(|v| v.parse().ok()) {
        Duration::from_secs(secs)
    } else {
        bail!(params[0].span().error(
            format!("`{name}` expects a simple duration ends with `ms` or `s`. Got {val} instead")
                .as_str()
        ))
    };

    thread::sleep(duration);

    Ok(Value::Null)
}

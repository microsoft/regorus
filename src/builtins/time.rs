// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::ensure_args_count;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;
use std::time::SystemTime;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("time.now_ns", (now_ns, 0));
}

fn now_ns(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "time.now_ns";
    ensure_args_count(span, name, params, args, 0)?;

    let now = SystemTime::now();
    let elapsed = match now.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(e) => e,
        Err(e) => bail!(span.error(format!("could not fetch elapsed time. {e}").as_str())),
    };
    let nanos = elapsed.as_nanos();
    Ok(Value::from(nanos))
}

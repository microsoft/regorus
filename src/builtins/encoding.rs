// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;
use data_encoding::BASE64;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("base64.decode", (base64_decode, 1));
}

fn base64_decode(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "base64.decode";
    ensure_args_count(span, name, params, args, 1)?;

    let encoded_str = ensure_string(name, &params[0], &args[0])?;
    let decoded_bytes = BASE64.decode(encoded_str.as_bytes())?;
    Ok(Value::String(
        String::from_utf8_lossy(&decoded_bytes).to_string(),
    ))
}

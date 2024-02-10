// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};

use crate::lexer::Span;
use crate::value::Value;

use itertools::Itertools;
use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("io.jwt.decode", (jwt_decode, 1));
    m.insert("io.jwt.decode_verify", (jwt_decode_verify, 2));
}

fn decode(span: &Span, jwt: String, strict: bool) -> Result<Value> {
    let Some((Ok(header), Ok(payload), Ok(signature))) = jwt
        .split('.')
        .map(|p| data_encoding::BASE64URL_NOPAD.decode(p.as_bytes()))
        .collect_tuple()
    else {
        if strict {
            bail!(span.error("invalid jwt token"));
        }
        return Ok(Value::Undefined);
    };

    let header = String::from_utf8_lossy(&header).to_string();
    let payload = String::from_utf8_lossy(&payload).to_string();
    let signature = data_encoding::HEXLOWER_PERMISSIVE.encode(&signature);

    let signature = Value::String(signature.into());
    let header = Value::from_json_str(&header)?;

    if header["enc"] != Value::Undefined {
        bail!(span.error("JWT is a JWE object, which is not supported"));
    }

    if header["cty"] == "JWT".into() {
        if payload.len() <= 2 || !payload.starts_with('"') || !payload.ends_with('"') {
            bail!(span.error("invalid nested JWT"));
        }
        // Ignore ""
        decode(span, payload[1..payload.len() - 1].to_string(), strict)
    } else {
        let payload = Value::from_json_str(&payload)?;
        Ok(Value::from_array([header, payload, signature].into()))
    }
}

fn jwt_decode(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "io.jwt.decode";
    ensure_args_count(span, name, params, args, 1)?;
    let jwt = ensure_string(name, &params[0], &args[0])?;

    decode(span, jwt.to_string(), strict) //header, payload, signature, strict)
}

fn jwt_decode_verify(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "io.jwt.decode_verify";
    ensure_args_count(span, name, params, args, 2)?;
    Ok(Value::Undefined)
}

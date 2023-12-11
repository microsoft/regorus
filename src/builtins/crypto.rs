// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
use constant_time_eq::constant_time_eq;
use hmac::{Hmac, Mac};
use md5::{Digest, Md5};
use sha1::Sha1;
use sha2::{Sha256, Sha512};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("crypto.hmac.equal", (hmac_equal_fixed_time, 2));
    m.insert("crypto.hmac.md5", (hmac_md5, 2));
    m.insert("crypto.hmac.sha1", (hmac_sha1, 2));
    m.insert("crypto.hmac.sha256", (hmac_sha256, 2));
    m.insert("crypto.hmac.sha512", (hmac_sha512, 2));

    m.insert("crypto.md5", (crypto_md5, 1));
    m.insert("crypto.sha1", (crypto_sha1, 1));
    m.insert("crypto.sha256", (crypto_sha256, 1));
}

fn hmac_equal_fixed_time(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "crypto.hmac.equal";
    ensure_args_count(span, name, params, args, 2)?;

    let hmac1 = ensure_string(name, &params[0], &args[0])?;
    let hmac2 = ensure_string(name, &params[1], &args[1])?;

    Ok(Value::Bool(constant_time_eq(
        hmac1.as_bytes(),
        hmac2.as_bytes(),
    )))
}

fn hmac_md5(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "crypto.hmac.md5";
    ensure_args_count(span, name, params, args, 2)?;

    let x = ensure_string(name, &params[0], &args[0])?;
    let key = ensure_string(name, &params[1], &args[1])?;

    let mut hmac = Hmac::<Md5>::new_from_slice(key.as_bytes())
        .or_else(|_| bail!(span.error("failed to create hmac instance")))?;

    hmac.update(x.as_bytes());
    let result = hmac.finalize();

    Ok(Value::String(hex::encode(result.into_bytes()).into()))
}

fn hmac_sha1(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "crypto.hmac.sha1";
    ensure_args_count(span, name, params, args, 2)?;

    let x = ensure_string(name, &params[0], &args[0])?;
    let key = ensure_string(name, &params[1], &args[1])?;

    let mut hmac = Hmac::<Sha1>::new_from_slice(key.as_bytes())
        .or_else(|_| bail!(span.error("failed to create hmac instance")))?;

    hmac.update(x.as_bytes());
    let result = hmac.finalize();

    Ok(Value::String(hex::encode(result.into_bytes()).into()))
}

fn hmac_sha256(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "crypto.hmac.sha256";
    ensure_args_count(span, name, params, args, 2)?;

    let x = ensure_string(name, &params[0], &args[0])?;
    let key = ensure_string(name, &params[1], &args[1])?;

    let mut hmac = Hmac::<Sha256>::new_from_slice(key.as_bytes())
        .or_else(|_| bail!(span.error("failed to create hmac instance")))?;

    hmac.update(x.as_bytes());
    let result = hmac.finalize();

    Ok(Value::String(hex::encode(result.into_bytes()).into()))
}

fn hmac_sha512(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "crypto.hmac.sha512";
    ensure_args_count(span, name, params, args, 2)?;

    let x = ensure_string(name, &params[0], &args[0])?;
    let key = ensure_string(name, &params[1], &args[1])?;

    let mut hmac = Hmac::<Sha512>::new_from_slice(key.as_bytes())
        .or_else(|_| bail!(span.error("failed to create hmac instance")))?;

    hmac.update(x.as_bytes());
    let result = hmac.finalize();

    Ok(Value::String(hex::encode(result.into_bytes()).into()))
}

fn crypto_md5(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "crypto.md5";
    ensure_args_count(span, name, params, args, 1)?;

    let x = ensure_string(name, &params[0], &args[0])?;

    let mut h = Md5::new();

    h.update(x.as_bytes());
    let result = h.finalize();

    Ok(Value::String(hex::encode(result).into()))
}

fn crypto_sha1(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "crypto.sha1";
    ensure_args_count(span, name, params, args, 1)?;

    let x = ensure_string(name, &params[0], &args[0])?;

    let mut h = Sha1::new();

    h.update(x.as_bytes());
    let result = h.finalize();

    Ok(Value::String(hex::encode(result).into()))
}

fn crypto_sha256(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "crypto.sha256";
    ensure_args_count(span, name, params, args, 1)?;

    let x = ensure_string(name, &params[0], &args[0])?;

    let mut h = Sha256::new();

    h.update(x.as_bytes());
    let result = h.finalize();

    Ok(Value::String(hex::encode(result).into()))
}

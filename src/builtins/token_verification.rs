// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::jwt::backend::Backend as _;
use crate::builtins::jwt::toolkit::JwtBackend;
use crate::builtins::jwt::utils::split_token;
use crate::builtins::utils::{ensure_args_count, ensure_object, ensure_string};
use crate::lexer::Span;
use crate::value::Value;
use alloc::collections::{BTreeMap, BTreeSet};

use chrono::Utc;

use crate::*;

use anyhow::{anyhow, Result};
use lazy_static::lazy_static;

lazy_static! {
    static ref ALLOWED_HEADER_KEYS: BTreeSet<Value> = {
        let mut set = BTreeSet::new();
        set.insert(Value::from("alg"));
        set.insert(Value::from("typ"));
        set.insert(Value::from("kid"));
        set.insert(Value::from("cty"));
        set
    };
    static ref KEY_TYP: Value = Value::from("typ");
    static ref KEY_ALG: Value = Value::from("alg");
    static ref KEY_ENC: Value = Value::from("enc");
    static ref KEY_CTY: Value = Value::from("cty");
    static ref KEY_AUD: Value = Value::from("aud");
    static ref KEY_ISS: Value = Value::from("iss");
    static ref KEY_EXP: Value = Value::from("exp");
    static ref KEY_NBF: Value = Value::from("nbf");
    static ref KEY_TIME: Value = Value::from("time");
    static ref KEY_CERT: Value = Value::from("cert");
    static ref KEY_SECRET: Value = Value::from("secret");
}

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("io.jwt.verify_hs256", (verify_hs256, 2));
    m.insert("io.jwt.verify_hs384", (verify_hs384, 2));
    m.insert("io.jwt.verify_hs512", (verify_hs512, 2));
    m.insert("io.jwt.verify_rs256", (verify_rs256, 2));
    m.insert("io.jwt.verify_rs384", (verify_rs384, 2));
    m.insert("io.jwt.verify_rs512", (verify_rs512, 2));
    m.insert("io.jwt.verify_ps256", (verify_ps256, 2));
    m.insert("io.jwt.verify_ps384", (verify_ps384, 2));
    m.insert("io.jwt.verify_ps512", (verify_ps512, 2));
    m.insert("io.jwt.verify_es256", (verify_es256, 2));
    m.insert("io.jwt.verify_es384", (verify_es384, 2));
    m.insert("io.jwt.verify_es512", (verify_es512, 2));
    m.insert("io.jwt.decode", (decode, 1));
    m.insert("io.jwt.decode_verify", (decode_verify, 2));
}

type VerifyImpl = fn(&str, &str) -> Result<bool>;

/// General wrapper for every Backend::verify_xxxxx function
fn verify_wrapper(
    buildin_name: &'static str,
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    verify_impl: VerifyImpl,
) -> Result<Value> {
    ensure_args_count(span, buildin_name, params, args, 2)?;
    let token = ensure_string(buildin_name, &params[0], &args[0])?;
    let secret = ensure_string(buildin_name, &params[1], &args[1])?;
    let verification_result = verify_impl(&token, &secret)?;

    Ok(Value::Bool(verification_result))
}

fn verify_hs256(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_hs256",
        span,
        params,
        args,
        JwtBackend::verify_hs256,
    )
}

fn verify_hs384(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_hs384",
        span,
        params,
        args,
        JwtBackend::verify_hs384,
    )
}

fn verify_hs512(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_hs512",
        span,
        params,
        args,
        JwtBackend::verify_hs512,
    )
}

fn verify_rs256(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_rs256",
        span,
        params,
        args,
        JwtBackend::verify_rs256,
    )
}

fn verify_rs384(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_rs384",
        span,
        params,
        args,
        JwtBackend::verify_rs384,
    )
}

fn verify_rs512(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_rs512",
        span,
        params,
        args,
        JwtBackend::verify_rs512,
    )
}

fn verify_ps256(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_ps256",
        span,
        params,
        args,
        JwtBackend::verify_ps256,
    )
}

fn verify_ps384(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_ps384",
        span,
        params,
        args,
        JwtBackend::verify_ps384,
    )
}

fn verify_ps512(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_ps512",
        span,
        params,
        args,
        JwtBackend::verify_ps512,
    )
}

fn verify_es256(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_es256",
        span,
        params,
        args,
        JwtBackend::verify_es256,
    )
}

fn verify_es384(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_es384",
        span,
        params,
        args,
        JwtBackend::verify_es384,
    )
}

fn verify_es512(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    verify_wrapper(
        "io.jwt.verify_es512",
        span,
        params,
        args,
        JwtBackend::verify_es512,
    )
}

fn decode(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let buildin_name = "io.jwt.decode";
    ensure_args_count(span, buildin_name, params, args, 1)?;

    let token = ensure_string(buildin_name, &params[0], &args[0])?;

    let (header, payload, signature) = decode_impl(&token)?;
    let result = vec![
        Value::Object(header),
        Value::Object(payload),
        Value::from(signature),
    ];

    Ok(Value::from_array(result))
}

fn decode_verify(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let buildin_name = "io.jwt.decode_verify";
    ensure_args_count(span, buildin_name, params, args, 2)?;

    let token = ensure_string(buildin_name, &params[0], &args[0])?;
    let constraints = ensure_object(buildin_name, &params[1], args[1].clone())?;

    match decode_verify_impl(&token, &constraints) {
        Ok((header, payload)) => Ok(Value::from_array(vec![
            Value::Bool(true),
            Value::Object(header),
            Value::Object(payload),
        ])),
        Err(_) => Ok(Value::from_array(vec![
            Value::Bool(false),
            Value::new_object(),
            Value::new_object(),
        ])),
    }
}

type Object = Rc<BTreeMap<Value, Value>>;

fn get_value<'a>(obj: &'a Object, key: &'a Value) -> Result<&'a Value> {
    obj.get(key).ok_or_else(|| anyhow!("Value not found"))
}

fn verify_header(header: &Object) -> Result<()> {
    if !header.iter().all(|(k, _)| ALLOWED_HEADER_KEYS.contains(k)) {
        return Err(anyhow!("Failed to verify JWT header"));
    }
    Ok(())
}

fn verify_type(header: &Object) -> Result<()> {
    let typ = get_value(header, &KEY_TYP)?.as_string()?;
    if typ.as_ref() == "JWT" {
        return Ok(());
    }
    Err(anyhow!("Non JWT tokens not supported"))
}

fn verify_algorithm(header: &Object, constraints: &Object) -> Result<()> {
    if let Some(expected_val) = constraints.get(&KEY_ALG) {
        let expected_alg = expected_val.as_string()?;
        let alg = get_value(header, &KEY_ALG)?.as_string()?;
        if alg != expected_alg {
            return Err(anyhow!("Failed to verify algorithm"));
        }
    }
    Ok(())
}

fn verify_audience(payload: &Object, constraints: &Object) -> Result<()> {
    if let Some(expected_val) = constraints.get(&KEY_AUD) {
        let expected_aud = expected_val.as_string()?;
        let val = get_value(payload, &KEY_AUD)?;
        match *val {
            Value::String(ref aud) => {
                if aud != expected_aud {
                    return Err(anyhow!("Failed to verify audience"));
                }
            }
            Value::Array(ref aud) => {
                if !aud.contains(&Value::String(expected_aud.clone())) {
                    return Err(anyhow!("Failed to verify audience"));
                }
            }
            _ => {
                return Err(anyhow!("Failed to verify audience"));
            }
        }
    } else if payload.contains_key(&KEY_AUD) {
        return Err(anyhow!("Failed to verify audience"));
    }
    Ok(())
}

fn verify_issuer(payload: &Object, constraints: &Object) -> Result<()> {
    if let Some(val) = constraints.get(&KEY_ISS) {
        let expected_iss = val.as_string()?;
        let iss = get_value(payload, &KEY_ISS)?.as_string()?;
        if iss != expected_iss {
            return Err(anyhow!("Failed to verify issuer"));
        }
    }
    Ok(())
}

fn verify_time(payload: &Object, constraints: &Object) -> Result<()> {
    if let Some(time_val) = constraints.get(&KEY_TIME) {
        let time = time_val.as_number()?;
        if let Some(exp_val) = payload.get(&KEY_EXP) {
            // Convert sec to nanosec
            let exp_ns = exp_val
                .as_number()?
                .mul(&number::Number::from(1_000_000_000.))?;
            if time >= &exp_ns {
                return Err(anyhow!("Failed to verify time"));
            }
        }

        if let Some(nbf_val) = payload.get(&KEY_NBF) {
            // Convert sec to nanosec
            let nbf_ns = nbf_val
                .as_number()?
                .mul(&number::Number::from(1_000_000_000.))?;
            if time < &nbf_ns {
                return Err(anyhow!("Failed to verify time"));
            }
        }
    } else {
        let now = number::Number::from(Utc::now().timestamp());
        if let Some(exp_val) = payload.get(&KEY_EXP) {
            if &now > exp_val.as_number()? {
                return Err(anyhow!("Failed to verify time"));
            }
        }
        if let Some(nbf_val) = payload.get(&KEY_NBF) {
            if &now < nbf_val.as_number()? {
                return Err(anyhow!("Failed to verify time"));
            }
        }
    }
    Ok(())
}

fn verify_hmac(token: &str, constraints: &Object, verify_impl: VerifyImpl) -> Result<bool> {
    let secret = get_value(constraints, &KEY_SECRET)?.as_string()?;
    verify_impl(token, secret)
}

fn verify_rsa(token: &str, constraints: &Object, verify_impl: VerifyImpl) -> Result<bool> {
    let cert = get_value(constraints, &KEY_CERT)?.as_string()?;
    // cert may contain multiple keys
    if let Ok(json_val) = serde_json::from_str::<serde_json::Value>(cert) {
        if let Some(keys) = json_val.get("keys").and_then(|k| k.as_array()) {
            for key in keys {
                if let Ok(key_json) = serde_json::to_string(key) {
                    if let Ok(result) = verify_impl(token, &key_json) {
                        if result {
                            return Ok(result);
                        }
                    }
                }
            }
        }
        return Err(anyhow!("Failed to verify RSA"));
    }
    verify_impl(token, cert)
}

fn decode_verify_impl(token: &str, constraints: &Object) -> Result<(Object, Object)> {
    let (header, payload, _) = decode_impl(token)?;

    verify_header(&header)?;
    verify_type(&header)?;
    verify_algorithm(&header, constraints)?;
    verify_audience(&payload, constraints)?;
    verify_issuer(&payload, constraints)?;
    verify_time(&payload, constraints)?;

    let alg = get_value(&header, &KEY_ALG)?.as_string()?;
    let result = match alg.as_ref() {
        "HS256" => verify_hmac(token, constraints, JwtBackend::verify_hs256)?,
        "HS384" => verify_hmac(token, constraints, JwtBackend::verify_hs384)?,
        "HS512" => verify_hmac(token, constraints, JwtBackend::verify_hs512)?,
        "RS256" => verify_rsa(token, constraints, JwtBackend::verify_rs256)?,
        "RS384" => verify_rsa(token, constraints, JwtBackend::verify_rs384)?,
        "RS512" => verify_rsa(token, constraints, JwtBackend::verify_rs512)?,
        "PS256" => verify_rsa(token, constraints, JwtBackend::verify_ps256)?,
        "PS384" => verify_rsa(token, constraints, JwtBackend::verify_ps384)?,
        "PS512" => verify_rsa(token, constraints, JwtBackend::verify_ps512)?,
        "ES256" => verify_rsa(token, constraints, JwtBackend::verify_es256)?,
        "ES384" => verify_rsa(token, constraints, JwtBackend::verify_es384)?,
        "ES512" => verify_rsa(token, constraints, JwtBackend::verify_es512)?,
        _ => return Err(anyhow!("Unknown algorithm")),
    };

    if !result {
        return Err(anyhow!("Failed to verify JWT"));
    }

    Ok((header, payload))
}

fn decode_impl(token: &str) -> Result<(Object, Object, String)> {
    let (header, payload, signature) = split_token(token)?;

    let header = Value::from_json_str(core::str::from_utf8(&JwtBackend::decode_base64url(
        header,
    )?)?)?;

    if let Value::Object(ref header_data) = header {
        // Restrict JWE support
        if header_data.contains_key(&KEY_ENC) {
            return Err(anyhow!("JWE not supported"));
        }

        // Support nested JWT
        if let Some(value) = header_data.get(&KEY_CTY) {
            if value.as_string()?.as_ref() == "JWT" {
                let decoded_payload = JwtBackend::decode_base64url(payload)?;
                let payload_str = core::str::from_utf8(&decoded_payload)?;

                // Trim the first and the last chars if they are quotes: ""
                let trimmed_payload = if payload_str.starts_with('"') && payload_str.ends_with('"')
                {
                    &payload_str[1..payload_str.len() - 1]
                } else {
                    payload_str
                };
                return decode_impl(trimmed_payload);
            }
        }
    }

    let payload = Value::from_json_str(core::str::from_utf8(&JwtBackend::decode_base64url(
        payload,
    )?)?)?;

    let hex_sign: String = JwtBackend::decode_base64url(signature)?
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect::<Vec<String>>()
        .join("");

    if let Value::Object(header_data) = header {
        if let Value::Object(payload_data) = payload {
            return Ok((header_data, payload_data, hex_sign));
        }
    }

    Err(anyhow!("Failed to decode JWT"))
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template encoding builtins: base64, base64ToString, base64ToJson,
//! uri, uriComponent, uriComponentToString, dataUri, dataUriToString.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use anyhow::Result;

use super::helpers::as_str;

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.base64", (fn_base64, 1));
    m.insert("azure.policy.fn.base64_to_string", (fn_base64_to_string, 1));
    m.insert("azure.policy.fn.base64_to_json", (fn_base64_to_json, 1));
    m.insert("azure.policy.fn.uri", (fn_uri, 2));
    m.insert("azure.policy.fn.uri_component", (fn_uri_component, 1));
    m.insert(
        "azure.policy.fn.uri_component_to_string",
        (fn_uri_component_to_string, 1),
    );
    m.insert("azure.policy.fn.data_uri", (fn_data_uri, 1));
    m.insert(
        "azure.policy.fn.data_uri_to_string",
        (fn_data_uri_to_string, 1),
    );
}

// ── Base64 helpers (pure implementation, no external deps) ────────────

const BASE64_CHARS: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn base64_encode(input: &[u8]) -> String {
    let cap = input.len().div_ceil(3).saturating_mul(4);
    let mut result = String::with_capacity(cap);
    for chunk in input.chunks(3) {
        let b0 = u32::from(*chunk.first().unwrap_or(&0));
        let b1 = u32::from(*chunk.get(1).unwrap_or(&0));
        let b2 = u32::from(*chunk.get(2).unwrap_or(&0));
        let triple = (b0 << 16) | (b1 << 8) | b2;
        let idx0 = usize::try_from((triple >> 18) & 0x3F).unwrap_or(0);
        let idx1 = usize::try_from((triple >> 12) & 0x3F).unwrap_or(0);
        let idx2 = usize::try_from((triple >> 6) & 0x3F).unwrap_or(0);
        let idx3 = usize::try_from(triple & 0x3F).unwrap_or(0);
        result.push(char::from(*BASE64_CHARS.get(idx0).unwrap_or(&b'A')));
        result.push(char::from(*BASE64_CHARS.get(idx1).unwrap_or(&b'A')));
        if chunk.len() > 1 {
            result.push(char::from(*BASE64_CHARS.get(idx2).unwrap_or(&b'A')));
        } else {
            result.push('=');
        }
        if chunk.len() > 2 {
            result.push(char::from(*BASE64_CHARS.get(idx3).unwrap_or(&b'A')));
        } else {
            result.push('=');
        }
    }
    result
}

const fn base64_decode_byte(c: u8) -> Option<u8> {
    match c {
        b'A'..=b'Z' => Some(c.wrapping_sub(b'A')),
        b'a'..=b'z' => Some(c.wrapping_sub(b'a').wrapping_add(26)),
        b'0'..=b'9' => Some(c.wrapping_sub(b'0').wrapping_add(52)),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

fn base64_decode(input: &str) -> Option<Vec<u8>> {
    let input = input.trim();
    if input.is_empty() {
        return Some(Vec::new());
    }
    let bytes: Vec<u8> = input
        .bytes()
        .filter(|&b| b != b'\n' && b != b'\r')
        .collect();
    if !bytes.len().is_multiple_of(4) {
        return None;
    }
    let mut result = Vec::with_capacity((bytes.len() / 4).saturating_mul(3));
    for chunk in bytes.chunks(4) {
        let [c0, c1, c2, c3] = <[u8; 4]>::try_from(chunk).ok()?;
        let a = base64_decode_byte(c0)?;
        let b = base64_decode_byte(c1)?;
        let triple = u32::from(a) << 18
            | u32::from(b) << 12
            | if c2 != b'=' {
                u32::from(base64_decode_byte(c2)?) << 6
            } else {
                0
            }
            | if c3 != b'=' {
                u32::from(base64_decode_byte(c3)?)
            } else {
                0
            };
        result.push(u8::try_from((triple >> 16) & 0xFF).unwrap_or(0));
        if c2 != b'=' {
            result.push(u8::try_from((triple >> 8) & 0xFF).unwrap_or(0));
        }
        if c3 != b'=' {
            result.push(u8::try_from(triple & 0xFF).unwrap_or(0));
        }
    }
    Some(result)
}

/// `base64(inputString)` → base64-encoded string.
fn fn_base64(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    Ok(Value::from(base64_encode(s.as_bytes())))
}

/// `base64ToString(base64Value)` → decoded UTF-8 string.
fn fn_base64_to_string(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    let Some(decoded) = base64_decode(s) else {
        return Ok(Value::Undefined);
    };
    String::from_utf8(decoded).map_or_else(|_| Ok(Value::Undefined), |text| Ok(Value::from(text)))
}

/// `base64ToJson(base64Value)` → parsed JSON value from base64-encoded string.
fn fn_base64_to_json(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    let Some(decoded) = base64_decode(s) else {
        return Ok(Value::Undefined);
    };
    let Ok(text) = String::from_utf8(decoded) else {
        return Ok(Value::Undefined);
    };
    Value::from_json_str(&text).map_or_else(|_| Ok(Value::Undefined), Ok)
}

// ── URI helpers (pure implementation) ─────────────────────────────────

const fn is_unreserved(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.' || b == b'~'
}

fn percent_encode(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if is_unreserved(b) {
            result.push(char::from(b));
        } else {
            // b >> 4 is in 0..=15 and b & 0x0F is in 0..=15, so from_digit
            // always returns Some for radix 16.
            result.push('%');
            result.push(
                core::char::from_digit(u32::from(b >> 4), 16)
                    .unwrap_or('0')
                    .to_ascii_uppercase(),
            );
            result.push(
                core::char::from_digit(u32::from(b & 0x0F), 16)
                    .unwrap_or('0')
                    .to_ascii_uppercase(),
            );
        }
    }
    result
}

fn percent_decode(s: &str) -> Option<String> {
    let bytes = s.as_bytes();
    let mut result = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if *bytes.get(i)? == b'%' {
            // Require exactly two hex digits after '%'; reject incomplete escapes.
            let hi = char::from(*bytes.get(i.checked_add(1)?)?).to_digit(16)?;
            let lo = char::from(*bytes.get(i.checked_add(2)?)?).to_digit(16)?;
            result.push(u8::try_from(hi.checked_mul(16)?.checked_add(lo)?).ok()?);
            i = i.checked_add(3)?;
        } else {
            result.push(*bytes.get(i)?);
            i = i.checked_add(1)?;
        }
    }
    String::from_utf8(result).ok()
}

/// `uri(baseUri, relativeUri)` → combined URI.
fn fn_uri(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    if args.len() != 2 {
        return Ok(Value::Undefined);
    }
    let (Some(base), Some(relative)) =
        (args.first().and_then(as_str), args.get(1).and_then(as_str))
    else {
        return Ok(Value::Undefined);
    };

    // Simple URI combination following Azure semantics.
    let combined = if relative.starts_with("http://") || relative.starts_with("https://") {
        // Relative is an absolute URL — use it directly.
        relative.to_string()
    } else if base.ends_with('/') {
        alloc::format!("{}{}", base, relative.trim_start_matches('/'))
    } else {
        // Find the end of the authority (scheme://host).  The path starts
        // after the third '/' (e.g. https://example.com/path → slash at
        // position after "com").  If there is no path component at all
        // (e.g. "https://example.com"), just append.
        let scheme_end = base.find("://").map(|p| p.wrapping_add(3)).unwrap_or(0);
        let path_slash = base.get(scheme_end..).and_then(|rest| rest.find('/'));

        path_slash.map_or_else(
            || {
                // Authority-only base (no path) — append with slash.
                alloc::format!("{}/{}", base, relative.trim_start_matches('/'))
            },
            |offset| {
                // There is a path — replace the last segment.
                let abs_pos = scheme_end.wrapping_add(offset);
                let last_slash = base
                    .get(abs_pos..)
                    .and_then(|p| p.rfind('/'))
                    .map(|o| abs_pos.wrapping_add(o));
                let cut = last_slash.unwrap_or(abs_pos);
                alloc::format!(
                    "{}/{}",
                    base.get(..cut).unwrap_or(base),
                    relative.trim_start_matches('/')
                )
            },
        )
    };

    Ok(Value::from(combined))
}

/// `uriComponent(stringToEncode)` → percent-encoded string.
fn fn_uri_component(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    Ok(Value::from(percent_encode(s)))
}

/// `uriComponentToString(uriEncodedString)` → decoded string.
fn fn_uri_component_to_string(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    percent_decode(s).map_or_else(|| Ok(Value::Undefined), |decoded| Ok(Value::from(decoded)))
}

/// `dataUri(stringToConvert)` → data URI (text/plain;charset=utf8).
fn fn_data_uri(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    let encoded = base64_encode(s.as_bytes());
    Ok(Value::from(alloc::format!(
        "data:text/plain;charset=utf8;base64,{}",
        encoded
    )))
}

/// `dataUriToString(dataUriToConvert)` → decoded string from data URI.
fn fn_data_uri_to_string(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };

    // Expected format: data:<mediatype>;base64,<data>
    let Some(rest) = s.strip_prefix("data:") else {
        return Ok(Value::Undefined);
    };

    // Find the base64 data after the last comma.
    let Some(comma_pos) = rest.rfind(',') else {
        return Ok(Value::Undefined);
    };
    let b64_data = rest.get(comma_pos.saturating_add(1)..).unwrap_or("");

    let Some(decoded) = base64_decode(b64_data) else {
        return Ok(Value::Undefined);
    };
    String::from_utf8(decoded).map_or_else(|_| Ok(Value::Undefined), |text| Ok(Value::from(text)))
}

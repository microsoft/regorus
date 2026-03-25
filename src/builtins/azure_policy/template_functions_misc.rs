// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template miscellaneous function builtins for Azure Policy expressions.
//!
//! Implements: json, join, items, indexFromEnd, tryGet, tryIndexFromEnd,
//!             guid, uniqueString.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;
use crate::Rc;

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use anyhow::Result;

use super::helpers::as_str;

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.json", (fn_json, 1));
    m.insert("azure.policy.fn.join", (fn_join, 2));
    m.insert("azure.policy.fn.items", (fn_items, 1));
    m.insert("azure.policy.fn.index_from_end", (fn_index_from_end, 2));
    m.insert("azure.policy.fn.try_get", (fn_try_get, 2));
    m.insert(
        "azure.policy.fn.try_index_from_end",
        (fn_try_index_from_end, 2),
    );
    m.insert("azure.policy.fn.guid", (fn_guid, 0));
    m.insert("azure.policy.fn.unique_string", (fn_unique_string, 0));
}

// ── json ──────────────────────────────────────────────────────────────

/// `json(arg)` → parses a JSON string into a typed value.
///
/// `json('null')` returns null, `json('{"a":1}')` returns an object, etc.
fn fn_json(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    Value::from_json_str(s).map_err(|e| anyhow::anyhow!("json(): {}", e))
}

// ── join ──────────────────────────────────────────────────────────────

/// `join(inputArray, delimiter)` → joins array elements with delimiter.
fn fn_join(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [arr_val, delim_val] = args
    else {
        return Ok(Value::Undefined);
    };
    let Value::Array(ref arr) = *arr_val else {
        return Ok(Value::Undefined);
    };
    let Some(delim) = as_str(delim_val) else {
        return Ok(Value::Undefined);
    };
    let parts: Vec<String> = arr
        .iter()
        .map(|v| match *v {
            Value::String(ref s) => s.to_string(),
            Value::Number(ref n) => n.format_decimal(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".to_string(),
            _ => v.to_string(),
        })
        .collect();
    Ok(Value::from(parts.join(delim)))
}

// ── items ─────────────────────────────────────────────────────────────

/// `items(object)` → array of `{"key": k, "value": v}` pairs.
fn fn_items(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(first) = args.first() else {
        return Ok(Value::Undefined);
    };
    let Value::Object(ref obj) = *first else {
        return Ok(Value::Undefined);
    };
    let mut result = Vec::with_capacity(obj.len());
    for (k, v) in obj.as_ref() {
        let mut entry = BTreeMap::<Value, Value>::new();
        entry.insert(Value::from("key"), k.clone());
        entry.insert(Value::from("value"), v.clone());
        result.push(Value::Object(Rc::new(entry)));
    }
    Ok(Value::Array(Rc::new(result)))
}

// ── indexFromEnd ──────────────────────────────────────────────────────

/// `indexFromEnd(sourceArray, reverseIndex)` → element at 1-based reverse index.
///
/// `indexFromEnd([a,b,c,d], 2)` returns `c` (2nd from end).
fn fn_index_from_end(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [arr_val, idx_val] = args
    else {
        return Ok(Value::Undefined);
    };
    let Value::Array(ref arr) = *arr_val else {
        return Ok(Value::Undefined);
    };
    let Some(rev_idx) = extract_usize(idx_val) else {
        return Ok(Value::Undefined);
    };
    if rev_idx == 0 || rev_idx > arr.len() {
        anyhow::bail!("indexFromEnd: reverse index {} out of bounds", rev_idx);
    }
    let pos = arr
        .len()
        .checked_sub(rev_idx)
        .ok_or_else(|| anyhow::anyhow!("indexFromEnd: arithmetic overflow"))?;
    arr.get(pos)
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("indexFromEnd: index out of bounds"))
}

// ── tryGet ────────────────────────────────────────────────────────────

/// `tryGet(itemToTest, keyOrIndex)` → value at key/index, or null if missing.
fn fn_try_get(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [item, key_or_idx] = args
    else {
        return Ok(Value::Undefined);
    };
    match *item {
        Value::Object(ref obj) => {
            // Property lookup by string key
            Ok(obj.get(key_or_idx).cloned().unwrap_or(Value::Null))
        }
        Value::Array(ref arr) => {
            // Index lookup
            let Some(idx) = extract_usize(key_or_idx) else {
                return Ok(Value::Null);
            };
            Ok(arr.get(idx).cloned().unwrap_or(Value::Null))
        }
        _ => Ok(Value::Null),
    }
}

// ── tryIndexFromEnd ───────────────────────────────────────────────────

/// `tryIndexFromEnd(sourceArray, reverseIndex)` → element or null if out of bounds.
fn fn_try_index_from_end(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [arr_val, idx_val] = args
    else {
        return Ok(Value::Undefined);
    };
    let Value::Array(ref arr) = *arr_val else {
        return Ok(Value::Null);
    };
    let Some(rev_idx) = extract_usize(idx_val) else {
        return Ok(Value::Null);
    };
    if rev_idx == 0 || rev_idx > arr.len() {
        return Ok(Value::Null);
    }
    let pos = arr.len().saturating_sub(rev_idx);
    Ok(arr.get(pos).cloned().unwrap_or(Value::Null))
}

// ── guid ──────────────────────────────────────────────────────────────

/// `guid(baseString, ...)` → deterministic UUID v5.
///
/// Azure uses namespace `11fb06fb-712d-4ddd-98c7-e71bbd588830` and joins
/// parameters with `-` before hashing with SHA-1 per RFC 4122 §4.3.
fn fn_guid(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    if args.is_empty() {
        return Ok(Value::Undefined);
    }

    let parts: Vec<String> = args
        .iter()
        .map(|v| match *v {
            Value::String(ref s) => s.to_string(),
            Value::Number(ref n) => n.format_decimal(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".to_string(),
            _ => v.to_string(),
        })
        .collect();
    let input = parts.join("-");

    // Namespace UUID: 11fb06fb-712d-4ddd-98c7-e71bbd588830
    let namespace: [u8; 16] = [
        0x11, 0xfb, 0x06, 0xfb, 0x71, 0x2d, 0x4d, 0xdd, 0x98, 0xc7, 0xe7, 0x1b, 0xbd, 0x58, 0x88,
        0x30,
    ];

    // UUID v5: SHA-1 of namespace + input, then set version and variant bits.
    let hash = sha1_hash(&namespace, input.as_bytes());

    // Take first 16 bytes
    let mut uuid_bytes = [0_u8; 16];
    uuid_bytes.copy_from_slice(&hash[..16]);

    // Set version (4 bits) to 5 (0101)
    uuid_bytes[6] = (uuid_bytes[6] & 0x0F) | 0x50;
    // Set variant (2 bits) to 10xx
    uuid_bytes[8] = (uuid_bytes[8] & 0x3F) | 0x80;

    let uuid_str = format!(
        "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        uuid_bytes[0], uuid_bytes[1], uuid_bytes[2], uuid_bytes[3],
        uuid_bytes[4], uuid_bytes[5],
        uuid_bytes[6], uuid_bytes[7],
        uuid_bytes[8], uuid_bytes[9],
        uuid_bytes[10], uuid_bytes[11], uuid_bytes[12], uuid_bytes[13], uuid_bytes[14], uuid_bytes[15],
    );

    Ok(Value::from(uuid_str))
}

/// Minimal SHA-1 implementation (only used for guid() UUID v5).
///
/// Computes SHA-1(namespace_bytes ++ data). Returns 20-byte digest.
fn sha1_hash(namespace: &[u8], data: &[u8]) -> [u8; 20] {
    // Concatenate namespace + data
    let mut message = Vec::with_capacity(namespace.len().saturating_add(data.len()));
    message.extend_from_slice(namespace);
    message.extend_from_slice(data);

    // SHA-1 initial hash values
    let mut h0: u32 = 0x6745_2301;
    let mut h1: u32 = 0xEFCD_AB89;
    let mut h2: u32 = 0x98BA_DCFE;
    let mut h3: u32 = 0x1032_5476;
    let mut h4: u32 = 0xC3D2_E1F0;

    let bit_len = u64::try_from(message.len()).unwrap_or(0).saturating_mul(8);

    // Padding
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&bit_len.to_be_bytes());

    // Process each 512-bit (64-byte) block
    for chunk in message.chunks_exact(64) {
        let mut w = [0_u32; 80];
        for (wi, src) in chunk.chunks_exact(4).zip(w.iter_mut().take(16)) {
            let bytes: [u8; 4] = wi.first_chunk::<4>().copied().unwrap_or([0; 4]);
            *src = u32::from_be_bytes(bytes);
        }
        for idx in 16_usize..80 {
            let v = w.get(idx.wrapping_sub(3)).copied().unwrap_or(0)
                ^ w.get(idx.wrapping_sub(8)).copied().unwrap_or(0)
                ^ w.get(idx.wrapping_sub(14)).copied().unwrap_or(0)
                ^ w.get(idx.wrapping_sub(16)).copied().unwrap_or(0);
            if let Some(slot) = w.get_mut(idx) {
                *slot = v.rotate_left(1);
            }
        }

        let (mut a, mut b, mut c, mut d, mut e) = (h0, h1, h2, h3, h4);

        for (idx, w_val) in w.iter().enumerate() {
            let (f, k) = match idx {
                0..=19 => ((b & c) | ((!b) & d), 0x5A82_7999_u32),
                20..=39 => (b ^ c ^ d, 0x6ED9_EBA1_u32),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1B_BCDC_u32),
                _ => (b ^ c ^ d, 0xCA62_C1D6_u32),
            };

            let temp = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(*w_val);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = temp;
        }

        h0 = h0.wrapping_add(a);
        h1 = h1.wrapping_add(b);
        h2 = h2.wrapping_add(c);
        h3 = h3.wrapping_add(d);
        h4 = h4.wrapping_add(e);
    }

    let mut result = [0_u8; 20];
    result[0..4].copy_from_slice(&h0.to_be_bytes());
    result[4..8].copy_from_slice(&h1.to_be_bytes());
    result[8..12].copy_from_slice(&h2.to_be_bytes());
    result[12..16].copy_from_slice(&h3.to_be_bytes());
    result[16..20].copy_from_slice(&h4.to_be_bytes());
    result
}

// ── uniqueString ──────────────────────────────────────────────────────

/// `uniqueString(baseString, ...)` → deterministic 13-character string.
///
/// Azure's implementation uses a deterministic hash. We use a FNV-1a-based
/// approach that produces a 13-character base-32 encoded string.
fn fn_unique_string(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    if args.is_empty() {
        return Ok(Value::Undefined);
    }

    let parts: Vec<String> = args
        .iter()
        .map(|v| match *v {
            Value::String(ref s) => s.to_string(),
            Value::Number(ref n) => n.format_decimal(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".to_string(),
            _ => v.to_string(),
        })
        .collect();

    // Use SHA-1 of the concatenated inputs for deterministic hashing,
    // then encode as base-32 (lowercase) to get a 13-character string.
    let input = parts.join("\0");
    let empty_ns = [];
    let hash = sha1_hash(&empty_ns, input.as_bytes());

    // Take first 8 bytes as a u64; encode in base-32 (a-z, 2-7) to 13 chars.
    let val = u64::from_be_bytes([
        hash[0], hash[1], hash[2], hash[3], hash[4], hash[5], hash[6], hash[7],
    ]);

    const ALPHABET: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";
    let mut result = [0_u8; 13];
    let mut remaining = val;
    for byte in result.iter_mut().rev() {
        *byte = ALPHABET
            .get(usize::try_from(remaining & 0x1F).unwrap_or(0))
            .copied()
            .unwrap_or(b'a');
        remaining >>= 5;
    }

    Ok(Value::from(
        core::str::from_utf8(&result).unwrap_or("").to_string(),
    ))
}

// ── Helpers ───────────────────────────────────────────────────────────

fn extract_usize(v: &Value) -> Option<usize> {
    match *v {
        Value::Number(ref n) => n
            .as_i64()
            .and_then(|x| usize::try_from(x).ok())
            .or_else(|| n.as_f64().and_then(|x| usize::try_from(f64_to_i64(x)).ok())),
        _ => None,
    }
}

#[expect(clippy::as_conversions)]
const fn f64_to_i64(x: f64) -> i64 {
    x as i64
}

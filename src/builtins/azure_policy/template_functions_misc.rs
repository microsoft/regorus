// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template miscellaneous function builtins for Azure Policy expressions.
//!
//! Implements: json, join, items, indexFromEnd, tryGet, tryIndexFromEnd.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;
use crate::Rc;

use alloc::collections::BTreeMap;
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
    // guid() and uniqueString() are not yet implemented. They are unsupported
    // during template dispatch, and the compiler will raise a compile error if
    // either function is encountered.
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

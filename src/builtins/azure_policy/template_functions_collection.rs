// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template collection function builtins for Azure Policy expressions.
//!
//! Implements: intersection, union, take, skip, range, array, coalesce, createObject.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;
use crate::Rc;

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use anyhow::Result;

use super::helpers::is_undefined;

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert(
        "azure.policy.fn.intersection",
        (fn_intersection, super::MAX_VARIADIC_ARGS),
    );
    m.insert(
        "azure.policy.fn.union",
        (fn_union, super::MAX_VARIADIC_ARGS),
    );
    m.insert("azure.policy.fn.take", (fn_take, 2));
    m.insert("azure.policy.fn.skip", (fn_skip, 2));
    m.insert("azure.policy.fn.range", (fn_range, 2));
    m.insert("azure.policy.fn.array", (fn_array, 1));
    m.insert(
        "azure.policy.fn.coalesce",
        (fn_coalesce, super::MAX_VARIADIC_ARGS),
    );
    m.insert(
        "azure.policy.fn.create_object",
        (fn_create_object, super::MAX_VARIADIC_ARGS),
    );
}

/// `intersection(arg1, arg2, ...)` → elements common to all arrays, or keys common
/// to all objects.
///
/// For arrays: returns elements present in every input array.
/// For objects: returns keys (with values from the first) present in every input.
fn fn_intersection(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(first) = args.first() else {
        return Ok(Value::Undefined);
    };
    let rest = args.get(1..).unwrap_or_default();

    match *first {
        Value::Array(ref first) => {
            // Intersection of arrays: keep elements from first that appear in all others.
            let mut result: Vec<Value> = first.as_ref().clone();
            for arg in rest {
                let Value::Array(ref other) = *arg else {
                    return Ok(Value::Undefined);
                };
                result.retain(|item| other.contains(item));
            }
            Ok(Value::from(result))
        }
        Value::Object(ref first) => {
            // Intersection of objects: keep key-value pairs from the first
            // object only when the key exists in every other object AND
            // the value is equal across all of them.
            let mut result: BTreeMap<Value, Value> = first.as_ref().clone();
            for arg in rest {
                let Value::Object(ref other) = *arg else {
                    return Ok(Value::Undefined);
                };
                result.retain(|k, v| other.get(k).is_some_and(|ov| *ov == *v));
            }
            Ok(Value::Object(Rc::new(result)))
        }
        _ => Ok(Value::Undefined),
    }
}

/// `union(arg1, arg2, ...)` → all unique elements from arrays, or merged objects.
///
/// For arrays: returns distinct elements across all arrays.
/// For objects: merges all objects (later values overwrite earlier for same key).
fn fn_union(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(first) = args.first() else {
        return Ok(Value::Undefined);
    };

    match *first {
        Value::Array(_) => {
            // Union of arrays: collect unique elements preserving first-seen order.
            let mut seen = alloc::collections::BTreeSet::<&Value>::new();
            let mut result = Vec::new();
            for arg in args {
                let Value::Array(ref arr) = *arg else {
                    return Ok(Value::Undefined);
                };
                for item in arr.iter() {
                    if seen.insert(item) {
                        result.push(item.clone());
                    }
                }
            }
            Ok(Value::from(result))
        }
        Value::Object(_) => {
            // Union of objects: recursive merge. Nested objects are merged
            // recursively; all other types (including arrays) use last-writer-wins.
            let mut result = BTreeMap::<Value, Value>::new();
            for arg in args {
                let Value::Object(ref obj) = *arg else {
                    return Ok(Value::Undefined);
                };
                for (k, v) in obj.iter() {
                    #[allow(clippy::needless_borrowed_reference)]
                    let merged = match (result.get(k), v) {
                        (Some(&Value::Object(ref prev)), &Value::Object(ref next)) => {
                            merge_objects(prev, next)
                        }
                        _ => v.clone(),
                    };
                    result.insert(k.clone(), merged);
                }
            }
            Ok(Value::Object(Rc::new(result)))
        }
        _ => Ok(Value::Undefined),
    }
}

/// `take(originalValue, numberToTake)` → first N elements of array or chars of string.
fn fn_take(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [original, count_val] = args
    else {
        return Ok(Value::Undefined);
    };

    let count = extract_usize(count_val).unwrap_or(0);

    match *original {
        Value::Array(ref arr) => {
            let n = count.min(arr.len());
            Ok(Value::from(arr.get(..n).unwrap_or_default().to_vec()))
        }
        Value::String(ref s) => {
            let taken: alloc::string::String = s.chars().take(count).collect();
            Ok(Value::from(taken))
        }
        _ => Ok(Value::Undefined),
    }
}

/// `skip(originalValue, numberToSkip)` → array/string after skipping N elements.
fn fn_skip(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [original, count_val] = args
    else {
        return Ok(Value::Undefined);
    };

    let count = extract_usize(count_val).unwrap_or(0);

    match *original {
        Value::Array(ref arr) => {
            let n = count.min(arr.len());
            Ok(Value::from(arr.get(n..).unwrap_or_default().to_vec()))
        }
        Value::String(ref s) => {
            let skipped: alloc::string::String = s.chars().skip(count).collect();
            Ok(Value::from(skipped))
        }
        _ => Ok(Value::Undefined),
    }
}

/// `range(startIndex, count)` → array of integers starting at startIndex.
///
/// Azure limits: count ≤ 10000, startIndex + count ≤ 2147483647.
fn fn_range(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [start_val, count_val] = args
    else {
        return Ok(Value::Undefined);
    };

    let (Some(start), Some(count)) = (extract_i64(start_val), extract_i64(count_val)) else {
        return Ok(Value::Undefined);
    };

    if count < 0 {
        return Ok(Value::Undefined);
    }

    // Enforce Azure-documented limits.
    if count > 10_000 {
        anyhow::bail!("range: count ({count}) exceeds maximum of 10000");
    }
    let end = start
        .checked_add(count)
        .ok_or_else(|| anyhow::anyhow!("range overflow"))?;
    if end > 2_147_483_647 {
        anyhow::bail!("range: startIndex + count ({end}) exceeds maximum of 2147483647");
    }

    let mut result = Vec::with_capacity(usize::try_from(count).unwrap_or(0));
    for i in 0..count {
        let val = start
            .checked_add(i)
            .ok_or_else(|| anyhow::anyhow!("range overflow"))?;
        result.push(Value::from(val));
    }
    Ok(Value::from(result))
}

/// `array(convertToArray)` → wraps a single value in an array.
///
/// If the input is already an array, returns it as-is.
fn fn_array(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::from(Vec::<Value>::new()));
    };
    match *arg {
        Value::Array(_) => Ok(arg.clone()),
        _ => Ok(Value::from(alloc::vec![arg.clone()])),
    }
}

/// `coalesce(arg1, arg2, ...)` → first non-null, non-undefined argument.
fn fn_coalesce(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    for arg in args {
        if !is_undefined(arg) && !matches!(arg, Value::Null) {
            return Ok(arg.clone());
        }
    }
    Ok(Value::Null)
}

/// `createObject(key1, value1, key2, value2, ...)` → object from key-value pairs.
fn fn_create_object(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    if !args.len().is_multiple_of(2) {
        anyhow::bail!(
            "createObject: expected an even number of arguments (key-value pairs), \
             but received {}",
            args.len()
        );
    }

    let mut map = BTreeMap::<Value, Value>::new();

    for pair in args.chunks(2) {
        #[allow(clippy::pattern_type_mismatch)]
        if let [key, value] = pair {
            map.insert(key.clone(), value.clone());
        }
    }

    Ok(Value::Object(Rc::new(map)))
}

// ── Helpers ───────────────────────────────────────────────────────────

/// Recursively merge two objects.  Nested objects are merged; everything
/// else (including arrays) uses the value from `incoming`.
fn merge_objects(base: &BTreeMap<Value, Value>, overlay: &BTreeMap<Value, Value>) -> Value {
    let mut result = base.clone();
    for (k, v) in overlay {
        #[allow(clippy::needless_borrowed_reference)]
        let merged = match (result.get(k), v) {
            (Some(&Value::Object(ref prev)), &Value::Object(ref next)) => merge_objects(prev, next),
            _ => v.clone(),
        };
        result.insert(k.clone(), merged);
    }
    Value::Object(Rc::new(result))
}

fn extract_usize(v: &Value) -> Option<usize> {
    match *v {
        Value::Number(ref n) => n
            .as_i64()
            .and_then(|x| usize::try_from(x).ok())
            .or_else(|| n.as_f64().and_then(|x| usize::try_from(f64_as_i64(x)).ok())),
        _ => None,
    }
}

fn extract_i64(v: &Value) -> Option<i64> {
    match *v {
        Value::Number(ref n) => n.as_i64().or_else(|| n.as_f64().map(f64_as_i64)),
        _ => None,
    }
}

/// Deliberate truncating conversion from `f64` → `i64`.
#[expect(clippy::as_conversions)]
const fn f64_as_i64(x: f64) -> i64 {
    x as i64
}

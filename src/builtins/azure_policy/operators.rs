// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure Policy utility builtins: parameter resolution, field resolution,
//! logic_all (for ARM `and()`), and if().
//!
//! The 20 condition operators (equals, notEquals, greater, …, exists) and
//! the logic_not / logic_any combinators are now compiled as first-class
//! RVM instructions (`PolicyEquals`, `PolicyNot`, `AllOfStart`/`AnyOfStart`,
//! etc.) and no longer go through the builtin dispatch path.

use crate::ast::{Expr, Ref};
use crate::lexer::Span;
use crate::value::Value;

use anyhow::Result;

use super::helpers::{as_string, is_true, is_undefined, resolve_path};

// ── Parameter resolution ──────────────────────────────────────────────

/// `azure.policy.get_parameter(params, defaults, name)`
///
/// Returns `params[name]` if it exists and is not undefined; otherwise
/// falls back to `defaults[name]`.  This lets the compiler bake parameter
/// default values into the program's literal table while still allowing
/// callers to override them via `input.parameters`.
pub(super) fn get_parameter(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [params_obj, defaults_obj, name] = args
    else {
        return Ok(Value::Undefined);
    };

    // Try caller-supplied parameters first.
    let val = &params_obj[name];
    if !is_undefined(val) {
        return Ok(val.clone());
    }

    // Fall back to compiled-in defaults.
    Ok(defaults_obj[name].clone())
}

// ── Field resolution ──────────────────────────────────────────────────

pub(super) fn resolve_field(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [resource, field_path] = args
    else {
        return Ok(Value::Undefined);
    };

    let Some(path) = as_string(field_path) else {
        return Ok(Value::Undefined);
    };

    Ok(resolve_path(resource, &path))
}

// ── Logic functions ───────────────────────────────────────────────────

/// `azure.policy.logic_all(a, b, ...)`
///
/// Used by the ARM template `and()` function.  Returns true iff every
/// argument is `Bool(true)`.
pub(super) fn logic_all(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    Ok(Value::Bool(args.iter().all(is_true)))
}

/// `azure.policy.logic_any(a, b, ...)`
///
/// Used by the ARM template `or()` function.  Returns true iff any
/// argument is `Bool(true)`.
pub(super) fn logic_any(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    Ok(Value::Bool(args.iter().any(is_true)))
}

/// `azure.policy.if(cond, when_true, when_false)`
pub(super) fn if_fn(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [cond, when_true, when_false] = args
    else {
        return Ok(Value::Undefined);
    };
    if is_true(cond) {
        Ok(when_true.clone())
    } else {
        Ok(when_false.clone())
    }
}

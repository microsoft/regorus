// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Planner support for `some .. in` expressions.

use alloc::collections::BTreeSet;
use alloc::string::String;

use crate::ast::{Expr, ExprRef};
use crate::compiler::destructuring_planner::destructuring::create_destructuring_plan_with_tracking;
use crate::compiler::destructuring_planner::utils::{
    check_literal_structure, validate_pattern_bindings, LiteralStructureCheck,
};
use crate::compiler::destructuring_planner::{
    BindingPlan, BindingPlannerError, Result, ScopingMode, VariableBindingContext,
};

/// Convenience function for some..in expressions (always allow shadowing for new bindings).
pub fn create_some_in_binding_plan<T: VariableBindingContext>(
    key_expr: &Option<ExprRef>,
    value_expr: &ExprRef,
    collection_expr: &ExprRef,
    context: &T,
) -> Result<BindingPlan> {
    let key_plan = if let Some(key) = key_expr {
        let mut newly_bound = BTreeSet::new();
        let plan = create_destructuring_plan_with_tracking(
            key,
            context,
            ScopingMode::RespectParent,
            &mut newly_bound,
        );
        if let Some(plan) = plan {
            validate_pattern_bindings(key, &newly_bound, context)?;
            Some(plan)
        } else {
            None
        }
    } else {
        None
    };

    let mut newly_bound_value = BTreeSet::new();
    let value_plan = create_destructuring_plan_with_tracking(
        value_expr,
        context,
        ScopingMode::RespectParent,
        &mut newly_bound_value,
    )
    .ok_or_else(|| BindingPlannerError::FailedToCreateDestructuringPlan {
        plan_type: String::from("some-in value"),
        span: value_expr.span().clone(),
    })?;

    validate_pattern_bindings(value_expr, &newly_bound_value, context)?;

    if let Expr::Array { items, .. } = collection_expr.as_ref() {
        let mut found_match = false;
        let mut mismatch_error: Option<BindingPlannerError> = None;
        let mut saw_unknown = false;

        for collection_item in items {
            match check_literal_structure(&value_plan, collection_item) {
                LiteralStructureCheck::Match => {
                    found_match = true;
                }
                LiteralStructureCheck::Unknown => {
                    saw_unknown = true;
                }
                mismatch => {
                    if let Some(err) = mismatch.into_error() {
                        if mismatch_error.is_none() {
                            mismatch_error = Some(err);
                        }
                    }
                }
            }
        }

        if !found_match && !saw_unknown {
            if let Some(err) = mismatch_error {
                return Err(err);
            }
        }
    }

    Ok(BindingPlan::SomeIn {
        collection_expr: collection_expr.clone(),
        key_plan,
        value_plan,
    })
}

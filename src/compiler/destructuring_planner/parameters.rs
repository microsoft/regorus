// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::unused_trait_names)]

//! Planner helpers for function parameters and loop indices.

use alloc::collections::BTreeSet;
use alloc::string::ToString;

use crate::ast::ExprRef;
use crate::compiler::destructuring_planner::create_destructuring_plan;
use crate::compiler::destructuring_planner::destructuring::create_destructuring_plan_with_tracking;
use crate::compiler::destructuring_planner::utils::validate_pattern_bindings;
use crate::compiler::destructuring_planner::{
    BindingPlan, BindingPlannerError, Result, ScopingMode, VariableBindingContext,
};

/// Convenience function for loop index expressions (respects parent scope).
pub fn create_loop_index_binding_plan<T: VariableBindingContext>(
    index_expr: &ExprRef,
    context: &T,
) -> Result<BindingPlan> {
    let destructuring_plan =
        create_destructuring_plan(index_expr, context, ScopingMode::RespectParent).ok_or_else(
            || BindingPlannerError::FailedToCreateDestructuringPlan {
                plan_type: "loop index".to_string(),
                span: index_expr.span().clone(),
            },
        )?;

    Ok(BindingPlan::LoopIndex {
        index_expr: index_expr.clone(),
        destructuring_plan,
    })
}

/// Convenience function for function parameters (always allow shadowing).
pub fn create_parameter_binding_plan<T: VariableBindingContext>(
    param_expr: &ExprRef,
    context: &T,
    scoping: ScopingMode,
) -> Result<BindingPlan> {
    let mut newly_bound = BTreeSet::new();
    let destructuring_plan =
        create_destructuring_plan_with_tracking(param_expr, context, scoping, &mut newly_bound)
            .ok_or_else(|| BindingPlannerError::FailedToCreateDestructuringPlan {
                plan_type: "parameter".to_string(),
                span: param_expr.span().clone(),
            })?;

    if scoping == ScopingMode::AllowShadowing {
        validate_pattern_bindings(param_expr, &newly_bound, context)?;
    }

    Ok(BindingPlan::Parameter {
        param_expr: param_expr.clone(),
        destructuring_plan,
    })
}

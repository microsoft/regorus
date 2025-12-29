// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::redundant_pub_crate,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

//! Shared helper routines for the destructuring planner modules.

use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::ast::{Expr, ExprRef};
use crate::compiler::destructuring_planner::{
    BindingPlannerError, DestructuringPlan, Result, ScopingMode, VariableBindingContext,
};
use crate::lexer::Span;
use crate::value::Value;

/// Result of statically comparing a destructuring plan with a literal expression.
pub(crate) enum LiteralStructureCheck {
    Match,
    Unknown,
    ArrayMismatch {
        expected: usize,
        actual: usize,
        span: Span,
    },
    ObjectMismatch {
        expected: Vec<String>,
        actual: Vec<String>,
        span: Span,
    },
}

impl LiteralStructureCheck {
    pub(crate) fn into_error(self) -> Option<BindingPlannerError> {
        match self {
            LiteralStructureCheck::Match | LiteralStructureCheck::Unknown => None,
            LiteralStructureCheck::ArrayMismatch {
                expected,
                actual,
                span,
            } => Some(BindingPlannerError::ArrayLengthMismatch {
                expected,
                actual,
                span,
            }),
            LiteralStructureCheck::ObjectMismatch {
                expected,
                actual,
                span,
            } => Some(BindingPlannerError::ObjectLiteralKeysMismatch {
                expected,
                actual,
                span,
            }),
        }
    }
}

/// Compare a destructuring plan against a literal expression.
pub(crate) fn check_literal_structure(
    plan: &DestructuringPlan,
    expr: &ExprRef,
) -> LiteralStructureCheck {
    match (plan, expr.as_ref()) {
        (DestructuringPlan::Array { element_plans }, Expr::Array { items, .. }) => {
            if items.len() != element_plans.len() {
                return LiteralStructureCheck::ArrayMismatch {
                    expected: element_plans.len(),
                    actual: items.len(),
                    span: expr.span().clone(),
                };
            }

            for (nested_plan, nested_expr) in element_plans.iter().zip(items.iter()) {
                match check_literal_structure(nested_plan, nested_expr) {
                    LiteralStructureCheck::Match => {}
                    LiteralStructureCheck::Unknown => return LiteralStructureCheck::Unknown,
                    mismatch => return mismatch,
                }
            }

            LiteralStructureCheck::Match
        }
        (
            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            },
            Expr::Object { fields, .. },
        ) => {
            if field_plans.is_empty() && dynamic_fields.is_empty() {
                return LiteralStructureCheck::Match;
            }

            if !field_plans.is_empty() {
                let expected_keys: Vec<String> = field_plans
                    .keys()
                    .map(format_literal_key_for_error)
                    .collect();

                let mut literal_fields: Vec<(Value, &ExprRef)> = Vec::new();
                let mut actual_keys: Vec<String> = Vec::new();
                for (_, key_expr, value_expr) in fields {
                    if let Some(key_value) = extract_literal_key(key_expr) {
                        actual_keys.push(format_literal_key_for_error(&key_value));
                        literal_fields.push((key_value, value_expr));
                    }
                }

                let mut expected_sorted = expected_keys.clone();
                expected_sorted.sort();
                let mut actual_sorted = actual_keys.clone();
                actual_sorted.sort();

                if expected_sorted != actual_sorted {
                    return LiteralStructureCheck::ObjectMismatch {
                        expected: expected_keys,
                        actual: actual_keys,
                        span: expr.span().clone(),
                    };
                }

                for (key_value, value_expr) in literal_fields {
                    if let Some(field_plan) = field_plans.get(&key_value) {
                        match check_literal_structure(field_plan, value_expr) {
                            LiteralStructureCheck::Match => {}
                            LiteralStructureCheck::Unknown => {
                                return LiteralStructureCheck::Unknown
                            }
                            mismatch => return mismatch,
                        }
                    }
                }

                if dynamic_fields.is_empty() {
                    return LiteralStructureCheck::Match;
                }
            }

            LiteralStructureCheck::Unknown
        }
        _ => LiteralStructureCheck::Unknown,
    }
}

pub(crate) fn ensure_literal_match(plan: &DestructuringPlan, expr: &ExprRef) -> Result<()> {
    check_literal_structure(plan, expr)
        .into_error()
        .map_or(Ok(()), Err)
}

pub(crate) fn collect_pattern_var_spans(expr: &ExprRef, spans: &mut Vec<Span>) {
    match expr.as_ref() {
        Expr::Var { span, .. } => {
            let name = span.text();
            if name != "_" && name != "input" && name != "data" {
                spans.push(span.clone());
            }
        }
        Expr::Array { items, .. } => {
            for item in items {
                collect_pattern_var_spans(item, spans);
            }
        }
        Expr::Set { items, .. } => {
            for item in items {
                collect_pattern_var_spans(item, spans);
            }
        }
        Expr::Object { fields, .. } => {
            for (_, _, value_expr) in fields {
                collect_pattern_var_spans(value_expr, spans);
            }
        }
        _ => {}
    }
}

pub(crate) fn validate_pattern_bindings<T: VariableBindingContext>(
    expr: &ExprRef,
    newly_bound: &BTreeSet<String>,
    context: &T,
) -> Result<()> {
    let mut candidate_vars = Vec::new();
    collect_pattern_var_spans(expr, &mut candidate_vars);

    for span in candidate_vars {
        let name = span.text().to_string();
        if newly_bound.contains(&name) {
            continue;
        }
        if !context.is_var_unbound(&name, ScopingMode::RespectParent) {
            return Err(BindingPlannerError::VariableAlreadyDefined { var: name, span });
        }
    }

    Ok(())
}

pub(crate) fn collect_plan_var_spans(plan: &DestructuringPlan, spans: &mut Vec<Span>) {
    match plan {
        DestructuringPlan::Var(span) => spans.push(span.clone()),
        DestructuringPlan::Array { element_plans } => {
            for nested in element_plans {
                collect_plan_var_spans(nested, spans);
            }
        }
        DestructuringPlan::Object {
            field_plans,
            dynamic_fields,
        } => {
            for nested in field_plans.values() {
                collect_plan_var_spans(nested, spans);
            }
            for (_, nested) in dynamic_fields {
                collect_plan_var_spans(nested, spans);
            }
        }
        DestructuringPlan::Ignore
        | DestructuringPlan::EqualityExpr(_)
        | DestructuringPlan::EqualityValue(_) => {}
    }
}

pub(crate) fn ensure_structural_compatibility(
    lhs_expr: &ExprRef,
    rhs_expr: &ExprRef,
) -> Result<()> {
    let lhs_is_array = matches!(lhs_expr.as_ref(), Expr::Array { .. });
    let rhs_is_array = matches!(rhs_expr.as_ref(), Expr::Array { .. });
    let lhs_is_object = matches!(lhs_expr.as_ref(), Expr::Object { .. });
    let rhs_is_object = matches!(rhs_expr.as_ref(), Expr::Object { .. });

    if (lhs_is_array && rhs_is_object) || (lhs_is_object && rhs_is_array) {
        return Err(BindingPlannerError::IncompatibleDestructuringPatterns {
            span: lhs_expr.span().clone(),
        });
    }

    Ok(())
}

/// Helper that discards destructuring plans which do not bind any variables.
pub(crate) fn plan_only_if_binds(plan: Option<DestructuringPlan>) -> Option<DestructuringPlan> {
    plan.and_then(|plan| (plan.introduces_binding() || plan.contains_wildcards()).then_some(plan))
}

pub(crate) fn extract_literal_key(expr: &ExprRef) -> Option<Value> {
    match expr.as_ref() {
        Expr::String { value, .. } => Some(value.clone()),
        Expr::RawString { value, .. } => Some(value.clone()),
        Expr::Number { value, .. } => Some(value.clone()),
        Expr::Bool { value, .. } => Some(value.clone()),
        Expr::Null { .. } => Some(Value::Null),
        _ => None,
    }
}

pub(crate) fn format_literal_key_for_error(value: &Value) -> String {
    match value {
        Value::String(s) => s.as_ref().to_string(),
        _ => value.to_string(),
    }
}

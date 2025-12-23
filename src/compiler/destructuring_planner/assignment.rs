// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::unreachable,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

//! Assignment-specific planning utilities.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::ast::{AssignOp, Expr, ExprRef};
use crate::compiler::destructuring_planner::create_destructuring_plan;
use crate::compiler::destructuring_planner::destructuring::create_destructuring_plan_with_tracking;
use crate::compiler::destructuring_planner::utils::{
    collect_plan_var_spans, ensure_literal_match, ensure_structural_compatibility,
    extract_literal_key, format_literal_key_for_error, plan_only_if_binds,
};
use crate::compiler::destructuring_planner::{
    AssignmentPlan, BindingPlan, BindingPlannerError, DestructuringPlan, Result, ScopingMode,
    VariableBindingContext, WildcardSide,
};
use crate::lexer::Span;
use crate::query::traversal::collect_expr_dependencies;
use crate::value::Value;

/// Convenience function for assignment expressions with specific := and = rules.
pub fn create_assignment_binding_plan<T: VariableBindingContext>(
    op: AssignOp,
    lhs_expr: &ExprRef,
    rhs_expr: &ExprRef,
    context: &T,
) -> Result<BindingPlan> {
    let assignment_plan = match op {
        AssignOp::ColEq => {
            // For :=, only LHS can be destructured
            if let Some(lhs_plan) = plan_only_if_binds(create_destructuring_plan(
                lhs_expr,
                context,
                ScopingMode::AllowShadowing,
            )) {
                let mut var_spans = Vec::new();
                collect_plan_var_spans(&lhs_plan, &mut var_spans);
                let mut lhs_scope_bindings = BTreeSet::new();
                for span in var_spans {
                    let name = span.text().to_string();
                    let is_duplicate = !lhs_scope_bindings.insert(name.clone());
                    let has_same_scope_binding = context.has_same_scope_binding(&name);

                    if is_duplicate || has_same_scope_binding {
                        return Err(BindingPlannerError::VariableAlreadyDefined {
                            var: name,
                            span,
                        });
                    }
                }

                ensure_structural_compatibility(lhs_expr, rhs_expr)?;
                ensure_literal_match(&lhs_plan, rhs_expr)?;
                AssignmentPlan::ColonEquals {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    lhs_plan,
                }
            } else {
                return Err(BindingPlannerError::ColonEqualsRequiresBindableLeft {
                    span: lhs_expr.span().clone(),
                });
            }
        }

        AssignOp::Eq => {
            let lhs_struct_plan =
                create_destructuring_plan(lhs_expr, context, ScopingMode::RespectParent);
            let rhs_struct_plan =
                create_destructuring_plan(rhs_expr, context, ScopingMode::RespectParent);

            let lhs_plan = plan_only_if_binds(lhs_struct_plan.clone());
            let rhs_plan = plan_only_if_binds(rhs_struct_plan.clone());

            let lhs_is_wildcard =
                matches!(lhs_expr.as_ref(), Expr::Var { span, .. } if span.text() == "_");
            let rhs_is_wildcard =
                matches!(rhs_expr.as_ref(), Expr::Var { span, .. } if span.text() == "_");

            if lhs_is_wildcard || rhs_is_wildcard {
                let wildcard_side = match (lhs_is_wildcard, rhs_is_wildcard) {
                    (true, true) => WildcardSide::Both,
                    (true, false) => WildcardSide::Lhs,
                    (false, true) => WildcardSide::Rhs,
                    (false, false) => unreachable!(),
                };

                AssignmentPlan::WildcardMatch {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    wildcard_side,
                }
            } else if lhs_plan.is_some() && rhs_plan.is_some() {
                // Both sides have unbound vars - recursively flatten all nested structures
                let mut element_pairs = Vec::new();
                let mut newly_bound = BTreeSet::new();
                flatten_assignment_pairs(
                    lhs_expr,
                    rhs_expr,
                    context,
                    &mut newly_bound,
                    &mut element_pairs,
                )?;
                order_element_pairs(&mut element_pairs, context);

                AssignmentPlan::EqualsBothSides {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    element_pairs,
                }
            } else if lhs_plan.is_none() && rhs_plan.is_none() {
                AssignmentPlan::EqualityCheck {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                }
            } else if let Some(lhs) = lhs_plan {
                ensure_structural_compatibility(lhs_expr, rhs_expr)?;
                ensure_literal_match(&lhs, rhs_expr)?;

                AssignmentPlan::EqualsBindLeft {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    lhs_plan: lhs,
                }
            } else if let Some(rhs) = rhs_plan {
                ensure_structural_compatibility(rhs_expr, lhs_expr)?;
                ensure_literal_match(&rhs, lhs_expr)?;

                AssignmentPlan::EqualsBindRight {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    rhs_plan: rhs,
                }
            } else if let Some(lhs) = lhs_struct_plan {
                ensure_structural_compatibility(lhs_expr, rhs_expr)?;
                ensure_literal_match(&lhs, rhs_expr)?;

                AssignmentPlan::EqualsBindLeft {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    lhs_plan: lhs,
                }
            } else if let Some(rhs) = rhs_struct_plan {
                ensure_structural_compatibility(rhs_expr, lhs_expr)?;
                ensure_literal_match(&rhs, lhs_expr)?;

                AssignmentPlan::EqualsBindRight {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                    rhs_plan: rhs,
                }
            } else {
                AssignmentPlan::EqualityCheck {
                    lhs_expr: lhs_expr.clone(),
                    rhs_expr: rhs_expr.clone(),
                }
            }
        }
    };

    Ok(BindingPlan::Assignment {
        plan: assignment_plan,
    })
}

/// Recursively flatten assignment destructuring into (value_expr, pattern_plan) pairs.
fn flatten_assignment_pairs<T: VariableBindingContext>(
    lhs_expr: &ExprRef,
    rhs_expr: &ExprRef,
    context: &T,
    newly_bound: &mut BTreeSet<String>,
    pairs: &mut Vec<(ExprRef, DestructuringPlan)>,
) -> Result<()> {
    let (lhs_plan, lhs_delta) =
        preview_binding_plan(lhs_expr, context, ScopingMode::RespectParent, newly_bound);
    let (rhs_plan, rhs_delta) =
        preview_binding_plan(rhs_expr, context, ScopingMode::RespectParent, newly_bound);

    if lhs_plan.is_none() && rhs_plan.is_none() {
        pairs.push((
            rhs_expr.clone(),
            DestructuringPlan::EqualityExpr(lhs_expr.clone()),
        ));
        return Ok(());
    }

    let lhs_is_array = matches!(lhs_expr.as_ref(), Expr::Array { .. });
    let rhs_is_array = matches!(rhs_expr.as_ref(), Expr::Array { .. });
    let lhs_is_object = matches!(lhs_expr.as_ref(), Expr::Object { .. });
    let rhs_is_object = matches!(rhs_expr.as_ref(), Expr::Object { .. });

    if (lhs_is_array && rhs_is_object) || (lhs_is_object && rhs_is_array) {
        return Err(BindingPlannerError::IncompatibleDestructuringPatterns {
            span: lhs_expr.span().clone(),
        });
    }

    if lhs_is_array && rhs_is_array {
        for (lhs_item, rhs_item) in collect_array_pairs(lhs_expr, rhs_expr)? {
            flatten_assignment_pairs(&lhs_item, &rhs_item, context, newly_bound, pairs)?;
        }
        return Ok(());
    }

    if lhs_is_object && rhs_is_object {
        if let Some(object_pairs) = collect_object_pairs(lhs_expr, rhs_expr)? {
            for (lhs_value, rhs_value) in object_pairs {
                flatten_assignment_pairs(&lhs_value, &rhs_value, context, newly_bound, pairs)?;
            }
            return Ok(());
        }
    }

    match (lhs_plan, rhs_plan, lhs_expr.as_ref(), rhs_expr.as_ref()) {
        // Case 1: LHS has pattern, RHS is value - add pair
        (Some(lhs_pattern), None, _, _) => {
            newly_bound.extend(lhs_delta);
            pairs.push((rhs_expr.clone(), lhs_pattern));
        }
        // Case 2: RHS has pattern, LHS is value - add pair
        (None, Some(rhs_pattern), _, _) => {
            newly_bound.extend(rhs_delta);
            pairs.push((lhs_expr.clone(), rhs_pattern));
        }
        // Case 5: Both have patterns but incompatible structures
        (Some(_), Some(_), _, _) => {
            return Err(BindingPlannerError::IncompatibleDestructuringPatterns {
                span: lhs_expr.span().clone(),
            });
        }
        // Remaining cases are handled by earlier match arms and guard
        (None, None, _, _) => {
            unreachable!("handled by equality guard above");
        }
    }

    Ok(())
}

fn collect_array_pairs(lhs_expr: &ExprRef, rhs_expr: &ExprRef) -> Result<Vec<(ExprRef, ExprRef)>> {
    let lhs_items = match lhs_expr.as_ref() {
        Expr::Array { items, .. } => items,
        _ => unreachable!(),
    };
    let rhs_items = match rhs_expr.as_ref() {
        Expr::Array { items, .. } => items,
        _ => unreachable!(),
    };

    if lhs_items.len() != rhs_items.len() {
        return Err(BindingPlannerError::ArraySizeMismatch {
            left_size: lhs_items.len(),
            right_size: rhs_items.len(),
            span: lhs_expr.span().clone(),
        });
    }

    Ok(lhs_items
        .iter()
        .cloned()
        .zip(rhs_items.iter().cloned())
        .collect())
}

fn order_element_pairs<T: VariableBindingContext>(
    element_pairs: &mut Vec<(ExprRef, DestructuringPlan)>,
    context: &T,
) {
    if element_pairs.len() <= 1 {
        return;
    }

    let mut remaining: Vec<_> = element_pairs
        .drain(..)
        .map(|(value_expr, plan)| {
            let binds = plan.bound_vars().into_iter().collect::<BTreeSet<_>>();
            let deps = collect_expr_dependencies(&value_expr);
            (value_expr, plan, deps, binds)
        })
        .collect();

    if remaining.iter().any(|(_, _, deps, _)| deps.is_none()) {
        *element_pairs = remaining
            .into_iter()
            .map(|(value_expr, plan, _, _)| (value_expr, plan))
            .collect();
        return;
    }

    let mut scheduled = BTreeSet::new();
    let mut ordered = Vec::with_capacity(remaining.len());

    while !remaining.is_empty() {
        let mut progress = false;

        for idx in 0..remaining.len() {
            let (_, _, deps, _) = &remaining[idx];
            let deps = deps.as_ref().expect("checked above");
            let ready = deps.iter().all(|var| {
                scheduled.contains(var) || !context.is_var_unbound(var, ScopingMode::RespectParent)
            });

            if ready {
                let (value_expr, plan, _deps, binds) = remaining.remove(idx);
                scheduled.extend(binds.into_iter());
                ordered.push((value_expr, plan));
                progress = true;
                break;
            }
        }

        if !progress {
            ordered.extend(
                remaining
                    .into_iter()
                    .map(|(value_expr, plan, _, _)| (value_expr, plan)),
            );
            break;
        }
    }

    *element_pairs = ordered;
}

fn collect_object_pairs(
    lhs_expr: &ExprRef,
    rhs_expr: &ExprRef,
) -> Result<Option<Vec<(ExprRef, ExprRef)>>> {
    let lhs_fields = match lhs_expr.as_ref() {
        Expr::Object { fields, .. } => fields,
        _ => unreachable!(),
    };
    let rhs_fields = match rhs_expr.as_ref() {
        Expr::Object { fields, .. } => fields,
        _ => unreachable!(),
    };

    let mut lhs_map: BTreeMap<Value, ExprRef> = BTreeMap::new();
    for (_, key_expr, val_expr) in lhs_fields {
        if let Some(key_value) = extract_literal_key(key_expr) {
            lhs_map.insert(key_value, val_expr.clone());
        } else {
            return Ok(None);
        }
    }

    let mut pairs = Vec::with_capacity(lhs_map.len());
    let mut rhs_literal_count = 0;
    let mut missing_literal_key: Option<(String, Span)> = None;

    for (_, key_expr, val_expr) in rhs_fields {
        if let Some(key_value) = extract_literal_key(key_expr) {
            rhs_literal_count += 1;

            if let Some(lhs_value_expr) = lhs_map.get(&key_value) {
                pairs.push((lhs_value_expr.clone(), val_expr.clone()));
            } else if missing_literal_key.is_none() {
                missing_literal_key = Some((
                    format_literal_key_for_error(&key_value),
                    key_expr.span().clone(),
                ));
            }
        } else {
            return Ok(None);
        }
    }

    if rhs_literal_count != lhs_map.len() {
        return Err(BindingPlannerError::ObjectFieldCountMismatch {
            left_count: lhs_map.len(),
            right_count: rhs_literal_count,
            span: lhs_expr.span().clone(),
        });
    }

    if let Some((key, span)) = missing_literal_key {
        return Err(BindingPlannerError::ObjectKeyNotFound { key, span });
    }

    Ok(Some(pairs))
}

fn preview_binding_plan<T: VariableBindingContext>(
    expr: &ExprRef,
    context: &T,
    scoping: ScopingMode,
    already_bound: &BTreeSet<String>,
) -> (Option<DestructuringPlan>, BTreeSet<String>) {
    let mut scratch = already_bound.clone();
    let plan = create_destructuring_plan_with_tracking(expr, context, scoping, &mut scratch);
    let mut delta: BTreeSet<String> = scratch.difference(already_bound).cloned().collect();
    let plan = plan_only_if_binds(plan);
    if plan.is_none() {
        delta.clear();
    }
    (plan, delta)
}

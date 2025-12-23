// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::unused_trait_names, clippy::pattern_type_mismatch)]

//! Core data structures used by the destructuring planner.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::ast::ExprRef;
use crate::lexer::Span;
use crate::value::Value;

/// Strategy for how to destructure an expression.
#[derive(Debug, Clone)]
pub enum DestructuringPlan {
    /// Bind the entire value to a variable.
    Var(Span),

    /// Ignore the value completely.
    Ignore,

    /// Check equality with the value of the dynamic expression.
    EqualityExpr(ExprRef),

    /// Check equality against a literal value captured at planning time.
    EqualityValue(Value),

    /// Destructure an array.
    Array {
        element_plans: Vec<DestructuringPlan>,
    },

    /// Destructure an object.
    Object {
        field_plans: BTreeMap<Value, DestructuringPlan>,
        dynamic_fields: Vec<(ExprRef, DestructuringPlan)>,
    },
}

impl DestructuringPlan {
    fn collect_bound_vars(&self, vars: &mut Vec<String>) {
        match self {
            DestructuringPlan::Var(name) => vars.push(name.text().to_string()),
            DestructuringPlan::Array { element_plans } => {
                for element in element_plans {
                    element.collect_bound_vars(vars);
                }
            }
            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            } => {
                for plan in field_plans.values() {
                    plan.collect_bound_vars(vars);
                }
                for (_, plan) in dynamic_fields {
                    plan.collect_bound_vars(vars);
                }
            }
            DestructuringPlan::Ignore
            | DestructuringPlan::EqualityExpr(_)
            | DestructuringPlan::EqualityValue(_) => {}
        }
    }

    pub(crate) fn contains_wildcards(&self) -> bool {
        match self {
            DestructuringPlan::Ignore => true,
            DestructuringPlan::Array { element_plans } => element_plans
                .iter()
                .any(DestructuringPlan::contains_wildcards),
            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            } => {
                field_plans
                    .values()
                    .any(DestructuringPlan::contains_wildcards)
                    || dynamic_fields
                        .iter()
                        .any(|(_, plan)| plan.contains_wildcards())
            }
            DestructuringPlan::Var(_)
            | DestructuringPlan::EqualityExpr(_)
            | DestructuringPlan::EqualityValue(_) => false,
        }
    }

    pub(crate) fn bound_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_bound_vars(&mut vars);
        vars
    }

    pub(crate) fn introduces_binding(&self) -> bool {
        match self {
            DestructuringPlan::Var(_) | DestructuringPlan::Ignore => true,
            DestructuringPlan::Array { element_plans } => element_plans
                .iter()
                .any(DestructuringPlan::introduces_binding),
            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            } => {
                field_plans
                    .values()
                    .any(DestructuringPlan::introduces_binding)
                    || dynamic_fields
                        .iter()
                        .any(|(_, plan)| plan.introduces_binding())
            }
            DestructuringPlan::EqualityExpr(_) | DestructuringPlan::EqualityValue(_) => false,
        }
    }
}

/// Strategy-based assignment plan with specific rules for := and = operators.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum AssignmentPlan {
    /// For := (ColEq) - only LHS can have patterns.
    ColonEquals {
        lhs_expr: ExprRef,
        rhs_expr: ExprRef,
        lhs_plan: DestructuringPlan,
    },

    /// For = (Eq) - only one side has unbound variables.
    EqualsBindLeft {
        lhs_expr: ExprRef,
        rhs_expr: ExprRef,
        lhs_plan: DestructuringPlan,
    },

    /// For = (Eq) - only one side has unbound variables.
    EqualsBindRight {
        lhs_expr: ExprRef,
        rhs_expr: ExprRef,
        rhs_plan: DestructuringPlan,
    },

    /// For = (Eq) - both sides have unbound vars, flattened to pairs.
    /// Each pair is (value_expr, destructuring_plan_for_pattern).
    EqualsBothSides {
        lhs_expr: ExprRef,
        rhs_expr: ExprRef,
        element_pairs: Vec<(ExprRef, DestructuringPlan)>,
    },

    /// No variables to bind - simple equality check.
    EqualityCheck {
        lhs_expr: ExprRef,
        rhs_expr: ExprRef,
    },

    /// No variables to bind and at least one side is a wildcard `_`.
    WildcardMatch {
        lhs_expr: ExprRef,
        rhs_expr: ExprRef,
        wildcard_side: WildcardSide,
    },
}

impl AssignmentPlan {
    pub(crate) fn bound_vars(&self) -> Vec<String> {
        match self {
            AssignmentPlan::ColonEquals { lhs_plan, .. }
            | AssignmentPlan::EqualsBindLeft { lhs_plan, .. } => lhs_plan.bound_vars(),
            AssignmentPlan::EqualsBindRight { rhs_plan, .. } => rhs_plan.bound_vars(),
            AssignmentPlan::EqualsBothSides { element_pairs, .. } => {
                let mut vars = Vec::new();
                for (_, plan) in element_pairs {
                    vars.extend(plan.bound_vars());
                }
                vars
            }
            AssignmentPlan::EqualityCheck { .. } | AssignmentPlan::WildcardMatch { .. } => {
                Vec::new()
            }
        }
    }
}

/// Indicates which side of an equality expression contains a wildcard `_`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum WildcardSide {
    Lhs,
    Rhs,
    Both,
}

/// High-level plan describing how bindings are produced in various contexts.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum BindingPlan {
    Assignment {
        plan: AssignmentPlan,
    },
    LoopIndex {
        index_expr: ExprRef,
        destructuring_plan: DestructuringPlan,
    },
    Parameter {
        param_expr: ExprRef,
        destructuring_plan: DestructuringPlan,
    },
    SomeIn {
        collection_expr: ExprRef,
        key_plan: Option<DestructuringPlan>,
        value_plan: DestructuringPlan,
    },
}

impl BindingPlan {
    /// Return the set of variables newly bound by this plan.
    pub fn bound_vars(&self) -> Vec<String> {
        match self {
            BindingPlan::Assignment { plan } => plan.bound_vars(),
            BindingPlan::LoopIndex {
                destructuring_plan, ..
            } => destructuring_plan.bound_vars(),
            BindingPlan::Parameter {
                destructuring_plan, ..
            } => destructuring_plan.bound_vars(),
            BindingPlan::SomeIn {
                key_plan,
                value_plan,
                ..
            } => {
                let mut vars = Vec::new();
                if let Some(key_destructuring) = key_plan {
                    vars.extend(key_destructuring.bound_vars());
                }
                vars.extend(value_plan.bound_vars());
                vars
            }
        }
    }
}

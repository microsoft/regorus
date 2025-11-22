// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Literal, LiteralStmt};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::RuleAnalysis;
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StatementTruth {
    AlwaysTrue,
    AlwaysFalse,
    Unknown,
}

impl TypeAnalyzer {
    pub(crate) fn analyze_stmt(
        &self,
        module_idx: u32,
        stmt: &LiteralStmt,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> StatementTruth {
        match &stmt.literal {
            Literal::SomeVars { .. } => {
                // Hoisted loops manage these bindings via binding plans.
                StatementTruth::Unknown
            }
            Literal::SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                let coll_fact =
                    self.infer_expr(module_idx, collection, bindings, result, rule_analysis);

                let mut truth = StatementTruth::Unknown;
                if let Some(const_value) = coll_fact.fact.constant.as_value() {
                    if collection_is_definitely_empty(const_value) {
                        truth = StatementTruth::AlwaysFalse;
                    }
                }

                if let Some(const_value) = coll_fact.fact.constant.as_value() {
                    result.constants.record(
                        module_idx,
                        collection.eidx(),
                        Some(const_value.clone()),
                    );
                }

                if let Some(k) = key {
                    let _ = self.infer_expr(module_idx, k, bindings, result, rule_analysis);
                }
                let _ = self.infer_expr(module_idx, value, bindings, result, rule_analysis);
                truth
            }
            Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
                let hybrid = self.infer_expr(module_idx, expr, bindings, result, rule_analysis);
                if matches!(stmt.literal, Literal::Expr { .. }) {
                    truth_from_positive_literal(expr, hybrid.fact.constant.as_value())
                } else {
                    truth_from_negated_literal(hybrid.fact.constant.as_value())
                }
            }
            Literal::Every { domain, query, .. } => {
                self.infer_expr(module_idx, domain, bindings, result, rule_analysis);
                bindings.push_scope();
                let _ =
                    self.analyze_query(module_idx, query, bindings, result, rule_analysis, true);
                bindings.pop_scope();
                StatementTruth::Unknown
            }
        }
    }
}

fn truth_from_positive_literal(expr: &Expr, constant: Option<&Value>) -> StatementTruth {
    if matches!(expr, Expr::AssignExpr { .. }) {
        // Unification statements can still succeed even when RHS is false.
        return StatementTruth::Unknown;
    }

    constant
        .and_then(|value| value.as_bool().ok().copied())
        .map(|flag| {
            if flag {
                StatementTruth::AlwaysTrue
            } else {
                StatementTruth::AlwaysFalse
            }
        })
        .unwrap_or(StatementTruth::Unknown)
}

fn truth_from_negated_literal(constant: Option<&Value>) -> StatementTruth {
    constant
        .and_then(|value| value.as_bool().ok().copied())
        .map(|flag| {
            if flag {
                StatementTruth::AlwaysFalse
            } else {
                StatementTruth::AlwaysTrue
            }
        })
        .unwrap_or(StatementTruth::Unknown)
}

fn collection_is_definitely_empty(value: &Value) -> bool {
    match value {
        Value::Array(items) => items.is_empty(),
        Value::Set(items) => items.is_empty(),
        Value::Object(fields) => fields.is_empty(),
        _ => false,
    }
}

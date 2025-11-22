// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::compiler::destructuring_planner::{AssignmentPlan, BindingPlan};

use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{RuleAnalysis, TypeFact};

use super::super::pipeline::{AnalysisState, TypeAnalyzer};

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn apply_binding_plan(
        &self,
        module_idx: u32,
        _expr: &crate::ast::Ref<crate::ast::Expr>,
        plan: &BindingPlan,
        current_fact: &TypeFact,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) {
        match plan {
            BindingPlan::Assignment { plan } => {
                self.apply_assignment_plan(module_idx, plan, bindings, result, rule_analysis);
            }
            BindingPlan::LoopIndex {
                destructuring_plan, ..
            } => {
                self.apply_destructuring_plan(
                    module_idx,
                    destructuring_plan,
                    current_fact,
                    bindings,
                    result,
                    rule_analysis,
                );
            }
            BindingPlan::Parameter {
                param_expr,
                destructuring_plan,
            } => {
                let expr_idx = param_expr.eidx();
                self.ensure_expr_capacity(module_idx, expr_idx, result);
                result
                    .lookup
                    .record_expr(module_idx, expr_idx, current_fact.clone());

                self.apply_destructuring_plan(
                    module_idx,
                    destructuring_plan,
                    current_fact,
                    bindings,
                    result,
                    rule_analysis,
                );
            }
            BindingPlan::SomeIn {
                key_plan,
                value_plan,
                ..
            } => {
                let iteration = self.build_iteration_facts(current_fact);
                if let Some(key_plan) = key_plan {
                    if let Some(key_fact) = iteration.key_fact.as_ref() {
                        self.apply_destructuring_plan(
                            module_idx,
                            key_plan,
                            key_fact,
                            bindings,
                            result,
                            rule_analysis,
                        );
                    }
                }
                self.apply_destructuring_plan(
                    module_idx,
                    value_plan,
                    &iteration.value_fact,
                    bindings,
                    result,
                    rule_analysis,
                );
            }
        }
    }

    pub(super) fn apply_assignment_plan(
        &self,
        module_idx: u32,
        plan: &AssignmentPlan,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) {
        use AssignmentPlan::*;

        match plan {
            ColonEquals {
                lhs_expr,
                rhs_expr,
                lhs_plan,
            }
            | EqualsBindLeft {
                lhs_plan,
                lhs_expr,
                rhs_expr,
            } => {
                let rhs_fact = self
                    .infer_expr(module_idx, rhs_expr, bindings, result, rule_analysis)
                    .fact;
                self.apply_destructuring_plan(
                    module_idx,
                    lhs_plan,
                    &rhs_fact,
                    bindings,
                    result,
                    rule_analysis,
                );
                let _ = self.infer_expr(module_idx, lhs_expr, bindings, result, rule_analysis);
            }
            EqualsBindRight {
                rhs_plan,
                lhs_expr,
                rhs_expr,
            } => {
                let lhs_fact = self
                    .infer_expr(module_idx, lhs_expr, bindings, result, rule_analysis)
                    .fact;
                self.apply_destructuring_plan(
                    module_idx,
                    rhs_plan,
                    &lhs_fact,
                    bindings,
                    result,
                    rule_analysis,
                );
                let _ = self.infer_expr(module_idx, rhs_expr, bindings, result, rule_analysis);
            }
            EqualsBothSides { element_pairs, .. } => {
                for (value_expr, element_plan) in element_pairs {
                    let value_fact = self
                        .infer_expr(module_idx, value_expr, bindings, result, rule_analysis)
                        .fact;
                    self.apply_destructuring_plan(
                        module_idx,
                        element_plan,
                        &value_fact,
                        bindings,
                        result,
                        rule_analysis,
                    );
                }
            }
            EqualityCheck {
                lhs_expr, rhs_expr, ..
            }
            | WildcardMatch {
                lhs_expr, rhs_expr, ..
            } => {
                let _ = self.infer_expr(module_idx, lhs_expr, bindings, result, rule_analysis);
                let _ = self.infer_expr(module_idx, rhs_expr, bindings, result, rule_analysis);
            }
        }
    }
}

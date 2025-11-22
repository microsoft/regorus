// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::boxed::Box;

use crate::ast::{Expr, LiteralStmt, Ref};
use crate::compiler::hoist::{HoistedLoop, LoopType};

use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};

use super::super::pipeline::{TypeAnalysisResult, TypeAnalyzer};

impl TypeAnalyzer {
    pub(crate) fn seed_statement_loops(
        &self,
        module_idx: u32,
        stmt: &LiteralStmt,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) {
        let Some(loop_lookup) = self.loop_lookup.as_ref() else {
            return;
        };

        if let Some(loops) = loop_lookup.get_statement_loops(module_idx, stmt.sidx) {
            for loop_info in loops {
                self.process_hoisted_loop(module_idx, loop_info, bindings, result, rule_analysis);
            }
        }
    }

    pub(crate) fn process_hoisted_loop(
        &self,
        module_idx: u32,
        loop_info: &HoistedLoop,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) {
        match loop_info.loop_type {
            LoopType::IndexIteration => {
                let collection_ty = self.infer_expr(
                    module_idx,
                    &loop_info.collection,
                    bindings,
                    result,
                    rule_analysis,
                );

                let iteration = self.build_iteration_facts(&collection_ty.fact);

                if let Some(key_expr) = &loop_info.key {
                    if let Some(key_fact) = iteration.key_fact.as_ref() {
                        self.seed_expr_with_fact(
                            module_idx,
                            key_expr,
                            key_fact.clone(),
                            bindings,
                            result,
                            rule_analysis,
                        );
                    }
                }

                self.seed_expr_with_fact(
                    module_idx,
                    &loop_info.value,
                    iteration.value_fact.clone(),
                    bindings,
                    result,
                    rule_analysis,
                );

                if let Some(loop_expr) = &loop_info.loop_expr {
                    if loop_expr.eidx() != loop_info.value.eidx() {
                        self.seed_expr_with_fact(
                            module_idx,
                            loop_expr,
                            iteration.value_fact.clone(),
                            bindings,
                            result,
                            rule_analysis,
                        );
                    }
                }
            }
            LoopType::Walk => {
                let fact = TypeFact::new(
                    TypeDescriptor::Structural(StructuralType::Array(Box::new(
                        StructuralType::Any,
                    ))),
                    TypeProvenance::Propagated,
                );
                self.seed_expr_with_fact(
                    module_idx,
                    &loop_info.value,
                    fact,
                    bindings,
                    result,
                    rule_analysis,
                );
            }
        }
    }

    pub(crate) fn seed_expr_with_fact(
        &self,
        module_idx: u32,
        expr: &Ref<Expr>,
        fact: TypeFact,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) {
        let eidx = expr.eidx();

        if let Some(existing) = result.lookup.get_expr(module_idx, eidx).cloned() {
            if let Some(loop_lookup) = self.loop_lookup.as_ref() {
                if let Some(plan) = loop_lookup.get_expr_binding_plan(module_idx, eidx) {
                    self.apply_binding_plan(
                        module_idx,
                        expr,
                        plan,
                        &existing,
                        bindings,
                        result,
                        rule_analysis,
                    );
                }
            }
            return;
        }

        self.ensure_expr_capacity(module_idx, eidx, result);
        result.lookup.record_expr(module_idx, eidx, fact.clone());

        if let ConstantValue::Known(value) = &fact.constant {
            result
                .constants
                .record(module_idx, eidx, Some(value.clone()));
        }

        if !fact.origins.is_empty() {
            rule_analysis.record_origins(&fact.origins);
        }

        if let Some(loop_lookup) = self.loop_lookup.as_ref() {
            if let Some(plan) = loop_lookup.get_expr_binding_plan(module_idx, eidx) {
                self.apply_binding_plan(
                    module_idx,
                    expr,
                    plan,
                    &fact,
                    bindings,
                    result,
                    rule_analysis,
                );
            }
        }
    }
}

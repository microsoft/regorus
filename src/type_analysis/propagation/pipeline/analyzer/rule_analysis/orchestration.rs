// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;

use crate::ast::{Expr, Module, Rule, RuleHead};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{RuleAnalysis, StructuralType, TypeDescriptor, TypeProvenance};
use crate::utils::get_path_string;

use super::super::super::result::AnalysisState;
use super::super::TypeAnalyzer;

impl TypeAnalyzer {
    pub(crate) fn analyze_module(
        &self,
        module_idx: u32,
        module: &crate::ast::Ref<Module>,
        result: &mut AnalysisState,
    ) {
        for (rule_idx, _) in module.policy.iter().enumerate() {
            self.ensure_rule_analyzed(module_idx, rule_idx, result);
        }
    }

    pub(super) fn analyze_rule(
        &self,
        module_idx: u32,
        rule_idx: usize,
        rule: &crate::ast::Ref<Rule>,
        result: &mut AnalysisState,
    ) {
        let mut aggregate = RuleAnalysis::default();

        // Check if this is a function rule (has parameters)
        let is_function_rule = matches!(
            rule.as_ref(),
            Rule::Spec {
                head: RuleHead::Func { .. },
                ..
            }
        );

        if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
            if let Expr::Var { .. } = refr.as_ref() {
                let module = &self.modules[module_idx as usize];
                let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
                    .unwrap_or_else(|_| "data".to_owned());

                if let Ok(var_path) = get_path_string(refr.as_ref(), Some(&module_path)) {
                    result.ensure_rule_capacity(module_idx, rule_idx + 1);
                    let current_state =
                        &result.rule_info[module_idx as usize][rule_idx].constant_state;

                    if matches!(
                        current_state,
                        crate::type_analysis::RuleConstantState::Unknown
                    ) {
                        result.rule_info[module_idx as usize][rule_idx].constant_state =
                            crate::type_analysis::RuleConstantState::InProgress;

                        // Skip constant folding for function rules - they need arguments
                        if !is_function_rule {
                            if let Some(value) =
                                self.try_evaluate_rule_constant(module_idx, &var_path)
                            {
                                aggregate.constant_state =
                                    crate::type_analysis::RuleConstantState::Done(value);
                            } else {
                                aggregate.constant_state =
                                    crate::type_analysis::RuleConstantState::NeedsRuntime;
                            }
                        } else {
                            // Function rules always need runtime (arguments)
                            aggregate.constant_state =
                                crate::type_analysis::RuleConstantState::NeedsRuntime;
                        }
                    }
                }
            }
        }

        match rule.as_ref() {
            Rule::Spec { head, bodies, .. } => {
                if bodies.is_empty() {
                    self.analyze_rule_head_without_body(module_idx, head, result, &mut aggregate);
                } else {
                    let last_body_index = bodies.len() - 1;
                    for (body_idx, body) in bodies.iter().enumerate() {
                        let mut body_analysis = RuleAnalysis::default();
                        self.analyze_rule_body(
                            module_idx,
                            rule_idx,
                            body_idx,
                            head,
                            body,
                            result,
                            &mut body_analysis,
                            body_idx == last_body_index,
                        );
                        aggregate.merge(body_analysis);
                    }
                }
            }
            Rule::Default { refr, value, .. } => {
                self.ensure_expr_capacity(module_idx, value.eidx(), result);
                let mut bindings = ScopedBindings::new();
                bindings.ensure_root_scope();
                let fact =
                    self.infer_expr(module_idx, value, &mut bindings, result, &mut aggregate);
                aggregate.record_origins(&fact.fact.origins);

                self.ensure_expr_capacity(module_idx, refr.eidx(), result);
                Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact.fact.clone());
            }
        }

        if let crate::type_analysis::RuleConstantState::Done(value) = &aggregate.constant_state {
            if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                let expr_idx = refr.eidx();
                self.ensure_expr_capacity(module_idx, expr_idx, result);

                let mut constant_fact =
                    crate::type_analysis::value_utils::value_to_type_fact(value);
                constant_fact.provenance = TypeProvenance::Rule;

                let slot = result.lookup.expr_types_mut().get_mut(module_idx, expr_idx);
                match slot {
                    Some(existing) => {
                        existing.constant =
                            crate::type_analysis::ConstantValue::Known(value.clone());

                        if should_replace_descriptor(
                            &existing.descriptor,
                            &constant_fact.descriptor,
                        ) {
                            existing.descriptor = constant_fact.descriptor.clone();
                        }

                        if matches!(existing.provenance, TypeProvenance::Unknown) {
                            existing.provenance = TypeProvenance::Rule;
                        }
                    }
                    None => {
                        *slot = Some(constant_fact);
                    }
                }

                result
                    .constants
                    .record(module_idx, expr_idx, Some(value.clone()));
            }
        }

        result.record_rule_analysis(module_idx, rule_idx, aggregate);
    }

    pub(crate) fn ensure_rule_analyzed(
        &self,
        module_idx: u32,
        rule_idx: usize,
        result: &mut AnalysisState,
    ) {
        let has_rule_info = result
            .rule_info
            .get(module_idx as usize)
            .and_then(|rules| rules.get(rule_idx))
            .map(|analysis| {
                !matches!(
                    analysis.constant_state,
                    crate::type_analysis::RuleConstantState::Unknown
                )
            })
            .unwrap_or(false);

        let has_expr_type = if let Some(module) = self.modules.get(module_idx as usize) {
            if let Some(rule) = module.policy.get(rule_idx) {
                if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                    result.lookup.get_expr(module_idx, refr.eidx()).is_some()
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        };

        if has_rule_info || has_expr_type {
            return;
        }

        if self.is_rule_on_stack(module_idx, rule_idx) {
            result.ensure_rule_capacity(module_idx, rule_idx + 1);
            result.rule_info[module_idx as usize][rule_idx].constant_state =
                crate::type_analysis::RuleConstantState::NeedsRuntime;
            return;
        }

        if let Some(module) = self.modules.get(module_idx as usize) {
            if let Some(rule) = module.policy.get(rule_idx) {
                if Self::rule_requires_arguments(rule.as_ref())
                    && !self
                        .function_param_facts
                        .borrow()
                        .contains_key(&(module_idx, rule_idx))
                {
                    result.ensure_rule_capacity(module_idx, rule_idx + 1);
                    let entry = &mut result.rule_info[module_idx as usize][rule_idx];
                    if matches!(
                        entry.constant_state,
                        crate::type_analysis::RuleConstantState::Unknown
                    ) {
                        entry.constant_state =
                            crate::type_analysis::RuleConstantState::NeedsRuntime;
                    }
                    return;
                }

                let rule_path =
                    if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                        if let Expr::Var { .. } = refr.as_ref() {
                            let module_path =
                                get_path_string(module.package.refr.as_ref(), Some("data"))
                                    .unwrap_or_else(|_| "data".to_owned());

                            let var_path = get_path_string(refr.as_ref(), Some(&module_path))
                                .unwrap_or_else(|_| "unknown".to_owned());

                            Some(var_path)
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                if let Some(ref path) = rule_path {
                    if self.entrypoint_filtering {
                        result.lookup.mark_reachable(path.clone());
                    }
                    result.lookup.set_current_rule(Some(path.clone()));
                }

                self.push_rule_stack(module_idx, rule_idx);
                self.analyze_rule(module_idx, rule_idx, rule, result);
                self.pop_rule_stack();

                result.lookup.set_current_rule(None);
            }
        }
    }

    fn is_rule_on_stack(&self, module_idx: u32, rule_idx: usize) -> bool {
        self.analysis_stack
            .borrow()
            .contains(&(module_idx, rule_idx))
    }

    fn push_rule_stack(&self, module_idx: u32, rule_idx: usize) {
        self.analysis_stack
            .borrow_mut()
            .push((module_idx, rule_idx));
    }

    fn pop_rule_stack(&self) {
        self.analysis_stack.borrow_mut().pop();
    }

    fn rule_requires_arguments(rule: &Rule) -> bool {
        matches!(
            rule,
            Rule::Spec {
                head: RuleHead::Func { .. },
                ..
            }
        )
    }
}

fn should_replace_descriptor(existing: &TypeDescriptor, replacement: &TypeDescriptor) -> bool {
    match (existing, replacement) {
        (TypeDescriptor::Structural(StructuralType::Any), _)
        | (TypeDescriptor::Structural(StructuralType::Unknown), _) => true,
        (
            TypeDescriptor::Structural(StructuralType::Array(existing_inner)),
            TypeDescriptor::Structural(StructuralType::Array(replacement_inner)),
        ) => {
            is_unknownish(existing_inner)
                || (!is_unknownish(replacement_inner)
                    && existing_inner.as_ref() != replacement_inner.as_ref())
        }
        (
            TypeDescriptor::Structural(StructuralType::Set(existing_inner)),
            TypeDescriptor::Structural(StructuralType::Set(replacement_inner)),
        ) => {
            is_unknownish(existing_inner)
                || (!is_unknownish(replacement_inner)
                    && existing_inner.as_ref() != replacement_inner.as_ref())
        }
        _ => false,
    }
}

fn is_unknownish(ty: &StructuralType) -> bool {
    matches!(ty, StructuralType::Any | StructuralType::Unknown)
}

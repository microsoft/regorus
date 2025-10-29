// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::ast::Expr;
use crate::type_analysis::model::{RuleAnalysis, TypeFact};
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::utils::path::{normalize_rule_path, AccessComponent, ReferenceChain};
use crate::value::Value;

impl TypeAnalyzer {
    pub(crate) fn try_resolve_rule_property(
        &self,
        module_idx: u32,
        expr_idx: u32,
        base_expr: &Expr,
        field_value: &Value,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> Option<TypeFact> {
        let field_name = match field_value.as_string() {
            Ok(name) => name,
            Err(_) => return None,
        };

        let reference = build_reference_chain(base_expr)?;
        let static_prefix = reference.static_prefix();
        if static_prefix.is_empty() || static_prefix[0] != "data" || static_prefix.len() < 2 {
            return None;
        }

        let base_path = static_prefix.join(".");
        let candidate_path = normalize_rule_path(&format!("{base_path}.{}", field_name.as_ref()));

        let current_rule_info = result.lookup.current_rule().map(|path| {
            let normalized = normalize_rule_path(path);
            let base = normalized
                .strip_suffix(".default")
                .unwrap_or(&normalized)
                .to_owned();
            (normalized, base)
        });

        let mut collected_facts = Vec::new();
        let mut processed_paths: BTreeSet<String> = BTreeSet::new();
        for info in self.rule_heads_for_name(module_idx, field_name.as_ref()) {
            let normalized_path = normalize_rule_path(&info.path);
            if normalized_path != candidate_path {
                continue;
            }

            let dependency_base = normalized_path
                .strip_suffix(".default")
                .unwrap_or(normalized_path.as_str());
            if let Some((current_norm, current_base)) = current_rule_info.as_ref() {
                if normalized_path == *current_norm || dependency_base == current_base.as_str() {
                    continue;
                }
            }

            let first_encounter = processed_paths.insert(normalized_path.clone());

            if first_encounter {
                result
                    .lookup
                    .record_rule_reference(module_idx, expr_idx, normalized_path.clone());
                rule_analysis.record_rule_dependency(normalized_path.clone());
            }

            let mut head_fact = result
                .lookup
                .get_expr(info.module_idx, info.expr_idx)
                .cloned();

            if head_fact.is_none() {
                if let Some(module) = self.modules.get(info.module_idx as usize) {
                    for (rule_idx, rule) in module.policy.iter().enumerate() {
                        if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                            if refr.eidx() == info.expr_idx {
                                self.ensure_rule_analyzed(info.module_idx, rule_idx, result);
                                head_fact = result
                                    .lookup
                                    .get_expr(info.module_idx, info.expr_idx)
                                    .cloned();
                                break;
                            }
                        }
                    }
                }
            }

            if let Some(fact) = head_fact {
                collected_facts.push(fact);
            }
        }

        if collected_facts.is_empty() {
            None
        } else {
            Some(Self::merge_rule_facts(&collected_facts))
        }
    }
}

fn build_reference_chain(expr: &Expr) -> Option<ReferenceChain> {
    let mut components: Vec<AccessComponent> = Vec::new();
    let mut current = expr;

    loop {
        match current {
            Expr::RefDot { refr, field, .. } => {
                let (_, field_value) = field.as_ref()?;
                let field_name = field_value.as_string().ok()?.as_ref().to_owned();
                components.push(AccessComponent::Field(field_name));
                current = refr.as_ref();
            }
            Expr::RefBrack { refr, .. } => {
                components.push(AccessComponent::Dynamic);
                current = refr.as_ref();
            }
            Expr::Var { value, .. } => {
                let root = value.as_string().ok()?.as_ref().to_owned();
                components.reverse();
                return Some(ReferenceChain { root, components });
            }
            _ => return None,
        }
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::type_analysis::model::{
    RuleAnalysis, RuleSpecializationSignature, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::pipeline::{RuleHeadInfo, TypeAnalysisResult, TypeAnalyzer};
use crate::type_analysis::result::RuleSpecializationRecord;
use crate::type_analysis::value_utils;
use crate::type_analysis::RuleConstantState;
use crate::utils::path::normalize_rule_path;
use crate::value::Value;

pub(crate) fn apply_rule_call_effects(
    analyzer: &TypeAnalyzer,
    module_idx: u32,
    expr_idx: u32,
    filtered_targets: Vec<RuleHeadInfo>,
    call_arg_facts: Vec<TypeFact>,
    result: &mut TypeAnalysisResult,
    rule_analysis: &mut RuleAnalysis,
) -> Vec<TypeFact> {
    let current_rule_info = result.lookup.current_rule().map(|path| {
        let normalized = normalize_rule_path(path);
        let base = normalized
            .strip_suffix(".default")
            .unwrap_or(&normalized)
            .to_owned();
        (normalized, base)
    });

    let mut collected_facts = Vec::new();
    let mut seen_paths: BTreeSet<String> = BTreeSet::new();

    for info in filtered_targets {
        let normalized_path = normalize_rule_path(&info.path);
        if !seen_paths.insert(normalized_path.clone()) {
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

        result
            .lookup
            .record_rule_reference(module_idx, expr_idx, normalized_path.clone());
        rule_analysis.record_rule_dependency(normalized_path.clone());

        let mut scratch_result = TypeAnalysisResult::new();
        let previous_param_facts = analyzer.prepare_function_rule_specialization(
            info.module_idx,
            info.rule_idx,
            &call_arg_facts,
            &mut scratch_result,
        );
        analyzer.ensure_rule_analyzed(info.module_idx, info.rule_idx, &mut scratch_result);
        analyzer.restore_function_rule_specialization(
            info.module_idx,
            info.rule_idx,
            previous_param_facts,
        );

        if !scratch_result.diagnostics.is_empty() {
            result.diagnostics.append(&mut scratch_result.diagnostics);
        }

        let head_fact = scratch_result
            .lookup
            .get_expr(info.module_idx, info.expr_idx)
            .cloned();

        let mut constant_fact: Option<TypeFact> = None;
        let mut constant_value: Option<Value> = None;
        if let Some(rule_entry) = scratch_result
            .rule_info
            .get(info.module_idx as usize)
            .and_then(|rules| rules.get(info.rule_idx))
        {
            if let RuleConstantState::Done(value) = &rule_entry.constant_state {
                let mut fact = value_utils::value_to_type_fact(value);
                fact.provenance = TypeProvenance::Rule;
                if let Some(existing) = head_fact.as_ref() {
                    if !existing.origins.is_empty() {
                        fact = fact.with_origins(existing.origins.clone());
                    }
                }
                constant_value = Some(value.clone());
                constant_fact = Some(fact);
            }
        }

        let record_head_fact = constant_fact.clone().or(head_fact.clone());
        let expr_facts = collect_specialization_expr_facts(&scratch_result);

        let record = RuleSpecializationRecord {
            signature: RuleSpecializationSignature::from_facts(
                info.module_idx,
                info.rule_idx,
                &call_arg_facts,
            ),
            parameter_facts: call_arg_facts.clone(),
            head_fact: record_head_fact.clone(),
            constant_value: constant_value.clone(),
            expr_facts,
            trace: None,
        };
        result.record_function_specialization(record);

        if let Some(fact) = constant_fact {
            collected_facts.push(fact);
            continue;
        }

        if let Some(fact) = head_fact {
            collected_facts.push(fact);
        }
    }

    collected_facts
}

pub(crate) fn collect_specialization_expr_facts(
    scratch: &TypeAnalysisResult,
) -> BTreeMap<u32, BTreeMap<u32, TypeFact>> {
    let mut modules: BTreeMap<u32, BTreeMap<u32, TypeFact>> = BTreeMap::new();

    for (module_idx, module_slots) in scratch.lookup.expr_types().modules().iter().enumerate() {
        let mut expr_map: BTreeMap<u32, TypeFact> = BTreeMap::new();
        for (expr_idx, slot) in module_slots.iter().enumerate() {
            if let Some(fact) = slot {
                expr_map.insert(expr_idx as u32, fact.clone());
            }
        }

        if !expr_map.is_empty() {
            modules.insert(module_idx as u32, expr_map);
        }
    }

    modules
}

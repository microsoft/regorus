// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Materialization of causality reports from static metadata + runtime trace.
//!
//! This module combines the compile-time `StaticConditionInfo` from
//! [`crate::static_provenance`] with the runtime [`crate::evaluation_trace::EvaluationTrace`]
//! to produce the final [`CausalityReport`] JSON output.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use serde::Serialize;

use crate::evaluation_trace::{
    AssumptionKind, ConditionMode, ConditionOutcome, EvaluationTrace, ExplanationDetail,
    ExplanationScope, ExplanationSettings, RuleOutcome, ValueMode,
};
use crate::rvm::program::Program;
use crate::static_provenance::{Provenance, ProvenanceRoot};
use crate::value::Value;

// ---------------------------------------------------------------------------
// Redaction
// ---------------------------------------------------------------------------

/// Field names that are redacted when value_mode is Redacted.
const SENSITIVE_FIELDS: &[&str] = &[
    "password",
    "secret",
    "token",
    "api_key",
    "apikey",
    "api-key",
    "jwt",
    "credential",
    "private_key",
    "privatekey",
    "access_key",
    "accesskey",
];

fn should_redact_path(provenance: Option<&Provenance>) -> bool {
    let Some(prov) = provenance else {
        return false;
    };
    for seg in &prov.segments {
        if let crate::static_provenance::Segment::Field(ref name) = *seg {
            let lower = str::to_ascii_lowercase(name);
            for sensitive in SENSITIVE_FIELDS {
                if lower.contains(sensitive) {
                    return true;
                }
            }
        }
    }
    false
}

fn should_redact_runtime_path(path: Option<&str>) -> bool {
    let Some(path) = path else {
        return false;
    };

    let lower = path.to_ascii_lowercase();
    SENSITIVE_FIELDS.iter().any(|field| lower.contains(field))
}

fn assumed_input_path_for_pc(trace: &EvaluationTrace, pc: u32) -> Option<String> {
    trace
        .assumptions
        .iter()
        .find(|assumption| assumption.pc == pc)
        .map(|assumption| assumption.input_path.clone())
}

fn operand_provenance_for_output(
    runtime_path: Option<&str>,
    static_provenance: Option<&Provenance>,
    outcome: &ConditionOutcome,
    trace: &EvaluationTrace,
) -> Option<String> {
    if let Some(path) = runtime_path {
        return Some(path.to_string());
    }

    if outcome.assumed
        && matches!(
            static_provenance.map(|provenance| &provenance.root),
            Some(ProvenanceRoot::RuleResult { .. })
        )
    {
        if let Some(path) = assumed_input_path_for_pc(trace, outcome.pc) {
            return Some(path);
        }
    }

    static_provenance.map(|provenance| provenance.to_string())
}

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

/// Top-level causality report.
#[derive(Debug, Clone, Serialize)]
pub struct CausalityReport {
    /// The value returned by the evaluated query.
    pub query_result: Value,
    /// Per-rule explanation details.
    pub rules: Vec<RuleExplanation>,
    /// Assumptions made when unknown input handling was active.
    pub assumptions: Vec<AssumptionRecord>,
}

/// Explanation for a single rule.
#[derive(Debug, Clone, Serialize)]
pub struct RuleExplanation {
    /// Fully-qualified rule name, e.g. `"data.test.allow"`.
    pub name: String,
    /// Rule type.
    #[serde(rename = "type")]
    pub rule_type: String,
    /// Final result of the rule.
    pub result: Value,
    /// Per-emission explanations for partial-set rules.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub emissions: Vec<EmissionExplanation>,
    /// Explanations for each definition that was evaluated.
    pub definitions: Vec<DefinitionExplanation>,
}

/// Explanation for a single emitted partial-set value.
#[derive(Debug, Clone, Serialize)]
pub struct EmissionExplanation {
    /// Stable 0-based index of this materialized emission within the rule.
    pub index: usize,
    /// Definition that produced this value.
    pub definition_index: u16,
    /// The emitted value.
    pub result: Value,
    /// Conditions active when the value was emitted.
    pub conditions: Vec<ConditionExplanation>,
}

/// Explanation for a single rule definition body.
#[derive(Debug, Clone, Serialize)]
pub struct DefinitionExplanation {
    /// 0-based definition index within the rule.
    pub index: u16,
    /// Whether this definition succeeded or failed.
    pub outcome: String,
    /// Source location of the definition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Condition evaluations within this definition.
    pub conditions: Vec<ConditionExplanation>,
}

/// A single condition evaluation.
#[derive(Debug, Clone, Serialize)]
pub struct ConditionExplanation {
    /// Source text of the condition.
    pub text: String,
    /// `"success"`, `"failure"`, or `"assumed"`.
    pub outcome: String,
    /// Source location.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Condition kind (comparison, existence, truthiness, etc.).
    pub kind: String,
    /// Operator (for comparisons).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// Left / actual operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub left: Option<OperandExplanation>,
    /// Right / expected operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub right: Option<OperandExplanation>,
    /// Loop or quantifier witness summary, when available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub witness: Option<LoopWitnessExplanation>,
    /// For binding conditions (`:=`): the variable name being bound.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binding_name: Option<String>,
}

/// Witness summary for a loop-backed condition.
#[derive(Debug, Clone, Serialize)]
pub struct LoopWitnessExplanation {
    pub total_iterations: u32,
    pub success_count: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_key: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_value: Option<Value>,
}

/// An operand value with optional provenance.
#[derive(Debug, Clone, Serialize)]
pub struct OperandExplanation {
    /// The runtime value (may be redacted).
    pub value: Value,
    /// Data path, e.g. `"input.role"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provenance: Option<String>,
    /// Whether the value was redacted.
    pub redacted: bool,
}

/// Source location.
#[derive(Debug, Clone, Serialize)]
pub struct SourceLocation {
    pub file: String,
    pub row: usize,
    pub col: usize,
}

/// A recorded assumption for the output.
#[derive(Debug, Clone, Serialize)]
pub struct AssumptionRecord {
    /// Kind of assumption.
    pub kind: String,
    /// Input path that was assumed.
    pub input_path: String,
    /// Condition text that was assumed to hold.
    pub assumed_holds: String,
    /// The comparison operator (e.g. "==", "!="), if applicable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// The non-input value that was compared against.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assumed_value: Option<Value>,
    /// Source location.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

// ---------------------------------------------------------------------------
// Materialization
// ---------------------------------------------------------------------------

/// Produce a [`CausalityReport`] from a program and its evaluation trace.
pub fn materialize(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    query_result: Value,
) -> CausalityReport {
    let rules = materialize_rules(program, trace, settings);
    let assumptions = if settings.detail == ExplanationDetail::Compact {
        Vec::new()
    } else {
        materialize_assumptions(program, trace)
    };

    CausalityReport {
        query_result,
        rules,
        assumptions,
    }
}

fn materialize_rules(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<RuleExplanation> {
    // Group rule outcomes by rule_index.
    let mut rules: Vec<RuleExplanation> = Vec::new();

    // Collect unique rule indices from outcomes.
    let mut seen_rules: Vec<u16> = Vec::new();
    for outcome in &trace.rule_outcomes {
        if !seen_rules.contains(&outcome.rule_index) {
            seen_rules.push(outcome.rule_index);
        }
    }

    for rule_idx in &seen_rules {
        let rule_info = match program.rule_infos.get(usize::from(*rule_idx)) {
            Some(info) => info,
            None => continue,
        };

        // Find the final result for this rule.
        let result = trace
            .rule_outcomes
            .iter()
            .rev()
            .find(|o| o.rule_index == *rule_idx && o.succeeded)
            .and_then(|o| o.result_value_idx)
            .and_then(|idx| trace.get_value(idx))
            .cloned()
            .unwrap_or(Value::Undefined);

        let rule_type_str = match rule_info.rule_type {
            crate::rvm::program::RuleType::Complete => "complete",
            crate::rvm::program::RuleType::PartialSet => "partial_set",
            crate::rvm::program::RuleType::PartialObject => "partial_object",
        };

        let emissions = materialize_rule_emissions(*rule_idx, rule_info, program, trace, settings);
        let definitions = if settings.scope == ExplanationScope::RuleSummary
            || (settings.detail == ExplanationDetail::Compact
                && rule_info.rule_type == crate::rvm::program::RuleType::PartialSet
                && !emissions.is_empty())
        {
            Vec::new()
        } else {
            materialize_definitions(*rule_idx, rule_info, program, trace, settings)
        };

        rules.push(RuleExplanation {
            name: rule_info.name.clone(),
            rule_type: rule_type_str.to_string(),
            result,
            emissions,
            definitions,
        });
    }

    rules
}

fn materialize_definitions(
    rule_idx: u16,
    rule_info: &crate::rvm::program::RuleInfo,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<DefinitionExplanation> {
    let mut defs: Vec<DefinitionExplanation> = Vec::new();

    let def_outcomes: Vec<&RuleOutcome> = trace
        .rule_outcomes
        .iter()
        .filter(|o| o.rule_index == rule_idx)
        .collect();

    for outcome in &def_outcomes {
        let def_idx = outcome.definition_index;

        // Get instruction range for this definition.
        let body_pcs = rule_info
            .definitions
            .get(usize::from(def_idx))
            .cloned()
            .unwrap_or_default();

        let first_pc = body_pcs.first().copied().unwrap_or(0);

        let location = get_source_location(usize::try_from(first_pc).unwrap_or(0), program);

        // Find conditions within this definition's instruction range.
        let last_pc = find_rule_return_pc(usize::try_from(first_pc).unwrap_or(0), program);

        let conditions = materialize_conditions(first_pc, last_pc, program, trace, settings);

        defs.push(DefinitionExplanation {
            index: def_idx,
            outcome: if outcome.succeeded {
                "success".to_string()
            } else {
                "failure".to_string()
            },
            location,
            conditions,
        });
    }

    defs
}

fn materialize_rule_emissions(
    rule_idx: u16,
    rule_info: &crate::rvm::program::RuleInfo,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<EmissionExplanation> {
    if rule_info.rule_type != crate::rvm::program::RuleType::PartialSet {
        return Vec::new();
    }

    if settings.scope == ExplanationScope::RuleSummary {
        return Vec::new();
    }

    let mut emissions: Vec<EmissionExplanation> = Vec::new();
    let mut seen_results: Vec<Value> = Vec::new();
    let target_emission_index = if settings.scope == ExplanationScope::SingleEmission {
        settings.emission_index
    } else {
        None
    };
    let target_emission_value = if settings.scope == ExplanationScope::SingleEmission {
        settings.emission_value.as_ref()
    } else {
        None
    };
    let mut emission_index = 0_usize;

    for emission in trace
        .emission_outcomes
        .iter()
        .filter(|outcome| outcome.rule_index == rule_idx)
    {
        let Some(result) = emission
            .value_idx
            .and_then(|idx| trace.get_value(idx))
            .cloned()
        else {
            continue;
        };

        if seen_results.contains(&result) {
            continue;
        }

        if target_emission_index.is_some_and(|target_index| emission_index != target_index) {
            seen_results.push(result);
            emission_index = emission_index.saturating_add(1);
            continue;
        }

        if target_emission_value.is_some_and(|target_value| &result != target_value) {
            seen_results.push(result);
            emission_index = emission_index.saturating_add(1);
            continue;
        }

        seen_results.push(result.clone());

        emissions.push(EmissionExplanation {
            index: emission_index,
            definition_index: emission.definition_index,
            result,
            conditions: materialize_condition_window(
                emission.condition_start_index,
                emission.condition_end_index,
                program,
                trace,
                settings,
            ),
        });

        emission_index = emission_index.saturating_add(1);

        if target_emission_index.is_some() {
            break;
        }
    }

    emissions
}

fn materialize_conditions(
    first_pc: u32,
    last_pc: u32,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let relevant_outcomes = select_condition_outcomes(first_pc, last_pc, trace, settings);

    finalize_condition_explanations(
        materialize_condition_explanations(relevant_outcomes, program, trace, settings),
        settings,
        false,
    )
}

fn materialize_condition_window(
    condition_start_index: u32,
    condition_end_index: u32,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let relevant_outcomes = select_condition_outcomes_in_window(
        condition_start_index,
        condition_end_index,
        trace,
        settings,
    );

    finalize_condition_explanations(
        materialize_condition_explanations(relevant_outcomes, program, trace, settings),
        settings,
        true,
    )
}

fn finalize_condition_explanations(
    mut conditions: Vec<ConditionExplanation>,
    settings: &ExplanationSettings,
    dedupe_for_emissions: bool,
) -> Vec<ConditionExplanation> {
    if dedupe_for_emissions && settings.detail != ExplanationDetail::Full {
        conditions = dedupe_emission_conditions(conditions);
    }

    if settings.detail == ExplanationDetail::Compact {
        conditions = compact_condition_explanations(conditions);
    }

    conditions
}

fn compact_condition_explanations(
    conditions: Vec<ConditionExplanation>,
) -> Vec<ConditionExplanation> {
    if conditions.is_empty() {
        return conditions;
    }

    let last_index = conditions.len().saturating_sub(1);

    conditions
        .into_iter()
        .enumerate()
        .filter_map(|(index, mut condition)| {
            let keep = index == last_index
                || condition.outcome != "success"
                || condition.kind == "existence";

            if !keep {
                return None;
            }

            condition.text = compact_condition_text(&condition);
            condition.location = None;
            condition.left = None;
            condition.right = None;
            condition.witness = None;

            Some(condition)
        })
        .collect()
}

fn compact_condition_text(condition: &ConditionExplanation) -> String {
    let Some(witness) = condition.witness.as_ref() else {
        return condition.text.clone();
    };

    alloc::format!(
        "{} [{}]",
        condition.text,
        format_loop_witness_summary(witness)
    )
}

fn format_loop_witness_summary(witness: &LoopWitnessExplanation) -> String {
    let mut summary = alloc::format!(
        "loop: {}/{} matched",
        witness.success_count,
        witness.total_iterations
    );

    if let Some(sample) = format_loop_witness_sample(witness) {
        summary.push_str("; sample: ");
        summary.push_str(&sample);
    }

    summary
}

fn format_loop_witness_sample(witness: &LoopWitnessExplanation) -> Option<String> {
    match (&witness.sample_key, &witness.sample_value) {
        (Some(key), Some(value)) => Some(alloc::format!("{key} => {value}")),
        (Some(key), None) => Some(key.to_string()),
        (None, Some(value)) => Some(value.to_string()),
        (None, None) => None,
    }
}

fn dedupe_emission_conditions(conditions: Vec<ConditionExplanation>) -> Vec<ConditionExplanation> {
    let mut deduped: Vec<ConditionExplanation> = Vec::new();

    'outer: for condition in conditions {
        for existing in &deduped {
            if existing.text == condition.text
                && existing.outcome == condition.outcome
                && existing.kind == condition.kind
                && existing.operator == condition.operator
                && operands_match(existing.left.as_ref(), condition.left.as_ref())
                && operands_match(existing.right.as_ref(), condition.right.as_ref())
                && witnesses_match(existing.witness.as_ref(), condition.witness.as_ref())
            {
                continue 'outer;
            }
        }

        deduped.push(condition);
    }

    deduped
}

fn operands_match(left: Option<&OperandExplanation>, right: Option<&OperandExplanation>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.value == right.value
                && left.provenance == right.provenance
                && left.redacted == right.redacted
        }
        _ => false,
    }
}

fn witnesses_match(
    left: Option<&LoopWitnessExplanation>,
    right: Option<&LoopWitnessExplanation>,
) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.total_iterations == right.total_iterations
                && left.success_count == right.success_count
                && left.sample_key == right.sample_key
                && left.sample_value == right.sample_value
        }
        _ => false,
    }
}

fn materialize_condition_explanations(
    relevant_outcomes: Vec<(usize, &ConditionOutcome)>,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let mut conditions: Vec<ConditionExplanation> = Vec::new();

    for (_, outcome) in &relevant_outcomes {
        let pc_usize: usize = outcome.pc.try_into().unwrap_or(0);

        let static_info = program
            .condition_infos
            .get(pc_usize)
            .and_then(Option::as_ref);

        let base_text = static_info.map(|i| i.text.clone()).unwrap_or_default();

        let kind = static_info
            .map(|i| format_condition_kind(&i.kind))
            .unwrap_or_else(|| "unknown".to_string());

        let operator = static_info
            .and_then(|i| i.operator.as_ref())
            .map(|op| op.to_string());

        let location = get_source_location(pc_usize, program);

        let outcome_str = if outcome.assumed {
            "assumed"
        } else if outcome.passed {
            "success"
        } else {
            "failure"
        };

        let (left, right) = materialize_operands(outcome, static_info, trace, settings);
        let witness = materialize_loop_witness(outcome, trace);
        let binding_name = static_info.and_then(|i| i.binding_name.clone());
        let text = decorate_condition_text(base_text, static_info, left.as_ref());

        conditions.push(ConditionExplanation {
            text,
            outcome: outcome_str.to_string(),
            location,
            kind,
            operator,
            left,
            right,
            witness,
            binding_name,
        });
    }

    if conditions
        .iter()
        .all(|condition| condition.witness.is_none())
    {
        if let Some(witness) = materialize_fallback_loop_witness(&relevant_outcomes, trace) {
            if let Some(last) = conditions.last_mut() {
                last.witness = Some(witness);
            }
        }
    }

    conditions
}

fn materialize_fallback_loop_witness(
    relevant_outcomes: &[(usize, &ConditionOutcome)],
    trace: &EvaluationTrace,
) -> Option<LoopWitnessExplanation> {
    let selected_indices: Vec<u32> = relevant_outcomes
        .iter()
        .filter_map(|(index, _)| u32::try_from(*index).ok())
        .collect();

    let stat = trace
        .loop_stats
        .iter()
        .rev()
        .find(|stat| {
            stat.anchor_condition_idx
                .is_some_and(|idx| selected_indices.contains(&idx))
        })
        .or_else(|| trace.loop_stats.last())?;

    Some(LoopWitnessExplanation {
        total_iterations: stat.total_iterations,
        success_count: stat.success_count,
        sample_key: stat
            .sample_key
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
        sample_value: stat
            .sample_value
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
    })
}

fn materialize_loop_witness(
    outcome: &ConditionOutcome,
    trace: &EvaluationTrace,
) -> Option<LoopWitnessExplanation> {
    let stat = outcome
        .loop_stat_idx
        .and_then(|idx| trace.loop_stats.get(usize::from(idx)))?;

    Some(LoopWitnessExplanation {
        total_iterations: stat.total_iterations,
        success_count: stat.success_count,
        sample_key: stat
            .sample_key
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
        sample_value: stat
            .sample_value
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
    })
}

fn decorate_condition_text(
    base_text: String,
    static_info: Option<&crate::static_provenance::StaticConditionInfo>,
    left: Option<&OperandExplanation>,
) -> String {
    let Some(info) = static_info else {
        return base_text;
    };

    match info.kind {
        crate::static_provenance::ConditionKind::Existence => left
            .map(format_operand_for_text)
            .filter(|value| !value.is_empty())
            .map(|value| alloc::format!("{base_text} [matched: {value}]"))
            .unwrap_or(base_text),
        _ => base_text,
    }
}

fn format_operand_for_text(operand: &OperandExplanation) -> String {
    operand.provenance.as_ref().map_or_else(
        || operand.value.to_string(),
        |path| alloc::format!("{path}={}", operand.value),
    )
}

fn select_condition_outcomes<'a>(
    first_pc: u32,
    last_pc: u32,
    trace: &'a EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    let outcomes: Vec<(usize, &ConditionOutcome)> = trace
        .condition_outcomes
        .iter()
        .enumerate()
        .filter(|outcome| outcome.1.pc >= first_pc && outcome.1.pc <= last_pc)
        .collect();

    select_condition_outcomes_from_slice(outcomes, settings)
}

fn select_condition_outcomes_in_window<'a>(
    condition_start_index: u32,
    condition_end_index: u32,
    trace: &'a EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    let start_idx = usize::try_from(condition_start_index).unwrap_or(usize::MAX);
    let end_idx = usize::try_from(condition_end_index).unwrap_or(usize::MAX);

    let outcomes: Vec<(usize, &ConditionOutcome)> = trace
        .condition_outcomes
        .get(start_idx..end_idx)
        .unwrap_or(&[])
        .iter()
        .enumerate()
        .map(|(offset, outcome)| (start_idx.saturating_add(offset), outcome))
        .collect();

    select_condition_outcomes_from_slice(outcomes, settings)
}

fn select_condition_outcomes_from_slice<'a>(
    outcomes: Vec<(usize, &'a ConditionOutcome)>,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    if settings.condition_mode == ConditionMode::AllContributing {
        return outcomes;
    }

    let mut selected: Vec<(usize, &ConditionOutcome)> = Vec::new();
    let mut seen_pcs: Vec<u32> = Vec::new();

    for outcome in outcomes.iter().rev().copied() {
        if seen_pcs.contains(&outcome.1.pc) {
            continue;
        }
        seen_pcs.push(outcome.1.pc);
        selected.push(outcome);
    }

    selected.reverse();
    selected
}

#[allow(clippy::option_if_let_else)]
fn materialize_operands(
    outcome: &ConditionOutcome,
    static_info: Option<&crate::static_provenance::StaticConditionInfo>,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> (Option<OperandExplanation>, Option<OperandExplanation>) {
    let actual = outcome
        .actual_value_idx
        .and_then(|idx| trace.get_value(idx))
        .cloned();
    let expected = outcome
        .expected_value_idx
        .and_then(|idx| trace.get_value(idx))
        .cloned();

    let (left_prov, right_prov) = static_info
        .and_then(|i| i.operands.as_ref())
        .map(|ops| (ops.left_provenance.as_ref(), ops.right_provenance.as_ref()))
        .unwrap_or((None, None));

    let left_runtime_path = outcome.actual_path.as_deref();
    let right_runtime_path = outcome.expected_path.as_deref();

    let redact = settings.value_mode == ValueMode::Redacted;

    let left_output_path =
        operand_provenance_for_output(left_runtime_path, left_prov, outcome, trace);
    let right_output_path =
        operand_provenance_for_output(right_runtime_path, right_prov, outcome, trace);

    let left = actual.map(|v| {
        let should_redact = redact
            && if left_output_path.is_some() {
                should_redact_runtime_path(left_output_path.as_deref())
            } else {
                should_redact_path(left_prov)
            };
        OperandExplanation {
            value: if should_redact {
                Value::from("<redacted>")
            } else {
                v
            },
            provenance: left_output_path.clone(),
            redacted: should_redact,
        }
    });

    let right = expected.map(|v| {
        let should_redact = redact
            && if right_output_path.is_some() {
                should_redact_runtime_path(right_output_path.as_deref())
            } else {
                should_redact_path(right_prov)
            };
        OperandExplanation {
            value: if should_redact {
                Value::from("<redacted>")
            } else {
                v
            },
            provenance: right_output_path.clone(),
            redacted: should_redact,
        }
    });

    (left, right)
}

fn materialize_assumptions(program: &Program, trace: &EvaluationTrace) -> Vec<AssumptionRecord> {
    trace
        .assumptions
        .iter()
        .map(|a| {
            let pc_usize: usize = a.pc.try_into().unwrap_or(0);
            let location = get_source_location(pc_usize, program);
            let kind_str = match a.kind {
                AssumptionKind::Exists => "exists",
                AssumptionKind::ConditionHolds => "condition_holds",
                AssumptionKind::CollectionExists => "collection_exists",
            };
            AssumptionRecord {
                kind: kind_str.to_string(),
                input_path: a.input_path.clone(),
                assumed_holds: a.condition_text.clone(),
                operator: a.operator.clone(),
                assumed_value: a.assumed_value.clone(),
                location,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn get_source_location(pc: usize, program: &Program) -> Option<SourceLocation> {
    let span = program.instruction_spans.get(pc)?.as_ref()?;
    let file_name = program
        .sources
        .get(span.source_index)
        .map(|s| s.name.clone())
        .unwrap_or_default();
    Some(SourceLocation {
        file: file_name,
        row: span.line,
        col: span.column,
    })
}

fn find_rule_return_pc(start_pc: usize, program: &Program) -> u32 {
    let mut pc = start_pc;
    while pc < program.instructions.len() {
        if matches!(
            program.instructions.get(pc),
            Some(crate::rvm::Instruction::RuleReturn {})
        ) {
            return u32::try_from(pc).unwrap_or(u32::MAX);
        }
        pc = pc.saturating_add(1);
    }
    u32::try_from(program.instructions.len().saturating_sub(1)).unwrap_or(u32::MAX)
}

fn format_condition_kind(kind: &crate::static_provenance::ConditionKind) -> String {
    use crate::static_provenance::ConditionKind;
    match *kind {
        ConditionKind::Comparison => "comparison",
        ConditionKind::Membership => "membership",
        ConditionKind::Truthiness => "truthiness",
        ConditionKind::Existence => "existence",
        ConditionKind::EqualityAssertion => "equality_assertion",
        ConditionKind::Negation => "negation",
        ConditionKind::Binding => "binding",
    }
    .to_string()
}

#[cfg(all(test, feature = "explanations"))]
#[allow(clippy::indexing_slicing, clippy::unwrap_used)]
mod tests {
    use alloc::vec;

    use super::{
        dedupe_emission_conditions, materialize, materialize_condition_explanations,
        materialize_conditions, materialize_rule_emissions, ConditionExplanation,
        OperandExplanation,
    };
    use crate::evaluation_trace::{
        AssumptionKind, ConditionMode, EvaluationTrace, ExplanationDetail, ExplanationScope,
        ExplanationSettings, ValueMode,
    };
    use crate::rvm::program::{Program, RuleInfo, RuleType, SourceFile, SpanInfo};
    use crate::static_provenance::{ConditionKind, StaticConditionInfo};
    use crate::{value::Value, Rc};

    const fn settings(condition_mode: ConditionMode) -> ExplanationSettings {
        ExplanationSettings {
            enabled: true,
            value_mode: ValueMode::Redacted,
            condition_mode,
            scope: ExplanationScope::AllEmissions,
            detail: ExplanationDetail::Standard,
            emission_index: None,
            emission_value: None,
            assume_unknown_input: false,
        }
    }

    fn settings_with_detail(
        condition_mode: ConditionMode,
        detail: ExplanationDetail,
    ) -> ExplanationSettings {
        ExplanationSettings {
            detail,
            ..settings(condition_mode)
        }
    }

    #[test]
    fn primary_only_keeps_last_outcome_per_condition_site() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "a\nb\nc\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 1)),
            Some(SpanInfo::new(0, 2, 1, 1)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond one".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond two".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(1, false, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);

        let conditions = materialize_conditions(
            1,
            2,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions.first().map(|c| c.text.as_str()),
            Some("cond one")
        );
        assert_eq!(
            conditions.first().map(|c| c.outcome.as_str()),
            Some("failure")
        );
        assert_eq!(conditions.get(1).map(|c| c.text.as_str()), Some("cond two"));
        assert_eq!(
            conditions.get(1).map(|c| c.outcome.as_str()),
            Some("success")
        );
    }

    #[test]
    fn all_contributing_keeps_all_outcomes() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "a\nb\n".into()));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 1))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(1, false, false, None, None, None, None);

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings(ConditionMode::AllContributing),
        );

        assert_eq!(conditions.len(), 2);
    }

    #[test]
    fn partial_set_rule_materializes_per_emission_conditions() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_condition(3, true, false, None, None, None, None);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"));
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_condition(3, true, false, None, None, None, None);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(emissions.len(), 2);
        assert_eq!(emissions[0].index, 0);
        assert_eq!(
            emissions.first().map(|emission| emission.result.clone()),
            Some(Value::from("violation a"))
        );
        assert_eq!(
            emissions.first().map(|emission| emission.conditions.len()),
            Some(2)
        );
        assert_eq!(
            emissions.get(1).map(|emission| emission.result.clone()),
            Some(Value::from("violation b"))
        );
        assert_eq!(emissions[1].index, 1);
        assert_eq!(
            emissions.get(1).map(|emission| emission.conditions.len()),
            Some(2)
        );
    }

    #[test]
    fn partial_set_rule_can_select_single_emission_by_index() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_condition(3, true, false, None, None, None, None);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"));
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_condition(3, true, false, None, None, None, None);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &ExplanationSettings {
                emission_index: Some(1),
                scope: ExplanationScope::SingleEmission,
                ..settings(ConditionMode::PrimaryOnly)
            },
        );

        assert_eq!(emissions.len(), 1);
        assert_eq!(emissions[0].index, 1);
        assert_eq!(emissions[0].result, Value::from("violation b"));
        assert_eq!(emissions[0].conditions.len(), 2);
    }

    #[test]
    fn partial_set_rule_can_select_single_emission_by_value() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_condition(3, true, false, None, None, None, None);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"));
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_condition(3, true, false, None, None, None, None);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &ExplanationSettings {
                scope: ExplanationScope::SingleEmission,
                emission_value: Some(Value::from("violation a")),
                ..settings(ConditionMode::PrimaryOnly)
            },
        );

        assert_eq!(emissions.len(), 1);
        assert_eq!(emissions[0].index, 0);
        assert_eq!(emissions[0].result, Value::from("violation a"));
        assert_eq!(emissions[0].conditions.len(), 2);
    }

    #[test]
    fn standard_detail_dedupes_emission_conditions_but_full_keeps_all() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "dup\ndup\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 3)),
            Some(SpanInfo::new(0, 2, 1, 3)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "dup".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "dup".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(2, true, false, None, None, None, None);
        trace.record_emission(0, 0, 0, 2, Value::from("violation a"));

        let standard = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Standard),
        );
        let full = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Full),
        );

        assert_eq!(standard.len(), 1);
        assert_eq!(standard[0].conditions.len(), 1);
        assert_eq!(full.len(), 1);
        assert_eq!(full[0].conditions.len(), 2);
    }

    #[test]
    fn compact_detail_inlines_witness_and_last_condition_but_strips_operands() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "helper\nsome item in coll\nfinal\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 6)),
            Some(SpanInfo::new(0, 2, 1, 17)),
            Some(SpanInfo::new(0, 3, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "helper".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "some item in coll".into(),
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "final".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_condition(
            2,
            true,
            false,
            Some(Value::from("match-a")),
            None,
            None,
            None,
        );
        trace.attach_loop_stat_to_last_condition(
            2,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );
        trace.record_condition(3, true, false, None, None, None, None);

        let conditions = materialize_conditions(
            1,
            3,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Compact),
        );

        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions[0].text,
            "some item in coll [matched: \"match-a\"] [loop: 2/3 matched; sample: 1 => \"match-a\"]"
        );
        assert_eq!(conditions[0].kind, "existence");
        assert!(conditions[0].left.is_none());
        assert!(conditions[0].right.is_none());
        assert!(conditions[0].location.is_none());
        assert!(conditions[0].witness.is_none());
        assert_eq!(conditions[1].text, "final");
        assert!(conditions[1].left.is_none());
        assert!(conditions[1].location.is_none());
    }

    #[test]
    fn standard_detail_keeps_structured_loop_witness() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None);
        trace.attach_loop_stat_to_last_condition(
            1,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Standard),
        );

        assert_eq!(conditions.len(), 1);
        assert_eq!(conditions[0].text, "every item in input.list { item > 0 }");
        let witness = conditions[0].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 2);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from("match-a")));
    }

    #[test]
    fn compact_detail_suppresses_partial_set_definition_scaffolding_and_assumptions() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "first\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 1, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            None,
        ];
        program.instructions = vec![
            crate::rvm::Instruction::LoadTrue { dest: 0 },
            crate::rvm::Instruction::LoadTrue { dest: 0 },
            crate::rvm::Instruction::RuleReturn {},
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info);

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None);
        trace.record_rule_outcome(0, 0, true, Some(Value::from("violation a")));
        trace.record_emission(0, 0, 0, 1, Value::from("violation a"));
        trace.record_assumption(
            AssumptionKind::ConditionHolds,
            "input.foo".into(),
            "input.foo == true".into(),
            1,
            Some("==".into()),
            Some(Value::Bool(true)),
        );

        let report = materialize(
            &program,
            &trace,
            &settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Compact),
            Value::from("violation a"),
        );

        assert_eq!(report.assumptions.len(), 0);
        assert_eq!(report.rules.len(), 1);
        assert_eq!(report.rules[0].emissions.len(), 1);
        assert_eq!(report.rules[0].definitions.len(), 0);
    }

    #[test]
    fn quantifier_condition_materializes_loop_witness_summary() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None);
        trace.attach_loop_stat_to_last_condition(
            1,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(conditions.len(), 1);
        let witness = conditions[0].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 2);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from("match-a")));
    }

    #[test]
    fn fallback_loop_witness_attaches_to_last_selected_condition() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "n > 1\nn < 3\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "n > 1".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "n < 3".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None);
        trace.record_condition(2, false, false, Some(Value::Bool(false)), None, None, None);
        trace.record_loop(
            2,
            Some(1),
            3,
            1,
            Some(Value::from(1_u64)),
            Some(Value::from(2_u64)),
        );

        let conditions = materialize_conditions(
            1,
            2,
            &program,
            &trace,
            &settings(ConditionMode::AllContributing),
        );

        assert_eq!(conditions.len(), 2);
        assert!(conditions[0].witness.is_none());
        let witness = conditions[1].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 1);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from(2_u64)));
    }

    #[test]
    fn rule_summary_scope_suppresses_definitions_and_emissions() {
        let mut program = Program::new();
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info);

        let mut trace = EvaluationTrace::new();
        trace.record_rule_outcome(0, 0, true, Some(Value::from("violation a")));
        trace.record_emission(0, 0, 0, 0, Value::from("violation a"));

        let report = materialize(
            &program,
            &trace,
            &ExplanationSettings {
                scope: ExplanationScope::RuleSummary,
                ..settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Standard)
            },
            Value::from("violation a"),
        );

        assert_eq!(report.rules.len(), 1);
        assert_eq!(report.rules[0].emissions.len(), 0);
        assert_eq!(report.rules[0].definitions.len(), 0);
    }

    #[test]
    fn existence_condition_text_includes_matched_value() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "some item in coll\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 8))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "some item in coll".into(),
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: false,
                binding_name: None,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(
            1,
            true,
            false,
            Some(Value::from("match-a")),
            None,
            None,
            None,
        );

        let conditions = materialize_condition_explanations(
            trace.condition_outcomes.iter().enumerate().collect(),
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(
            conditions.first().map(|condition| condition.text.as_str()),
            Some("some item in coll [matched: \"match-a\"]")
        );
    }

    #[test]
    fn emission_dedup_keeps_distinct_witness_values() {
        let conditions = vec![
            ConditionExplanation {
                text: "some item in coll [matched: a]".into(),
                outcome: "success".into(),
                location: None,
                kind: "existence".into(),
                operator: None,
                left: Some(OperandExplanation {
                    value: Value::from("a"),
                    provenance: None,
                    redacted: false,
                }),
                right: None,
                witness: None,
                binding_name: None,
            },
            ConditionExplanation {
                text: "some item in coll [matched: b]".into(),
                outcome: "success".into(),
                location: None,
                kind: "existence".into(),
                operator: None,
                left: Some(OperandExplanation {
                    value: Value::from("b"),
                    provenance: None,
                    redacted: false,
                }),
                right: None,
                witness: None,
                binding_name: None,
            },
        ];

        let deduped = dedupe_emission_conditions(conditions);

        assert_eq!(deduped.len(), 2);
    }
}

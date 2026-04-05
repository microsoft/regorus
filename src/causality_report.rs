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
    AssumptionKind, ConditionOutcome, EvaluationTrace, ExplanationSettings, RuleOutcome, ValueMode,
};
use crate::rvm::program::Program;
use crate::static_provenance::Provenance;
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
    /// Explanations for each definition that was evaluated.
    pub definitions: Vec<DefinitionExplanation>,
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
    let assumptions = materialize_assumptions(program, trace);

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

        let definitions = materialize_definitions(*rule_idx, rule_info, program, trace, settings);

        rules.push(RuleExplanation {
            name: rule_info.name.clone(),
            rule_type: rule_type_str.to_string(),
            result,
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

fn materialize_conditions(
    first_pc: u32,
    last_pc: u32,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let mut conditions: Vec<ConditionExplanation> = Vec::new();

    // Find all condition outcomes whose PC falls within [first_pc, last_pc].
    for outcome in &trace.condition_outcomes {
        if outcome.pc < first_pc || outcome.pc > last_pc {
            continue;
        }

        let pc_usize: usize = outcome.pc.try_into().unwrap_or(0);

        let static_info = program
            .condition_infos
            .get(pc_usize)
            .and_then(Option::as_ref);

        let text = static_info.map(|i| i.text.clone()).unwrap_or_default();

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

        conditions.push(ConditionExplanation {
            text,
            outcome: outcome_str.to_string(),
            location,
            kind,
            operator,
            left,
            right,
        });
    }

    conditions
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

    let redact = settings.value_mode == ValueMode::Redacted;

    let left = actual.map(|v| {
        let should_redact = redact && should_redact_path(left_prov);
        OperandExplanation {
            value: if should_redact {
                Value::from("<redacted>")
            } else {
                v
            },
            provenance: left_prov.map(|p| p.to_string()),
            redacted: should_redact,
        }
    });

    let right = expected.map(|v| {
        let should_redact = redact && should_redact_path(right_prov);
        OperandExplanation {
            value: if should_redact {
                Value::from("<redacted>")
            } else {
                v
            },
            provenance: right_prov.map(|p| p.to_string()),
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
    }
    .to_string()
}

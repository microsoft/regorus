// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Runtime evaluation trace for causality / explanation reporting.
//!
//! This module provides a lightweight, append-only trace that captures the
//! runtime outcomes needed to produce causality reports.  All structural
//! metadata (provenance paths, condition text, operators) lives in the
//! compiled `Program` via [`crate::static_provenance`]; the trace only
//! records:
//!
//! - Which conditions passed / failed and their runtime values.
//! - Loop iteration statistics and sample witnesses.
//! - Which rule definitions were attempted and their outcomes.
//! - Assumptions recorded when unknown input handling is active.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use serde::Serialize;

use crate::value::Value;

// ---------------------------------------------------------------------------
// Settings
// ---------------------------------------------------------------------------

/// Controls how much runtime value information is captured.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ValueMode {
    /// Redact values that look like secrets (password, token, …).
    #[default]
    Redacted,
    /// Capture all values as-is.
    Full,
}

/// Controls which conditions are included in the final report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ConditionMode {
    /// Only the primary (typically last) condition per block.
    #[default]
    PrimaryOnly,
    /// All conditions that contributed to the block's outcome.
    AllContributing,
}

/// Controls which portion of the rule report is materialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExplanationScope {
    /// Include explanations for every emitted result.
    #[default]
    AllEmissions,
    /// Include explanations for a single emitted result.
    SingleEmission,
    /// Suppress per-emission details and keep only the rule-level summary.
    RuleSummary,
}

/// Controls the amount of explanation detail materialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExplanationDetail {
    /// Reserve only the shortest useful causal set.
    Compact,
    /// Keep the current end-user default output.
    #[default]
    Standard,
    /// Include the fullest available explanation detail.
    Full,
}

/// Controls whether the engine runs in causality or partial-evaluation mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EvaluationMode {
    /// One sufficient explanation, short-circuit after first success.
    #[default]
    Causality,
    /// Explore all branches, collect disjunctive assumption sets.
    PartialEval,
}

/// Settings governing explanation capture and reporting.
#[derive(Debug, Clone)]
pub struct ExplanationSettings {
    pub enabled: bool,
    pub value_mode: ValueMode,
    pub condition_mode: ConditionMode,
    pub scope: ExplanationScope,
    pub detail: ExplanationDetail,
    pub emission_index: Option<usize>,
    pub emission_value: Option<Value>,
    pub assume_unknown_input: bool,
    pub eval_mode: EvaluationMode,
    /// Paths treated as unknown for partial evaluation.
    /// Default: `["input"]`. A path is considered unknown if it equals
    /// or is a child of any entry (e.g. `"input"` matches `"input.foo"`).
    pub unknowns: Vec<String>,
}

impl Default for ExplanationSettings {
    fn default() -> Self {
        Self {
            enabled: false,
            value_mode: ValueMode::default(),
            condition_mode: ConditionMode::default(),
            scope: ExplanationScope::default(),
            detail: ExplanationDetail::default(),
            emission_index: None,
            emission_value: None,
            assume_unknown_input: false,
            eval_mode: EvaluationMode::default(),
            unknowns: vec![String::from("input")],
        }
    }
}

impl ExplanationSettings {
    /// Check whether `path` falls under one of the configured unknown prefixes.
    pub fn is_unknown_path(&self, path: &str) -> bool {
        for prefix in &self.unknowns {
            if path == prefix.as_str()
                || path.starts_with(&alloc::format!("{}.", prefix))
                || path.starts_with(&alloc::format!("{}[", prefix))
            {
                return true;
            }
        }
        false
    }
}

// ---------------------------------------------------------------------------
// Trace events
// ---------------------------------------------------------------------------

/// Index into `EvaluationTrace::captured_values`.
type ValueIdx = u16;

/// Outcome of a single assertion instruction.
#[derive(Debug, Clone)]
pub struct ConditionOutcome {
    /// Program counter (instruction index) of the assertion.
    pub pc: u32,
    /// Did the condition pass?
    pub passed: bool,
    /// Was this an assumption (unknown input assumed to hold)?
    pub assumed: bool,
    /// Index of the actual (LHS) value in `captured_values`, if captured.
    pub actual_value_idx: Option<ValueIdx>,
    /// Runtime provenance path for the actual value, if available.
    pub actual_path: Option<String>,
    /// Index of the expected (RHS) value in `captured_values`, if captured.
    pub expected_value_idx: Option<ValueIdx>,
    /// Runtime provenance path for the expected value, if available.
    pub expected_path: Option<String>,
    /// Index of the loop summary in `loop_stats`, if this condition has one.
    pub loop_stat_idx: Option<ValueIdx>,
}

/// Statistics for a completed loop.
#[derive(Debug, Clone)]
pub struct LoopStat {
    /// PC of the `LoopStart` instruction.
    pub pc: u32,
    /// Condition outcome index this loop summary should be attached to, when known.
    pub anchor_condition_idx: Option<u32>,
    /// Total iterations executed.
    pub total_iterations: u32,
    /// Iterations that succeeded (body completed without failure).
    pub success_count: u32,
    /// Sample successful key (index into `captured_values`).
    pub sample_key: Option<ValueIdx>,
    /// Sample successful value (index into `captured_values`).
    pub sample_value: Option<ValueIdx>,
}

/// Outcome of a rule definition evaluation.
#[derive(Debug, Clone)]
pub struct RuleOutcome {
    /// Rule index in `Program::rule_infos`.
    pub rule_index: u16,
    /// Which definition within the rule (0-based).
    pub definition_index: u16,
    /// Did this definition succeed?
    pub succeeded: bool,
    /// Index of the result value in `captured_values`, if captured.
    pub result_value_idx: Option<ValueIdx>,
}

/// A single emitted result value for a partial-set rule.
#[derive(Debug, Clone)]
pub struct EmissionOutcome {
    /// Rule index in `Program::rule_infos`.
    pub rule_index: u16,
    /// Definition that produced this emission.
    pub definition_index: u16,
    /// Start index into `condition_outcomes` for the active body window.
    pub condition_start_index: u32,
    /// End index into `condition_outcomes` for the active body window.
    pub condition_end_index: u32,
    /// Index of the emitted value in `captured_values`.
    pub value_idx: Option<ValueIdx>,
}

/// An assumption recorded when unknown input handling skips an assertion.
#[derive(Debug, Clone)]
pub struct Assumption {
    /// What kind of assumption was made.
    pub kind: AssumptionKind,
    /// Human-readable input path, e.g. `"input.role"`.
    pub input_path: String,
    /// Text of the condition that was assumed, e.g. `"input.role == \"admin\""`.
    pub condition_text: String,
    /// PC of the assertion that was skipped.
    pub pc: u32,
    /// The comparison operator, e.g. `"=="`, `"!="`, `"<"`.
    /// `None` for existence checks.
    pub operator: Option<String>,
    /// The non-input value that was compared against, e.g. `"admin"`.
    /// `None` for existence checks or when the value is not available.
    pub assumed_value: Option<Value>,
    /// Rule index when the assumption was recorded (PE mode).
    pub rule_index: u16,
    /// Definition index within the rule (PE mode).
    pub definition_index: u16,
    /// Loop iteration index when the assumption was recorded (PE mode).
    /// `None` when not inside a loop or when loop tracking is not active.
    pub iteration_index: Option<u32>,
    /// Conjunction scope ID — assumptions with the same conjunction_id belong
    /// to the same rule body execution (including sub-rule calls).
    pub conjunction_id: u32,
    /// If this assumption was recorded inside a `not` body, this holds the
    /// negation scope ID.  In `materialize_pe`, inner assumptions with the
    /// same `negation_scope_id` are grouped under their parent
    /// `NegationHolds` assumption.  Causality mode ignores this field.
    pub negation_scope_id: Option<u32>,
    /// For `NegationHolds` assumptions only: the negation scope ID of the
    /// inner body this negation owns.  Used in `materialize_pe` to find
    /// which inner assumptions belong to this negation.
    pub owned_negation_scope_id: Option<u32>,
    /// When the assumption originates from indexing a known data object with
    /// an unknown input key (e.g. `data.perms[input.role]`), this captures
    /// the concrete data object so `materialize_pe` can invert the lookup.
    pub data_lookup_context: Option<DataLookupContext>,
}

/// Context for inverting a data lookup during partial evaluation.
///
/// When `data.some_object[input.some_key] == value`, the data object is known
/// but the key is unknown. By storing the object we can later invert: find
/// which key(s) in the object map to the compared value.
#[derive(Debug, Clone)]
pub struct DataLookupContext {
    /// The concrete data object that was indexed.
    pub data_object: Value,
    /// The full input path of the unknown key, e.g. `"input.user.role"`.
    pub key_input_path: String,
}

/// Kinds of assumptions that can be recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum AssumptionKind {
    /// An input path was assumed to exist (not undefined).
    Exists,
    /// A condition involving input was assumed to hold (evaluate to true).
    ConditionHolds,
    /// An input collection was assumed to exist for iteration.
    CollectionExists,
    /// A negation was assumed to hold (the negated rule depends on unknowns).
    NegationHolds,
}

// ---------------------------------------------------------------------------
// EvaluationTrace
// ---------------------------------------------------------------------------

/// Lightweight, append-only trace of runtime evaluation outcomes.
///
/// Created fresh for each evaluation.  After evaluation completes, the trace
/// is combined with the `Program`'s static metadata to produce the
/// materialized report.
#[derive(Debug, Default)]
pub struct EvaluationTrace {
    /// Condition outcomes in evaluation order.
    pub condition_outcomes: Vec<ConditionOutcome>,
    /// Captured runtime values (Rc-bumped, no deep copy).
    pub captured_values: Vec<Value>,
    /// Loop statistics.
    pub loop_stats: Vec<LoopStat>,
    /// Rule definition outcomes.
    pub rule_outcomes: Vec<RuleOutcome>,
    /// Emitted values for partial-set rules.
    pub emission_outcomes: Vec<EmissionOutcome>,
    /// Assumptions from unknown input handling.
    pub assumptions: Vec<Assumption>,
    /// Warnings generated during evaluation (e.g. comprehension soundness).
    pub warnings: Vec<String>,
    /// Monotonically increasing counter for unique iteration IDs.
    pub next_iteration_id: u32,
    /// Monotonically increasing counter for conjunction scope IDs.
    pub next_conjunction_id: u32,
    /// Monotonically increasing counter for negation scope IDs.
    pub next_negation_scope_id: u32,
    /// Stack of active negation scope IDs.  Assumptions recorded while this
    /// stack is non-empty get tagged with the top-of-stack ID.
    pub negation_scope_stack: Vec<u32>,
}

impl EvaluationTrace {
    pub fn new() -> Self {
        Self::default()
    }

    /// Clear the trace for reuse.
    pub fn clear(&mut self) {
        self.condition_outcomes.clear();
        self.captured_values.clear();
        self.loop_stats.clear();
        self.rule_outcomes.clear();
        self.emission_outcomes.clear();
        self.assumptions.clear();
        self.warnings.clear();
        self.next_iteration_id = 0;
        self.next_conjunction_id = 0;
        self.next_negation_scope_id = 0;
        self.negation_scope_stack.clear();
    }

    /// Returns true if the trace is empty (nothing recorded).
    pub const fn is_empty(&self) -> bool {
        self.condition_outcomes.is_empty()
            && self.loop_stats.is_empty()
            && self.rule_outcomes.is_empty()
            && self.assumptions.is_empty()
    }

    /// Capture a value and return its index.
    pub fn capture_value(&mut self, value: Value) -> Option<ValueIdx> {
        let idx = self.captured_values.len();
        let idx_u16 = u16::try_from(idx).ok()?;
        self.captured_values.push(value);
        Some(idx_u16)
    }

    /// Record a condition outcome.
    #[allow(clippy::too_many_arguments)]
    pub fn record_condition(
        &mut self,
        pc: u32,
        passed: bool,
        assumed: bool,
        actual: Option<Value>,
        actual_path: Option<String>,
        expected: Option<Value>,
        expected_path: Option<String>,
    ) {
        let actual_idx = actual.and_then(|v| self.capture_value(v));
        let expected_idx = expected.and_then(|v| self.capture_value(v));
        self.condition_outcomes.push(ConditionOutcome {
            pc,
            passed,
            assumed,
            actual_value_idx: actual_idx,
            actual_path,
            expected_value_idx: expected_idx,
            expected_path,
            loop_stat_idx: None,
        });
    }

    /// Attach a loop summary to the most recently recorded condition outcome.
    pub fn attach_loop_stat_to_last_condition(
        &mut self,
        pc: u32,
        total_iterations: u32,
        success_count: u32,
        sample_key: Option<Value>,
        sample_value: Option<Value>,
    ) {
        let key_idx = sample_key.and_then(|v| self.capture_value(v));
        let val_idx = sample_value.and_then(|v| self.capture_value(v));
        let loop_idx = self.loop_stats.len();
        let Some(loop_idx_u16) = u16::try_from(loop_idx).ok() else {
            return;
        };

        self.loop_stats.push(LoopStat {
            pc,
            anchor_condition_idx: self
                .condition_outcomes
                .len()
                .checked_sub(1)
                .and_then(|idx| u32::try_from(idx).ok()),
            total_iterations,
            success_count,
            sample_key: key_idx,
            sample_value: val_idx,
        });

        if let Some(outcome) = self.condition_outcomes.last_mut() {
            outcome.loop_stat_idx = Some(loop_idx_u16);
        }
    }

    /// Record a loop completion.
    pub fn record_loop(
        &mut self,
        pc: u32,
        anchor_condition_idx: Option<u32>,
        total_iterations: u32,
        success_count: u32,
        sample_key: Option<Value>,
        sample_value: Option<Value>,
    ) {
        let key_idx = sample_key.and_then(|v| self.capture_value(v));
        let val_idx = sample_value.and_then(|v| self.capture_value(v));
        self.loop_stats.push(LoopStat {
            pc,
            anchor_condition_idx,
            total_iterations,
            success_count,
            sample_key: key_idx,
            sample_value: val_idx,
        });
    }

    /// Record a rule definition outcome.
    pub fn record_rule_outcome(
        &mut self,
        rule_index: u16,
        definition_index: u16,
        succeeded: bool,
        result_value: Option<Value>,
    ) {
        let result_idx = result_value.and_then(|v| self.capture_value(v));
        self.rule_outcomes.push(RuleOutcome {
            rule_index,
            definition_index,
            succeeded,
            result_value_idx: result_idx,
        });
    }

    /// Record a partial-set emission and the body-window conditions active at the time.
    pub fn record_emission(
        &mut self,
        rule_index: u16,
        definition_index: u16,
        condition_start_index: u32,
        condition_end_index: u32,
        value: Value,
    ) {
        let value_idx = self.capture_value(value);
        self.emission_outcomes.push(EmissionOutcome {
            rule_index,
            definition_index,
            condition_start_index,
            condition_end_index,
            value_idx,
        });
    }

    /// Record an assumption from unknown input handling.
    #[allow(clippy::too_many_arguments)]
    pub fn record_assumption(
        &mut self,
        kind: AssumptionKind,
        input_path: String,
        condition_text: String,
        pc: u32,
        operator: Option<String>,
        assumed_value: Option<Value>,
        rule_index: u16,
        definition_index: u16,
        iteration_index: Option<u32>,
        conjunction_id: u32,
    ) {
        // Pick up the current negation scope (if any) from the stack.
        let negation_scope_id = self.negation_scope_stack.last().copied();
        self.assumptions.push(Assumption {
            kind,
            input_path,
            condition_text,
            pc,
            operator,
            assumed_value,
            rule_index,
            definition_index,
            iteration_index,
            conjunction_id,
            negation_scope_id,
            owned_negation_scope_id: None,
            data_lookup_context: None,
        });
    }

    /// Push a negation scope — called when entering a `not` body.
    /// Returns the scope ID so the caller can record it on the
    /// `NegationHolds` assumption later.
    pub fn push_negation_scope(&mut self) -> u32 {
        let id = self.next_negation_scope_id;
        self.next_negation_scope_id = id.saturating_add(1);
        self.negation_scope_stack.push(id);
        id
    }

    /// Pop the current negation scope.
    pub fn pop_negation_scope(&mut self) {
        self.negation_scope_stack.pop();
    }

    /// Resolve a captured value by index.
    pub fn get_value(&self, idx: ValueIdx) -> Option<&Value> {
        self.captured_values.get(usize::from(idx))
    }
}

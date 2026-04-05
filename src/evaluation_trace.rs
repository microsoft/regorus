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

/// Settings governing explanation capture and reporting.
#[derive(Debug, Clone, Default)]
pub struct ExplanationSettings {
    pub enabled: bool,
    pub value_mode: ValueMode,
    pub condition_mode: ConditionMode,
    pub assume_unknown_input: bool,
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
    /// Index of the expected (RHS) value in `captured_values`, if captured.
    pub expected_value_idx: Option<ValueIdx>,
}

/// Statistics for a completed loop.
#[derive(Debug, Clone)]
pub struct LoopStat {
    /// PC of the `LoopStart` instruction.
    pub pc: u32,
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
    /// Assumptions from unknown input handling.
    pub assumptions: Vec<Assumption>,
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
        self.assumptions.clear();
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
    pub fn record_condition(
        &mut self,
        pc: u32,
        passed: bool,
        assumed: bool,
        actual: Option<Value>,
        expected: Option<Value>,
    ) {
        let actual_idx = actual.and_then(|v| self.capture_value(v));
        let expected_idx = expected.and_then(|v| self.capture_value(v));
        self.condition_outcomes.push(ConditionOutcome {
            pc,
            passed,
            assumed,
            actual_value_idx: actual_idx,
            expected_value_idx: expected_idx,
        });
    }

    /// Record a loop completion.
    pub fn record_loop(
        &mut self,
        pc: u32,
        total_iterations: u32,
        success_count: u32,
        sample_key: Option<Value>,
        sample_value: Option<Value>,
    ) {
        let key_idx = sample_key.and_then(|v| self.capture_value(v));
        let val_idx = sample_value.and_then(|v| self.capture_value(v));
        self.loop_stats.push(LoopStat {
            pc,
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

    /// Record an assumption from unknown input handling.
    pub fn record_assumption(
        &mut self,
        kind: AssumptionKind,
        input_path: String,
        condition_text: String,
        pc: u32,
        operator: Option<String>,
        assumed_value: Option<Value>,
    ) {
        self.assumptions.push(Assumption {
            kind,
            input_path,
            condition_text,
            pc,
            operator,
            assumed_value,
        });
    }

    /// Resolve a captured value by index.
    pub fn get_value(&self, idx: ValueIdx) -> Option<&Value> {
        self.captured_values.get(usize::from(idx))
    }
}

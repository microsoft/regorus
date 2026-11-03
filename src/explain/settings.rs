// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

/// How runtime values are recorded in explanations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ValueMode {
    /// Withhold the runtime values that report generation classifies as
    /// sensitive, for example values read from paths containing `password`
    /// or `token`, and mark them as
    /// [`Redacted`](super::ReportedValue::Redacted). This applies to
    /// operands, loop samples, proof iteration
    /// [`bindings`](super::Derivation::bindings), the values of a
    /// [`RuleOutcome::Conflict`](super::RuleOutcome::Conflict), and the
    /// results, emitted keys and values, and per-result
    /// [`results`](super::RuleExplanation::results) keys and values of the
    /// rules the query depends on.
    ///
    /// Never redacted, because evaluation returns them to the caller anyway:
    /// the query result, and for the top-level evaluation of the rule the
    /// query names (see [`QueryTarget`](super::QueryTarget)) its result, the
    /// keys and values of its emissions, and the `key` and `value` of each
    /// of its [`ResultExplanation`](super::ResultExplanation)s. Condition
    /// text and
    /// source-template operand paths are policy source and are reported as
    /// written. Opted-in concrete paths can contain runtime-derived keys:
    /// sensitive paths are withheld in their entirety and marked
    /// [`ConcretePath::Redacted`](super::ConcretePath::Redacted). Redaction
    /// is best effort, not a secrecy guarantee. Partial evaluation results
    /// are not affected.
    #[default]
    Redacted,
    /// Record all values as they are.
    Full,
}

/// Which conditions of a rule body are reported.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ConditionMode {
    /// Only the condition that decided the body's outcome: the first
    /// condition whose outcome is [`Failure`](super::Outcome::Failure) or
    /// [`Undefined`](super::Outcome::Undefined), or the last condition of a
    /// successful body.
    #[default]
    PrimaryOnly,
    /// Every condition that contributed to the body's outcome.
    AllContributing,
}

/// Which parts of a rule's explanation are reported.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ExplanationScope {
    /// Explain every emitted value and every evaluated definition.
    #[default]
    All,
    /// Explain only the emission with this 0-based index (see
    /// [`EmissionExplanation`](super::EmissionExplanation)) of the top-level
    /// evaluation of the rule the query names (see
    /// [`QueryTarget::call_instance`](super::QueryTarget::call_instance)).
    SingleEmission(usize),
    /// Report rule results only, without definitions or emissions.
    RuleSummary,
}

/// Settings for explanation capture and reporting.
///
/// Start from [`ExplanationSettings::default`] and set the fields you need.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExplanationSettings {
    /// How runtime values are recorded.
    pub value_mode: ValueMode,
    /// Which conditions are reported.
    pub condition_mode: ConditionMode,
    /// Which parts of each rule are reported.
    pub scope: ExplanationScope,
    /// Capture concrete operand paths separately from policy-source
    /// templates. Off by default. Distinct-element counting is independent:
    /// when identity cannot be tracked, its count is unavailable, not zero.
    pub capture_paths: bool,
    /// Maximum retained proofs across all results of one queried rule
    /// invocation. Helpers use no slots. Counts are not limited by this
    /// cap, and stay [`Count::Exact`](super::Count::Exact) unless
    /// evaluation stops early; zero retains counts without proofs.
    /// Default: 64.
    pub max_derivations: usize,
}

impl Default for ExplanationSettings {
    fn default() -> Self {
        Self {
            value_mode: ValueMode::default(),
            condition_mode: ConditionMode::default(),
            scope: ExplanationScope::default(),
            capture_paths: false,
            max_derivations: 64,
        }
    }
}

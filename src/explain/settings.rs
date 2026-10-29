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
    /// operands, loop samples, and the results and emitted keys and values of
    /// the rules the query depends on.
    ///
    /// The query result, and the result and emissions of the top-level
    /// evaluation of the rule the query names, are never redacted, because
    /// evaluation returns them to the caller anyway. Condition text and
    /// operand paths are policy source and are reported as written. Partial
    /// evaluation results are not affected.
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
    /// evaluation of the rule the query names.
    SingleEmission(usize),
    /// Report rule results only, without definitions or emissions.
    RuleSummary,
}

/// Settings for explanation capture and reporting.
///
/// Start from [`ExplanationSettings::default`] and set the fields you need.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct ExplanationSettings {
    /// How runtime values are recorded.
    pub value_mode: ValueMode,
    /// Which conditions are reported.
    pub condition_mode: ConditionMode,
    /// Which parts of each rule are reported.
    pub scope: ExplanationScope,
}

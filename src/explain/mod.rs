// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Explanations of policy evaluation results.
//!
//! This module is enabled by the default-off `explanations` cargo feature.
//! Explanations are produced by the RVM only, so the feature implies `rvm`
//! and has the same requirements (currently `std` and `arc`).
//!
//! It defines the typed, serializable results shared by explanation capture
//! and reporting:
//!
//! - [`ExplanationSettings`] selects what an explanation captures.
//! - [`ExplanationReport`] explains why a query produced its result.
//! - [`PartialEvalResult`] holds the residual conditions of a partial
//!   evaluation.
//! - [`ExplainError`] reports why an explanation could not be produced.
//!
//! The report types are `#[non_exhaustive]` so that fields and variants can
//! be added without breaking callers. They implement [`serde::Serialize`];
//! JSON is produced only by the language bindings. Consumers of an
//! [`ExplanationReport`] should accept unknown fields and enum values.
//! Consumers that enforce a [`PartialEvalResult`] must instead fail closed:
//! they combine its alternatives as its [`RuleKind`] says, use it only when
//! its [`ResidualStatus`] is `exact`, and reject an unknown [`RuleKind`],
//! [`ResidualStatus`] or [`ResidualKind`] (see [`ResidualCondition`]).
//!
//! Runtime values use the crate's usual [`Value`](crate::Value)
//! serialization, except that an undefined value is omitted, which keeps it
//! distinct from `false`, `null` and the string `"<undefined>"`. An absent
//! `query_result` always means undefined; an absent rule `result` means
//! undefined unless a `result_redacted: true` flag says it was withheld
//! (see [`ReportedValue`]). Sets serialize as arrays, and non-string object
//! keys as JSON strings.
//!
//! A report is complete: it explains every rule within the selected scope.
//! Signalling a report that was cut short will come with bounded tracing.

mod error;
mod report;
mod settings;

#[cfg(test)]
pub(crate) mod fixtures;
#[cfg(test)]
#[allow(clippy::panic_in_result_fn)]
mod tests;

pub use error::ExplainError;
pub use report::{
    ConditionExplanation, ConditionKind, DefinitionExplanation, EmissionExplanation,
    ExplanationReport, LoopWitness, Operand, Operator, Outcome, PartialEvalResult, ReportedValue,
    ResidualCondition, ResidualKind, ResidualQuery, ResidualStatus, RuleExplanation, RuleKind,
    SourceLocation,
};
pub use settings::{ConditionMode, ExplanationScope, ExplanationSettings, ValueMode};

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
//! - [`Provenance`] decodes, from a compiled program, the policy text,
//!   location, kind, operand references and owning rule of each check.
//!
//! The report types are `#[non_exhaustive]` so that fields and variants can
//! be added without breaking callers. They implement [`serde::Serialize`];
//! JSON is produced only by the language bindings. Consumers of an
//! [`ExplanationReport`] should accept unknown fields and enum values.
//! Consumers that enforce a [`PartialEvalResult`] must instead fail closed:
//! they combine its alternatives as its [`RuleKind`] says, use it only when
//! its [`ResidualStatus`] is `exact` (or `partial`, if they handle
//! unresolved alternatives, and then only to fail closed), and reject an
//! unknown [`RuleKind`], [`ResidualStatus`], [`ResidualAlternativeStatus`]
//! or [`ResidualKind`] (see [`ResidualCondition`]), and a [`ResidualCall`] or
//! [`ResidualArgument`] that breaks the rules on [`ResidualCall`].
//!
//! Runtime values use the crate's usual [`Value`](crate::Value)
//! serialization, except that an undefined value is omitted, which keeps it
//! distinct from `false`, `null` and the string `"<undefined>"`. In a report
//! for a successful evaluation, an absent `query_result` means undefined.
//! A report can also accompany a failed evaluation, such as one that
//! failed on a [`RuleOutcome::Conflict`]: the evaluation error is then
//! authoritative, an absent `query_result` means there is no result rather
//! than undefined, and the conflicting rule's outcome identifies the cause.
//! Such a report covers rules only up to the error. No API returns one yet;
//! the producer API is later work.
//! An absent rule `result` means
//! undefined unless a `result_redacted: true` or `result_elided: true` flag
//! says it was withheld or not stored due to capture limits
//! (see [`ReportedValue`]). Sets serialize as arrays, and non-string object
//! keys as JSON strings.
//!
//! A serialized report starts with `schema_version`
//! ([`ExplanationReport::SCHEMA_VERSION`]) and identifies what was queried
//! in [`QueryTarget`]. Each [`RuleExplanation`] says whether the rule
//! matched, matched nothing or conflicted ([`RuleOutcome`]).
//!
//! [`ConditionSite`] stores policy text once per site. Evaluated conditions
//! in definitions and proofs reference it by site ID and identify their
//! owning rule invocation. [`ResultExplanation`] groups attribution by Rego
//! result equality, with bounded proofs, each with the loop iterations that
//! produced it ([`IterationBinding`]), and unit-named counts that are exact
//! or, when evaluation stopped early, lower bounds ([`Count`]). Distinct
//! elements are identified by loop site, iterated collection and key
//! ([`DistinctElements`]). Concrete operand paths are independently opt-in;
//! [`ConcretePath`] distinguishes not captured, unrepresentable, and a
//! captured absence of a direct path.
//!
//! A report for a successful evaluation is complete: it explains every rule
//! within the selected scope. A report accompanying a failed evaluation
//! covers rules only up to the error.
//! Signalling a report that was cut short will come with bounded tracing.

mod error;
mod provenance;
mod report;
mod settings;

#[cfg(test)]
pub(crate) mod fixtures;
#[cfg(test)]
#[allow(clippy::panic_in_result_fn)]
mod tests;

pub use error::ExplainError;
pub use provenance::{CheckSite, Provenance, RuleOwner, SiteId, SiteOwner};
pub use report::{
    ConcretePath, ConditionExplanation, ConditionKind, ConditionOwner, ConditionSite, Count,
    DefinitionExplanation, Derivation, DistinctElements, EmissionExplanation, ExplanationReport,
    IterationBinding, LoopWitness, Operand, Operator, Outcome, PartialEvalResult, PathRoot,
    PathSegment, QueryTarget, ReportedValue, ResidualAlternativeStatus, ResidualArgument,
    ResidualCall, ResidualCondition, ResidualKind, ResidualQuery, ResidualStatus,
    ResidualUnresolved, ResidualUnresolvedReason, ResultExplanation, RuleExplanation, RuleKind,
    RuleOutcome, SourceLocation,
};
pub use settings::{ConditionMode, ExplanationScope, ExplanationSettings, ValueMode};

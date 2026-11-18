// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::program::RuleType;
use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use serde::ser::{Error as _, SerializeMap as _, SerializeStruct, Serializer};
use serde::Serialize;

/// Serialization helper: an undefined value is omitted from the output.
const fn is_undefined(value: &Value) -> bool {
    matches!(*value, Value::Undefined)
}

/// Serialization helper: a missing or undefined value is omitted from the
/// output.
const fn is_absent(value: &Option<Value>) -> bool {
    matches!(*value, None | Some(Value::Undefined))
}

/// Whether [`serialize_reported`] writes a field for `value`.
const fn is_reported(value: Option<&ReportedValue>) -> bool {
    match value {
        Some(reported) => match *reported {
            ReportedValue::Known(ref known) => !is_undefined(known),
            ReportedValue::Redacted | ReportedValue::Elided => true,
        },
        None => false,
    }
}

/// Length hint for `serialize_struct`: the number of fields written.
fn field_count(written: &[bool]) -> usize {
    written.iter().filter(|flag| **flag).count()
}

/// Writes a known value or its redaction/elision marker.
fn serialize_reported<S: SerializeStruct>(
    state: &mut S,
    field: &'static str,
    flag: &'static str,
    elided: &'static str,
    value: Option<&ReportedValue>,
) -> Result<(), S::Error> {
    let Some(reported) = value else {
        state.skip_field(field)?;
        state.skip_field(flag)?;
        return state.skip_field(elided);
    };
    match *reported {
        ReportedValue::Known(ref known) if !is_undefined(known) => {
            state.serialize_field(field, known)?;
            state.skip_field(flag)?;
            state.skip_field(elided)
        }
        ReportedValue::Known(_) => {
            state.skip_field(field)?;
            state.skip_field(flag)?;
            state.skip_field(elided)
        }
        ReportedValue::Redacted => {
            state.skip_field(field)?;
            state.serialize_field(flag, &true)?;
            state.skip_field(elided)
        }
        ReportedValue::Elided => {
            state.skip_field(field)?;
            state.skip_field(flag)?;
            state.serialize_field(elided, &true)
        }
    }
}

/// Writes a [`ReportedValue`] as an object of its own: `{"value": ...}`,
/// `{"redacted": true}`, `{"elided": true}`, or `{}` for undefined.
struct ReportedEntry<'a>(&'a ReportedValue);

impl Serialize for ReportedEntry<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[is_reported(Some(self.0))]);
        let mut state = serializer.serialize_struct("ReportedValue", len)?;
        serialize_reported(&mut state, "value", "redacted", "elided", Some(self.0))?;
        state.end()
    }
}

/// Writes a list of [`ReportedValue`]s as a JSON array of [`ReportedEntry`].
struct ReportedEntries<'a>(&'a [ReportedValue]);

impl Serialize for ReportedEntries<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.0.iter().map(ReportedEntry))
    }
}

/// Explanation of why a query produced its result.
///
/// A report for a successful evaluation is complete: it explains every rule
/// within the selected [`ExplanationScope`](super::ExplanationScope).
///
/// Serializes as `{"schema_version": 2, "query": ..., "query_result": ...,
/// "rules": [...], "checks": [...]}`, with `schema_version` always first
/// (see [`ExplanationReport::SCHEMA_VERSION`]) and `query_result` omitted
/// when undefined or when there is no result.
///
/// A report for a failed evaluation, for example one that failed on a
/// [`RuleOutcome::Conflict`], accompanies the evaluation error. The error is
/// authoritative: `query_result` is then absent because there is no result,
/// not because it is undefined, and the report covers rules only up to the
/// error. No API returns such a report yet; the producer API is later work.
///
/// Serializing a report fails if any [`ResultExplanation`] in it has more
/// proofs than its `derivations_total`; see [`ResultExplanation::new`].
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ExplanationReport {
    /// What was queried; see [`QueryTarget`].
    pub query: QueryTarget,
    /// The value returned by the query. Omitted from JSON when undefined,
    /// and [`Value::Undefined`] when the evaluation failed and returned no
    /// value.
    pub query_result: Value,
    /// Explanations of the rules that the query evaluated.
    pub rules: Vec<RuleExplanation>,
    /// Static check metadata, stored once per site in this report.
    /// Every condition's `site_id` resolves to exactly one entry here.
    pub checks: Vec<ConditionSite>,
}

impl ExplanationReport {
    /// Version of the report's serialized shape, always written first as
    /// `schema_version`. It changes when existing fields change meaning or
    /// shape; adding fields or enum values does not change it. A report
    /// without `schema_version` uses the version 1 shape, in which each
    /// condition carried its own text, kind, location and operator, and
    /// which had no `query`, rule `outcome` or per-result attribution.
    /// Consumers should reject a version they don't know.
    pub const SCHEMA_VERSION: u32 = 2;
}

impl Serialize for ExplanationReport {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let defined = !is_undefined(&self.query_result);
        let len = field_count(&[true, true, defined, true, true]);
        let mut state = serializer.serialize_struct("ExplanationReport", len)?;
        state.serialize_field("schema_version", &Self::SCHEMA_VERSION)?;
        state.serialize_field("query", &self.query)?;
        if defined {
            state.serialize_field("query_result", &self.query_result)?;
        } else {
            state.skip_field("query_result")?;
        }
        state.serialize_field("rules", &self.rules)?;
        state.serialize_field("checks", &self.checks)?;
        state.end()
    }
}

/// What a report's query evaluated.
///
/// Serializes as `{"entry_point": ..., "rule": ..., "call_instance": ...,
/// "with_overrides": ...}`; `rule` and `call_instance` are omitted when
/// absent.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct QueryTarget {
    /// The query or entry point as the caller gave it, for example
    /// `data.test.allow`. Copied verbatim, including caller-supplied literals;
    /// never redacted. Callers must not put secrets in this string.
    pub entry_point: String,
    /// Fully qualified rule or function the query names. `None` when the
    /// query is not a rule reference, such as an expression over several
    /// rules.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule: Option<String>,
    /// [`RuleExplanation::call_instance`] of the top-level evaluation of
    /// [`rule`](Self::rule). It tells that evaluation apart from other
    /// evaluations of the same rule, for example under a `with` inside the
    /// policy. `None` when there is no such entry in
    /// [`ExplanationReport::rules`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub call_instance: Option<u64>,
    /// Whether the query itself applied `with` overrides, so its top-level
    /// evaluation saw replaced `input` or `data` rather than the documents
    /// the evaluation was given. `with` modifiers inside the policy are not
    /// counted here; they show up as separate rule evaluations.
    pub with_overrides: bool,
}

/// Explanation of one evaluation of a rule.
///
/// There is one per evaluation, in evaluation order, so a name can repeat:
/// for example a function called with different arguments, or a rule
/// evaluated again under `with`.
///
/// Serializes as `{"name": ..., "call_instance": ..., "kind": ...,
/// "outcome": ..., "result": ..., "emissions": [...], "definitions": [...],
/// "results": [...]}`. `result` is written as `"result": ...`, or replaced
/// by `"result_redacted": true` or `"result_elided": true` when withheld
/// (see [`ReportedValue`]), and is omitted when undefined. Empty
/// `emissions` and `definitions`, and `results` that were not captured, are
/// omitted.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct RuleExplanation {
    /// Fully qualified rule name, for example `data.test.allow`.
    pub name: String,
    /// Report-local invocation identifier, unique across all rule/function
    /// evaluations, including repeated calls and evaluations under `with`.
    /// Identifiers are small sequential numbers the producer assigns within the report, not
    /// addresses or hashes, so they stay below 2^53 and are exact in JSON
    /// consumers that read numbers as doubles.
    pub call_instance: u64,
    /// Kind of rule.
    pub kind: RuleKind,
    /// Whether a definition matched, none did, or definitions conflicted.
    pub outcome: RuleOutcome,
    /// Final value of the rule. A complete rule or function with no
    /// successful definition returns its default, or undefined if absent.
    /// A partial set with no contributions returns an empty set (`[]` in
    /// JSON); a partial object returns an empty object (`{}`). On a
    /// [`RuleOutcome::Conflict`] it is undefined, not the default.
    /// Undefined is omitted; redaction/elision have explicit markers.
    pub result: ReportedValue,
    /// Explanations of the values emitted by a partial rule.
    pub emissions: Vec<EmissionExplanation>,
    /// Explanations of the evaluated rule bodies; see
    /// [`DefinitionExplanation`].
    pub definitions: Vec<DefinitionExplanation>,
    /// Per-result attribution for the queried rule, grouped by Rego value
    /// equality (and key for partial objects), not by serialized JSON.
    /// `None` means not captured, including helper summaries; `Some([])`
    /// means captured with no defined results. Helpers never consume the
    /// queried rule's proof budget. Legacy `emissions` remain per contribution.
    pub results: Option<Vec<ResultExplanation>>,
    /// Body attempts, including failed parameter matches and failed bodies
    /// before a successful `else`. `None` means not captured; an empty list
    /// means no attempt ran, for example a default-only rule.
    pub attempts: Option<Vec<AttemptExplanation>>,
    /// Logical scopes entered within this invocation. `None` means not
    /// captured, not that no nested scopes existed.
    pub scopes: Option<Vec<ScopeExplanation>>,
    /// Uses of callee results by this invocation, including cached results.
    /// `None` means not captured. Each use retains its caller's scope:
    /// a cached result can be used both positively and negatively.
    pub calls: Option<Vec<CallUse>>,
}

impl Serialize for RuleExplanation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[
            true,
            true,
            true,
            true,
            is_reported(Some(&self.result)),
            !self.emissions.is_empty(),
            !self.definitions.is_empty(),
            self.results.is_some(),
            self.attempts.is_some(),
            self.scopes.is_some(),
            self.calls.is_some(),
        ]);
        let mut state = serializer.serialize_struct("RuleExplanation", len)?;
        state.serialize_field("name", &self.name)?;
        state.serialize_field("call_instance", &self.call_instance)?;
        state.serialize_field("kind", &self.kind)?;
        state.serialize_field("outcome", &self.outcome)?;
        serialize_reported(
            &mut state,
            "result",
            "result_redacted",
            "result_elided",
            Some(&self.result),
        )?;
        if self.emissions.is_empty() {
            state.skip_field("emissions")?;
        } else {
            state.serialize_field("emissions", &self.emissions)?;
        }
        if self.definitions.is_empty() {
            state.skip_field("definitions")?;
        } else {
            state.serialize_field("definitions", &self.definitions)?;
        }
        match self.results {
            Some(ref results) => state.serialize_field("results", results)?,
            None => state.skip_field("results")?,
        }
        match self.attempts {
            Some(ref attempts) => state.serialize_field("attempts", attempts)?,
            None => state.skip_field("attempts")?,
        }
        match self.scopes {
            Some(ref scopes) => state.serialize_field("scopes", scopes)?,
            None => state.skip_field("scopes")?,
        }
        match self.calls {
            Some(ref calls) => state.serialize_field("calls", calls)?,
            None => state.skip_field("calls")?,
        }
        state.end()
    }
}

/// Whether a rule evaluation matched.
///
/// Serializes as `{"status": "matched"}`, `{"status": "no_match"}` or
/// `{"status": "conflict", "values": [...]}`.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum RuleOutcome {
    /// At least one definition body succeeded: it gave a complete rule or
    /// function its value, or contributed to a partial rule.
    Matched,
    /// No definition body succeeded. The result is the default of a complete
    /// rule or function, or undefined without one; a partial rule's result
    /// is empty.
    NoMatch,
    /// Successful definitions of a complete rule or function produced
    /// different values, or of a partial object different values for one
    /// key. Rego makes this an evaluation error, so the rule's result is
    /// undefined and its default is not used.
    Conflict {
        /// At least two of the conflicting values, distinct by Rego
        /// equality, in evaluation order. Each is subject to
        /// [`ValueMode`](super::ValueMode) and capture limits like any
        /// other value, so it can be redacted or elided. Each serializes as
        /// `{"value": ...}`, `{"redacted": true}` or `{"elided": true}`.
        values: Vec<ReportedValue>,
        /// Conflicting partial-object key, subject to value redaction and
        /// elision. Absent for complete rules/functions, or when not captured;
        /// absence never means that every object key conflicted.
        key: Option<ReportedValue>,
    },
}

impl Serialize for RuleOutcome {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let (status, values, key) = match *self {
            Self::Matched => ("matched", None, None),
            Self::NoMatch => ("no_match", None, None),
            Self::Conflict {
                ref values,
                ref key,
            } => ("conflict", Some(values), key.as_ref()),
        };
        let len = field_count(&[true, values.is_some(), is_reported(key)]);
        let mut state = serializer.serialize_struct("RuleOutcome", len)?;
        state.serialize_field("status", status)?;
        match values {
            Some(values) => state.serialize_field("values", &ReportedEntries(values))?,
            None => state.skip_field("values")?,
        }
        serialize_reported(&mut state, "key", "key_redacted", "key_elided", key)?;
        state.end()
    }
}

/// Kind of rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum RuleKind {
    /// A complete rule, such as `allow if ...`.
    Complete,
    /// A partial set rule, such as `deny contains msg if ...`.
    PartialSet,
    /// A partial object rule, such as `labels[k] := v if ...`.
    PartialObject,
    /// A function, such as `is_admin(user) if ...`.
    Function,
}

/// Maps the compiled rule type. Functions are compiled as complete rules, so
/// this never returns [`RuleKind::Function`]; producers set it for rules with
/// function information.
impl From<RuleType> for RuleKind {
    fn from(rule_type: RuleType) -> Self {
        match rule_type {
            RuleType::Complete => Self::Complete,
            RuleType::PartialSet => Self::PartialSet,
            RuleType::PartialObject => Self::PartialObject,
        }
    }
}

/// Explanation of one value emitted by a partial rule.
///
/// There is one emission per successful contribution, in evaluation order: a
/// value contributed twice, by two definitions or two loop iterations, has two
/// emissions.
///
/// Serializes as `{"index": ..., "definition": ..., "key": ..., "value": ...,
/// "conditions": [...]}`. `key` and `value` are replaced by
/// `"key_redacted": true` / `"value_redacted": true` when redacted, or
/// `"key_elided": true` / `"value_elided": true` when elided, and are
/// omitted when undefined; `key` is also omitted for a partial set.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct EmissionExplanation {
    /// 0-based index of the emission within the rule.
    pub index: usize,
    /// 0-based index of the definition that emitted the value.
    pub definition: usize,
    /// Key of a partial object entry; `None` (absent from JSON) for a
    /// partial set.
    pub key: Option<ReportedValue>,
    /// The set member, or the value of the partial object entry.
    pub value: ReportedValue,
    /// Conditions that held when the value was emitted.
    pub conditions: Vec<ConditionExplanation>,
}

impl Serialize for EmissionExplanation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[
            true,
            true,
            is_reported(self.key.as_ref()),
            is_reported(Some(&self.value)),
            true,
        ]);
        let mut state = serializer.serialize_struct("EmissionExplanation", len)?;
        state.serialize_field("index", &self.index)?;
        state.serialize_field("definition", &self.definition)?;
        serialize_reported(
            &mut state,
            "key",
            "key_redacted",
            "key_elided",
            self.key.as_ref(),
        )?;
        serialize_reported(
            &mut state,
            "value",
            "value_redacted",
            "value_elided",
            Some(&self.value),
        )?;
        state.serialize_field("conditions", &self.conditions)?;
        state.end()
    }
}

/// Explanation of one evaluated body of a rule definition.
///
/// For a complete rule or function there is one per evaluated definition,
/// describing the body that decided it: the first body that succeeded, or
/// the last body evaluated when none did. A partial rule evaluates every
/// body, so it has one per evaluated body.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct DefinitionExplanation {
    /// 0-based index of the definition within the rule.
    pub index: usize,
    /// 0-based index of the body within the definition: 0 for the main
    /// body, then its `else` branches or additional query blocks
    /// (`p { a } { b }`) in source order.
    pub body: usize,
    /// Whether the body succeeded: [`Outcome::Success`],
    /// [`Outcome::Failure`] or [`Outcome::Assumed`].
    pub outcome: Outcome,
    /// Source location of the definition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Reported conditions of the body.
    pub conditions: Vec<ConditionExplanation>,
}

/// Outcome of a condition or definition body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum Outcome {
    /// It held.
    Success,
    /// It did not hold: a condition was `false`, or a body failed.
    Failure,
    /// A condition's value was undefined.
    Undefined,
    /// It depends on unknown input and was assumed to hold.
    Assumed,
}

/// Static metadata for a compiled condition site.
///
/// Site identifiers are unique within a report's program, not stable across
/// compilations. Repeated calls/iterations share this metadata, never operands.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ConditionSite {
    /// Identifier used by [`ConditionExplanation::site_id`].
    pub site_id: u32,
    /// Source text of the condition.
    pub text: String,
    /// Kind of condition.
    pub kind: ConditionKind,
    /// Source location of the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Operator of a comparison or membership test.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<Operator>,
}

/// Rule/function invocation that evaluated a condition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct ConditionOwner {
    /// Fully qualified rule/function name, including for helper checks.
    pub rule: String,
    /// Matches the owning [`RuleExplanation::call_instance`], not the
    /// caller's invocation even when they return equal values.
    pub call_instance: u64,
    /// Dynamic body attempt in the owning invocation. Absent when not
    /// captured or outside a body; inspect the invocation's `attempts`
    /// capture state before concluding no attempt existed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub attempt: Option<u64>,
    /// Innermost logical scope in that invocation, not the caller's scope.
    /// Absent outside a scope or when scope capture was unavailable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scope: Option<u64>,
}

/// One dynamic try of a definition/body in a rule invocation.
///
/// Attempts start before parameter matching. A rejected match has outcome
/// [`Outcome::Undefined`]; a body returning `false` successfully has outcome
/// [`Outcome::Success`]. Failed attempts are context, never independent causes
/// of a successful derivation. `else` bodies are separate attempts.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct AttemptExplanation {
    /// Evaluation-local identifier, assigned sequentially by the VM.
    pub attempt: u64,
    /// Definition within the enclosing [`RuleExplanation`].
    pub definition: usize,
    /// Body within that definition, zero for the primary body.
    pub body: usize,
    /// Absent if evaluation aborted before this attempt completed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub outcome: Option<Outcome>,
    /// Checks evaluated in this attempt, including failed pre-`else` bodies
    /// not retained by the deciding-body [`DefinitionExplanation`] summary.
    /// Absent when not captured; captured empty can represent a parameter
    /// match rejected before any body checks. These remain context unless
    /// they belong to the successful producing path.
    ///
    /// Captured parameter bindings can use [`ConditionKind::Binding`] at
    /// the parameter's source site: `binding` names the parameter and `left`
    /// holds the actual argument, including its concrete path or causal
    /// origins. The owner is the callee attempt. This records a real binding,
    /// not a fabricated body predicate: binding a defined `false` succeeds.
    /// It also works for a value-only function with no body checks.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conditions: Option<Vec<ConditionExplanation>>,
}

/// Logical construct enclosing checks, emissions or nested scopes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ScopeKind {
    /// A `not` operand, entered before its evaluation.
    Negation,
    /// An `every` quantifier.
    Every,
    /// An array comprehension.
    ArrayComprehension,
    /// A set comprehension.
    SetComprehension,
    /// An object comprehension.
    ObjectComprehension,
}

/// One dynamic entry into a logical construct within a rule invocation.
///
/// Scopes form call-local trees: a callee starts a new tree even when used
/// inside a caller's negation. Follow [`CallUse`] edges to recover polarity
/// for a particular use; do not assign one inherited polarity to a cached
/// callee used under several different scopes.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ScopeExplanation {
    /// Evaluation-local identifier, assigned sequentially by the VM.
    pub scope: u64,
    /// Construct that was entered.
    pub kind: ScopeKind,
    /// Parent scope in the same invocation, absent at its local root.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<u64>,
    /// Attempt within the enclosing [`RuleExplanation`].
    pub attempt: u64,
    /// Static construct site in [`ExplanationReport::checks`].
    pub site_id: u32,
    /// Outcome of the enclosing construct, not of its inner checks.
    /// Negation never has outcome `Undefined`; a comprehension succeeds
    /// even when empty. Absent if evaluation aborted before the scope ended.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub outcome: Option<Outcome>,
}

/// One use of a callee result by the enclosing rule invocation.
///
/// The callee's checks retain their own owners/scopes. Local polarity is
/// the parity of negation scopes enclosing a check; logical polarity for
/// one use also follows the caller scope on each edge from the query.
/// A fresh call and each cached reuse have separate edges to the same
/// callee invocation. Equal returned values do not identify invocations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct CallUse {
    /// Callee [`RuleExplanation::call_instance`].
    pub call_instance: u64,
    /// Caller attempt, absent outside a body or when not captured.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub attempt: Option<u64>,
    /// Innermost caller scope, absent at its local root or when not captured.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scope: Option<u64>,
}

/// One evaluation of a condition, referencing text/semantics stored once
/// in [`ExplanationReport::checks`]. A proof can contain several evaluations
/// of the same site, with different operands or helper call instances.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ConditionExplanation {
    /// Static check site; must resolve in [`ExplanationReport::checks`].
    pub site_id: u32,
    /// Invocation that evaluated this check.
    pub owner: ConditionOwner,
    /// Outcome of this evaluation, not an aggregate over other iterations.
    pub outcome: Outcome,
    /// Left operand, or the checked value of a unary condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub left: Option<Operand>,
    /// Right operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub right: Option<Operand>,
    /// Iteration summary of a loop-backed condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub witness: Option<LoopWitness>,
    /// Variable bound by a binding condition, such as `x` in `x := ...`,
    /// or a parameter binding in [`AttemptExplanation::conditions`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
}

/// Kind of condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ConditionKind {
    /// A comparison such as `a == b` or `a < b`.
    Comparison,
    /// A membership test such as `x in xs`.
    Membership,
    /// A loop over a collection, such as `some x in xs` or `every x in xs`.
    /// Its iterations are summarized in
    /// [`witness`](ConditionExplanation::witness).
    Iteration,
    /// A value that must be truthy.
    Truthiness,
    /// A value that must be defined.
    Existence,
    /// A negated expression, `not ...`.
    Negation,
    /// A variable binding, `x := ...`, or captured parameter-binding evidence.
    Binding,
}

/// Operator of a comparison or membership condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub enum Operator {
    /// `==`
    #[serde(rename = "==")]
    Eq,
    /// `!=`
    #[serde(rename = "!=")]
    Ne,
    /// `<`
    #[serde(rename = "<")]
    Lt,
    /// `<=`
    #[serde(rename = "<=")]
    Le,
    /// `>`
    #[serde(rename = ">")]
    Gt,
    /// `>=`
    #[serde(rename = ">=")]
    Ge,
    /// `in`
    #[serde(rename = "in")]
    In,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match *self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::In => "in",
        })
    }
}

/// A runtime value that may have been withheld.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ReportedValue {
    /// The recorded value.
    Known(Value),
    /// The value was withheld by [`ValueMode::Redacted`](super::ValueMode::Redacted).
    Redacted,
    /// Not stored because a producer capture limit was reached. Not
    /// undefined, and not a redaction decision.
    /// [`ExplanationSettings`](super::ExplanationSettings) has no value-size
    /// setting yet; its only limit,
    /// [`max_derivations`](super::ExplanationSettings::max_derivations),
    /// drops whole proofs and counts them in
    /// [`ResultExplanation::derivations_dropped`] rather than eliding
    /// values. Serializes as `"elided": true`, or as `"<field>_elided": true`
    /// (for example `result_elided`, `key_elided` or `value_elided`) in a
    /// named position.
    Elided,
}

/// A runtime operand of a condition.
///
/// Serializes as `{"path": ..., "concrete_path": {...}, "value": ...}`.
/// `concrete_path` is always present (see [`ConcretePath`]); `path` is
/// omitted when absent. `value` is replaced by `"redacted": true` or
/// `"elided": true` when withheld, and omitted when undefined.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct Operand {
    /// The runtime value.
    pub value: ReportedValue,
    /// The reference the value was read from, as written in the policy, for
    /// example `input.user.role` or `data.tokens[input.user.name]`. Like
    /// condition text, it is policy source and is never redacted.
    pub path: Option<String>,
    /// Concrete origin, independently controlled by
    /// [`ExplanationSettings::capture_paths`](super::ExplanationSettings::capture_paths).
    /// A policy source template in `path` is not a captured concrete path.
    pub concrete_path: ConcretePath,
    /// Inputs that influenced a computed operand; their values are not
    /// asserted to equal this operand's value. Independently opt-in with
    /// concrete path capture and subject to its redaction rules. `None`
    /// means not captured, not no dependencies.
    pub origins: Option<CausalOrigins>,
}

impl Serialize for Operand {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[
            self.path.is_some(),
            true,
            is_reported(Some(&self.value)),
            self.origins.is_some(),
        ]);
        let mut state = serializer.serialize_struct("Operand", len)?;
        match self.path {
            Some(ref path) => state.serialize_field("path", path)?,
            None => state.skip_field("path")?,
        }
        state.serialize_field("concrete_path", &self.concrete_path)?;
        serialize_reported(&mut state, "value", "redacted", "elided", Some(&self.value))?;
        match self.origins {
            Some(ref origins) => state.serialize_field("origins", origins)?,
            None => state.skip_field("origins")?,
        }
        state.end()
    }
}

/// Bounded causal input identities for a computed operand, not direct reads
/// of the operand's returned value.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct CausalOrigins {
    /// Captured identities; sensitive paths are withheld in their entirety
    /// using [`ConcretePath::Redacted`], never replaced by fabricated keys.
    pub paths: Vec<ConcretePath>,
    /// Whether every contributing origin is represented. `false` means
    /// some origins were omitted; an empty incomplete list proves nothing
    /// about whether inputs contributed.
    pub complete: bool,
}

/// Whether a concrete operand path was captured.
///
/// Serializes as `{"status": ...}`, plus `root` and `segments` for
/// [`ConcretePath::Captured`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
#[serde(tag = "status", rename_all = "snake_case")]
#[non_exhaustive]
pub enum ConcretePath {
    /// No capture was attempted: path capture was off, or the producer does
    /// not track provenance for this operand. Says nothing about whether
    /// the operand has a direct path.
    #[default]
    NotCaptured,
    /// Path capture was enabled, but the path was withheld by redaction.
    /// Runtime-derived keys can be sensitive even when the policy-source
    /// template is not. Producers must withhold the entire concrete path
    /// when a segment is sensitive, rather than stringify/redact one key
    /// into a different reference.
    Redacted,
    /// Capture established that this operand has no direct path (a literal
    /// or computed value). This does not imply no causal input dependencies.
    NoPath,
    /// Capture established that this operand has a direct reference, but a
    /// segment can't be expressed as a [`PathSegment`]: a non-string object
    /// key or a set member. Unlike [`ConcretePath::NotCaptured`], capture
    /// was enabled and the provenance was tracked.
    Unrepresentable,
    /// A direct reference, including its namespace and typed segments.
    Captured {
        /// Root namespace of the reference.
        root: PathRoot,
        /// Segments after the root; empty means the root itself.
        segments: Vec<PathSegment>,
    },
}

/// Root namespace of a concrete reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum PathRoot {
    /// Evaluation input.
    Input,
    /// Policy data.
    Data,
    /// Host-supplied ambient context, separate from evaluation input.
    Context,
}

/// One path segment. Numeric-looking object keys remain keys, never indices.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum PathSegment {
    /// String object key, preserved verbatim including punctuation and
    /// escapes. Non-string object keys and set-member references are not
    /// representable here: producers use [`ConcretePath::Unrepresentable`],
    /// never coerce them into strings or array indices.
    Key(String),
    /// Array index.
    Index(u64),
}

/// A successful producing path, including helper checks, without copying
/// policy text. Definition/body indices refer to the queried rule; each
/// check's owner identifies the invocation that actually evaluated it.
///
/// Serializes as `{"definition": ..., "body": ..., "conditions": [...],
/// "bindings": [...]}`, with `bindings` omitted when not captured and an
/// empty array when capture established that no loops contributed.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct Derivation {
    /// Producing definition index.
    pub definition: usize,
    /// Producing body index (`0` is the primary body).
    pub body: usize,
    /// Producing body attempt, resolving in the queried invocation's
    /// [`RuleExplanation::attempts`]. Absent when not captured.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub attempt: Option<u64>,
    /// Whether this derivation depends on unknown information. Absent when
    /// not established, including when a helper's evidence was not captured.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conditionality: Option<Conditionality>,
    /// Evaluated checks on this producing path, in evaluation order.
    /// Contributing parameter bindings may be copied from callee attempts,
    /// retaining their callee owners. An argument's presence alone does not
    /// establish that it contributed to the result.
    pub conditions: Vec<ConditionExplanation>,
    /// The loop iteration that produced this proof at each loop on its
    /// path, outermost first, unlike a condition's loop-wide
    /// [`witness`](ConditionExplanation::witness). `Some([])` means no loop
    /// contributed; `None` means iteration bindings were not captured.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bindings: Option<Vec<IterationBinding>>,
}

/// Whether unknown information is necessary for a particular derivation or
/// for the existence of a result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum Conditionality {
    /// A derivation uses no assumption; a result has at least one such
    /// derivation, even if other contributors remain conditional.
    Concrete,
    /// A derivation needs an assumption; all derivations of a result do.
    /// Producers must establish this beyond retained evidence/capture caps.
    Assumed,
}

/// The iteration of one loop that a [`Derivation`] went through.
///
/// `(site_id, collection, key)` is the element's identity, the same one
/// [`DistinctElements`] counts. Serializes as `{"site_id": ...,
/// "collection": ..., "key": ..., "value": ...}`; `key` and `value` are
/// replaced by `"key_redacted": true` / `"value_redacted": true` or
/// `"key_elided": true` / `"value_elided": true` when withheld, and are
/// omitted when undefined.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct IterationBinding {
    /// Compiled loop site, resolving in [`ExplanationReport::checks`].
    pub site_id: u32,
    /// The iterated collection; see [`DistinctElements::collection`].
    /// Identifiers are small sequential numbers the producer assigns within the report, not
    /// addresses or hashes, so they stay below 2^53 and are exact in JSON
    /// consumers that read numbers as doubles.
    pub collection: u64,
    /// Key of the iteration: an array index, an object key, or the member
    /// of a set. Subject to [`ValueMode`](super::ValueMode) and capture
    /// limits like other runtime values.
    pub key: ReportedValue,
    /// Value of the iteration; equal to `key` for a set. Subject to
    /// [`ValueMode`](super::ValueMode) and capture limits like other
    /// runtime values.
    pub value: ReportedValue,
}

impl Serialize for IterationBinding {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[
            true,
            true,
            is_reported(Some(&self.key)),
            is_reported(Some(&self.value)),
        ]);
        let mut state = serializer.serialize_struct("IterationBinding", len)?;
        state.serialize_field("site_id", &self.site_id)?;
        state.serialize_field("collection", &self.collection)?;
        serialize_reported(
            &mut state,
            "key",
            "key_redacted",
            "key_elided",
            Some(&self.key),
        )?;
        serialize_reported(
            &mut state,
            "value",
            "value_redacted",
            "value_elided",
            Some(&self.value),
        )?;
        state.end()
    }
}

/// A count that is exact, or a lower bound when evaluation stopped early.
///
/// Evaluation stops at the first success where only one is needed, for
/// example `some x in xs` in a body that only has to hold, or a complete
/// rule whose value is already decided. What it skipped is not counted, so
/// such a count is [`Count::AtLeast`]. Serializes as `{"exact": n}` or
/// `{"at_least": n}`; consumers must not read an `at_least` count as exact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum Count {
    /// Every occurrence was observed: there are exactly this many.
    Exact(u64),
    /// Evaluation stopped early after observing this many; there may be
    /// more.
    AtLeast(u64),
}

impl Count {
    /// The number observed: the exact count, or the lower bound.
    pub const fn value(self) -> u64 {
        match self {
            Self::Exact(count) | Self::AtLeast(count) => count,
        }
    }

    /// Whether the count is exact rather than a lower bound.
    pub const fn is_exact(self) -> bool {
        matches!(self, Self::Exact(_))
    }
}

/// Count of distinct contributing elements of one iterated collection at
/// one loop site, for one result.
///
/// An element's identity is `(site_id, collection, key)`: its position or
/// key within one particular collection iterated at one loop site, not its
/// value. Each `(site_id, collection)` pair has its own entry, so elements
/// of different collections at the same position or key are never merged,
/// for example in a nested loop over each resource's tags, or a helper
/// called over different collections. Invocations of the site that iterate
/// the same collection share an entry.
///
/// Serializes as `{"site_id": ..., "loop": ..., "collection": ...,
/// "count": ...}`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct DistinctElements {
    /// Compiled loop site, resolving in [`ExplanationReport::checks`].
    /// Disambiguates loops with identical source templates in separate
    /// definitions.
    pub site_id: u32,
    /// Loop identity in policy-source form, e.g. `input.resources[_]`.
    /// This labels the iterated side, not resources reached by cross-lookups.
    #[serde(rename = "loop")]
    pub loop_name: String,
    /// Report-local identifier of the iterated collection. Producers give
    /// two iterations the same identifier only when they iterate the same
    /// collection: the same concrete `input` or `data` reference or, for a
    /// computed collection, the same evaluated instance. Not stable across
    /// reports. [`IterationBinding::collection`] uses the same identifiers.
    /// Identifiers are small sequential numbers the producer assigns within the report, not
    /// addresses or hashes, so they stay below 2^53 and are exact in JSON
    /// consumers that read numbers as doubles.
    pub collection: u64,
    /// Distinct element identities over all derivations, including those
    /// beyond the proof cap: never a count of retained samples or of
    /// distinct values. [`Count::AtLeast`] when the loop stopped early.
    /// `None` serializes as `null`: unavailable, never a guessed zero.
    pub count: Option<Count>,
}

/// Attribution for one deduplicated queried-rule result.
///
/// Counts are per result, not global loop successes, and are not limited
/// by the proof cap: they are [`Count::Exact`] unless evaluation stopped
/// early. `derivations_shown` and `derivations_dropped` are derived, not
/// stored: `derivations_shown` is `proofs.len()` and `derivations_total`
/// is `derivations_shown + derivations_dropped`, including when the proof
/// budget is zero. `derivations_dropped` has the same exactness as
/// `derivations_total`.
///
/// Producers must build it with [`ResultExplanation::new`], which rejects
/// more proofs than `derivations_total`, or otherwise keep
/// `proofs.len() <= derivations_total`. Serializing a result that breaks
/// this fails, and so does serializing any report containing it. The
/// configurable proof
/// budget is shared across results of one queried rule invocation, never
/// consumed by helper summaries.
///
/// Serializes as `{"key": ..., "value": ..., "derivations_total": ...,
/// "derivations_shown": n, "derivations_dropped": {...},
/// "distinct_elements": [...], "proofs": [...]}`. `key` and `value` are
/// replaced by `"key_redacted": true` / `"value_redacted": true` or
/// `"key_elided": true` / `"value_elided": true` when withheld, and are
/// omitted when undefined; `key` is also omitted when absent.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ResultExplanation {
    /// Partial-object key; absent for complete/function/partial-set results.
    pub key: Option<ReportedValue>,
    /// Complete/function result or emitted partial-rule value.
    pub value: ReportedValue,
    /// Whether this result's existence depends on assumptions. One concrete
    /// derivation suffices for `Concrete`, but does not make an assumed
    /// contributor concrete. `None` means unknown, never concrete by default.
    /// Computed independently of retained proofs, so a cap cannot certify
    /// concreteness or hide a concrete derivation.
    pub conditionality: Option<Conditionality>,
    /// Successful derivations producing this result, as `{"exact": n}`, or
    /// `{"at_least": n}` when evaluation stopped early.
    pub derivations_total: Count,
    /// Distinct contributors, one entry per loop site and iterated
    /// collection. Empty means no contributing loop; unavailable counts use
    /// `null`.
    pub distinct_elements: Vec<DistinctElements>,
    /// Bounded successful producing paths.
    pub proofs: Vec<Derivation>,
}

impl ResultExplanation {
    /// Creates a result explanation, or `None` when `proofs` has more
    /// entries than `derivations_total` counts.
    pub fn new(
        key: Option<ReportedValue>,
        value: ReportedValue,
        derivations_total: Count,
        distinct_elements: Vec<DistinctElements>,
        proofs: Vec<Derivation>,
    ) -> Option<Self> {
        let result = Self {
            key,
            value,
            conditionality: None,
            derivations_total,
            distinct_elements,
            proofs,
        };
        result.derivations_dropped().map(|_| result)
    }

    /// Retained derivations: `proofs.len()`.
    pub fn derivations_shown(&self) -> u64 {
        u64::try_from(self.proofs.len()).unwrap_or(u64::MAX)
    }

    /// Successful derivations not retained due to the proof budget:
    /// `derivations_total - derivations_shown`, with the exactness of
    /// `derivations_total`. With a [`Count::AtLeast`] total it is a lower
    /// bound too. `None` when there are more proofs than
    /// `derivations_total`, which breaks the contract.
    pub fn derivations_dropped(&self) -> Option<Count> {
        let shown = self.derivations_shown();
        match self.derivations_total {
            Count::Exact(total) => total.checked_sub(shown).map(Count::Exact),
            Count::AtLeast(total) => total.checked_sub(shown).map(Count::AtLeast),
        }
    }
}

impl Serialize for ResultExplanation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let dropped = self.derivations_dropped().ok_or_else(|| {
            S::Error::custom("result explanation has more proofs than derivations_total")
        })?;
        let len = field_count(&[
            true,
            true,
            true,
            true,
            true,
            is_reported(self.key.as_ref()),
            is_reported(Some(&self.value)),
            self.conditionality.is_some(),
        ]);
        let mut state = serializer.serialize_struct("ResultExplanation", len)?;
        serialize_reported(
            &mut state,
            "key",
            "key_redacted",
            "key_elided",
            self.key.as_ref(),
        )?;
        serialize_reported(
            &mut state,
            "value",
            "value_redacted",
            "value_elided",
            Some(&self.value),
        )?;
        match self.conditionality {
            Some(conditionality) => state.serialize_field("conditionality", &conditionality)?,
            None => state.skip_field("conditionality")?,
        }
        state.serialize_field("derivations_total", &self.derivations_total)?;
        state.serialize_field("derivations_shown", &self.derivations_shown())?;
        state.serialize_field("derivations_dropped", &dropped)?;
        state.serialize_field("distinct_elements", &self.distinct_elements)?;
        state.serialize_field("proofs", &self.proofs)?;
        state.end()
    }
}

/// Iteration summary of a loop-backed condition.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct LoopWitness {
    /// Number of iterations executed, saturating at `u32::MAX`.
    pub iterations: u32,
    /// Number of iterations whose body succeeded, saturating at `u32::MAX`.
    pub successes: u32,
    /// Key of a sample iteration whose outcome matches the condition's: a
    /// successful iteration when the condition held, otherwise a failing one
    /// (the counterexample of a failed `every`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_key: Option<Operand>,
    /// Value of the sample iteration. Its `path` is the iterated collection
    /// as written in the policy, for example `input.users`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_value: Option<Operand>,
}

/// A position in a policy source file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct SourceLocation {
    /// Name of the policy file.
    pub file: String,
    /// 1-based line.
    pub line: usize,
    /// 1-based column.
    pub column: usize,
}

/// Result of a partial evaluation.
///
/// `kind` is the kind of the queried rule and decides how the alternatives
/// combine; a query that is not a rule reference is reported as
/// [`RuleKind::Complete`]. `status` says whether the result can be used:
///
/// - [`ResidualStatus::Exact`]: when the query does not depend on unknown
///   input, `result` is its value and `residual_queries` is empty.
///   Otherwise `result` is undefined and each residual query is an
///   alternative that contributes when all of its conditions hold:
///   - Complete rule or function: the alternatives are ordered, and the
///     first one whose conditions hold gives the value. A trailing
///     alternative with no conditions is the default. When none holds, the
///     result is undefined.
///   - Partial set: the result is the set of the values of every
///     alternative whose conditions hold, or an empty set when none holds.
///   - Partial object: the result is the object of the `key` and `value` of
///     every alternative whose conditions hold, or an empty object when none
///     holds.
/// - [`ResidualStatus::Partial`]: as for `Exact`, but at least one
///   alternative is [unresolved](ResidualAlternativeStatus::Unresolved): a
///   part of the outcome that can't be represented. Its `conditions` are
///   necessary for it to contribute a value, so when they don't all hold it
///   contributes none. When they all hold, the outcome is unknown, except
///   that the members or entries that exact alternatives contribute to a
///   partial set or object are in it if evaluation succeeds; which other
///   members or entries it has, whether it is empty, and the whole
///   collection are unknown. A `Partial` result, of any kind, never
///   establishes that evaluation succeeds: the unresolved part may make it
///   fail with an error even when its conditions don't hold, as in
///   `allow if { x := to_number(input.n); input.flag; x > 0 }` with
///   `input.flag` false and `input.n` set to `"abc"`. Consumers may
///   therefore use a `Partial` result only to fail closed (for example, to
///   deny), never to allow.
/// - Any other status: the outcome can't be represented, so `result` is
///   undefined and `residual_queries` is empty. It is unknown, not
///   undefined or empty, and consumers must fail closed: they must not
///   derive a decision from this result.
///
/// The status is `Partial` if and only if at least one alternative is
/// unresolved, so an `Exact` result has none. In an `Exact` or `Partial`
/// result, every exact alternative has a `value`, and only the alternatives
/// of a partial object have a `key`; an unresolved alternative omits a key
/// or value it can't represent. Consumers reject a result that breaks this,
/// and serializing fails for a result whose `status` breaks the first rule,
/// a result of another status with alternatives, or an alternative whose
/// `unresolved` doesn't match its `status`.
///
/// To keep the conditions of an unresolved alternative necessary, producers
/// omit only whole top-level conditions they can't represent, never part
/// of one. If any condition inside `negated`, at any depth, can't be
/// represented, they omit the whole [`ResidualKind::NegationHolds`]
/// condition rather than weaken it: dropping a conjunct makes the negated
/// conjunction weaker and so its negation stronger, which would no longer
/// be necessary. For example, with `deny if { input.tier == "Free"; not
/// exempt }` and `exempt if { input.owner == "ops"; glob.match(...) }`, the
/// alternative keeps `input.tier == "Free"` and drops `not exempt`
/// entirely; `not input.owner == "ops"` would wrongly rule out a resource
/// owned by `ops` that is not exempt.
///
/// Only the `else` chain of one definition is ordered. Alternatives from
/// different definitions, or from different iterations of one body, are not,
/// and conflicting values are an error in Rego rather than a first match.
/// Producers therefore return [`ResidualStatus::PossibleConflict`] whenever
/// they can't rule out a conflict. In an `Exact` or `Partial` result for a
/// complete rule or function, any two alternatives with different values
/// (by Rego equality) are in one `else` chain or one is a trailing default,
/// and in a partial object no two alternatives with the same key and
/// different values can hold together. So that conflicts fail closed, an
/// unresolved key counts as possibly equal to every other key, and an
/// unresolved value as different from every other value: an alternative
/// with an unresolved key that can hold together with another alternative
/// of the same partial object makes the result `PossibleConflict`.
/// `PossibleConflict` and `Unsupported` take precedence over `Partial`.
///
/// JSON can't distinguish a set from an array, or a non-string object key
/// from a string, so producers return [`ResidualStatus::Unsupported`] when a
/// residual key or value, or a condition value, contains a set or an object
/// with non-string keys. The sole exception is the **outermost set**
/// container of an `in` collection: its JSON array has identical membership
/// semantics. Every element must still be JSON-lossless recursively.
/// For example, `input.x in {1, 2}` can use `[1, 2]`, but
/// `input.x in [{1, 2}]` and `input.x in {{1, 2}}` are unsupported:
/// `[1, 2]` as an input array must not match a nested Rego set. Likewise,
/// a non-string-keyed object anywhere in the collection is unsupported.
///
/// Values here are policy data needed to apply the residual, so they are
/// not subject to [`ValueMode`](super::ValueMode).
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct PartialEvalResult {
    /// Kind of the queried rule, which decides how the alternatives
    /// combine. Consumers reject a kind they don't recognize.
    pub kind: RuleKind,
    /// Whether `result` and `residual_queries` describe the outcome.
    pub status: ResidualStatus,
    /// The query result when it does not depend on unknown input. Omitted
    /// from JSON when undefined.
    pub result: Value,
    /// Alternative residual queries.
    pub residual_queries: Vec<ResidualQuery>,
    /// Human-readable messages about the partial evaluation, such as why the
    /// status is not [`ResidualStatus::Exact`]. Omitted from JSON when
    /// empty.
    pub warnings: Vec<String>,
}

impl Serialize for PartialEvalResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let unresolved = self
            .residual_queries
            .iter()
            .any(|query| query.status == ResidualAlternativeStatus::Unresolved);
        if (self.status == ResidualStatus::Partial) != unresolved {
            return Err(S::Error::custom(
                "partial evaluation status is partial without an unresolved alternative, \
                 or another status with one",
            ));
        }
        if !matches!(self.status, ResidualStatus::Exact | ResidualStatus::Partial)
            && !self.residual_queries.is_empty()
        {
            return Err(S::Error::custom(
                "partial evaluation result has alternatives but is neither exact nor partial",
            ));
        }
        let defined = !is_undefined(&self.result);
        let warned = !self.warnings.is_empty();
        let len = field_count(&[true, true, defined, true, warned]);
        let mut state = serializer.serialize_struct("PartialEvalResult", len)?;
        state.serialize_field("kind", &self.kind)?;
        state.serialize_field("status", &self.status)?;
        if defined {
            state.serialize_field("result", &self.result)?;
        } else {
            state.skip_field("result")?;
        }
        state.serialize_field("residual_queries", &self.residual_queries)?;
        if warned {
            state.serialize_field("warnings", &self.warnings)?;
        } else {
            state.skip_field("warnings")?;
        }
        state.end()
    }
}

/// Whether a partial evaluation could represent its outcome.
///
/// Consumers must treat every status other than [`ResidualStatus::Exact`],
/// including one they don't recognize, as an unknown outcome and fail
/// closed. Consumers that handle unresolved alternatives may also accept
/// [`ResidualStatus::Partial`], but only to fail closed; older consumers
/// reject it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ResidualStatus {
    /// `result` and `residual_queries` describe the outcome for every input.
    Exact,
    /// As for `Exact`, but at least one alternative is
    /// [unresolved](ResidualAlternativeStatus::Unresolved). It may be used
    /// only to fail closed, never to allow; see [`PartialEvalResult`].
    Partial,
    /// Alternatives with different values that are not ordered, from
    /// different definitions or iterations, might hold together.
    PossibleConflict,
    /// The outcome can't be expressed, even with unresolved alternatives.
    /// A construct that affects only one alternative, such as a value
    /// computed from unknown input, makes that alternative unresolved
    /// instead, except for these, which make the whole result unsupported:
    /// a residual key or value, or a condition value, that contains a set
    /// or an object with non-string keys (see [`PartialEvalResult`]), and a
    /// [`ResidualCall`] with a known argument that is not a string or with
    /// a `regex.match` pattern that doesn't compile or exceeds the regorus
    /// regex size limit.
    Unsupported,
}

/// One alternative of a partial evaluation: a conjunction of conditions on
/// unknown input and what the query produces when they all hold.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ResidualQuery {
    /// Key of the entry, for a partial object only; absent from JSON
    /// otherwise.
    pub key: Option<Value>,
    /// The value the query produces, for example `true`, the set member for
    /// a partial set, or the entry value for a partial object. Omitted from
    /// JSON when undefined.
    pub value: Value,
    /// Conditions that must all hold.
    pub conditions: Vec<ResidualCondition>,
    /// Whether the alternative is fully represented. Omitted from JSON when
    /// [`ResidualAlternativeStatus::Exact`], so an absent `status` means
    /// exact.
    pub status: ResidualAlternativeStatus,
    /// Why the alternative is unresolved. Present if and only if `status` is
    /// [`ResidualAlternativeStatus::Unresolved`]; serialization fails
    /// otherwise.
    pub unresolved: Option<ResidualUnresolved>,
}

impl Serialize for ResidualQuery {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let is_unresolved = self.status == ResidualAlternativeStatus::Unresolved;
        if self.unresolved.is_some() != is_unresolved {
            return Err(S::Error::custom(
                "residual query has `unresolved` without unresolved status, or the reverse",
            ));
        }
        let keyed = !is_absent(&self.key);
        let valued = !is_undefined(&self.value);
        let len = field_count(&[keyed, valued, true, is_unresolved, is_unresolved]);
        let mut state = serializer.serialize_struct("ResidualQuery", len)?;
        match self.key {
            Some(ref key) if keyed => state.serialize_field("key", key)?,
            _ => state.skip_field("key")?,
        }
        if valued {
            state.serialize_field("value", &self.value)?;
        } else {
            state.skip_field("value")?;
        }
        state.serialize_field("conditions", &self.conditions)?;
        match self.unresolved {
            Some(ref unresolved) => {
                state.serialize_field("status", &self.status)?;
                state.serialize_field("unresolved", unresolved)?;
            }
            None => {
                state.skip_field("status")?;
                state.skip_field("unresolved")?;
            }
        }
        state.end()
    }
}

/// Whether one alternative of a partial evaluation is fully represented.
///
/// Consumers reject a status they don't recognize.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ResidualAlternativeStatus {
    /// The alternative's key, value and conditions are exact.
    Exact,
    /// Part of the alternative can't be represented, so whole top-level
    /// conditions may be missing and its key or value absent. The
    /// conditions present are still necessary for it to contribute a
    /// value, but evaluation may fail with an error even when they don't
    /// hold. See [`PartialEvalResult`].
    /// Only a [`ResidualStatus::Partial`] result has unresolved alternatives.
    Unresolved,
}

/// Why an alternative of a partial evaluation is unresolved.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct ResidualUnresolved {
    /// The kind of construct that can't be represented.
    pub reason: ResidualUnresolvedReason,
    /// Human-readable details, such as the expression involved. It holds
    /// only policy source text and builtin names, never input, data or
    /// other runtime values, so it needs no redaction. Omitted from JSON
    /// when absent.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

/// The kind of construct that makes an alternative unresolved.
///
/// The reason is informational: consumers treat every unresolved
/// alternative alike, whatever its reason.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ResidualUnresolvedReason {
    /// The value depends on unknown input, as in
    /// `msg := sprintf("%s", [input.name])`.
    UnknownValue,
    /// The key of a partial object entry depends on unknown input.
    TaintedKey,
    /// A condition calls a builtin outside the [`ResidualCall`] allowlist,
    /// or calls an allowlisted one in another form it doesn't allow. A call
    /// that can never return `true`, such as one with a known argument that
    /// is not a string or a pattern that doesn't compile, makes the whole
    /// result [`ResidualStatus::Unsupported`] instead.
    UnsupportedBuiltin,
    /// A condition uses another construct that can't be expressed.
    UnsupportedConstruct,
}

/// One condition on unknown input in a residual query.
///
/// The structured fields describe the condition as `input_path operator
/// value`: producers put the unknown input on the left and mirror the
/// operator, so `18 < input.age` becomes `input.age > 18`. A condition that
/// does not fit this shape, such as `input.a < input.b`, leaves them unset;
/// `text` is always present. A [`ResidualKind::BuiltinCall`] condition is
/// described by `call` instead.
///
/// Consumers that enforce residual conditions must reject a condition they
/// can't evaluate: one whose `kind` or `operator` they don't recognize, or
/// one without the structured fields they need. New kinds may be added, but
/// a field added later never narrows the condition its `kind` describes.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ResidualCondition {
    /// Source text of the condition, for example `input.role == "admin"`.
    pub text: String,
    /// What must hold.
    pub kind: ResidualKind,
    /// Operator of a comparison.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<Operator>,
    /// The unknown path, for example `input.role`. It is root-qualified: it
    /// starts with `input.`, `data.` or `context.`, and consumers reject a
    /// path with any other root.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub input_path: Option<String>,
    /// The known value the input is compared with; absent from JSON when
    /// the condition has no comparison value. An undefined value is never
    /// compared, so it is omitted too.
    #[serde(skip_serializing_if = "is_absent")]
    pub value: Option<Value>,
    /// For [`ResidualKind::NegationHolds`]: the conditions that must not all
    /// hold together.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub negated: Vec<ResidualCondition>,
    /// For [`ResidualKind::BuiltinCall`]: the call that must return `true`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub call: Option<ResidualCall>,
    /// Fully qualified name of the rule the condition came from.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule: Option<String>,
    /// Source location of the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

/// What a residual condition requires of unknown input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ResidualKind {
    /// The input path is defined.
    Exists,
    /// The input path is defined and not `false`, as in `if input.enabled`.
    Truthy,
    /// The condition holds.
    ConditionHolds,
    /// The input collection exists and can be iterated.
    CollectionExists,
    /// The negated conditions do not all hold.
    NegationHolds,
    /// The builtin call in `call` returns `true`.
    BuiltinCall,
}

/// A builtin call in a [`ResidualKind::BuiltinCall`] condition.
///
/// Only these pure predicates are allowed, each with exactly two arguments
/// in Rego order:
///
/// - `startswith(search, base)`, `endswith(search, base)` and
///   `contains(haystack, needle)`;
/// - `regex.match(pattern, value)`, only with a constant pattern: `pattern`
///   is a [`ResidualArgument::Value`].
///
/// Every [`ResidualArgument::Value`] argument is a string. A call with a
/// known argument that is not a string can never return `true`, and may
/// raise an error, so producers return [`ResidualStatus::Unsupported`] for
/// the whole result.
///
/// The condition holds when the builtin returns `true`. An input path that
/// is undefined makes the condition not hold, as the call is then
/// undefined. An input path whose value is defined but not a string makes
/// the call fail: regorus raises an error with strict builtin errors and
/// returns undefined without them, and consumers can't tell which applies.
/// Consumers must therefore treat it as an evaluation error and reject the
/// whole result, not just the condition or its alternative; this also
/// applies inside `negated`. Consumers never coerce an argument to a
/// string.
///
/// Strings are compared ordinally, as sequences of Unicode scalar values,
/// with no normalization or case folding; consumers use ordinal string
/// APIs, not culture-sensitive ones.
///
/// The pattern has regorus `regex.match` semantics: the syntax of the Rust
/// `regex` crate and an unanchored match. Classes such as `\d`, `\w`, `\s`
/// and `\b`, and case-insensitive matching with `(?i)`, are Unicode-aware
/// by default. Consumers reject a pattern their engine can't evaluate with
/// identical semantics. With a pattern that doesn't compile, or that
/// exceeds the regorus regex size limit, the call can never return `true`,
/// and may raise an error, so producers return
/// [`ResidualStatus::Unsupported`] for the whole result.
///
/// Consumers must fail closed: they reject a call to any other builtin, a
/// call with another number of arguments, a known argument (one with the
/// key `value`) that is not a string, a `regex.match` whose pattern is not
/// a known argument, and an argument that is not an object with exactly
/// one of the keys `input_path` and `value`.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ResidualCall {
    /// Builtin name as written in Rego, for example `startswith` or
    /// `regex.match`.
    pub name: String,
    /// The arguments, in order.
    pub arguments: Vec<ResidualArgument>,
}

/// One argument of a [`ResidualCall`]: a JSON object with the single key
/// `input_path` or `value`. Consumers reject any other shape.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ResidualArgument {
    /// An unknown path, root-qualified as for
    /// [`ResidualCondition::input_path`].
    InputPath(String),
    /// A known string. Serializing any other value fails.
    Value(Value),
}

impl Serialize for ResidualArgument {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(1))?;
        match *self {
            Self::InputPath(ref path) => map.serialize_entry("input_path", path)?,
            Self::Value(ref value @ Value::String(_)) => map.serialize_entry("value", value)?,
            Self::Value(_) => {
                return Err(S::Error::custom("residual call argument is not a string"));
            }
        }
        map.end()
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::program::RuleType;
use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use serde::ser::{SerializeStruct, Serializer};
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
            ReportedValue::Redacted => true,
        },
        None => false,
    }
}

/// Length hint for `serialize_struct`: the number of fields written.
fn field_count(written: &[bool]) -> usize {
    written.iter().filter(|flag| **flag).count()
}

/// Writes a known value as `field`, or a redacted one as `flag: true`. An
/// undefined or missing value writes neither.
fn serialize_reported<S: SerializeStruct>(
    state: &mut S,
    field: &'static str,
    flag: &'static str,
    value: Option<&ReportedValue>,
) -> Result<(), S::Error> {
    let Some(reported) = value else {
        state.skip_field(field)?;
        return state.skip_field(flag);
    };
    match *reported {
        ReportedValue::Known(ref known) if !is_undefined(known) => {
            state.serialize_field(field, known)?;
            state.skip_field(flag)
        }
        ReportedValue::Known(_) => {
            state.skip_field(field)?;
            state.skip_field(flag)
        }
        ReportedValue::Redacted => {
            state.skip_field(field)?;
            state.serialize_field(flag, &true)
        }
    }
}

/// Explanation of why a query produced its result.
///
/// A report is complete: it explains every rule within the selected
/// [`ExplanationScope`](super::ExplanationScope).
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ExplanationReport {
    /// The value returned by the query. Omitted from JSON when undefined.
    #[serde(skip_serializing_if = "is_undefined")]
    pub query_result: Value,
    /// Explanations of the rules that the query evaluated.
    pub rules: Vec<RuleExplanation>,
}

/// Explanation of one evaluation of a rule.
///
/// There is one per evaluation, in evaluation order, so a name can repeat:
/// for example a function called with different arguments, or a rule
/// evaluated again under `with`.
///
/// Serializes `result` as `"result": ...`, or as `"result_redacted": true`
/// when it was withheld.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct RuleExplanation {
    /// Fully qualified rule name, for example `data.test.allow`.
    pub name: String,
    /// Kind of rule.
    pub kind: RuleKind,
    /// Final value of the rule. When no definition succeeded, this is the
    /// rule's default value, if it has one. It is undefined when no
    /// definition succeeded and there is no default, or when complete
    /// definitions conflict (the default is not used then). Omitted from
    /// JSON when undefined.
    pub result: ReportedValue,
    /// Explanations of the values emitted by a partial rule.
    pub emissions: Vec<EmissionExplanation>,
    /// Explanations of the evaluated rule bodies; see
    /// [`DefinitionExplanation`].
    pub definitions: Vec<DefinitionExplanation>,
}

impl Serialize for RuleExplanation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[
            true,
            true,
            is_reported(Some(&self.result)),
            !self.emissions.is_empty(),
            !self.definitions.is_empty(),
        ]);
        let mut state = serializer.serialize_struct("RuleExplanation", len)?;
        state.serialize_field("name", &self.name)?;
        state.serialize_field("kind", &self.kind)?;
        serialize_reported(&mut state, "result", "result_redacted", Some(&self.result))?;
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
/// Serializes `key` and `value` as `"key": ...` and `"value": ...`, or as
/// `"key_redacted": true` and `"value_redacted": true` when withheld.
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
        serialize_reported(&mut state, "key", "key_redacted", self.key.as_ref())?;
        serialize_reported(&mut state, "value", "value_redacted", Some(&self.value))?;
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

/// Explanation of one condition in a rule body.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ConditionExplanation {
    /// Source text of the condition.
    pub text: String,
    /// Outcome of the condition.
    pub outcome: Outcome,
    /// Kind of condition.
    pub kind: ConditionKind,
    /// Source location of the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Operator of a comparison or membership test.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<Operator>,
    /// Left operand, or the checked value of a unary condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub left: Option<Operand>,
    /// Right operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub right: Option<Operand>,
    /// Iteration summary of a loop-backed condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub witness: Option<LoopWitness>,
    /// Variable bound by a binding condition, such as `x` in `x := ...`.
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
    /// A variable binding, `x := ...`.
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
}

/// A runtime operand of a condition.
///
/// Serializes as `{"value": ..., "path": ...}` for a known value and
/// `{"path": ..., "redacted": true}` for a redacted one. `value` is omitted
/// when the known value is undefined.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct Operand {
    /// The runtime value.
    pub value: ReportedValue,
    /// The reference the value was read from, as written in the policy, for
    /// example `input.user.role` or `data.tokens[input.user.name]`. Like
    /// condition text, it is policy source and is never redacted.
    pub path: Option<String>,
}

impl Serialize for Operand {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let len = field_count(&[self.path.is_some(), is_reported(Some(&self.value))]);
        let mut state = serializer.serialize_struct("Operand", len)?;
        match self.path {
            Some(ref path) => state.serialize_field("path", path)?,
            None => state.skip_field("path")?,
        }
        serialize_reported(&mut state, "value", "redacted", Some(&self.value))?;
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
/// - Any other status: the outcome can't be represented, so `result` is
///   undefined and `residual_queries` is empty. It is unknown, not
///   undefined or empty, and consumers must fail closed: they must not
///   derive a decision from this result.
///
/// In an `Exact` result, every alternative has a `value`, and only the
/// alternatives of a partial object have a `key`; consumers reject a result
/// that breaks this.
///
/// Only the `else` chain of one definition is ordered. Alternatives from
/// different definitions, or from different iterations of one body, are not,
/// and conflicting values are an error in Rego rather than a first match.
/// Producers therefore return [`ResidualStatus::PossibleConflict`] whenever
/// they can't rule out a conflict: in an `Exact` result for a complete rule
/// or function, any two alternatives with different values (by Rego
/// equality) are in one `else` chain or one is a trailing default, and in a
/// partial object no two alternatives with the same key and different values
/// can hold together.
///
/// JSON can't distinguish a set from an array, or a non-string object key
/// from a string, so producers return [`ResidualStatus::Unsupported`] when a
/// residual key or value, or a condition value other than the collection of
/// an `in` test, contains a set or an object with non-string keys.
///
/// Values here are policy data needed to apply the residual, so they are
/// not subject to [`ValueMode`](super::ValueMode).
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct PartialEvalResult {
    /// Kind of the queried rule, which decides how the alternatives
    /// combine. Consumers reject a kind they don't recognize.
    pub kind: RuleKind,
    /// Whether `result` and `residual_queries` describe the outcome.
    pub status: ResidualStatus,
    /// The query result when it does not depend on unknown input. Omitted
    /// from JSON when undefined.
    #[serde(skip_serializing_if = "is_undefined")]
    pub result: Value,
    /// Alternative residual queries.
    pub residual_queries: Vec<ResidualQuery>,
    /// Human-readable messages about the partial evaluation, such as why the
    /// status is not [`ResidualStatus::Exact`].
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

/// Whether a partial evaluation could represent its outcome.
///
/// Consumers must treat every status other than [`ResidualStatus::Exact`],
/// including one they don't recognize, as an unknown outcome and fail
/// closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ResidualStatus {
    /// `result` and `residual_queries` describe the outcome for every input.
    Exact,
    /// Alternatives with different values that are not ordered, from
    /// different definitions or iterations, might hold together.
    PossibleConflict,
    /// The residual uses a construct that can't be expressed, such as a
    /// value computed from unknown input or a set value.
    Unsupported,
}

/// One alternative of a partial evaluation: a conjunction of conditions on
/// unknown input and what the query produces when they all hold.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct ResidualQuery {
    /// Key of the entry, for a partial object only; absent from JSON
    /// otherwise.
    #[serde(skip_serializing_if = "is_absent")]
    pub key: Option<Value>,
    /// The value the query produces, for example `true`, the set member for
    /// a partial set, or the entry value for a partial object.
    #[serde(skip_serializing_if = "is_undefined")]
    pub value: Value,
    /// Conditions that must all hold.
    pub conditions: Vec<ResidualCondition>,
}

/// One condition on unknown input in a residual query.
///
/// The structured fields describe the condition as `input_path operator
/// value`: producers put the unknown input on the left and mirror the
/// operator, so `18 < input.age` becomes `input.age > 18`. A condition that
/// does not fit this shape, such as `input.a < input.b`, leaves them unset;
/// `text` is always present.
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
    /// The unknown input path, for example `input.role`.
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
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Low-level evaluation events for building explanations.
//!
//! An [`ExplanationRecorder`] installed on a
//! [`RegoVM`](crate::rvm::RegoVM) with
//! [`set_explanation_recorder`](crate::rvm::RegoVM::set_explanation_recorder)
//! receives one call per executed check, rule-body end, rule emission,
//! builtin error and construct whose contributions are not captured. Events
//! borrow the VM's values; a recorder copies what it keeps.
//!
//! Events identify their instruction by program counter
//! ([`HookContext::pc`]). Source text, locations and rule names are not part
//! of the events: they are decoded from the program when a report is built.
//!
//! Events describe the evaluation that ran, which can differ from the
//! policy's text:
//!
//! - A rule (complete or partial) is evaluated once per evaluation. Later
//!   references use the cached value and produce no events, so a rule's
//!   events belong to the context of its first reference.
//! - Likewise, a builtin call answered from the evaluation's cache reports
//!   no error again.
//! - Matching a rule's or function's parameter patterns, such as the `1` in
//!   `f(1)`, is not reported as checks of its body.
//! - Destructuring an array checks its length, which is reported as a
//!   comparison of the array's length with the pattern's.
//! - Iterating an empty collection, or a value that is not a collection,
//!   runs no iteration and reports no check of its own.
//! - Errors that end the evaluation, such as exceeded limits or numeric
//!   overflow, are not reported.
//! - Azure Policy conditions and their logical combinations
//!   (`allOf`, `anyOf`, `not`) are not reported.
//!
//! The recorder runs inside the evaluation: its time and allocations count
//! toward the VM's limits. If it panics, the panic propagates out of the
//! evaluation and the recorder is dropped.

use crate::value::Value;

use super::report::{ConditionKind, Operator, Outcome};

/// Receives evaluation events from the RVM.
///
/// Every method has an empty default, so a recorder implements only the
/// events it needs.
pub trait ExplanationRecorder: Send + Sync {
    /// A new evaluation starts. Called once per evaluation, in both
    /// execution modes, but not when a suspended evaluation resumes. A
    /// recorder installed while an evaluation is suspended receives the rest
    /// of that evaluation's events without a reset.
    fn reset(&mut self) {}

    /// A check in a rule body was executed.
    fn check(&mut self, _context: &HookContext, _event: &CheckEvent<'_>) {}

    /// A rule body ran to its end, or stopped because a check failed.
    fn body_end(&mut self, _context: &HookContext, _event: &BodyEndEvent<'_>) {}

    /// A partial set or partial object rule produced a value.
    fn emission(&mut self, _context: &HookContext, _event: &EmissionEvent<'_>) {}

    /// A builtin call or an arithmetic operator returned an error, or a
    /// division or modulo by zero made its result undefined. Some builtins
    /// return undefined rather than an error when builtin errors are not
    /// strict; those report nothing.
    fn builtin_error(&mut self, _context: &HookContext, _event: &BuiltinErrorEvent<'_>) {}

    /// A construct started whose contributions are not reported as checks
    /// (see [`UncapturedConstruct`]).
    fn not_captured(&mut self, _context: &HookContext, _event: &NotCapturedEvent) {}
}

/// Where an event happened.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct HookContext {
    /// Program counter of the instruction that produced the event. For
    /// [`body_end`](ExplanationRecorder::body_end) it is the instruction at
    /// which the body ended.
    pub pc: usize,
    /// Index of the executing rule in the program's rule table, or `None`
    /// outside any rule.
    pub rule_index: Option<u16>,
    /// Index of the executing definition of the rule.
    pub definition_index: usize,
    /// Index of the executing body within the definition (`else` bodies
    /// follow the first body).
    pub body_index: usize,
    /// Number of rule and function calls in progress, including the
    /// executing rule. Checks of a called helper have a larger depth than
    /// the call site.
    pub call_depth: usize,
    /// Whether the event happened inside a comprehension, either directly
    /// or in a rule or function evaluated for it. Such events are not part
    /// of the enclosing body's own checks: see
    /// [`UncapturedConstruct::Comprehension`].
    pub in_comprehension: bool,
}

/// A check in a rule body.
///
/// The operands depend on [`kind`](Self::kind):
///
/// - [`Comparison`](ConditionKind::Comparison) and
///   [`Membership`](ConditionKind::Membership): `left` and `right` are the
///   compared values (for `x in xs`, `x` and `xs`) and `operator` is set.
/// - [`Truthiness`](ConditionKind::Truthiness): `left` is the checked value.
/// - [`Negation`](ConditionKind::Negation): the operands describe the negated
///   expression: a comparison or membership as above, otherwise `left` is its
///   value. The outcome is that of the negation, which is never
///   [`Undefined`](Outcome::Undefined): `not` of an undefined expression
///   succeeds.
/// - [`Iteration`](ConditionKind::Iteration): the end of an `every`
///   quantifier; `left` is the iterated collection. The outcome is the
///   quantifier's; the checks of each iteration are reported separately.
///   The end of a `some` iteration is not a check.
/// - [`Existence`](ConditionKind::Existence): a value that must be defined
///   was undefined, for example the right side of `_ = x`, a field matched
///   by an object pattern or the collection of an iteration (`some x in xs`,
///   `xs[_]`). Only failures
///   are reported; `left` is the undefined value.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct CheckEvent<'a> {
    /// Kind of check.
    pub kind: ConditionKind,
    /// Operator of a comparison or membership.
    pub operator: Option<Operator>,
    /// Left operand, or the checked value.
    pub left: &'a Value,
    /// Right operand of a comparison or membership.
    pub right: Option<&'a Value>,
    /// [`Success`](Outcome::Success), [`Failure`](Outcome::Failure), or
    /// [`Undefined`](Outcome::Undefined) when the checked value, or an
    /// operand of a comparison or membership, was undefined (except for
    /// negations, see above).
    pub outcome: Outcome,
}

/// The end of a rule body.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct BodyEndEvent<'a> {
    /// [`Success`](Outcome::Success) when the body ran to its end,
    /// [`Failure`](Outcome::Failure) when it stopped early.
    pub outcome: Outcome,
    /// For a complete rule or a function whose body succeeded, the value the
    /// body produced. It can be undefined, for example when the body's
    /// iteration matched nothing.
    pub result: Option<&'a Value>,
}

/// A value produced by a partial set rule (`contains`) or a partial object
/// rule. Undefined keys and values are not reported.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct EmissionEvent<'a> {
    /// Key of a partial object rule's entry; `None` for a partial set rule.
    pub key: Option<&'a Value>,
    /// The emitted set element or object value.
    pub value: &'a Value,
}

/// An error returned by a builtin call or an arithmetic operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct BuiltinErrorEvent<'a> {
    /// Name of the builtin, for example `"json.unmarshal"`. Operators use
    /// their builtin names: `"plus"`, `"minus"`,
    /// `"mul"`, `"div"`, `"rem"`, `"or"` (`|`) and `"and"` (`&`).
    pub name: &'a str,
    /// The error message, without a source location. Operator errors name
    /// the offending operand's type rather than its value, for example
    /// `"operand 1 must be number but got string"`.
    pub message: &'a str,
    /// Whether the error is raised from the call, failing the rule body.
    /// Otherwise the call's result is undefined. Builtin errors are raised
    /// when strict builtin errors are enabled; some arithmetic errors, such
    /// as adding a number to a string, are always raised.
    pub raised: bool,
}

/// A construct whose contributions are not reported as checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct NotCapturedEvent {
    /// The construct.
    pub construct: UncapturedConstruct,
}

/// Constructs whose contributions are not captured yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum UncapturedConstruct {
    /// An array, set or object comprehension. Its checks, and the checks of
    /// rules and functions evaluated for it, are still delivered with
    /// [`HookContext::in_comprehension`] set, but which of them produced the
    /// comprehension's elements is not tracked.
    Comprehension,
}

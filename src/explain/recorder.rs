// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Low-level evaluation events for building explanations.
//!
//! An [`ExplanationRecorder`] installed on a
//! [`RegoVM`](crate::rvm::RegoVM) with
//! [`set_explanation_recorder`](crate::rvm::RegoVM::set_explanation_recorder)
//! receives one call per executed check, rule-body end, rule emission, comprehension yield,
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
//!   references report reuse of that invocation, not another evaluation.
//! - Likewise, a builtin call answered from the evaluation's cache reports
//!   no error again.
//! - Matching a rule's or function's parameter patterns, such as the `1` in
//!   `f(1)`, is not reported as checks of its body.
//! - Destructuring an array checks its length, which is reported as a
//!   comparison of the array's length with the pattern's.
//! - Iterating an empty collection, or a value that is not a collection,
//!   runs no iteration and reports no iteration body checks. A guarded loop
//!   can still report a loop-level [`Iteration`](ConditionKind::Iteration) check.
//! - Errors that end the evaluation, such as exceeded limits or numeric
//!   overflow, have no dedicated error event; active invocations end aborted.
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

    /// An invocation starts, before parameter matching or default selection.
    /// `context` belongs to the caller; the event identifies the callee.
    /// Undefined function arguments still produce a start/end pair for a
    /// function target, but not for an invalid or non-function target.
    fn call_start(&mut self, _context: &HookContext, _event: &CallStartEvent) {}

    /// An invocation completes or aborts. `context` identifies the callee at
    /// its call site; definition/body indices are zero, not a selected body.
    /// Non-nested legacy mixed-mode termination aborts outstanding captured
    /// invocations rather than inventing completion or changing the VM result.
    /// Loading another program aborts outstanding calls before discarding their
    /// execution context, and cancels any suspended continuation.
    fn call_end(&mut self, _context: &HookContext, _event: &CallEndEvent<'_>) {}

    /// A caller uses a cached rule result. No new invocation is created.
    /// A function call short-circuited by undefined arguments is not a cache use.
    fn call_reused(&mut self, _context: &HookContext, _event: &CallReusedEvent) {}

    /// A check in a rule body was executed.
    fn check(&mut self, _context: &HookContext, _event: &CheckEvent<'_>) {}

    /// A rule body ran to its end, or stopped because a check failed.
    fn body_end(&mut self, _context: &HookContext, _event: &BodyEndEvent<'_>) {}

    /// A partial set or partial object rule produced a value.
    fn emission(&mut self, _context: &HookContext, _event: &EmissionEvent<'_>) {}

    /// A comprehension successfully yielded a defined element or entry.
    ///
    /// These are raw yields, not distinct final elements or proofs. Checks
    /// are not associated with individual yields; the comprehension still
    /// reports [`UncapturedConstruct::Comprehension`].
    fn comprehension_emission(
        &mut self,
        _context: &HookContext,
        _event: &ComprehensionEmissionEvent<'_>,
    ) {
    }

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
    /// Evaluation-local executing invocation, or `None` outside a captured
    /// invocation (including a call already active when capture was installed,
    /// or one whose capture was aborted).
    pub call_instance: Option<u64>,
    /// Program counter of the instruction that produced the event, except
    /// for [`check`](ExplanationRecorder::check), where it is the pc of the
    /// check's site in a Rego program's
    /// [`Provenance`](crate::explain::Provenance), found with
    /// [`site_at`](crate::explain::Provenance::site_at). A check of a value
    /// that must be defined ([`Existence`](ConditionKind::Existence)) has no
    /// site. For [`body_end`](ExplanationRecorder::body_end) it is the
    /// instruction at which the body ended. Lifecycle start/reuse events
    /// identify the caller's call site; end events retain that same site.
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

/// A fresh rule or function invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct CallStartEvent {
    /// Sequential evaluation-local identifier, starting at one. Suspension
    /// retains it; only a fresh evaluation resets the sequence.
    pub call_instance: u64,
    /// Callee's index in the program's rule table.
    pub rule_index: u16,
}

/// How a completed invocation obtained its result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CallResultSource {
    /// Rule/function evaluation, including an empty partial collection.
    Body,
    /// A default value was selected, including a default-only rule.
    Default,
    /// No value was produced, including undefined function arguments.
    Undefined,
}

/// A terminal invocation event.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct CallEndEvent<'a> {
    /// `None` means evaluation aborted, not a completed undefined result.
    /// An abort makes both `source` and `result` absent.
    pub source: Option<CallResultSource>,
    /// A completed invocation always supplies its result, including
    /// `Some(&Value::Undefined)` for ordinary undefined.
    pub result: Option<&'a Value>,
}

/// A further use of an already evaluated rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct CallReusedEvent {
    /// Original captured invocation. `None` means its identity was not
    /// captured, for example because a recorder was installed after caching.
    /// It never means a fresh invocation or no reuse, and unrelated `None`
    /// uses must not be merged or treated as complete call-graph evidence.
    pub call_instance: Option<u64>,
    /// Cached rule's index in the program's rule table.
    pub rule_index: u16,
}

/// A check in a rule body.
///
/// The operands depend on [`kind`](Self::kind):
///
/// - [`Comparison`](ConditionKind::Comparison) and
///   [`Membership`](ConditionKind::Membership): `left` and `right` are the
///   compared values (for `x in xs`, `x` and `xs`) and `operator` is set.
///   For `k, v in xs`, `left` is the key `k` and `right` is `xs`; `v` is not
///   reported. The key is evaluated only when `v` and `xs` are defined and
///   `xs` is an array or an object: otherwise `left` is
///   [`Undefined`](Value::Undefined), and the outcome is
///   [`Failure`](Outcome::Failure) when `v` and `xs` are defined.
/// - [`Truthiness`](ConditionKind::Truthiness): `left` is the checked value.
///   A directly guarded equality, ordering or containment operation whose
///   destination aliases an operand is reported this way, matching its static
///   check site, regardless of strict builtin error handling. If a strict
///   ordering comparison errors before writing the destination, `left` is the
///   undefined expression result, not the stale value held by that register.
/// - [`Negation`](ConditionKind::Negation): the operands describe the negated
///   expression: a comparison or membership as above, otherwise `left` is its
///   value. The outcome is that of the negation, which is never
///   [`Undefined`](Outcome::Undefined): `not` of an undefined expression
///   succeeds.
/// - [`Iteration`](ConditionKind::Iteration): `left` is the iterated
///   collection. For an `every` quantifier, reported at its end with the
///   quantifier's outcome; the checks of each iteration are reported
///   separately. Other iterations (`some x in xs`, `xs[_]`) report their
///   result when guarded as a condition inside an `every` body. An undefined
///   collection is reported once with outcome [`Undefined`](Outcome::Undefined),
///   whether or not the iteration has a result guard. Outside `every`, the
///   end of a `some` or indexed iteration is not a check.
/// - [`Existence`](ConditionKind::Existence): a value that must be defined
///   was undefined, for example the right side of `_ = x` or a field matched
///   by an object pattern. Only failures are reported; `left` is the
///   undefined value.
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
    /// negations, see above). With strict builtin errors, comparing values
    /// of different types with `<`, `<=`, `>` or `>=` raises an error that
    /// fails the rule body. When the comparison is checked, it is reported
    /// first: as `Undefined`, or as a failed [`Negation`](ConditionKind::Negation)
    /// under `not`.
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

/// A defined value yielded by a comprehension, after updating its result.
///
/// The context identifies the yield instruction. Its `in_comprehension`
/// flag is set, and its rule/call fields belong to the comprehension's
/// executing body, not a helper called by that body.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct ComprehensionEmissionEvent<'a> {
    /// Program counter of the corresponding `ComprehensionBegin`.
    ///
    /// This is a static site, not a dynamic invocation, scope or iteration
    /// identity. Repeated entries at the same site share this value.
    pub begin_pc: usize,
    /// The yielded element, before set deduplication or object overwrites.
    pub element: ComprehensionElement<'a>,
}

/// Payload of a successful comprehension yield. Undefined keys and values
/// are not reported. Each successful yield is reported, including duplicate
/// set members and repeated object keys; earlier object values may therefore
/// be absent from the final result.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum ComprehensionElement<'a> {
    /// An array element, in append order.
    Array(&'a Value),
    /// A set member, including repeated yields of the same value.
    Set(&'a Value),
    /// An object entry.
    Object {
        /// The yielded key.
        key: &'a Value,
        /// The yielded value.
        value: &'a Value,
    },
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
    /// comprehension's elements is not tracked. Raw yielded values are
    /// delivered separately by [`ExplanationRecorder::comprehension_emission`].
    Comprehension,
}

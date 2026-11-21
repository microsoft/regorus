//! A caller-assembled trace policy whose history stays with the caller.

use alloc::{boxed::Box, string::String, sync::Arc, vec::Vec};
use core::fmt;

#[cfg(verus_keep_ghost)]
use self::verify::*;
use super::decision::PolicyDecision;
use super::evaluate::CompiledPolicy;
#[cfg(verus_keep_ghost)]
use super::rule::verify::{
    diagnostic_identity, diagnostic_output, policy_rule_diagnostic, policy_rule_source,
};
use super::rule::{Diagnostic, PolicyRule, pack_policy_rule};
use history_store::{History, Store};
use history_syntax::{Event, Rule};
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics as sem;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{no_invariant_compile_failure, no_invariant_failure};
use junco_core::{CompileError, HistoryError};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
#[cfg(verus_keep_ghost)]
use vstd::view::DeepView;

/// Renders a violated rule's `(failed_precondition, allowed_fixes)` from the candidate event.
#[cfg(not(verus_keep_ghost))]
pub type TraceDiagnostic<E> = Arc<dyn Fn(&E) -> (String, Vec<String>) + Send + Sync>;

// Verus cannot model a dyn Fn with auto-trait bounds; retain the same native Arc payload.
#[cfg(verus_keep_ghost)]
pub type TraceDiagnostic<E> = NativeTraceDiagnostic<E>;

#[cfg(verus_keep_ghost)]
#[doc(hidden)]
#[verus_verify(external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(E))]
pub struct NativeTraceDiagnostic<E> {
    inner: Arc<dyn Fn(&E) -> (String, Vec<String>) + Send + Sync>,
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

    // Callback identities describe physical selection, not freshness or deterministic outputs.
    pub uninterp spec fn trace_callback_identity<D>(diagnostic: D) -> int;
    pub uninterp spec fn trace_diagnostic_identity<E>(diagnostic: TraceDiagnostic<E>) -> int;
    // One observed invocation of the stored Arc Fn, retaining its actual argument reference.
    pub uninterp spec fn trace_arc_call<E>(diagnostic: TraceDiagnostic<E>, argument: &E,
        output: (String, Vec<String>)) -> bool;
    pub uninterp spec fn trace_rule_source<E: Event>(item: TraceRule<E>) -> Rule<E>;
    pub uninterp spec fn trace_rule_diagnostic<E: Event>(item: TraceRule<E>) -> TraceDiagnostic<E>;
    pub open spec fn trace_rule_diagnostic_id<E: Event>(item: TraceRule<E>) -> int {
        trace_diagnostic_identity(trace_rule_diagnostic(item))
    }
    pub open(super) spec fn trace_wf<E: Event>(policy: TracePolicy<E>) -> bool {
        super::super::evaluate::verify::policy_wf(policy.compiled)
    }
    pub open(super) spec fn trace_store<E: Event>(policy: TracePolicy<E>) -> Arc<Store<E>> {
        super::super::evaluate::verify::policy_store(policy.compiled)
    }
    pub open(super) spec fn trace_sources<E: Event>(policy: TracePolicy<E>) -> Seq<Rule<E>> {
        super::super::evaluate::verify::policy_sources(policy.compiled)
    }
    pub open(super) spec fn trace_diagnostic_ids<E: Event>(policy: TracePolicy<E>) -> Seq<int> {
        super::super::evaluate::verify::policy_diagnostic_ids(policy.compiled)
    }
    pub open(super) spec fn trace_context_calls<E: Event>(policy: TracePolicy<E>) -> nat {
        super::super::evaluate::verify::policy_context_calls(policy.compiled)
    }
    pub open(super) spec fn trace_diagnostic_calls<E: Event>(policy: TracePolicy<E>) -> nat {
        super::super::evaluate::verify::policy_diagnostic_calls(policy.compiled)
    }
    pub open(super) spec fn trace_selected_index<E: Event>(policy: TracePolicy<E>) -> nat {
        super::super::evaluate::verify::policy_selected_index(policy.compiled)
    }
    pub open(super) spec fn trace_selected_diagnostic_id<E: Event>(policy: TracePolicy<E>) -> int {
        super::super::evaluate::verify::policy_selected_diagnostic_id(policy.compiled)
    }
    pub open(super) spec fn trace_selected_source<E: Event>(policy: TracePolicy<E>) -> Rule<E> {
        super::super::evaluate::verify::policy_selected_source(policy.compiled)
    }
    pub closed spec fn trace_frame<E: Event>(before: TracePolicy<E>, after: TracePolicy<E>) -> bool {
        super::super::evaluate::verify::policy_frame(before.compiled, after.compiled)
    }
    pub closed spec fn trace_callbacks_frame<E: Event>(before: TracePolicy<E>, after: TracePolicy<E>) -> bool {
        super::super::evaluate::verify::policy_callbacks_frame(before.compiled, after.compiled)
    }

    /// Exposes constructor readiness without exposing the compiled policy field.
    pub proof fn lemma_trace_wf<E: Event>(policy: TracePolicy<E>)
        requires trace_wf(policy),
        ensures history_store::typed::verify::store_wf(*trace_store(policy)),
            trace_sources(policy).len() == trace_diagnostic_ids(policy).len(),
            trace_context_calls(policy) == trace_diagnostic_calls(policy),
    {
        super::super::evaluate::verify::lemma_policy_wf(policy.compiled);
    }
    pub open(super) spec fn trace_decision_result<E: Event>(
        before: TracePolicy<E>, after: TracePolicy<E>, history: History<E>, candidate: E,
        result: Result<PolicyDecision, HistoryError>,
    ) -> bool {
        super::super::evaluate::policy_decision_result(before.compiled, after.compiled, history, candidate, result)
            && no_invariant_failure(result)
            && trace_wf(after) && trace_store(after) == trace_store(before)
            && trace_sources(after) == trace_sources(before)
            && trace_diagnostic_ids(after) == trace_diagnostic_ids(before)
            && ((result == Err(HistoryError::WrongHistoryOwner))
                == !history_store::typed::verify::same_store_owner(trace_store(before), history_store::history::verify::store_of(history)))
            && match result {
                Err(_) => trace_context_calls(after) == trace_context_calls(before)
                    && trace_diagnostic_calls(after) == trace_diagnostic_calls(before),
                Ok(PolicyDecision::Grant) => trace_context_calls(after) == trace_context_calls(before)
                    && trace_diagnostic_calls(after) == trace_diagnostic_calls(before)
                    && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                        sem::policy_permits(sem::rule_views(trace_sources(before)), candidate,
                            history_store::history::verify::raw_events(history))),
                Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) =>
                    trace_context_calls(after) == trace_context_calls(before) + 1
                        && trace_diagnostic_calls(after) == trace_diagnostic_calls(before) + 1
                        && trace_selected_index(after) < trace_sources(before).len()
                        && trace_selected_diagnostic_id(after) == trace_diagnostic_ids(before)[trace_selected_index(after) as int]
                        && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                            sem::least_violation(sem::rule_views(trace_sources(before)), candidate,
                                history_store::history::verify::raw_events(history), trace_selected_index(after) as int))
                        && diagnostic_output(super::super::evaluate::verify::policy_trace(after.compiled).calls.last().diagnostic_id,
                            candidate, failed_precondition@, allowed_fixes.deep_view()),
            }
    }

    // Eliminate the compiled frame and callback log before repackaging the facade result.
    pub(super) proof fn lemma_trace_decision_result<E: Event>(
        before: TracePolicy<E>, after: TracePolicy<E>, history: History<E>, candidate: E,
        result: Result<PolicyDecision, HistoryError>,
    )
        requires trace_wf(before),
            super::super::evaluate::policy_decision_result(
                before.compiled, after.compiled, history, candidate, result),
            result matches Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) ==>
                diagnostic_output(super::super::evaluate::verify::policy_trace(after.compiled).calls.last().diagnostic_id,
                    candidate, failed_precondition@, allowed_fixes.deep_view()),
        ensures trace_decision_result(before, after, history, candidate, result),
    {
        super::super::evaluate::verify::lemma_policy_decision_result_facts(
            before.compiled, after.compiled, history, candidate, result);
    }

    /// Eliminates facade outcomes using public source, owner, and callback observations only.
    pub proof fn lemma_trace_decision_result_facts<E: Event>(
        before: TracePolicy<E>, after: TracePolicy<E>, history: History<E>, candidate: E,
        result: Result<PolicyDecision, HistoryError>)
        requires trace_decision_result(before, after, history, candidate, result),
        ensures trace_wf(after), trace_frame(before, after),
            trace_store(after) == trace_store(before), trace_sources(after) == trace_sources(before),
            trace_diagnostic_ids(after) == trace_diagnostic_ids(before),
            no_invariant_failure(result),
            (result == Err(HistoryError::WrongHistoryOwner))
                == !history_store::typed::verify::same_store_owner(trace_store(before), history_store::history::verify::store_of(history)),
            match result {
                Err(_) => trace_callbacks_frame(before, after)
                    && trace_context_calls(after) == trace_context_calls(before)
                    && trace_diagnostic_calls(after) == trace_diagnostic_calls(before),
                Ok(PolicyDecision::Grant) => trace_callbacks_frame(before, after)
                    && trace_context_calls(after) == trace_context_calls(before)
                    && trace_diagnostic_calls(after) == trace_diagnostic_calls(before)
                    && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                        sem::policy_permits(sem::rule_views(trace_sources(before)), candidate,
                            history_store::history::verify::raw_events(history))),
                Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) =>
                    trace_context_calls(after) == trace_context_calls(before) + 1
                        && trace_diagnostic_calls(after) == trace_diagnostic_calls(before) + 1
                        && trace_selected_index(after) < trace_sources(before).len()
                        && trace_selected_source(after) == trace_sources(before)[trace_selected_index(after) as int]
                        && trace_selected_diagnostic_id(after) == trace_diagnostic_ids(before)[trace_selected_index(after) as int]
                        && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                            sem::least_violation(sem::rule_views(trace_sources(before)), candidate,
                                history_store::history::verify::raw_events(history), trace_selected_index(after) as int))
                        && diagnostic_output(trace_selected_diagnostic_id(after), candidate,
                            failed_precondition@, allowed_fixes.deep_view()),
            },
    {
        super::super::evaluate::verify::lemma_policy_decision_result_facts(
            before.compiled, after.compiled, history, candidate, result);
    }
    }
}

// Only native Arc allocation and storage of the supplied Fn are opaque.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => requires forall|argument: &E| call_requires(diagnostic, (argument,)),
    ensures trace_diagnostic_identity(result) == trace_callback_identity(diagnostic),
        forall|value: E, output: (String, Vec<String>)|
            diagnostic_output(trace_diagnostic_identity(result), value, output.0@, output.1.deep_view()) ==>
                exists|argument: &E| *argument == value && call_ensures(diagnostic, (argument,), output),
        forall|argument: &E, output: (String, Vec<String>)|
            trace_arc_call(result, argument, output) ==> call_ensures(diagnostic, (argument,), output))]
fn store_trace_diagnostic<E: Event, D: Fn(&E) -> (String, Vec<String>) + Send + Sync + 'static>(
    diagnostic: D,
) -> TraceDiagnostic<E> {
    #[cfg(not(verus_keep_ghost))]
    {
        Arc::new(diagnostic)
    }
    #[cfg(verus_keep_ghost)]
    {
        NativeTraceDiagnostic {
            inner: Arc::new(diagnostic),
        }
    }
}

// Native field movement retains the actual Arc, not just a source-language approximation.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures trace_rule_source(result) == rule,
    trace_rule_diagnostic(result) == diagnostic)]
fn pack_trace_rule<E: Event>(rule: Rule<E>, diagnostic: TraceDiagnostic<E>) -> TraceRule<E> {
    TraceRule { rule, diagnostic }
}

#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures result.0 == trace_rule_source(item),
    result.1 == trace_rule_diagnostic(item))]
fn unpack_trace_rule<E: Event>(item: TraceRule<E>) -> (Rule<E>, TraceDiagnostic<E>) {
    let TraceRule { rule, diagnostic } = item;
    (rule, diagnostic)
}

// One Box stores a closure that makes exactly one call to the original Arc Fn,
// with the very reference the box receives. The identity denotes that original callback.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures diagnostic_identity(result) == trace_diagnostic_identity(diagnostic),
    forall|value: E, output: (String, Vec<String>)|
        diagnostic_output(diagnostic_identity(result), value, output.0@, output.1.deep_view()) ==>
            exists|argument: &E| *argument == value && trace_arc_call(diagnostic, argument, output))]
fn forward_trace_diagnostic<E: Event + 'static>(diagnostic: TraceDiagnostic<E>) -> Diagnostic<E> {
    #[cfg(not(verus_keep_ghost))]
    {
        Box::new(move |event: &E| diagnostic(event))
    }
    #[cfg(verus_keep_ghost)]
    {
        super::rule::NativeDiagnostic {
            inner: Box::new(move |event: &E| (diagnostic.inner)(event)),
        }
    }
}

/// Converts one trace entry without changing its source or diagnostic selection.
#[verus_verify]
#[verus_spec(result => ensures policy_rule_source(result) == trace_rule_source(item),
    policy_rule_diagnostic(result) == trace_rule_diagnostic_id(item),
    forall|value: E, output: (String, Vec<String>)|
        diagnostic_output(policy_rule_diagnostic(result), value, output.0@, output.1.deep_view()) ==>
            exists|argument: &E| *argument == value && trace_arc_call(trace_rule_diagnostic(item), argument, output))]
pub(crate) fn trace_rule_into_policy_rule<E: Event + 'static>(
    item: TraceRule<E>,
) -> PolicyRule<E, E> {
    let (rule, diagnostic) = unpack_trace_rule(item);
    let diagnostic = forward_trace_diagnostic(diagnostic);
    pack_policy_rule(rule, diagnostic)
}

/// One caller-supplied rule paired with the diagnostic its violation surfaces.
#[verus_verify(external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(E))]
pub struct TraceRule<E: Event> {
    /// The past-regex rule.
    pub rule: Rule<E>,
    /// Renders the denial when `rule` is violated.
    pub diagnostic: TraceDiagnostic<E>,
}

#[verus_verify]
impl<E: Event> TraceRule<E> {
    /// Pairs `rule` with `diagnostic`, retaining the supplied Fn's observed outputs.
    #[verus_spec(result => requires forall|argument: &E| call_requires(diagnostic, (argument,)),
        ensures trace_rule_source(result) == rule,
            trace_rule_diagnostic_id(result) == trace_callback_identity(diagnostic),
            forall|value: E, output: (String, Vec<String>)|
                diagnostic_output(trace_rule_diagnostic_id(result), value, output.0@, output.1.deep_view()) ==>
                    exists|argument: &E| *argument == value && call_ensures(diagnostic, (argument,), output))]
    pub fn new(
        rule: Rule<E>,
        diagnostic: impl Fn(&E) -> (String, Vec<String>) + Send + Sync + 'static,
    ) -> Self {
        let diagnostic = store_trace_diagnostic(diagnostic);
        pack_trace_rule(rule, diagnostic)
    }
}

#[verus_verify]
impl<E: Event> Clone for TraceRule<E> {
    // Only the diagnostic's identity is promised: the rule's source equality would assume that
    // the component type's `Clone` is the identity, which Rust does not guarantee.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures trace_rule_diagnostic_id(result) == trace_rule_diagnostic_id(*self))]
    fn clone(&self) -> Self {
        Self {
            rule: self.rule.clone(),
            #[cfg(not(verus_keep_ghost))]
            diagnostic: Arc::clone(&self.diagnostic),
            #[cfg(verus_keep_ghost)]
            diagnostic: NativeTraceDiagnostic {
                inner: Arc::clone(&self.diagnostic.inner),
            },
        }
    }
}

impl<E: Event> fmt::Debug for TraceRule<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TraceRule")
            .field("rule", &self.rule)
            .finish_non_exhaustive()
    }
}

/// A caller-assembled rule table compiled once and decided against external histories.
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(E))]
pub struct TracePolicy<E: Event> {
    compiled: CompiledPolicy<E, E>,
}

#[verus_verify]
impl<E: Event + 'static> TracePolicy<E> {
    /// Compiles the streaming input in order and drains its remaining rules on failure.
    /// Exact source and diagnostic order require the input's `into_iter_yields` law.
    /// Native event laws exclude internal invariant failures, not ordinary compile/resource errors.
    #[verus_spec(result => requires history_store::typed::verify::store_wf(*store),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            result matches Ok(policy) ==> trace_wf(policy) && trace_store(policy) == store
            && trace_context_calls(policy) == 0 && trace_diagnostic_calls(policy) == 0
            && forall|items: Seq<TraceRule<E>>| junco_core::verify::history_specs::into_iter_yields(rules, items) ==>
                trace_sources(policy) == items.map(|i: int, item: TraceRule<E>| trace_rule_source(item))
                    && trace_diagnostic_ids(policy) == items.map(|i: int, item: TraceRule<E>| trace_rule_diagnostic_id(item)))]
    pub fn new<I: IntoIterator<Item = TraceRule<E>>>(
        store: Arc<Store<E>>,
        rules: I,
    ) -> Result<Self, CompileError> {
        proof_decl! { let ghost input = rules; }
        let convert = I::into_iter;
        let iterator = convert(rules);
        proof_decl! { let ghost converted = iterator; }
        proof! { assert(call_ensures(convert, (input,), converted)); }
        let conversion = trace_rule_into_policy_rule::<E>;
        let mapped = iterator.map(conversion);
        proof_decl! { let ghost mapped_input = mapped; }
        proof! {
            if converted.obeys_prophetic_iter_laws() {
                vstd::std_specs::iter::map_postcondition(converted, conversion, mapped_input);
                junco_core::verify::history_specs::lemma_iterator_into_iter_yields(mapped_input);
            }
        }
        let compiled = CompiledPolicy::from_rules(store, mapped)?;
        proof! {
            assert forall|items: Seq<TraceRule<E>>|
                junco_core::verify::history_specs::into_iter_yields(input, items) implies
                    super::evaluate::verify::policy_sources(compiled)
                        == items.map(|i: int, item: TraceRule<E>| trace_rule_source(item))
                    && super::evaluate::verify::policy_diagnostic_ids(compiled)
                        == items.map(|i: int, item: TraceRule<E>| trace_rule_diagnostic_id(item)) by {
                assert(converted.obeys_prophetic_iter_laws());
                assert(converted.remaining() == items);
                vstd::std_specs::iter::map_postcondition(converted, conversion, mapped_input);
                super::evaluate::verify::lemma_completed_iterator_conversion(mapped_input);
                assert(mapped_input.will_return_none());
                vstd::std_specs::iter::map_postcondition(converted, conversion, mapped_input);
                assert(mapped_input.remaining().len() == items.len());
                assert forall|i: int| 0 <= i < items.len() implies
                    policy_rule_source(mapped_input.remaining()[i]) == trace_rule_source(items[i])
                        && policy_rule_diagnostic(mapped_input.remaining()[i]) == trace_rule_diagnostic_id(items[i]) by {
                    assert(call_ensures(conversion, (items[i],), mapped_input.remaining()[i]));
                }
                assert(super::evaluate::verify::policy_sources(compiled)
                    =~= items.map(|i: int, item: TraceRule<E>| trace_rule_source(item)));
                assert(super::evaluate::verify::policy_diagnostic_ids(compiled)
                    =~= items.map(|i: int, item: TraceRule<E>| trace_rule_diagnostic_id(item)));
            }
        }
        Ok(Self { compiled })
    }

    /// Decides against the unchanged external history, using the candidate as the actual context.
    /// Grant/error invokes no diagnostic; denial invokes only the least violating rule's Fn once.
    /// Retained runtime structure and callback identities survive every outcome.
    /// Operational errors cannot be internal invariant failures.
    #[verus_spec(result => requires trace_wf(*old(self)), history_store::history::verify::history_wf(*history),
        ensures trace_decision_result(*old(self), *final(self), *history, *candidate, result),
            no_invariant_failure(result))]
    pub fn decide(
        &mut self,
        history: &History<E>,
        candidate: &E,
    ) -> Result<PolicyDecision, HistoryError> {
        proof_decl! { let ghost before = *self; }
        let context =
            verus_exec_expr! { || -> (value: E) ensures value == *candidate { *candidate } };
        proof_decl! { let ghost actual_context = context; }
        proof! { assert(call_requires(context, ())); }
        let result = self.compiled.decide(history, candidate, context);
        proof! {
            if let Ok(PolicyDecision::Deny { ref failed_precondition, ref allowed_fixes }) = result {
                let value = choose|value: E| call_ensures(actual_context, (), value)
                    && diagnostic_output(super::evaluate::verify::policy_trace(self.compiled).calls.last().diagnostic_id,
                        value, failed_precondition@, allowed_fixes.deep_view());
                assert(value == *candidate);
                assert(diagnostic_output(super::evaluate::verify::policy_trace(self.compiled).calls.last().diagnostic_id,
                    *candidate, failed_precondition@, allowed_fixes.deep_view()));
            }
            lemma_trace_decision_result(before, *self, *history, *candidate, result);
        }
        result
    }
}

//! Checked ordered construction and first-violation selection for trace-policy tables.
//! Native leaves unpack source/callback fields and invoke only the selected diagnostic.

use alloc::{sync::Arc, vec::Vec};

#[cfg(verus_keep_ghost)]
use self::verify::*;
use super::decision::PolicyDecision;
#[cfg(verus_keep_ghost)]
use super::rule::verify::{diagnostic_output, policy_rule_diagnostic, policy_rule_source};
use super::rule::{NativeDiagnostic, PolicyRule};
use crate::CompiledRule;
#[cfg(verus_keep_ghost)]
use crate::compiled_rule::verify as compiled;
#[cfg(verus_keep_ghost)]
use history_store::typed::verify as books;
use history_store::{History, Store};
use history_syntax::{Event, Rule, RuleMode};
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
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

#[cfg(verus_keep_ghost)]
verus! {
broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
}

#[cfg(not(verus_keep_ghost))]
type DiagnosticTrace<E> = core::marker::PhantomData<E>;

#[cfg(verus_keep_ghost)]
vstd::prelude::verus! {
pub(crate) struct DiagnosticCall<E: Event> {
    pub index: nat,
    pub source: history_syntax::Rule<E>,
    pub diagnostic_id: int,
    pub failed_precondition: Seq<char>,
    pub allowed_fixes: Seq<Seq<char>>,
}

pub(crate) tracked struct DiagnosticTrace<E: Event> {
    pub ghost context_calls: nat,
    pub ghost diagnostic_calls: nat,
    pub ghost calls: Seq<DiagnosticCall<E>>,
}

impl<E: Event> DiagnosticTrace<E> {
    pub(crate) open spec fn wf(self) -> bool {
        self.context_calls == self.calls.len() && self.diagnostic_calls == self.calls.len()
    }
    pub(crate) proof fn empty() -> (tracked trace: Self)
        ensures trace.wf(), trace.calls == Seq::<DiagnosticCall<E>>::empty(),
    {
        DiagnosticTrace { context_calls: 0, diagnostic_calls: 0, calls: Seq::empty() }
    }
}
}

#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => requires mut_ref_current(_trace@).wf(), _diagnostic_id@ == diagnostic.id(),
    call_requires(context, ()),
    ensures result is Deny, mut_ref_future(_trace@).wf(),
        mut_ref_future(_trace@).context_calls == mut_ref_current(_trace@).context_calls + 1,
        mut_ref_future(_trace@).diagnostic_calls == mut_ref_current(_trace@).diagnostic_calls + 1,
        result matches PolicyDecision::Deny { failed_precondition, allowed_fixes } ==>
            mut_ref_future(_trace@).calls == mut_ref_current(_trace@).calls.push(DiagnosticCall {
                index: _index@, source: _source@, diagnostic_id: _diagnostic_id@,
                failed_precondition: failed_precondition@, allowed_fixes: allowed_fixes.deep_view(),
            }) && exists|value: C| call_ensures(context, (), value)
                && diagnostic_output(_diagnostic_id@, value, failed_precondition@, allowed_fixes.deep_view()))]
fn render_denial<E: Event, C, F: FnOnce() -> C>(
    diagnostic: &super::rule::NativeDiagnostic<C>,
    context: F,
    _index: vstd::prelude::Ghost<vstd::prelude::nat>,
    _source: vstd::prelude::Ghost<history_syntax::Rule<E>>,
    _diagnostic_id: vstd::prelude::Ghost<vstd::prelude::int>,
    _trace: vstd::prelude::Tracked<&mut DiagnosticTrace<E>>,
) -> PolicyDecision {
    let context = context();
    let (failed_precondition, allowed_fixes) = (diagnostic.inner)(&context);
    PolicyDecision::Deny {
        failed_precondition,
        allowed_fixes,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub open(crate) spec fn policy_decision_result<E: Event, C>(before: CompiledPolicy<E, C>, after: CompiledPolicy<E, C>,
    history: History<E>, candidate: E, result: Result<PolicyDecision, HistoryError>) -> bool {
    verify::policy_wf(after) && verify::policy_frame(before, after)
        && no_invariant_failure(result)
        && ((result == Err(HistoryError::WrongHistoryOwner))
            == !books::same_store_owner(before.store, history_store::history::verify::store_of(history)))
        && match result {
            Err(_) => after.callback_trace@ == before.callback_trace@,
            Ok(PolicyDecision::Grant) => after.callback_trace@ == before.callback_trace@
                && crate::compiled_rule::verify::ordered_result(verify::policy_sources(before), history, candidate, Ok(None)),
            Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) => {
                let call = after.callback_trace@.calls.last();
                let index = call.index as int;
                after.callback_trace@.calls.len() == before.callback_trace@.calls.len() + 1
                    && 0 <= index < verify::policy_sources(before).len()
                    && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                        sem::least_violation(sem::rule_views(verify::policy_sources(before)), candidate,
                            history_store::history::verify::raw_events(history), index))
                    && after.callback_trace@.calls == before.callback_trace@.calls.push(DiagnosticCall {
                        index: call.index, source: verify::policy_sources(before)[index],
                        diagnostic_id: verify::policy_diagnostic_ids(before)[index],
                        failed_precondition: failed_precondition@, allowed_fixes: allowed_fixes.deep_view(),
                    })
            },
        }
}

// The value here is the actual context returned at the selected callback invocation.
// Outputs are observations, never a deterministic function of a callback identity.
pub open(crate) spec fn policy_context_result<E: Event, C, F: FnOnce() -> C>(
    after: CompiledPolicy<E, C>, context: F, result: Result<PolicyDecision, HistoryError>,
) -> bool {
    result matches Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) ==>
        exists|value: C| call_ensures(context, (), value)
            && diagnostic_output(after.callback_trace@.calls.last().diagnostic_id,
                value, failed_precondition@, allowed_fixes.deep_view())
}
}

/// One compiled runtime rule paired with the diagnostic rendered when it is violated.
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(C))]
pub(crate) struct CompiledPolicyRule<E: Event, C> {
    pub(crate) runtime: CompiledRule<E>,
    pub(crate) diagnostic: NativeDiagnostic<C>,
}

/// A policy table whose compiled rules and caches survive successive decisions.
///
/// Construction checks source order and physical diagnostic pairing. Native field projection
/// and arbitrary diagnostic invocation remain explicit leaves, not callback content laws.
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(C))]
pub struct CompiledPolicy<E: Event, C> {
    pub(crate) store: Arc<Store<E>>,
    pub(crate) rules: Vec<CompiledPolicyRule<E, C>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) callback_trace: Tracked<DiagnosticTrace<E>>,
}

// Move the two native fields together; this leaf asserts no constructor or iterator law.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures result.0 == policy_rule_source(item),
    result.1.id() == policy_rule_diagnostic(item))]
fn unpack_policy_rule<E: Event, C>(item: PolicyRule<E, C>) -> (Rule<E>, NativeDiagnostic<C>) {
    let PolicyRule { rule, diagnostic } = item;
    #[cfg(verus_keep_ghost)]
    {
        (rule, diagnostic)
    }
    #[cfg(not(verus_keep_ghost))]
    {
        (rule, NativeDiagnostic { inner: diagnostic })
    }
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

    pub open(crate) spec fn entry_sources<E: Event, C>(entries: Seq<CompiledPolicyRule<E, C>>) -> Seq<Rule<E>> {
        entries.map(|i: int, entry: CompiledPolicyRule<E, C>| compiled::source_rule(entry.runtime))
    }
    pub open(crate) spec fn entry_diagnostic_ids<E: Event, C>(entries: Seq<CompiledPolicyRule<E, C>>) -> Seq<int> {
        entries.map(|i: int, entry: CompiledPolicyRule<E, C>| entry.diagnostic.id())
    }
    pub open(crate) spec fn policy_entries_wf<E: Event, C>(entries: Seq<CompiledPolicyRule<E, C>>, store: Arc<Store<E>>) -> bool {
        books::store_wf(*store) && forall|i: int| 0 <= i < entries.len() ==>
            compiled::compiled_wf(entries[i].runtime) && entries[i].runtime.store == store
    }
    pub open(crate) spec fn policy_entries_frame<E: Event, C>(before: Seq<CompiledPolicyRule<E, C>>, after: Seq<CompiledPolicyRule<E, C>>) -> bool {
        before.len() == after.len() && entry_diagnostic_ids(before) == entry_diagnostic_ids(after)
            && forall|i: int| 0 <= i < before.len() ==>
                compiled::compiled_structure_frame(before[i].runtime, after[i].runtime)
    }
    pub(crate) proof fn lemma_policy_entries_frame_facts<E: Event, C>(
        before: Seq<CompiledPolicyRule<E, C>>, after: Seq<CompiledPolicyRule<E, C>>)
        requires policy_entries_frame(before, after),
        ensures entry_sources(before) == entry_sources(after),
            entry_diagnostic_ids(before) == entry_diagnostic_ids(after),
    {
        assert(entry_sources(before) =~= entry_sources(after));
    }
    pub open(crate) spec fn policy_store<E: Event, C>(policy: CompiledPolicy<E, C>) -> Arc<Store<E>> { policy.store }
    pub open(crate) spec fn policy_trace<E: Event, C>(policy: CompiledPolicy<E, C>) -> DiagnosticTrace<E> { policy.callback_trace@ }
    pub open(crate) spec fn policy_trace_empty<E: Event, C>(policy: CompiledPolicy<E, C>) -> bool {
        policy.callback_trace@.calls == Seq::<DiagnosticCall<E>>::empty()
    }
    pub open(crate) spec fn policy_sources<E: Event, C>(policy: CompiledPolicy<E, C>) -> Seq<Rule<E>> {
        entry_sources(policy.rules@)
    }
    pub open(crate) spec fn policy_diagnostic_ids<E: Event, C>(policy: CompiledPolicy<E, C>) -> Seq<int> {
        entry_diagnostic_ids(policy.rules@)
    }
    pub open(crate) spec fn policy_wf<E: Event, C>(policy: CompiledPolicy<E, C>) -> bool {
        policy_entries_wf(policy.rules@, policy.store) && policy.callback_trace@.wf()
    }
    pub open(crate) spec fn policy_frame<E: Event, C>(before: CompiledPolicy<E, C>, after: CompiledPolicy<E, C>) -> bool {
        policy_wf(after) && before.store == after.store && policy_entries_frame(before.rules@, after.rules@)
    }

    /// Callback observations expose selection and cardinality, not the native log representation.
    pub open(crate) spec fn policy_context_calls<E: Event, C>(policy: CompiledPolicy<E, C>) -> nat {
        policy.callback_trace@.context_calls
    }
    pub open(crate) spec fn policy_diagnostic_calls<E: Event, C>(policy: CompiledPolicy<E, C>) -> nat {
        policy.callback_trace@.diagnostic_calls
    }
    pub open(crate) spec fn policy_selected_index<E: Event, C>(policy: CompiledPolicy<E, C>) -> nat {
        policy.callback_trace@.calls.last().index
    }
    pub open(crate) spec fn policy_selected_source<E: Event, C>(policy: CompiledPolicy<E, C>) -> Rule<E> {
        policy.callback_trace@.calls.last().source
    }
    pub open(crate) spec fn policy_selected_diagnostic_id<E: Event, C>(policy: CompiledPolicy<E, C>) -> int {
        policy.callback_trace@.calls.last().diagnostic_id
    }
    pub open(crate) spec fn policy_callbacks_frame<E: Event, C>(before: CompiledPolicy<E, C>, after: CompiledPolicy<E, C>) -> bool {
        after.callback_trace@ == before.callback_trace@
    }

    /// Constructor and retained-state facts needed by public decision clients.
    pub proof fn lemma_policy_wf<E: Event, C>(policy: CompiledPolicy<E, C>)
        requires policy_wf(policy),
        ensures books::store_wf(*policy_store(policy)),
            policy_sources(policy).len() == policy_diagnostic_ids(policy).len(),
            policy_context_calls(policy) == policy_diagnostic_calls(policy),
            policy_trace_empty(policy) ==> policy_context_calls(policy) == 0 && policy_diagnostic_calls(policy) == 0,
    {}

    /// Eliminates ordered decisions while keeping compiled entries and callback logs private.
    pub proof fn lemma_policy_decision_result_facts<E: Event, C>(
        before: CompiledPolicy<E, C>, after: CompiledPolicy<E, C>,
        history: History<E>, candidate: E, result: Result<PolicyDecision, HistoryError>)
        requires policy_decision_result(before, after, history, candidate, result),
        ensures policy_wf(after), policy_frame(before, after),
            policy_store(after) == policy_store(before),
            policy_sources(after) == policy_sources(before),
            policy_diagnostic_ids(after) == policy_diagnostic_ids(before),
            no_invariant_failure(result),
            (result == Err(HistoryError::WrongHistoryOwner))
                == !books::same_store_owner(policy_store(before), history_store::history::verify::store_of(history)),
            match result {
                Err(_) => policy_callbacks_frame(before, after)
                    && policy_context_calls(after) == policy_context_calls(before)
                    && policy_diagnostic_calls(after) == policy_diagnostic_calls(before),
                Ok(PolicyDecision::Grant) => policy_callbacks_frame(before, after)
                    && policy_context_calls(after) == policy_context_calls(before)
                    && policy_diagnostic_calls(after) == policy_diagnostic_calls(before)
                    && compiled::ordered_result(policy_sources(before), history, candidate, Ok(None))
                    && (junco_core::spec::hypotheses::event_obligations::<E>() ==> sem::policy_permits(
                        sem::rule_views(policy_sources(before)), candidate, history_store::history::verify::raw_events(history))),
                Ok(PolicyDecision::Deny { .. }) => policy_selected_index(after) < policy_sources(before).len()
                    && policy_selected_source(after) == policy_sources(before)[policy_selected_index(after) as int]
                    && policy_selected_diagnostic_id(after) == policy_diagnostic_ids(before)[policy_selected_index(after) as int]
                    && (junco_core::spec::hypotheses::event_obligations::<E>() ==> sem::least_violation(sem::rule_views(policy_sources(before)),
                        candidate, history_store::history::verify::raw_events(history), policy_selected_index(after) as int))
                    && (policy_wf(before) ==> policy_context_calls(after) == policy_context_calls(before) + 1
                        && policy_diagnostic_calls(after) == policy_diagnostic_calls(before) + 1),
            },
    {
        lemma_policy_entries_frame_facts(before.rules@, after.rules@);
        if let Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) = result {
            let call = after.callback_trace@.calls.last();
            let appended = DiagnosticCall {
                index: call.index, source: policy_sources(before)[call.index as int],
                diagnostic_id: policy_diagnostic_ids(before)[call.index as int],
                failed_precondition: failed_precondition@, allowed_fixes: allowed_fixes.deep_view(),
            };
            assert(after.callback_trace@.calls == before.callback_trace@.calls.push(appended));
            assert(call == appended);
        }
    }

    /// Retains the actual context/output observation separately from the five-argument result API.
    pub proof fn lemma_policy_context_result_facts<E: Event, C, F: FnOnce() -> C>(
        after: CompiledPolicy<E, C>, context: F, result: Result<PolicyDecision, HistoryError>)
        requires policy_context_result(after, context, result),
        ensures result matches Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) ==>
            exists|value: C| call_ensures(context, (), value)
                && diagnostic_output(policy_selected_diagnostic_id(after), value,
                    failed_precondition@, allowed_fixes.deep_view()),
    {
        reveal(policy_context_result);
        reveal(policy_selected_diagnostic_id);
        if let Ok(PolicyDecision::Deny { .. }) = result {
            assert(policy_selected_diagnostic_id(after) == after.callback_trace@.calls.last().diagnostic_id);
        }
    }
    // Iterator identity conversion lets the map caller observe actual constructor completion.
    pub(crate) proof fn lemma_completed_iterator_conversion<I: Iterator>(iterator: I)
        requires iterator.obeys_prophetic_iter_laws(),
            exists|actual: I| call_ensures(I::into_iter, (iterator,), actual)
                && (actual.obeys_prophetic_iter_laws() ==> actual.will_return_none()),
        ensures iterator.will_return_none(),
    {
        let actual = choose|actual: I| call_ensures(I::into_iter, (iterator,), actual)
            && (actual.obeys_prophetic_iter_laws() ==> actual.will_return_none());
        assert(actual == iterator);
    }
    }
}

#[verus_verify]
impl<E: Event, C> CompiledPolicy<E, C> {
    /// Keeps arbitrary conversions streaming; exact input facts require their conversion law.
    /// Native event laws exclude internal invariant failures while preserving resource errors.
    #[verus_spec(result => requires books::store_wf(*store),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            result matches Ok(policy) ==> policy_wf(policy) && policy_store(policy) == store
            && policy_trace_empty(policy)
            && forall|items: Seq<PolicyRule<E, C>>|
                junco_core::verify::history_specs::into_iter_yields(rules, items) ==>
                    policy_sources(policy) == items.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
                    && policy_diagnostic_ids(policy) == items.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item)),
            result is Ok ==> exists|converted: I::IntoIter|
                call_ensures(I::into_iter, (rules,), converted)
                    && (converted.obeys_prophetic_iter_laws() ==> converted.will_return_none()))]
    pub fn from_rules<I: IntoIterator<Item = PolicyRule<E, C>>>(
        store: Arc<Store<E>>,
        rules: I,
    ) -> Result<Self, CompileError> {
        proof_decl! { let ghost input = rules; }
        let convert = I::into_iter;
        let iterator = convert(rules);
        proof_decl! { let ghost converted = iterator; }
        proof! { assert(call_ensures(convert, (input,), converted)); }
        let result = Self::from_iterator(store, iterator);
        proof! {
            if let Ok(ref policy) = result {
                assert(exists|actual: I::IntoIter| call_ensures(I::into_iter, (input,), actual)
                    && (actual.obeys_prophetic_iter_laws() ==> actual.will_return_none()));
                assert forall|items: Seq<PolicyRule<E, C>>|
                    junco_core::verify::history_specs::into_iter_yields(input, items) implies
                        policy_sources(*policy) == items.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
                        && policy_diagnostic_ids(*policy) == items.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item)) by {
                    assert(converted.obeys_prophetic_iter_laws());
                    assert(converted.remaining() == items);
                }
            }
        }
        result
    }
}

#[verus_verify]
impl<E: Event, C> CompiledPolicy<E, C> {
    /// Compiles every source rule in order and preserves its paired diagnostic.
    #[verus_verify]
    #[verus_spec(result => requires books::store_wf(*store),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            result matches Ok(policy) ==> policy_wf(policy) && policy_store(policy) == store
            && policy_sources(policy) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
            && policy_diagnostic_ids(policy) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
            && policy_trace_empty(policy))]
    pub fn new(store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>) -> Result<Self, CompileError> {
        Self::from_iterator(store, rules.into_iter())
    }

    // Arbitrary iterators may diverge; actual yields are paired even without prophetic laws.
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    #[verus_spec(result => requires books::store_wf(*store),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            result matches Ok(policy) ==> policy_wf(policy) && policy.store == store
            && policy.callback_trace@.calls == Seq::<DiagnosticCall<E>>::empty()
            && (iterator.obeys_prophetic_iter_laws() ==>
                policy_sources(policy) == iterator.remaining().map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
                && policy_diagnostic_ids(policy) == iterator.remaining().map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
                && iterator.will_return_none()))]
    fn from_iterator<I: Iterator<Item = PolicyRule<E, C>>>(
        store: Arc<Store<E>>,
        iterator: I,
    ) -> Result<Self, CompileError> {
        proof_decl! { let ghost original_iterator = iterator; }
        proof_decl! { let ghost mut yielded: Seq<PolicyRule<E, C>> = Seq::empty(); }
        let mut compiled = Vec::new();
        let mut remaining = iterator;
        let mut world = ObservationWorld;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            books::store_wf(*store), policy_entries_wf(compiled@, store),
            compiled@.len() == yielded.len(),
            entry_sources(compiled@) == yielded.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)),
            entry_diagnostic_ids(compiled@) == yielded.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item)),
            original_iterator == iterator,
            remaining.obeys_prophetic_iter_laws() == original_iterator.obeys_prophetic_iter_laws(),
            remaining.obeys_prophetic_iter_laws() ==> remaining.will_return_none() == original_iterator.will_return_none(),
            remaining.obeys_prophetic_iter_laws() ==> yielded + remaining.remaining() == original_iterator.remaining()))]
        loop {
            let item = match remaining.next() {
                Some(item) => item,
                None => {
                    proof! {
                        if original_iterator.obeys_prophetic_iter_laws() {
                            assert(remaining.remaining().len() == 0);
                            assert(yielded =~= original_iterator.remaining());
                            assert(original_iterator.will_return_none());
                        }
                    }
                    return Ok(Self {
                        store,
                        rules: compiled,
                        #[cfg(verus_keep_ghost)]
                        callback_trace: verus_exec_expr! { Tracked(DiagnosticTrace::empty()) },
                    });
                }
            };
            proof_decl! { let ghost current_item = item; }
            proof_decl! { let ghost previous_entries = compiled@; }
            proof_decl! { let ghost previous_yielded = yielded; }
            let (rule, diagnostic) = unpack_policy_rule(item);
            if world.try_reserve_vec(&mut compiled, 1).is_err() {
                rule.dispose();
                #[cfg_attr(verus_keep_ghost, verus_spec(invariant books::store_wf(*store)))]
                loop {
                    match remaining.next() {
                        Some(pending) => {
                            let (source, _diagnostic) = unpack_policy_rule(pending);
                            source.dispose();
                        }
                        None => return Err(CompileError::Runtime(HistoryError::AllocationFailed)),
                    }
                }
            }
            let runtime = match CompiledRule::new(history_store::typed::share_store(&store), rule) {
                Ok(runtime) => runtime,
                Err(error) =>
                {
                    #[cfg_attr(verus_keep_ghost, verus_spec(invariant books::store_wf(*store),
                        junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure::<CompiledRule<E>>(Err(error))))]
                    loop {
                        match remaining.next() {
                            Some(pending) => {
                                let (source, _diagnostic) = unpack_policy_rule(pending);
                                source.dispose();
                            }
                            None => return Err(error),
                        }
                    }
                }
            };
            compiled.push(CompiledPolicyRule {
                runtime,
                diagnostic,
            });
            proof! {
                yielded = yielded.push(current_item);
                assert forall|i: int| 0 <= i < compiled@.len() implies
                    compiled::compiled_wf(compiled@[i].runtime) && compiled@[i].runtime.store == store by {
                    if i < previous_entries.len() {
                        assert(compiled@[i] == previous_entries[i]);
                    }
                }
                assert forall|i: int| 0 <= i < yielded.len() implies
                    compiled::source_rule(compiled@[i].runtime) == policy_rule_source(yielded[i])
                        && compiled@[i].diagnostic.id() == policy_rule_diagnostic(yielded[i]) by {
                    if i < previous_yielded.len() {
                        assert(compiled@[i] == previous_entries[i]);
                        assert(yielded[i] == previous_yielded[i]);
                        assert(entry_sources(previous_entries)[i] == previous_yielded.map(|j: int, item: PolicyRule<E, C>| policy_rule_source(item))[i]);
                        assert(entry_diagnostic_ids(previous_entries)[i] == previous_yielded.map(|j: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))[i]);
                    } else { assert(yielded[i] == current_item); }
                }
                assert(entry_sources(compiled@) =~= yielded.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)));
                assert(entry_diagnostic_ids(compiled@) =~= yielded.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item)));
            }
        }
    }

    /// Returns the first violation without appending to the caller's history.
    ///
    /// `context` and the selected diagnostic run once on denial only. Foreign histories are
    /// rejected even by an empty table, before callbacks or candidate encoding.
    /// Matching native store owners cannot return `WrongHistoryOwner`.
    /// Operational errors cannot be internal invariant failures.
    #[verus_verify]
    #[verus_spec(result => requires verify::policy_wf(*old(self)), history_store::history::verify::history_wf(*history),
        call_requires(context, ()),
        ensures policy_decision_result(*old(self), *final(self), *history, *probe, result),
            policy_context_result(*final(self), context, result),
            no_invariant_failure(result))]
    pub fn decide(
        &mut self,
        history: &History<E>,
        probe: &E,
        context: impl FnOnce() -> C,
    ) -> Result<PolicyDecision, HistoryError> {
        self.decide_with_limits(
            history,
            probe,
            context,
            &mut Unmetered,
            &mut ObservationWorld,
        )
    }

    #[verus_verify]
    #[verus_spec(result => requires verify::policy_wf(*old(self)), history_store::history::verify::history_wf(*history),
        call_requires(context, ()),
        ensures policy_decision_result(*old(self), *final(self), *history, *probe, result),
            policy_context_result(*final(self), context, result),
            no_invariant_failure(result))]
    pub(super) fn decide_with_limits<L: Limits>(
        &mut self,
        history: &History<E>,
        probe: &E,
        context: impl FnOnce() -> C,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<PolicyDecision, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        proof_decl! { let ghost original_context = context; }
        let index = self.first_violation_with(history, probe, limits, world)?;
        proof! {
            assert(verify::policy_sources(*self) =~= verify::policy_sources(entry));
            assert(verify::policy_diagnostic_ids(*self) == verify::policy_diagnostic_ids(entry));
        }
        match index {
            None => Ok(PolicyDecision::Grant),
            Some(index) => {
                let rule = &self.rules[index];
                let decision = render_denial::<E, C, _>(
                    &rule.diagnostic,
                    context,
                    verus_exec_expr! { Ghost(index as nat) },
                    verus_exec_expr! { Ghost(crate::compiled_rule::verify::source_rule(rule.runtime)) },
                    verus_exec_expr! { Ghost(rule.diagnostic.id()) },
                    verus_exec_expr! { Tracked(self.callback_trace.borrow_mut()) },
                );
                proof! {
                    assert(compiled::source_rule(rule.runtime) == verify::policy_sources(entry)[index as int]);
                    assert(rule.diagnostic.id() == verify::policy_diagnostic_ids(entry)[index as int]);
                    assert(verify::policy_wf(*self));
                    assert(verify::policy_frame(entry, *self));
                    assert(index < verify::policy_sources(entry).len());
                    assert(junco_core::spec::hypotheses::event_obligations::<E>() ==> sem::least_violation(
                        sem::rule_views(verify::policy_sources(entry)), *probe,
                        history_store::history::verify::raw_events(*history), index as int));
                    let ghost observed_decision = decision;
                    if let PolicyDecision::Deny { failed_precondition, allowed_fixes } = observed_decision {
                        assert(self.callback_trace@.calls == entry.callback_trace@.calls.push(DiagnosticCall {
                            index: index as nat, source: verify::policy_sources(entry)[index as int],
                            diagnostic_id: verify::policy_diagnostic_ids(entry)[index as int],
                            failed_precondition: failed_precondition@, allowed_fixes: allowed_fixes.deep_view(),
                        }));
                    }
                    assert(self.callback_trace@.calls.last().diagnostic_id == rule.diagnostic.id());
                    if let PolicyDecision::Deny { ref failed_precondition, ref allowed_fixes } = decision {
                        let value = choose|value: C| call_ensures(original_context, (), value)
                            && diagnostic_output(rule.diagnostic.id(), value, failed_precondition@, allowed_fixes.deep_view());
                        assert(diagnostic_output(self.callback_trace@.calls.last().diagnostic_id,
                            value, failed_precondition@, allowed_fixes.deep_view()));
                    }
                    assert(policy_decision_result(entry, *self, *history, *probe, Ok(decision)));
                    assert(policy_context_result(*self, original_context, Ok(decision)));
                }
                Ok(decision)
            }
        }
    }

    #[verus_verify]
    #[verus_spec(result => requires verify::policy_wf(*old(self)), history_store::history::verify::history_wf(*history),
        ensures no_invariant_failure(result),
            verify::policy_wf(*final(self)), verify::policy_frame(*old(self), *final(self)),
            final(self).callback_trace@ == old(self).callback_trace@,
            (result == Err(HistoryError::WrongHistoryOwner))
                == !books::same_store_owner(old(self).store, history_store::history::verify::store_of(*history)),
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            crate::compiled_rule::verify::ordered_result(verify::policy_sources(*old(self)), *history, *probe, result))]
    fn first_violation_with<L: Limits>(
        &mut self,
        history: &History<E>,
        probe: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<usize>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        if !CompiledRule::same_owner(&self.store, history.store()) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= self.rules@.len(), verify::policy_wf(*self), verify::policy_frame(entry, *self),
            entry == *old(self),
            self.callback_trace@ == entry.callback_trace@,
            history_store::history::verify::history_wf(*history),
            books::same_store_owner(entry.store, history_store::history::verify::store_of(*history)),
            junco_core::spec::hypotheses::event_obligations::<E>() ==>
                forall|j: int| 0 <= j < index ==> !sem::rule_violated(
                    verify::policy_sources(entry)[j]@, *probe, history_store::history::verify::raw_events(*history)),
            decreases self.rules@.len() - index))]
        while index < self.rules.len() {
            proof_decl! { let ghost before = *self; }
            let rule = &mut self.rules[index];
            let answer = rule
                .runtime
                .accepts_history_with_limits(history, probe, limits, world);
            let mode = rule.runtime.mode();
            proof! {
                if junco_core::spec::hypotheses::event_obligations::<E>() {
                    crate::compiled_rule::verify::lemma_dsl_violation(rule.runtime, *history, *probe, answer, mode);
                }
                verify::lemma_policy_entries_frame_facts(entry.rules@, before.rules@);
                assert forall|j: int| 0 <= j < entry.rules@.len() implies
                    compiled::compiled_structure_frame(entry.rules@[j].runtime, self.rules@[j].runtime)
                        && self.rules@[j].diagnostic.id() == entry.rules@[j].diagnostic.id() by {
                    if j != index as int { assert(self.rules@[j] == before.rules@[j]); }
                    assert(verify::entry_diagnostic_ids(before.rules@)[j] == verify::entry_diagnostic_ids(entry.rules@)[j]);
                }
                assert(verify::entry_diagnostic_ids(self.rules@) =~= verify::entry_diagnostic_ids(entry.rules@));
                verify::lemma_policy_entries_frame_facts(entry.rules@, self.rules@);
                assert(verify::policy_wf(*self));
                assert(verify::policy_frame(entry, *self));
            }
            let violated = match answer? {
                None => false,
                Some(inside) => match mode {
                    RuleMode::Forbid => inside,
                    RuleMode::Require => !inside,
                },
            };
            if violated {
                return Ok(Some(index));
            }
            index += 1;
        }
        proof! {
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                crate::compiled_rule::verify::lemma_no_violation_permits(
                    verify::policy_sources(entry), *probe, history_store::history::verify::raw_events(*history));
            }
        }
        Ok(None)
    }
}

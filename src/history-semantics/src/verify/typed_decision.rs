//! Owned DSL → finite component books → retained numeric runtime composition.
//!
//! The public constructor and decision bodies supply the structural flattening,
//! finite published snapshots, history correspondence, and cached numeric answer.
//! Native Eq/Hash/projection remain conditional; retained provenance follows lifecycle resources.
//! Ordered Vec construction, first-source denial, callback pairing, and validator
//! append/no-append transactions are exercised by actual checked API clients below.

use crate::compile::verify as numeric;
use crate::compiled_rule::CompiledRule;
use crate::compiled_rule::verify as typed;
use crate::policy::evaluate::{policy_decision_result, verify as policy};
use crate::policy::rule::verify::{policy_rule_diagnostic, policy_rule_source};
use crate::policy::{CompiledPolicy, PolicyDecision, PolicyRule};
use crate::runtime::{RuleRuntime, verify as cache};
use crate::spec::monitor::{check_frame, check_step};
use crate::validator::{Decision, Validator};
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_store::history::{History, verify as raw};
use history_store::typed::{Store, borrow_store, share_store, verify as books};
use history_syntax::Event;
use history_syntax::syntax::Rule;
use history_syntax::{Head, RegexExpr, RuleMode};
use junco_core::errors::{CompileError, HistoryError};
use junco_core::event::Request;
use junco_core::flat::FlatPair;
use junco_core::kernel::verify as graph;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
use junco_core::spec::semantics as dsl;
use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;

verus! {
broadcast use {junco_core::kernel::verify::group_kernel_views,
    vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// The numeric constructor's property is preserved by successful and failed batches.
pub(crate) open spec fn runtime_represents(template: FlatPair<u64>, runtime: RuleRuntime) -> bool {
    cache::runtime_wf(runtime)
        && numeric::regex_correct(runtime.pair.store.graph(), template, template.root as nat, runtime.pair.root)
}

pub(crate) proof fn lemma_runtime_frame(template: FlatPair<u64>, before: RuleRuntime, after: RuleRuntime)
    requires runtime_represents(template, before), cache::runtime_wf(after),
        crate::progress::verify::pair_frame(before.pair, after.pair),
    ensures runtime_represents(template, after),
{
    let first = before.pair.store.graph();
    let last = after.pair.store.graph();
    graph::lemma_graph_wf_elim(first);
    graph::lemma_lift_regex_stable(first, last, before.pair.root@);
    assert forall|theta: junco_core::verify::history_specs::Subst,
        word: Seq<junco_core::verify::history_specs::EventView>|
        junco_core::verify::history_specs::event_wf(theta, theta.len()) implies
            graph::regex_lang(last, theta, after.pair.root@, word)
                == numeric::source_regex(template, template.root as nat, theta, word) by {
        assert(graph::regex_lang(first, theta, before.pair.root@, word)
            == numeric::source_regex(template, template.root as nat, theta, word));
    }
}

/// Shared Arc adapters establish matching ownership before the public decision.
pub(crate) fn shared_store_owner_decision_client<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, candidate: &E,
) -> (result: Result<(CompiledRule<E>, History<E>, Result<Option<bool>, HistoryError>), CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok((compiled, history, answer)) ==>
        typed::decision_requires(compiled, history)
            && books::same_store_owner(compiled.store, raw::store_of(history))
            && answer != Err(HistoryError::WrongHistoryOwner),
{
    let history_owner = share_store(&store);
    let ghost source = rule;
    let mut compiled = CompiledRule::new(store, rule)?;
    let history = History::new(history_owner)?;
    proof {
        raw::lemma_empty_history(history, history_owner);
        typed::lemma_constructed_decision(compiled, source, store, history);
        books::lemma_same_store_owner_identity(compiled.store, raw::store_of(history));
    }
    let answer = compiled.accepts_history(&history, candidate);
    Ok((compiled, history, answer))
}

/// Distinct constructor receipts contradict successful native pointer comparison.
pub(crate) fn independent_store_owner_decision_client<E: Event>(
    rule: Rule<E>, candidate: &E,
) -> (result: Result<(CompiledRule<E>, History<E>, Result<Option<bool>, HistoryError>), CompileError>)
    ensures result matches Ok((compiled, history, answer)) ==>
        typed::decision_requires(compiled, history)
            && !books::same_store_owner(compiled.store, raw::store_of(history))
            && answer == Err(HistoryError::WrongHistoryOwner),
{
    let (left, right) = match books::independently_constructed_stores_client::<E, E>() {
        Ok(owners) => owners,
        Err(error) => { rule.dispose(); return Err(CompileError::Runtime(error)); },
    };
    let left = Arc::new(left);
    let right = Arc::new(right);
    let left_referent = borrow_store(&left);
    let right_referent = borrow_store(&right);
    let same = CompiledRule::same_owner(&left, &right);
    proof {
        assert(books::store_id(*left_referent) != books::store_id(*right_referent));
        assert(!same);
    }
    let ghost source = rule;
    let mut compiled = CompiledRule::new(left, rule)?;
    let history = History::new(right)?;
    proof {
        raw::lemma_empty_history(history, right);
        typed::lemma_constructed_decision(compiled, source, left, history);
    }
    let answer = compiled.accepts_history(&history, candidate);
    Ok((compiled, history, answer))
}

/// This is the actual public consuming constructor followed by the public decision.
/// No numeric-only event restriction or semantic-equivalence premise is supplied.
pub(crate) fn public_compiled_decision<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, history: &History<E>, candidate: &E,
) -> (result: Result<Option<bool>, CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history),
    ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> (result matches Ok(answer)
        ==> answer == dsl::rule_evaluation(rule@, *candidate, raw::raw_events(*history))),
{
    let ghost source = rule;
    let mut compiled = CompiledRule::new(store, rule)?;
    proof { typed::lemma_constructed_decision(compiled, source, store, *history); }
    let accepted = compiled.accepts_history(history, candidate)?;
    Ok(accepted)
}

/// Real retained decisions span append, rollback, same-length replacement, truncate,
/// and a fresh-owner fork, without any caller-supplied cache-provenance premise.
pub(crate) fn retained_history_lifecycle<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, history: &mut History<E>, appended: E,
    replacement: E, truncate_to: usize, candidate: &E,
) -> (result: Result<Option<bool>, CompileError>)
    requires books::store_wf(*store), raw::history_wf(*old(history)),
    ensures raw::history_wf(*final(history)),
        junco_core::spec::hypotheses::event_obligations::<E>() ==> (result matches Ok(answer)
            ==> answer == dsl::rule_evaluation(rule@, *candidate, raw::raw_events(*final(history)))),
{
    let ghost source = rule;
    let mut compiled = CompiledRule::new(store, rule)?;
    proof { typed::lemma_constructed_decision(compiled, source, store, *history); }
    let checkpoint = history.checkpoint();
    let _ = compiled.accepts_history(history, candidate)?;
    history.push(appended)?;
    let _ = compiled.accepts_history(history, candidate)?;
    history.rollback(checkpoint)?;
    let _ = compiled.accepts_history(history, candidate)?;
    history.push(replacement)?;
    history.truncate(truncate_to)?;
    let _ = compiled.accepts_history(history, candidate)?;
    let fork = history.try_clone()?;
    proof { raw::lemma_clone_raw_word(*history, fork); }
    let accepted = compiled.accepts_history(&fork, candidate)?;
    proof {
        assert(raw::raw_word(*history) =~= raw::raw_events(*history).map(
            |i: int, event: E| history_syntax::spec::events::event_view(event)));
        assert(raw::raw_word(fork) =~= raw::raw_events(fork).map(
            |i: int, event: E| history_syntax::spec::events::event_view(event)));
    }
    Ok(accepted)
}

/// Retained-prefix clients exercise the very same body with explicit host fault leaves.
/// Later book extensions are acquired inside that body from both the constants'
/// and the history's finite published snapshots before deriving DSL semantics.
pub(crate) fn compiled_cached_decision<E: Event, L: Limits>(
    compiled: &mut CompiledRule<E>, history: &History<E>, candidate: &E,
    limits: &mut L, world: &mut ObservationWorld,
) -> (result: Result<Option<bool>, HistoryError>)
    requires typed::decision_requires(*old(compiled), *history),
    ensures typed::decision_result(*old(compiled), *final(compiled), *history, *candidate, result),
        junco_core::spec::hypotheses::event_obligations::<E>() ==>
            typed::dsl_result(typed::source_rule(*old(compiled)), *history, *candidate, result),
{
    compiled.accepts_history_with_limits(history, candidate, limits, world)
}

// These clients exercise construction and transactions, rather than assuming a verdict.
pub(crate) fn validator_check_client<E: Event, M>(
    state: &mut Validator<E>, request: Request<E, M>,
) -> (result: Result<Decision<E, M>, HistoryError>)
    requires old(state).wf(),
    ensures final(state).wf(), check_frame(old(state)@, final(state)@, request, result),
        junco_core::spec::hypotheses::event_obligations::<E>() ==> check_step(old(state)@, request, result),
{
    state.check(request)
}

pub(crate) fn compiled_policy_decide_client<E: Event, C, F: FnOnce() -> C>(
    state: &mut CompiledPolicy<E, C>, history: &History<E>, candidate: &E, context: F,
) -> (result: Result<PolicyDecision, HistoryError>)
    requires policy::policy_wf(*old(state)), raw::history_wf(*history), call_requires(context, ()),
    ensures policy_decision_result(*old(state), *final(state), *history, *candidate, result),
{
    state.decide(history, candidate, context)
}

pub(crate) fn validator_from_rules_client<E: Event>(
    store: Arc<Store<E>>, rules: Vec<Rule<E>>,
) -> (result: Result<Validator<E>, CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok(state) ==> state.wf()
        && state@.rules == dsl::rule_views(rules@) && state@.history == Seq::<E>::empty(),
{
    let ghost original = rules@;
    let count = rules.len();
    let mut builder = Validator::builder(store);
    let mut remaining = rules.into_iter();
    let mut index: usize = 0;
    proof { assert(builder.rules() =~= dsl::rule_views(original.take(0))); }
    while index < count
        invariant count == original.len(), index <= original.len(), builder.wf(),
            builder.rules() == dsl::rule_views(original.take(index as int)),
            remaining.remaining() == original.skip(index as int),
            remaining.obeys_prophetic_iter_laws(),
        decreases original.len() - index,
    {
        let item = remaining.next();
        match item {
            Some(source) => { builder.add_rule(source)?; },
            None => { proof { assert(false); } },
        }
        index += 1;
        proof {
            assert(builder.rules() =~= dsl::rule_views(original.take(index as int)));
        }
    }
    let state = builder.finish()?;
    proof { assert(original.take(original.len() as int) =~= original); }
    Ok(state)
}

pub(crate) fn compiled_policy_from_vec_client<E: Event, C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>,
) -> (result: Result<CompiledPolicy<E, C>, CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok(state) ==> policy::policy_wf(state)
        && policy::policy_store(state) == store
        && policy::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && policy::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && policy::policy_trace_empty(state),
{
    CompiledPolicy::new(store, rules)
}

pub(crate) fn validator_require_empty_then_forbid_all_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>, second_head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::event_obligations::<E>(), dsl::head_matches(head@, history_syntax::spec::events::event_view(request.event)), second_head == head,
    ensures result matches Ok((state, decision)) ==> state.wf()
        && state@.rules == dsl::rule_views(seq![Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty }, Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::All }])
        && state@.history == Seq::<E>::empty()
        && dsl::least_violation(state@.rules, request.event, state@.history, 0)
        && decision is Denied && (decision matches Decision::Denied(denial) ==> denial.mode == RuleMode::Require && denial.event == request.event),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty });
    rules.push(Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::All });
    let ghost sources = rules@;
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        assert(state@.rules[0] == sources[0]@);
        assert(dsl::least_violation(state@.rules, request.event, state@.history, 0));
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { lemma_denied_at_zero(before@, request, decision); }
    Ok((state, decision))
}

pub(crate) fn validator_forbid_all_then_require_empty_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>, second_head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::event_obligations::<E>(), dsl::head_matches(head@, history_syntax::spec::events::event_view(request.event)), second_head == head,
    ensures result matches Ok((state, decision)) ==> state.wf()
        && state@.rules == dsl::rule_views(seq![Rule { mode: RuleMode::Forbid, head: head, tail: RegexExpr::All }, Rule { mode: RuleMode::Require, head: second_head, tail: RegexExpr::Empty }])
        && state@.history == Seq::<E>::empty()
        && dsl::least_violation(state@.rules, request.event, state@.history, 0)
        && decision is Denied && (decision matches Decision::Denied(denial) ==> denial.mode == RuleMode::Forbid && denial.event == request.event),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Forbid, head: head, tail: RegexExpr::All });
    rules.push(Rule { mode: RuleMode::Require, head: second_head, tail: RegexExpr::Empty });
    let ghost sources = rules@;
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        assert(state@.rules[0] == sources[0]@);
        assert(dsl::least_violation(state@.rules, request.event, state@.history, 0));
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { lemma_denied_at_zero(before@, request, decision); }
    Ok((state, decision))
}

/// A `check_step` whose first rule is violated denies with that rule's mode.
proof fn lemma_denied_at_zero<E: Event, M>(before: crate::spec::monitor::ValidatorView<E>, request: Request<E, M>, decision: Decision<E, M>)
    requires check_step(before, request, Ok(decision)),
        dsl::least_violation(before.rules, request.event, before.history, 0),
    ensures decision is Denied,
        decision matches Decision::Denied(denial) ==> denial.mode == before.rules[0].mode,
{
    match decision {
        Decision::Grant(_) => {
            assert(dsl::policy_denies(before.rules, request.event, before.history));
        },
        Decision::Denied(denial) => {
            let index = choose|i: int| #[trigger] dsl::least_violation(before.rules, request.event, before.history, i)
                && denial.mode == before.rules[i].mode;
            if index > 0 {
                assert(!dsl::rule_violated(before.rules[0], request.event, before.history));
            }
        },
    }
}

pub(crate) fn validator_require_all_and_forbid_empty_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>, second_head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::event_obligations::<E>(), dsl::head_matches(head@, history_syntax::spec::events::event_view(request.event)), second_head == head,
    ensures result matches Ok((state, decision)) ==> state.wf()
        && state@.rules == dsl::rule_views(seq![Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::All }, Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::Empty }])
        && state@.history == seq![request.event]
        && decision is Grant && (decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::All });
    rules.push(Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::Empty });
    let ghost sources = rules@;
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        assert forall|i: int| 0 <= i < state@.rules.len() implies
            !dsl::rule_violated(state@.rules[i], request.event, state@.history) by {
            assert(state@.rules[i] == sources[i]@);
        }
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { lemma_granted(before@, state@, request, decision); }
    Ok((state, decision))
}

pub(crate) fn validator_head_mismatch_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::event_obligations::<E>(), !dsl::head_matches(head@, history_syntax::spec::events::event_view(request.event)),
    ensures result matches Ok((state, decision)) ==> state.wf()
        && state@.rules == dsl::rule_views(seq![Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty }])
        && state@.history == seq![request.event]
        && decision is Grant && (decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty });
    let ghost sources = rules@;
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        assert forall|i: int| 0 <= i < state@.rules.len() implies
            !dsl::rule_violated(state@.rules[i], request.event, state@.history) by {
            assert(state@.rules[i] == sources[i]@);
        }
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { lemma_granted(before@, state@, request, decision); }
    Ok((state, decision))
}

pub(crate) fn validator_empty_table_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::event_obligations::<E>(),
    ensures result matches Ok((state, decision)) ==> state.wf()
        && state@.rules == Seq::<history_syntax::spec::events::RuleView<E::Component>>::empty()
        && state@.history == seq![request.event]
        && decision is Grant && (decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata),
{
    let rules = Vec::new();
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof { assert(state@.rules =~= Seq::<history_syntax::spec::events::RuleView<E::Component>>::empty()); }
    let decision = validator_check_client(&mut state, request)?;
    proof { lemma_granted(before@, state@, request, decision); }
    Ok((state, decision))
}

/// A `check` on an empty history that violates no rule grants and commits exactly the event.
proof fn lemma_granted<E: Event, M>(before: crate::spec::monitor::ValidatorView<E>, after: crate::spec::monitor::ValidatorView<E>, request: Request<E, M>, decision: Decision<E, M>)
    requires check_frame(before, after, request, Ok(decision)), check_step(before, request, Ok(decision)),
        before.history == Seq::<E>::empty(),
        forall|i: int| 0 <= i < before.rules.len() ==> !dsl::rule_violated(before.rules[i], request.event, before.history),
    ensures decision is Grant, after.history == seq![request.event],
        decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata,
{
    if let Decision::Denied(denial) = decision {
        let index = choose|i: int| #[trigger] dsl::least_violation(before.rules, request.event, before.history, i)
            && denial.mode == before.rules[i].mode;
        assert(false);
    }
    assert(after.history =~= seq![request.event]);
}

pub(crate) fn compiled_policy_require_empty_then_forbid_all_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>, second_head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::event_obligations::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Require, head: head@, tail: RegexExpr::Empty }, Rule { mode: RuleMode::Forbid, head: second_head@, tail: RegexExpr::All }], dsl::head_matches(head@@, history_syntax::spec::events::event_view(*candidate)), second_head@ == head@,
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> policy::policy_wf(state)
        && policy::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && policy::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Deny && policy::policy_trace(state).calls.len() == 1
        && policy::policy_trace(state).context_calls == 1 && policy::policy_trace(state).diagnostic_calls == 1
        && policy::policy_trace(state).calls[0].index == 0
        && policy::policy_trace(state).calls[0].source == policy_rule_source(rules@[0])
        && policy::policy_trace(state).calls[0].diagnostic_id == policy_rule_diagnostic(rules@[0]),
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        assert(dsl::least_violation(dsl::rule_views(policy::policy_sources(state)), *candidate, raw::raw_events(*history), 0));
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        if decision is Deny {
            let index = policy::policy_trace(state).calls.last().index;
            assert(index == 0) by {
                if index > 0 { assert(!dsl::rule_violated(policy::policy_sources(before)[0]@, *candidate, raw::raw_events(*history))); }
            }
        }
    }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_forbid_all_then_require_empty_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>, second_head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::event_obligations::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Forbid, head: head@, tail: RegexExpr::All }, Rule { mode: RuleMode::Require, head: second_head@, tail: RegexExpr::Empty }], dsl::head_matches(head@@, history_syntax::spec::events::event_view(*candidate)), second_head@ == head@,
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> policy::policy_wf(state)
        && policy::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && policy::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Deny && policy::policy_trace(state).calls.len() == 1
        && policy::policy_trace(state).context_calls == 1 && policy::policy_trace(state).diagnostic_calls == 1
        && policy::policy_trace(state).calls[0].index == 0
        && policy::policy_trace(state).calls[0].source == policy_rule_source(rules@[0])
        && policy::policy_trace(state).calls[0].diagnostic_id == policy_rule_diagnostic(rules@[0]),
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        assert(dsl::least_violation(dsl::rule_views(policy::policy_sources(state)), *candidate, raw::raw_events(*history), 0));
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        if decision is Deny {
            let index = policy::policy_trace(state).calls.last().index;
            assert(index == 0) by {
                if index > 0 { assert(!dsl::rule_violated(policy::policy_sources(before)[0]@, *candidate, raw::raw_events(*history))); }
            }
        }
    }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_require_all_and_forbid_empty_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>, second_head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::event_obligations::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Require, head: head@, tail: RegexExpr::All }, Rule { mode: RuleMode::Forbid, head: second_head@, tail: RegexExpr::Empty }], dsl::head_matches(head@@, history_syntax::spec::events::event_view(*candidate)), second_head@ == head@,
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> policy::policy_wf(state)
        && policy::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && policy::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Grant && policy::policy_trace_empty(state)
        && policy::policy_trace(state).context_calls == 0 && policy::policy_trace(state).diagnostic_calls == 0,
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    proof {
        assert forall|i: int| 0 <= i < policy::policy_sources(state).len() implies
            !dsl::rule_violated(policy::policy_sources(state)[i]@, *candidate, raw::raw_events(*history)) by {}
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    Ok((state, decision))
}

pub(crate) fn compiled_policy_head_mismatch_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::event_obligations::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Require, head: head@, tail: RegexExpr::Empty }], !dsl::head_matches(head@@, history_syntax::spec::events::event_view(*candidate)),
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> policy::policy_wf(state)
        && policy::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && policy::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Grant && policy::policy_trace_empty(state)
        && policy::policy_trace(state).context_calls == 0 && policy::policy_trace(state).diagnostic_calls == 0,
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    proof {
        assert forall|i: int| 0 <= i < policy::policy_sources(state).len() implies
            !dsl::rule_violated(policy::policy_sources(state)[i]@, *candidate, raw::raw_events(*history)) by {}
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    Ok((state, decision))
}

pub(crate) fn compiled_policy_empty_table_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::event_obligations::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![],
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> policy::policy_wf(state)
        && policy::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && policy::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Grant && policy::policy_trace_empty(state)
        && policy::policy_trace(state).context_calls == 0 && policy::policy_trace(state).diagnostic_calls == 0,
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    proof {
        assert forall|i: int| 0 <= i < policy::policy_sources(state).len() implies
            !dsl::rule_violated(policy::policy_sources(state)[i]@, *candidate, raw::raw_events(*history)) by {}
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    Ok((state, decision))
}

}

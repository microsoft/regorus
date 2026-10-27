// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Typed policy examples and a direct connection to the production fold/answer bodies.

use super::history_algebra::{self as algebra, src_sem};
use super::history_specs::{
    self as language, EventView, Head, HeadField, Regex, SrcTest, Subst, Term,
};
use crate::languages::history_table::Event;
use crate::rvm::program::HistoryField;
use crate::rvm::vm::history_tables::graph::ObservationWorld;
use crate::rvm::vm::history_tables::kernel::verify as model;
use crate::rvm::vm::history_tables::kernel::{Bindings, KernelResult, RegexId};
use crate::rvm::vm::history_tables::progress::{verify as progress, CompiledPair};
use crate::utils::limits::ExecutionTimer;
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

pub open spec fn event(principal: nat, action: nat, resource: nat) -> EventView {
    EventView { principal, action, resource }
}

pub open spec fn any_head() -> Head {
    Head { principal: HeadField::Any, action: HeadField::Any, resource: HeadField::Any }
}

pub open spec fn release_head() -> Head {
    Head { principal: HeadField::Bind, action: HeadField::Constant(3), resource: HeadField::Bind }
}

pub open spec fn prior_edit_test() -> SrcTest {
    SrcTest::And(seq![
        SrcTest::Eq(HistoryField::Principal, Term::Variable(HistoryField::Principal)),
        SrcTest::Eq(HistoryField::Action, Term::Constant(2)),
        SrcTest::Eq(HistoryField::Resource, Term::Variable(HistoryField::Resource)),
    ])
}

pub open spec fn prior_edit_tail() -> Regex<SrcTest> {
    Regex::Concat(seq![Regex::All, Regex::Test(prior_edit_test()), Regex::All])
}

pub proof fn epsilon_versus_test_true_on_empty_history(request: EventView)
    ensures language::pair_lang(any_head(), Regex::Epsilon, request, Seq::empty()),
        !language::pair_lang(any_head(), Regex::Test(SrcTest::Bool(true)), request, Seq::empty()),
{
    let theta = event(0, 0, 0);
    language::lemma_pair_lang_substitutions(any_head(), Regex::Epsilon, request, Seq::empty(), theta);
    language::lemma_pair_lang_substitutions(any_head(), Regex::Test(SrcTest::Bool(true)), request, Seq::empty(), theta);
}

pub proof fn candidate_bindings_are_fixed_and_domain_scoped(principal: nat, resource: nat)
    ensures language::head_match(release_head(), event(principal, 3, resource), event(principal, 0, resource)),
        language::src_test_holds(event(principal, 0, resource), prior_edit_test(), event(principal, 2, resource)),
        forall|other: nat| other != principal ==> !language::src_test_holds(
            event(principal, 0, resource), prior_edit_test(), event(other, 2, resource)),
        forall|other: nat| other != resource ==> !language::src_test_holds(
            event(principal, 0, resource), prior_edit_test(), event(principal, 2, other)),
{
    reveal_with_fuel(language::src_test_holds, 3);
    let children = prior_edit_test()->And_0;
    assert forall|i: int| 0 <= i < children.len() implies language::src_test_holds(
        event(principal, 0, resource), children[i], event(principal, 2, resource)) by {
        assert(i == 0 || i == 1 || i == 2);
    }
}

pub proof fn prior_edit_grants_matching_release(principal: nat, resource: nat)
    ensures language::pair_lang(release_head(), prior_edit_tail(),
        event(principal, 3, resource), seq![event(principal, 2, resource)]),
{
    candidate_bindings_are_fixed_and_domain_scoped(principal, resource);
    let theta = event(principal, 0, resource);
    let history = seq![event(principal, 2, resource)];
    let empty = Seq::<EventView>::empty();
    let singleton = seq![empty];
    singleton.lemma_flatten_one_element();
    singleton.lemma_flatten_push(history);
    singleton.push(history).lemma_flatten_push(empty);
    let parts = singleton.push(history).push(empty);
    assert(parts.flatten() =~= history);
    let children = prior_edit_tail()->Concat_0;
    assert forall|i: int| 0 <= i < children.len()
        implies language::lang(src_sem(theta), children[i], parts[i]) by {
        assert(i == 0 || i == 1 || i == 2);
    }
    assert(language::lang(src_sem(theta), prior_edit_tail(), history));
    language::lemma_pair_lang_substitutions(release_head(), prior_edit_tail(),
        event(principal, 3, resource), history, theta);
}

pub proof fn same_event_differs_under_candidate_bindings(principal: nat, other: nat, resource: nat)
    requires principal != other,
    ensures language::src_test_holds(event(principal, 0, resource), prior_edit_test(), event(principal, 2, resource)),
        !language::src_test_holds(event(other, 0, resource), prior_edit_test(), event(principal, 2, resource)),
{
    candidate_bindings_are_fixed_and_domain_scoped(principal, resource);
    candidate_bindings_are_fixed_and_domain_scoped(other, resource);
}

pub proof fn mandatory_field_neq_is_eq_complement(theta: Subst, field: HistoryField, value: nat, request: EventView)
    ensures language::src_test_holds(theta, SrcTest::Neq(field, Term::Constant(value)), request)
        == !language::src_test_holds(theta, SrcTest::Eq(field, Term::Constant(value)), request),
{ }

pub proof fn empty_regex_lists_keep_their_identities(theta: Subst, history: Seq<EventView>)
    ensures language::lang(src_sem(theta), Regex::Concat(Seq::empty()), history) == (history.len() == 0),
        !language::lang(src_sem(theta), Regex::Union(Seq::empty()), history),
        language::lang(src_sem(theta), Regex::Intersect(Seq::empty()), history),
{
    algebra::lemma_parts_concat_nil(src_sem(theta), history);
}

pub proof fn regex_not_is_not_one_event_neq(theta: Subst, first: EventView, second: EventView)
    ensures language::lang(src_sem(theta), Regex::Not(Box::new(Regex::Test(SrcTest::Bool(true)))), seq![first, second]),
        !language::lang(src_sem(theta), Regex::Test(SrcTest::Bool(false)), seq![first, second]),
{
    reveal_with_fuel(language::lang, 2);
    assert(seq![first, second].len() == 2);
}

pub proof fn star_accepts_two_typed_events(theta: Subst, first: EventView, second: EventView)
    ensures language::lang(src_sem(theta), Regex::Star(Box::new(Regex::Test(SrcTest::Bool(true)))), seq![first, second]),
{
    let item = Regex::Test(SrcTest::Bool(true));
    algebra::lemma_parts_star_single(src_sem(theta), item, seq![first]);
    algebra::lemma_parts_star_single(src_sem(theta), item, seq![second]);
    algebra::lemma_parts_star_join(src_sem(theta), item, seq![first], seq![second]);
    assert(seq![first] + seq![second] =~= seq![first, second]);
}

/// The same production bodies used by HISTORY_STEP implement the typed decision.
pub(crate) fn fold_decision(
    pair: &mut CompiledPair, residual: RegexId, events: &[Event], bindings: &Bindings,
    timer: &mut ExecutionTimer, world: &mut ObservationWorld,
) -> (result: KernelResult<bool>)
    requires progress::pair_wf(*old(pair)),
        residual@ < (*old(pair)).store.graph().regexes.len(),
    ensures progress::pair_wf(*final(pair)),
        progress::pair_frame(*old(pair), *final(pair)),
        result matches Ok(answer) ==> answer == model::regex_lang(
            (*old(pair)).store.graph(), bindings@, residual@, model::events_view(events@)),
{
    hide(language::lang);
    hide(model::lift_regex);
    hide(model::test_holds);
    proof {
        assert(model::graph_wf((*pair).store.graph()));
    }
    let ghost entry = *pair;
    let out = pair.fold(residual, events, bindings, timer, world)?;
    proof {
        let graph = (*pair).store.graph();
        let word = model::events_view(events@);
        assert(progress::residual_folds(*pair, bindings@, residual, word, out));
        assert(model::regex_lang(graph, bindings@, out@, Seq::<EventView>::empty())
            == model::regex_lang(graph, bindings@, residual@, word + Seq::<EventView>::empty()));
        assert(word + Seq::<EventView>::empty() =~= word);
        language::lemma_nullable_iff_nil(model::gsem(bindings@), model::lift_regex(graph, out@));
        model::lemma_graph_wf_elim(entry.store.graph());
        model::lemma_lift_regex_stable(entry.store.graph(), graph, residual@);
        assert(language::nullable(model::lift_regex(graph, out@))
            == model::regex_lang(entry.store.graph(), bindings@, residual@, word));
    }
    let ghost folded = *pair;
    let answer = pair.answer(out, timer, world)?;
    proof {
        assert((*pair).store.graph() == folded.store.graph());
        assert(progress::pair_frame(entry, *pair));
    }
    Ok(answer)
}

}

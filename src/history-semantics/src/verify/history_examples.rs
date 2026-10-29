// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Typed policy examples connected to the production fold, answer, and cache transaction bodies.

use super::history_algebra::{self as algebra, src_sem};
use crate::compile::verify as source;
use crate::progress::{CompiledPair, verify as progress};
use crate::runtime::RuleRuntime;
use crate::runtime::verify::{self as cache, HistorySnapshots};
use alloc::boxed::Box;
use history_store::cache::HistoryCursor;
use history_store::history::StoredHistory;
use history_store::store::Event;
use history_syntax::syntax::Component;
use junco_core::flat::FlatPair;
use junco_core::kernel::verify as model;
use junco_core::kernel::{Bindings, KernelResult, RegexId};
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
use junco_core::verify::history_specs::{
    self as language, EventView, Head, HeadField, Regex, SrcTest, Subst, Term,
};
use vstd::prelude::*;

verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;

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
        SrcTest::Eq(Component::Principal, Term::Variable(Component::Principal)),
        SrcTest::Eq(Component::Action, Term::Constant(2)),
        SrcTest::Eq(Component::Resource, Term::Variable(Component::Resource)),
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

pub proof fn mandatory_field_neq_is_eq_complement(theta: Subst, field: Component, value: nat, request: EventView)
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
pub(crate) fn fold_decision<L: Limits>(
    pair: &mut CompiledPair, residual: RegexId, events: &[Event], bindings: &Bindings,
    limits: &mut L, world: &mut ObservationWorld,
) -> (result: KernelResult<bool>)
    requires progress::pair_wf(*old(pair)),
        residual@ < (*old(pair)).store.graph().regexes.len(),
    ensures progress::pair_wf(*final(pair)),
        progress::pair_frame(*old(pair), *final(pair)),
        result matches Ok(answer) ==> answer == model::regex_lang(
            (*old(pair)).store.graph(), bindings@, residual@, history_store::store::verify::events_view(events@)),
{
    hide(language::lang);
    hide(model::lift_regex);
    hide(model::test_holds);
    proof {
        assert(model::graph_wf((*pair).store.graph()));
    }
    let ghost entry = *pair;
    let out = pair.fold(residual, events, bindings, limits, world)?;
    proof {
        let graph = (*pair).store.graph();
        let word = history_store::store::verify::events_view(events@);
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
    let answer = pair.answer(out, limits, world)?;
    proof {
        assert((*pair).store.graph() == folded.store.graph());
        assert(progress::pair_frame(entry, *pair));
    }
    Ok(answer)
}

pub(crate) proof fn cache_rejects_wrong_residual(
    pair: CompiledPair, cursor: HistoryCursor, snapshots: HistorySnapshots,
)
    requires progress::pair_wf(pair),
        pair.root@ == pair.store.graph().constants.empty,
        cursor.residual@ == pair.store.graph().constants.all,
        snapshots.contains_key((cursor.history, cursor.revision)),
        cursor.consumed <= snapshots[(cursor.history, cursor.revision)].len(),
        language::event_wf(cursor.bindings@),
    ensures !cache::cursor_matches_snapshot(pair, cursor, snapshots),
        !cache::cursor_cache_wf(pair, seq![cursor], snapshots),
{
    let graph = pair.store.graph();
    let empty = Seq::<EventView>::empty();
    let prefix = snapshots[(cursor.history, cursor.revision)].take(cursor.consumed as int);
    model::lemma_graph_wf_elim(graph);
    assert(model::lift_regex(graph, pair.root@) == Regex::Empty);
    assert(model::lift_regex(graph, cursor.residual@) == Regex::All);
    assert(model::regex_lang(graph, cursor.bindings@, cursor.residual@, empty));
    assert(!model::regex_lang(graph, cursor.bindings@, pair.root@, prefix + empty));
    if cache::cursor_matches_snapshot(pair, cursor, snapshots) {
        assert(model::regex_lang(graph, cursor.bindings@, cursor.residual@, empty)
            == model::regex_lang(graph, cursor.bindings@, pair.root@, prefix + empty));
    }
    if cache::cursor_cache_wf(pair, seq![cursor], snapshots) {
        assert(seq![cursor][0] == cursor);
        assert(cache::cursor_matches_snapshot(pair, seq![cursor][0], snapshots));
    }
}

/// Cache selection and every batch use the production transaction bodies.
pub(crate) fn cached_decision<L: Limits>(
    runtime: &mut RuleRuntime, history: usize, bindings: &Bindings, stored: &StoredHistory,
    target_len: usize, batch_size: usize, limits: &mut L, world: &mut ObservationWorld,
) -> (result: KernelResult<bool>)
    requires cache::cursor_cache_wf(old(runtime).pair, old(runtime).cursors@, old(runtime).snapshots@),
        cache::snapshot_compatible(old(runtime).snapshots@, history, (stored@.revision as u64),
            stored@.events),
        language::event_wf(bindings@), batch_size > 0, target_len <= stored@.events.len(),
    ensures cache::cursor_cache_wf(final(runtime).pair, final(runtime).cursors@, final(runtime).snapshots@),
        progress::pair_frame(old(runtime).pair, final(runtime).pair),
        result matches Ok(answer) ==> answer == model::regex_lang(
            old(runtime).pair.store.graph(), bindings@, old(runtime).pair.root@,
            stored@.events.take(target_len as int)),
{
    hide(language::lang);
    hide(model::lift_regex);
    hide(model::test_holds);
    reveal(cache::runtime_wf);
    reveal(cache::resume_requires);
    reveal(cache::resume_ensures);
    reveal(cache::advance_requires);
    reveal(cache::advance_ensures);
    proof { history_store::history::lemma_stored_history_view(*stored); }
    let ghost entry = runtime.pair;
    let mut cursor = runtime.resume_cursor(history, bindings, stored, target_len);
    loop
        invariant entry == old(runtime).pair,
            progress::pair_wf(entry),
            cache::cursor_cache_wf(runtime.pair, runtime.cursors@, runtime.snapshots@),
            progress::pair_frame(entry, runtime.pair),
            runtime.snapshots@.contains_key((history, (stored@.revision as u64))),
            runtime.snapshots@[(history, (stored@.revision as u64))] == stored@.events,
            cache::batch_matches_snapshot(runtime.pair, cursor, history, (stored@.revision as u64),
                *bindings, runtime.snapshots@),
            cursor.consumed <= target_len, target_len <= stored@.events.len(),
            language::event_wf(bindings@), batch_size > 0,
        decreases target_len - cursor.consumed,
    {
        proof { history_store::history::lemma_stored_history_view(*stored); }
        let ghost batch_entry = runtime.pair;
        let ghost consumed = cursor.consumed;
        let result = runtime.advance_cursor(&mut cursor, history, bindings, stored,
            target_len, batch_size, limits, world);
        proof {
            let first = entry.store.graph();
            let last = runtime.pair.store.graph();
            assert(first.tests.is_prefix_of(last.tests));
            assert(first.regexes.is_prefix_of(last.regexes));
            assert(first.transitions.is_prefix_of(last.transitions));
            assert(progress::pair_frame(entry, runtime.pair));
            // Only the table facts: `unique_nodes` adds a quadratic `no_duplicates` matching loop.
            assert(model::tables_wf(first)) by { model::lemma_graph_wf_elim(first); }
            model::lemma_lift_regex_stable(first, batch_entry.store.graph(), entry.root@);
        }
        match result {
            Err(error) => return Err(error),
            Ok(Some(answer)) => return Ok(answer),
            Ok(None) => {
                proof {
                    language::lemma_selected_end(consumed as nat, target_len as nat, batch_size as nat);
                    assert(consumed < target_len);
                    assert(consumed < cursor.consumed);
                }
            },
        }
    }
}

/// Construction and cache-backed decisions preserve the supplied numeric template's language.
pub(crate) fn template_cached_decision<L: Limits>(
    template: &FlatPair<u64>, precompile: bool, history: usize, bindings: &Bindings,
    stored: &StoredHistory, target_len: usize, batch_size: usize,
    limits: &mut L, world: &mut ObservationWorld,
) -> (result: KernelResult<bool>)
    requires language::event_wf(bindings@), batch_size > 0, target_len <= stored@.events.len(),
    ensures result matches Ok(answer) ==> answer == source::source_regex(
        *template, template.root as nat, bindings@,
        stored@.events.take(target_len as int)),
{
    hide(language::lang);
    hide(model::lift_regex);
    hide(model::test_holds);
    reveal(cache::constructor_result);
    reveal(cache::runtime_wf);
    let mut runtime = RuleRuntime::new(template, precompile, limits, world)?;
    cached_decision(&mut runtime, history, bindings, stored, target_len, batch_size, limits, world)
}

/// The portable encoding endpoint reaches the same construction and cache transaction bodies.
pub(crate) fn flat_template_cached_decision<L: Limits>(
    template: &FlatPair<u64>, precompile: bool, history: usize, request: &Event,
    stored: &StoredHistory, target_len: usize, batch_size: usize,
    Ghost(candidate): Ghost<Seq<u64>>, Ghost(word): Ghost<Seq<Seq<u64>>>,
    limits: &mut L, world: &mut ObservationWorld,
) -> (result: KernelResult<Option<bool>>)
    requires junco_core::flat::verify::structural_wf(*template), batch_size > 0,
        target_len <= stored@.events.len(), junco_core::verify::encoding::event_representation(candidate, request@),
        junco_core::verify::encoding::word_representation(word, stored@.events.take(target_len as int)),
    ensures result matches Ok(answer) ==> match answer {
        None => !junco_core::flat::verify::head_matches(template.head@, candidate,
            junco_core::verify::encoding::numeric_equality()),
        Some(accepted) => junco_core::flat::verify::head_matches(template.head@, candidate,
            junco_core::verify::encoding::numeric_equality())
            && accepted == junco_core::flat::verify::lang(template.tests@, template.regexes@,
                template.root as nat, candidate, word, junco_core::verify::encoding::numeric_equality()),
    },
{
    proof { source::lemma_flat_head(*template, candidate, request@); }
    let bindings = match crate::compile::bindings(template, request) {
        Some(bindings) => {
            proof { source::lemma_bindings_match(*template, *request, bindings); }
            bindings
        },
        None => {
            proof { source::lemma_head_rejects(*template, *request); }
            return Ok(None);
        },
    };
    proof { assert(language::event_wf(bindings@)); }
    let accepted = template_cached_decision(template, precompile, history, &bindings,
        stored, target_len, batch_size, limits, world)?;
    proof {
        source::lemma_flat_regex(*template, template.root as nat, candidate, request@,
            word, stored@.events.take(target_len as int), bindings@);
    }
    Ok(Some(accepted))
}

}

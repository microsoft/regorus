//! Owned DSL → finite component books → retained numeric runtime composition.
//!
//! The public constructor and decision bodies supply the structural flattening,
//! finite published snapshots, history correspondence, and cached numeric answer.
//! Native Eq/Hash/projection remain conditional; retained provenance follows lifecycle resources.

use crate::compile::verify as numeric;
use crate::compiled_rule::CompiledRule;
use crate::compiled_rule::verify as typed;
use crate::runtime::{RuleRuntime, verify as cache};
use alloc::sync::Arc;
use history_store::history::{History, verify as raw};
use history_store::typed::{Store, verify as books};
use history_syntax::Event;
use history_syntax::syntax::Rule;
use junco_core::error::{CompileError, HistoryError};
use junco_core::flat::FlatPair;
use junco_core::kernel::verify as graph;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
use junco_core::verify::dsl;
use vstd::prelude::*;

verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;

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
    reveal(cache::runtime_wf);
    let first = before.pair.store.graph();
    let last = after.pair.store.graph();
    graph::lemma_graph_wf_elim(first);
    graph::lemma_lift_regex_stable(first, last, before.pair.root@);
    assert forall|theta: junco_core::verify::history_specs::Subst,
        word: Seq<junco_core::verify::history_specs::EventView>|
        junco_core::verify::history_specs::event_wf(theta) implies
            graph::regex_lang(last, theta, after.pair.root@, word)
                == numeric::source_regex(template, template.root as nat, theta, word) by {
        assert(graph::regex_lang(first, theta, before.pair.root@, word)
            == numeric::source_regex(template, template.root as nat, theta, word));
    }
}

/// This is the actual public consuming constructor followed by the public decision.
/// No numeric-only event restriction or semantic-equivalence premise is supplied.
pub(crate) fn public_compiled_decision<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, history: &History<E>, candidate: &E,
) -> (result: Result<Option<bool>, CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history),
    ensures books::native_obligations::<E>() ==> (result matches Ok(answer) ==> match answer {
        None => !dsl::head_matches(rule.head@, books::projection(*candidate)),
        Some(accepted) => dsl::head_matches(rule.head@, books::projection(*candidate))
            && accepted == dsl::lang(rule.tail@, rule.head@,
                books::projection(*candidate), raw::raw_word(*history)),
    }),
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
        books::native_obligations::<E>() ==> (result matches Ok(answer) ==> match answer {
            None => !dsl::head_matches(rule.head@, books::projection(*candidate)),
            Some(accepted) => dsl::head_matches(rule.head@, books::projection(*candidate))
                && accepted == dsl::lang(rule.tail@, rule.head@,
                    books::projection(*candidate), raw::raw_word(*final(history))),
        }),
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
        books::native_obligations::<E>() ==>
            typed::dsl_result(typed::source_rule(*old(compiled)), *history, *candidate, result),
{
    compiled.accepts_history_with_limits(history, candidate, limits, world)
}

}

// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use super::error::{
    invalid_truth_assignment as assignment_error, missing_transition_atom,
    symbolic_invariant as invariant,
};
#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
use super::kernel::*;
#[cfg(verus_keep_ghost)]
use super::normalize::verify as norm;
use super::normalize::*;
use super::work::WorkVec;
#[cfg(verus_keep_ghost)]
use crate::verify::history_algebra as algebra;
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::{KernelStoreSpec, SmallVecSpecFns};
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use crate::verify::value_specs::Data;
#[cfg(verus_keep_ghost)]
use alloc::boxed::Box;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(out) => id@ < cache@.len() && cache@[id@ as int] == Some(out), Err(_) => true,
})]
fn cached(cache: &[Option<TransitionId>], id: RegexId) -> KernelResult<TransitionId> {
    match cache.get(id.index()?) {
        Some(Some(value)) => Ok(*value),
        _ => Err(invariant()),
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        derivative_cache_wf(old(store).graph(), old(cache)@),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), derivative_cache_wf(final(store).graph(), final(cache)@),
        old(cache)@.is_prefix_of(final(cache)@),
        forall|i: int| old(cache)@.len() <= i < final(cache)@.len() ==> final(cache)@[i] is None,
        result is Err ==> final(cache)@ == old(cache)@,
        result is Ok ==> id@ < final(cache)@.len()
            && final(cache)@.len() == if old(cache)@.len() > id@ { old(cache)@.len() } else { id@ + 1 },
)]
fn grow_cache<G: KernelStore>(
    store: &mut G,
    cache: &mut Vec<Option<TransitionId>>,
    id: RegexId,
) -> KernelResult<()> {
    let required = match id.index()?.checked_add(1) {
        Some(v) => v,
        None => return Err(invariant()),
    };
    if required > cache.len() {
        let extra = match required.checked_sub(cache.len()) {
            Some(v) => v,
            None => return Err(invariant()),
        };
        let bytes = match extra.checked_mul(core::mem::size_of::<Option<TransitionId>>()) {
            Some(v) => v,
            None => return Err(invariant()),
        };
        store.reserve_derivatives(cache, extra)?;
        store.charge_aux(bytes)?;
        cache.resize(required, None);
        proof! {
            assert forall|i: int| 0 <= i < cache@.len() implies match #[trigger] cache@[i] {
                Some(out) => derivative_correct(store.graph(), i as nat, out), None => true,
            } by {
                if i >= old(cache)@.len() { assert(cache@[i] is None); }
                else { assert(cache@[i] == old(cache)@[i]); }
            }
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), derivative_factors_wf(store.graph(), id, count as nat, concat),
        derivative_tasks_wf(store.graph(), old(tasks).view()),
    ensures derivative_tasks_wf(store.graph(), final(tasks).view()),
        old(tasks).view().is_prefix_of(final(tasks).view()),
        result is Ok ==> final(tasks).view().len() <= old(tasks).view().len() + count,
        forall|j: int| #![trigger final(tasks).view()[j]] old(tasks).view().len() <= j < final(tasks).view().len() ==> final(tasks).view()[j].0@
            == derivative_children_ids(store.graph(), id)[j - old(tasks).view().len()] && !final(tasks).view()[j].1,
)]
fn schedule_derivative_children<G: KernelStore>(
    store: &G,
    id: RegexId,
    count: usize,
    concat: bool,
    tasks: &mut WorkVec<(RegexId, bool)>,
) -> KernelResult<()> {
    proof! { model::lemma_graph_regex_wf(store.graph(), id@); }
    let mut prefix = true;
    let mut failure = None;
    let mut i = 0;
    proof_decl! { let ghost start = tasks.view(); }
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant i <= count, derivative_tasks_wf(store.graph(), tasks.view()),
        model::graph_wf(store.graph()), derivative_factors_wf(store.graph(), id, count as nat, concat),
        model::regex_node_wf_at(store.graph(), store.graph().regexes[id@ as int], id@),
        prefix == derivative_prefix(store.graph(), id, i as nat),
        start == old(tasks).view(), start.is_prefix_of(tasks.view()),
        forall|j: int| #![trigger tasks.view()[j]] start.len() <= j < tasks.view().len() ==> tasks.view()[j].0@
            == derivative_children_ids(store.graph(), id)[j - start.len()] && !tasks.view()[j].1,
        invariant_except_break failure is None, tasks.view().len() <= start.len() + i,
            (!concat || prefix) ==> tasks.view().len() == start.len() + i,
        ensures failure is None ==> tasks.view().len() <= start.len() + count,
        decreases count - i))]
    while i < count {
        let child = loop_try!(regex_child(store, id, i), failure);
        proof_decl! { let ghost prior = tasks.view(); }
        if !concat || prefix {
            tasks.push((child, false));
        }
        proof! {
            assert forall|j: int| #![trigger tasks.view()[j]] start.len() <= j < tasks.view().len() implies tasks.view()[j].0@
                == derivative_children_ids(store.graph(), id)[j - start.len()] && !tasks.view()[j].1 by {
                if j < prior.len() { assert(tasks.view()[j] == prior[j]); } else {
                    assert(j == start.len() + i);
                    assert(child@ == derivative_children_ids(store.graph(), id)[i as int]);
                }
            }
        }
        let n = loop_try!(nullable(store, child), failure);
        prefix &= n;
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), start <= count,
        id@ < store.graph().regexes.len(), count == derivative_children_ids(store.graph(), id).len(),
    ensures match result { Ok(suffix) =>
        super::normalize::verify::regex_ids_valid(store.graph(), suffix.view())
        && model::regex_ids(suffix.view()) == derivative_children_ids(store.graph(), id).subrange(start as int, count as int),
        Err(_) => true },
)]
fn concat_suffix<G: KernelStore>(
    store: &G,
    id: RegexId,
    start: usize,
    count: usize,
) -> KernelResult<WorkVec<RegexId>> {
    proof! { model::lemma_graph_regex_wf(store.graph(), id@); }
    let mut suffix = WorkVec::new();
    let mut failure = None;
    let mut i = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant start <= i <= count,
        model::graph_wf(store.graph()), id@ < store.graph().regexes.len(),
        count == derivative_children_ids(store.graph(), id).len(),
        model::regex_node_wf_at(store.graph(), store.graph().regexes[id@ as int], id@),
        super::normalize::verify::regex_ids_valid(store.graph(), suffix.view()),
        suffix.view().len() == i - start,
        forall|j: int| 0 <= j < suffix.view().len() ==> suffix.view()[j]@ == derivative_children_ids(store.graph(), id)[start as int + j],
        ensures failure.is_none() ==> i == count, decreases count - i))]
    while i < count {
        proof_decl! { let ghost prior_suffix = suffix.view(); }
        let child = loop_try!(regex_child(store, id, i), failure);
        suffix.push(child);
        proof! {
            assert(child@ == derivative_children_ids(store.graph(), id)[i as int]);
            assert(suffix.view() == prior_suffix.push(child));
            assert forall|j: int| 0 <= j < suffix.view().len() implies
                model::regex_ids(suffix.view())[j] == derivative_children_ids(store.graph(), id)[start as int + j] by {
                if j < prior_suffix.len() {
                    assert(suffix.view()[j] == prior_suffix[j]);
                    assert(prior_suffix[j]@ == derivative_children_ids(store.graph(), id)[start as int + j]);
                } else { assert(suffix.view()[j] == child); assert(start + j == i); }
            }
            assert(model::regex_ids(suffix.view()) =~= derivative_children_ids(store.graph(), id).subrange(start as int, i as int + 1));
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    proof! {
        assert(model::regex_ids(suffix.view()) =~= derivative_children_ids(store.graph(), id).subrange(start as int, count as int));
    }
    Ok(suffix)
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
struct DerivativeFactors {
    root: RegexId,
    count: usize,
    concat: bool,
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        derivative_cache_wf(old(store).graph(), cache@),
        derivative_factors_wf(old(store).graph(), factors.root, factors.count as nat, factors.concat), index < factors.count,
        derivative_results(old(store).graph(), factors.root, factors.concat, index as nat, old(results).view()),
        prefix == derivative_prefix(old(store).graph(), factors.root, index as nat),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        derivative_cache_wf(final(store).graph(), cache@),
        match result { Ok(next) => next == derivative_prefix(final(store).graph(), factors.root, index as nat + 1)
            && derivative_results(final(store).graph(), factors.root, factors.concat, index as nat + 1, final(results).view()), Err(_) => true },
)]
fn derivative_child_step<G: KernelStore>(
    store: &mut G,
    cache: &[Option<TransitionId>],
    factors: DerivativeFactors,
    index: usize,
    results: &mut WorkVec<TransitionId>,
    prefix: bool,
) -> KernelResult<bool> {
    proof_decl! { let ghost before = store.graph(); let ghost prior_results = results.view(); }
    proof! { derivative_frame(store.graph()); model::lemma_graph_regex_wf(store.graph(), factors.root@); }
    store.checkpoint()?;
    let child = regex_child(store, factors.root, index)?;
    if !factors.concat || prefix {
        let d = cached(cache, child)?;
        if factors.concat {
            let start = match index.checked_add(1) {
                Some(v) => v,
                None => return Err(invariant()),
            };
            let suffix = concat_suffix(store, factors.root, start, factors.count)?;
            results.push(transition_append(store, d, &suffix)?);
            proof! {
                derivative_append_factor(store.graph(), factors.root, index as int, d, suffix.view(), results.view().last());
                derivative_results_push(store.graph(), factors.root, true, index as nat, prior_results, results.view().last());
            }
        } else {
            results.push(d);
            proof! { derivative_results_push(store.graph(), factors.root, false, index as nat, prior_results, d); }
        }
    }
    proof! {
        if factors.concat && !prefix { derivative_results_skip(store.graph(), factors.root, index as nat, results.view()); }
    }
    let n = nullable(store, child)?;
    Ok(prefix && n)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        derivative_cache_wf(old(store).graph(), cache@),
        derivative_factors_wf(old(store).graph(), id, count as nat, concat),
        match old(store).graph().regexes[id@ as int].kind {
            model::RegexKindNode::Union(_) => !concat && !intersect,
            model::RegexKindNode::Intersect(_) => !concat && intersect,
            model::RegexKindNode::Concat(_) => concat && !intersect,
            _ => false,
        },
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        derivative_cache_wf(final(store).graph(), cache@),
        match result { Ok(out) => derivative_correct(final(store).graph(), id@, out), Err(_) => true },
)]
fn derivative_children<G: KernelStore>(
    store: &mut G,
    cache: &[Option<TransitionId>],
    id: RegexId,
    count: usize,
    concat: bool,
    intersect: bool,
) -> KernelResult<TransitionId> {
    proof_decl! { let ghost entry = store.graph(); }
    proof! { derivative_frame(store.graph()); }
    let factors = DerivativeFactors {
        root: id,
        count,
        concat,
    };
    let mut results = WorkVec::new();
    let mut state = Ok(true);
    scan!(state,index,count,state.is_ok(),prior=>derivative_child_step(store,cache,factors,index,&mut results,prior);
        invariant index <= count, model::graph_extends(entry, store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            model::graph_wf(entry), id@ < entry.regexes.len(), factors.root == id, factors.count == count, factors.concat == concat,
            derivative_cache_wf(store.graph(), cache@), derivative_factors_wf(store.graph(), id, count as nat, concat),
            store.graph().regexes[id@ as int] == entry.regexes[id@ as int],
            match state { Ok(prefix) => prefix == derivative_prefix(store.graph(), id, index as nat)
                && derivative_results(store.graph(), id, concat, index as nat, results.view()), Err(_) => true },
        decreases count - index);
    state?;
    proof! {
        derivative_frame(store.graph());
        derivative_result_future(store.graph(), id, concat, intersect, results.view());
    }
    if intersect {
        transition_intersect(store, &results)
    } else {
        transition_union(store, &results)
    }
}
// `cache@` is specified as a `Vec` view; a slice parameter would change every caller's contract.
#[allow(clippy::ptr_arg)]
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        derivative_cache_wf(old(store).graph(), old(cache)@), derivative_tasks_wf(old(store).graph(), old(tasks).view()),
        id@ < old(store).graph().regexes.len(),
        match old(store).graph().regexes[id@ as int].kind {
            model::RegexKindNode::Union(cs) => kind == 0 && cs.len() == count,
            model::RegexKindNode::Intersect(cs) => kind == 1 && cs.len() == count,
            model::RegexKindNode::Concat(cs) => kind == 2 && cs.len() == count,
            _ => false,
        },
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(), final(cache)@ == old(cache)@,
        derivative_cache_wf(final(store).graph(), final(cache)@), derivative_tasks_wf(final(store).graph(), final(tasks).view()),
        match result { Ok(Some(out)) => derivative_correct(final(store).graph(), id@, out), _ => true },
        result is Ok ==> final(tasks).view() == old(tasks).view()
            || (derivative_tasks_wf(old(store).graph(), final(tasks).view())
                && derivative_work(old(store).graph(), final(tasks).view())
                    < derivative_work(old(store).graph(), old(tasks).view().push((id, finish)))),
)]
fn derivative_branch<G: KernelStore>(
    store: &mut G,
    cache: &mut Vec<Option<TransitionId>>,
    id: RegexId,
    count: usize,
    kind: u8,
    finish: bool,
    tasks: &mut WorkVec<(RegexId, bool)>,
) -> KernelResult<Option<TransitionId>> {
    proof! { derivative_frame(store.graph()); }
    if finish {
        Ok(Some(derivative_children(
            store,
            cache,
            id,
            count,
            kind == 2,
            kind == 1,
        )?))
    } else {
        tasks.push((id, true));
        schedule_derivative_children(store, id, count, kind == 2, tasks)?;
        proof! { derivative_lemma_work_branch(store.graph(), id, old(tasks).view(), tasks.view()); }
        Ok(None)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), id@ < old(store).graph().regexes.len(),
        derivative_cache_wf(old(store).graph(), old(cache)@), derivative_tasks_wf(old(store).graph(), old(tasks).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        derivative_cache_wf(final(store).graph(), final(cache)@), derivative_tasks_wf(final(store).graph(), final(tasks).view()),
        result is Ok ==> derivative_work(final(store).graph(), final(tasks).view())
            < derivative_work(old(store).graph(), old(tasks).view().push((id, finish))),
)]
fn derivative_step<G: KernelStore>(
    store: &mut G,
    cache: &mut Vec<Option<TransitionId>>,
    id: RegexId,
    finish: bool,
    tasks: &mut WorkVec<(RegexId, bool)>,
) -> KernelResult<()> {
    proof_decl! { let ghost before = store.graph(); let ghost prior_tasks = tasks.view(); }
    proof! { derivative_frame(store.graph()); model::lemma_graph_regex_wf(store.graph(), id@); derivative_constants(store.graph()); }
    store.checkpoint()?;
    grow_cache(store, cache, id)?;
    let index = id.index()?;
    let pending = match cache.get(index) {
        Some(None) => true,
        Some(Some(_)) => false,
        None => return Err(invariant()),
    };
    if pending {
        let c = store.constants();
        proof! { derivative_step_future(store.graph(), id, cache@); }
        let out = match regex_head(store, id)? {
            RegexHead::Empty | RegexHead::Epsilon => Some(c.transition_empty),
            RegexHead::All => Some(c.transition_all),
            RegexHead::Test(test) => Some(transition_if(
                store,
                test,
                c.transition_epsilon,
                c.transition_empty,
            )?),
            RegexHead::Star(inner) => {
                if finish {
                    let d = cached(cache, inner)?;
                    Some(transition_append(store, d, &[id])?)
                } else {
                    tasks.push((id, true));
                    tasks.push((inner, false));
                    proof! { derivative_lemma_work_unary(store.graph(), id, prior_tasks, inner); }
                    None
                }
            }
            RegexHead::Not(inner) => {
                if finish {
                    let d = cached(cache, inner)?;
                    Some(transition_not(store, d)?)
                } else {
                    tasks.push((id, true));
                    tasks.push((inner, false));
                    proof! { derivative_lemma_work_unary(store.graph(), id, prior_tasks, inner); }
                    None
                }
            }
            RegexHead::Union(n) => derivative_branch(store, cache, id, n, 0, finish, tasks)?,
            RegexHead::Intersect(n) => derivative_branch(store, cache, id, n, 1, finish, tasks)?,
            RegexHead::Concat(n) => derivative_branch(store, cache, id, n, 2, finish, tasks)?,
        };
        if let Some(out) = out {
            proof! {
                derivative_constants(store.graph());
                assert(derivative_native_result(store.graph(), id, cache@, out));
                assert(derivative_correct(store.graph(), id@, out));
            }
            match cache.as_mut_slice().get_mut(index) {
                Some(slot) => *slot = Some(out),
                None => return Err(invariant()),
            }
            proof! {
                assert forall|i: int| 0 <= i < cache@.len() implies match #[trigger] cache@[i] {
                    Some(t) => derivative_correct(store.graph(), i as nat, t), None => true,
                } by { if i == index { assert(cache@[i] == Some(out)); } }
            }
        }
    }
    proof! {
        derivative_lemma_step_post(before, store.graph(), id, finish, prior_tasks, tasks.view());
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        derivative_cache_wf(old(store).graph(), old(cache)@), derivative_tasks_wf(old(store).graph(), old(tasks).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        derivative_cache_wf(final(store).graph(), final(cache)@), derivative_tasks_wf(final(store).graph(), final(tasks).view()),
        result is Ok ==> derivative_work(final(store).graph(), final(tasks).view()) < derivative_work(old(store).graph(), old(tasks).view()),
)]
fn derivative_next<G: KernelStore>(
    store: &mut G,
    cache: &mut Vec<Option<TransitionId>>,
    tasks: &mut WorkVec<(RegexId, bool)>,
) -> KernelResult<()> {
    let (id, finish) = match tasks.pop() {
        Some(v) => v,
        None => return Err(invariant()),
    };
    proof! { assert(old(tasks).view() =~= tasks.view().push((id, finish))); }
    derivative_step(store, cache, id, finish, tasks)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), root@ < old(store).graph().regexes.len(),
        derivative_cache_wf(old(store).graph(), old(cache)@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        derivative_cache_wf(final(store).graph(), final(cache)@),
        match result { Ok(out) => derivative_correct(final(store).graph(), root@, out), Err(_) => true },
)]
pub(crate) fn symbolic_derivative<G: KernelStore>(
    store: &mut G,
    cache: &mut Vec<Option<TransitionId>>,
    root: RegexId,
) -> KernelResult<TransitionId> {
    proof_decl! { let ghost entry = store.graph(); }
    let mut tasks = WorkVec::new();
    tasks.push((root, false));
    let mut state = Ok(());
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant model::graph_extends(entry, store.graph()), model::graph_wf(entry),
        store.restoration() == old(store).restoration(),
        model::graph_wf(store.graph()), store.valid_store(), root@ < store.graph().regexes.len(),
        derivative_cache_wf(store.graph(), cache@), derivative_tasks_wf(store.graph(), tasks.view()),
        decreases if state is Ok { derivative_work(store.graph(), tasks.view()) + 1 } else { 0 }))]
    while !tasks.is_empty() && state.is_ok() {
        proof! { derivative_extends(entry, store.graph()); }
        state = derivative_next(store, cache, &mut tasks);
    }
    state?;
    cached(cache, root)
}
#[verus_verify]
#[verus_spec(result => ensures result.is_ok() == assignment_valid(atoms@.len(), words@))]
fn validate_assignment(atoms: &AtomSet, words: &[u64]) -> KernelResult<()> {
    let count = atoms.ids().len();
    let rounded = match count.checked_add(63) {
        Some(v) => v,
        None => return Err(assignment_error()),
    };
    let required = match rounded.checked_div(64) {
        Some(v) => v,
        None => return Err(assignment_error()),
    };
    if words.len() != required {
        return Err(assignment_error());
    }
    let remainder = match count.checked_rem(64) {
        Some(v) => v,
        None => return Err(assignment_error()),
    };
    if remainder != 0 {
        let shift = match u32::try_from(remainder) {
            Ok(v) => v,
            Err(_) => return Err(assignment_error()),
        };
        let last = match words.last() {
            Some(v) => *v,
            None => return Err(assignment_error()),
        };
        let high = match last.checked_shr(shift) {
            Some(v) => v,
            None => return Err(assignment_error()),
        };
        if high != 0 {
            return Err(assignment_error());
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::atom_ids_wf(old(store).graph(), atoms@),
        match previous { Some(i) => positive_atom_at(old(store).graph(), atoms@, primitive@, i), None => true },
    ensures final(store).graph() == old(store).graph(),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store() == old(store).valid_store(),
        match result { Ok(Some(i)) => positive_atom_at(final(store).graph(), atoms@, primitive@, i), _ => true },
)]
fn positive_atom_step<G: KernelStore>(
    store: &mut G,
    primitive: Primitive,
    atoms: &AtomSet,
    index: usize,
    previous: Option<usize>,
) -> KernelResult<Option<usize>> {
    store.checkpoint()?;
    let base = match atoms.ids().get(index) {
        Some(v) => *v,
        None => return Err(missing_transition_atom()),
    };
    let head = test_head(store, base)?;
    if matches!(head,TestHead::Atom(p,true) if p==primitive) {
        Ok(Some(index))
    } else {
        Ok(previous)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::atom_ids_wf(old(store).graph(), atoms@),
        id@ < old(store).graph().tests.len(),
        old(store).graph().tests[id@ as int] == model::TestNode::Atom(primitive@, positive),
    ensures final(store).graph() == old(store).graph(),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store() == old(store).valid_store(),
        match result { Ok(i) => positive_atom_at(final(store).graph(), atoms@, primitive@, i), Err(_) => true },
)]
fn positive_atom_index<G: KernelStore>(
    store: &mut G,
    id: TestId,
    primitive: Primitive,
    positive: bool,
    atoms: &AtomSet,
) -> KernelResult<usize> {
    if positive {
        proof! {
            assert forall|i: int, j: int| 0 <= i < j < atoms@.len()
                implies vstd::std_specs::cmp::OrdSpec::cmp_spec(&atoms@[i], &atoms@[j]) is Less by {
                assert(model::test_ids(atoms@)[i] == atoms@[i]@);
                assert(model::test_ids(atoms@)[j] == atoms@[j]@);
            }
        }
        return match atoms.ids().binary_search(&id) {
            Ok(index) => Ok(index),
            Err(_) => Err(missing_transition_atom()),
        };
    }
    let mut state = Ok(None);
    scan!(state,index,atoms.ids().len(),state.is_ok(),previous=>positive_atom_step(store,primitive,atoms,index,previous);
        invariant store.graph() == old(store).graph(),
            store.restoration() == old(store).restoration(),
            store.valid_store() == old(store).valid_store(), model::atom_ids_wf(store.graph(), atoms@),
            match state { Ok(Some(i)) => positive_atom_at(store.graph(), atoms@, primitive@, i), _ => true },
            decreases atoms@.len() - index,
    );
    let selected = state?;
    match selected {
        Some(index) => Ok(index),
        None => Err(missing_transition_atom()),
    }
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(value) => index / 64 < words@.len() && value == truth_word_bit(words@, index as nat),
    Err(_) => index / 64 >= words@.len(),
})]
fn atom_truth(words: &[u64], index: usize) -> KernelResult<bool> {
    let word = match index.checked_div(64) {
        Some(v) => v,
        None => return Err(assignment_error()),
    };
    let bit = match index.checked_rem(64) {
        Some(v) => v,
        None => return Err(assignment_error()),
    };
    let shift = match u32::try_from(bit) {
        Ok(v) => v,
        Err(_) => return Err(assignment_error()),
    };
    let value = match words.get(word) {
        Some(v) => *v,
        None => return Err(assignment_error()),
    };
    let shifted = match value.checked_shr(shift) {
        Some(v) => v,
        None => return Err(assignment_error()),
    };
    Ok(shifted & 1 != 0)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), id@ < store.graph().tests.len(),
        count == test_children(store.graph(), id).len(), test_tasks_wf(store.graph(), old(tasks).view()),
    ensures test_tasks_wf(store.graph(), final(tasks).view()),
        result.is_ok() ==> final(tasks).view() == old(tasks).view() + child_test_tasks(store.graph(), id, 0),
)]
fn schedule_test_children<G: KernelStore>(
    store: &G,
    id: TestId,
    count: usize,
    tasks: &mut WorkVec<(TestId, bool)>,
) -> KernelResult<()> {
    proof! { model::lemma_graph_test_wf(store.graph(), id@); }
    let mut failure = None;
    let mut remaining = count;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining <= count, model::graph_wf(store.graph()), id@ < store.graph().tests.len(),
            count == test_children(store.graph(), id).len(), test_tasks_wf(store.graph(), old(tasks).view()),
            test_tasks_wf(store.graph(), tasks.view()),
            failure.is_none() ==> tasks.view() == old(tasks).view() + child_test_tasks(store.graph(), id, remaining as nat),
        ensures failure.is_none() ==> remaining == 0,
        decreases remaining,
    ))]
    while remaining != 0 {
        let i = loop_try!(
            match remaining.checked_sub(1) {
                Some(value) => Ok(value),
                None => Err(invariant()),
            },
            failure
        );
        remaining = i;
        let child = loop_try!(test_child(store, id, i), failure);
        proof! {
            assert(child@ == test_children(store.graph(), id)[i as int]);
            model::lemma_graph_test_wf(store.graph(), id@);
            assert(child@ < store.graph().tests.len());
            assert(child_test_tasks(store.graph(), id, i as nat)
                =~= child_test_tasks(store.graph(), id, i as nat + 1).push((child, false)));
        }
        tasks.push((child, false));
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(out) => count <= old(values).view().len()
        && final(values).view() == old(values).view().take(old(values).view().len() - count)
        && out == bool_fold(old(values).view().skip(old(values).view().len() - count), and),
    Err(_) => true,
})]
fn fold_test_values(values: &mut WorkVec<bool>, count: usize, and: bool) -> KernelResult<bool> {
    let mut out = and;
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= count, i <= old(values).view().len(),
            values.view() == old(values).view().take(old(values).view().len() - i),
            out == bool_fold(old(values).view().skip(old(values).view().len() - i), and),
        ensures failure.is_none() ==> i == count,
        decreases count - i,
    ))]
    while i < count {
        let value = loop_try!(
            match values.pop() {
                Some(v) => Ok(v),
                None => Err(invariant()),
            },
            failure
        );
        proof! {
            let suffix = old(values).view().skip(old(values).view().len() - i);
            bool_fold_prepend(value, suffix, and);
            assert(old(values).view().skip(old(values).view().len() - i - 1) =~= seq![value] + suffix);
        }
        if and {
            out &= value
        } else {
            out |= value
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(out)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), id@ < store.graph().tests.len(),
        store.graph().tests[id@ as int] == (if and { model::TestNode::And(test_children(store.graph(), id)) } else { model::TestNode::Or(test_children(store.graph(), id)) }),
        count == test_children(store.graph(), id).len(), test_tasks_wf(store.graph(), old(tasks).view()),
    ensures test_tasks_wf(store.graph(), final(tasks).view()),
        result.is_ok() ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event)
                == test_run(store.graph(), final(tasks).view(), final(values).view(), sym, theta, event),
        result.is_ok() ==> final(tasks).view() == old(tasks).view()
            || norm::test_not_work(store.graph(), final(tasks).view())
                < norm::test_not_work(store.graph(), old(tasks).view().push((id, finish))),
)]
fn evaluate_test_branch<G: KernelStore>(
    store: &G,
    id: TestId,
    count: usize,
    and: bool,
    finish: bool,
    tasks: &mut WorkVec<(TestId, bool)>,
    values: &mut WorkVec<bool>,
) -> KernelResult<()> {
    if finish {
        let out = fold_test_values(values, count, and)?;
        values.push(out);
        proof! {
            assert(old(tasks).view().push((id, finish)).drop_last() =~= old(tasks).view());
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event)
                    == test_run(store.graph(), tasks.view(), values.view(), sym, theta, event) by {
                test_run_unfold(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event);
            }
        }
    } else {
        tasks.push((id, true));
        schedule_test_children(store, id, count, tasks)?;
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event)
                    == test_run(store.graph(), tasks.view(), values.view(), sym, theta, event) by {
                test_expand(store.graph(), id, old(tasks).view(), old(values).view(), sym, theta, event);
            }
            test_lemma_eval_branch_work(store.graph(), id, old(tasks).view());
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), id@ < old(store).graph().tests.len(),
        model::atom_ids_wf(old(store).graph(), atoms@), test_tasks_wf(old(store).graph(), old(tasks).view()),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store() == old(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        test_tasks_wf(final(store).graph(), final(tasks).view()),
        result.is_ok() ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            truth_words_realize(final(store).graph(), atoms@, words@, sym, theta, event) ==>
                test_run(final(store).graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event)
                    == test_run(final(store).graph(), final(tasks).view(), final(values).view(), sym, theta, event),
        result.is_ok() ==> norm::test_not_work(final(store).graph(), final(tasks).view())
            < norm::test_not_work(old(store).graph(), old(tasks).view().push((id, finish))),
)]
fn evaluate_test_step<G: KernelStore>(
    store: &mut G,
    id: TestId,
    finish: bool,
    atoms: &AtomSet,
    words: &[u64],
    tasks: &mut WorkVec<(TestId, bool)>,
    values: &mut WorkVec<bool>,
) -> KernelResult<()> {
    store.checkpoint()?;
    match test_head(store, id)? {
        TestHead::True => values.push(true),
        TestHead::False => values.push(false),
        TestHead::Atom(primitive, positive) => {
            let index = positive_atom_index(store, id, primitive, positive, atoms)?;
            let value = atom_truth(words, index)?;
            values.push(if positive { value } else { !value });
            proof! {
                realized_atom_value(store.graph(), atoms@, words@, id, primitive@, positive, index, value);
            }
        }
        TestHead::And(n) => evaluate_test_branch(store, id, n, true, finish, tasks, values)?,
        TestHead::Or(n) => evaluate_test_branch(store, id, n, false, finish, tasks, values)?,
    }
    proof! {
        assert(old(tasks).view().push((id, finish)).drop_last() =~= old(tasks).view());
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            truth_words_realize(store.graph(), atoms@, words@, sym, theta, event) implies
                test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event)
                    == test_run(store.graph(), tasks.view(), values.view(), sym, theta, event) by {
            test_run_unfold(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), sym, theta, event);
        }
        test_lemma_eval_step_work(store.graph(), id, finish, old(tasks).view(), tasks.view());
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), model::atom_ids_wf(old(store).graph(), atoms@),
        test_tasks_wf(old(store).graph(), old(tasks).view()),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store() == old(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        test_tasks_wf(final(store).graph(), final(tasks).view()),
        result.is_ok() ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            truth_words_realize(final(store).graph(), atoms@, words@, sym, theta, event) ==>
                test_run(final(store).graph(), old(tasks).view(), old(values).view(), sym, theta, event)
                    == test_run(final(store).graph(), final(tasks).view(), final(values).view(), sym, theta, event),
        result.is_ok() ==> norm::test_not_work(final(store).graph(), final(tasks).view())
            < norm::test_not_work(old(store).graph(), old(tasks).view()),
)]
fn evaluate_test_next<G: KernelStore>(
    store: &mut G,
    atoms: &AtomSet,
    words: &[u64],
    tasks: &mut WorkVec<(TestId, bool)>,
    values: &mut WorkVec<bool>,
) -> KernelResult<()> {
    let (id, finish) = match tasks.pop() {
        Some(v) => v,
        None => return Err(invariant()),
    };
    proof! { assert(old(tasks).view() =~= tasks.view().push((id, finish))); }
    evaluate_test_step(store, id, finish, atoms, words, tasks, values)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), root@ < old(store).graph().tests.len(),
        model::atom_ids_wf(old(store).graph(), atoms@),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store() == old(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        result matches Ok(value) ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            truth_words_realize(final(store).graph(), atoms@, words@, sym, theta, event) ==>
                value == model::test_holds(sym, theta, model::lift_test(final(store).graph(), root@), event),
)]
fn evaluate_test<G: KernelStore>(
    store: &mut G,
    root: TestId,
    atoms: &AtomSet,
    words: &[u64],
) -> KernelResult<bool> {
    let mut tasks = WorkVec::new();
    let mut values = WorkVec::new();
    tasks.push((root, false));
    let mut state = Ok(());
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_run(store.graph(), tasks.view(), values.view(), sym, theta, event)
                == Some(seq![model::test_holds(sym, theta, model::lift_test(store.graph(), root@), event)]) by {
            test_run_unfold(store.graph(), tasks.view(), values.view(), sym, theta, event);
            test_run_unfold(store.graph(), Seq::empty(), seq![model::test_holds(sym, theta, model::lift_test(store.graph(), root@), event)], sym, theta, event);
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant store.graph() == old(store).graph(), store.valid_store() == old(store).valid_store(),
            store.restoration() == old(store).restoration(),
            model::graph_wf(store.graph()), model::atom_ids_wf(store.graph(), atoms@), test_tasks_wf(store.graph(), tasks.view()),
            root@ < store.graph().tests.len(),
            state.is_ok() ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                truth_words_realize(store.graph(), atoms@, words@, sym, theta, event) ==>
                    test_run(store.graph(), tasks.view(), values.view(), sym, theta, event)
                        == Some(seq![model::test_holds(sym, theta, model::lift_test(store.graph(), root@), event)]),
        decreases if state is Ok { norm::test_not_work(store.graph(), tasks.view()) + 1 } else { 0 },
    ))]
    while !tasks.is_empty() && state.is_ok() {
        state = evaluate_test_next(store, atoms, words, &mut tasks, &mut values);
    }
    state?;
    match values.pop() {
        Some(v) => Ok(v),
        None => Err(invariant()),
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), id@ < store.graph().transitions.len(),
        count == transition_children(store.graph(), id).len(), interp_tasks_wf(store.graph(), old(tasks).view()),
    ensures interp_tasks_wf(store.graph(), final(tasks).view()),
        result.is_ok() ==> final(tasks).view() == old(tasks).view() + child_interp_tasks(store.graph(), id, 0),
)]
fn schedule_transition_children<G: KernelStore>(
    store: &G,
    id: TransitionId,
    count: usize,
    tasks: &mut WorkVec<(TransitionId, bool)>,
) -> KernelResult<()> {
    proof! { model::lemma_graph_transition_wf(store.graph(), id@); }
    let mut failure = None;
    let mut remaining = count;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining <= count, model::graph_wf(store.graph()), id@ < store.graph().transitions.len(),
            count == transition_children(store.graph(), id).len(), interp_tasks_wf(store.graph(), old(tasks).view()),
            interp_tasks_wf(store.graph(), tasks.view()),
            failure.is_none() ==> tasks.view() == old(tasks).view() + child_interp_tasks(store.graph(), id, remaining as nat),
        ensures failure.is_none() ==> remaining == 0,
        decreases remaining,
    ))]
    while remaining != 0 {
        let i = loop_try!(
            match remaining.checked_sub(1) {
                Some(value) => Ok(value),
                None => Err(invariant()),
            },
            failure
        );
        remaining = i;
        let child = loop_try!(transition_child(store, id, i), failure);
        proof! {
            model::lemma_graph_transition_wf(store.graph(), id@);
            assert(child@ == transition_children(store.graph(), id)[i as int]);
            assert(child@ < store.graph().transitions.len());
            assert(child_interp_tasks(store.graph(), id, i as nat)
                =~= child_interp_tasks(store.graph(), id, i as nat + 1).push((child, false)));
        }
        tasks.push((child, false));
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), norm::regex_ids_valid(old(store).graph(), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        norm::regex_ids_valid(final(store).graph(), final(values).view()),
        result.is_ok() ==> interp_set_result(final(store).graph(), old(values).view(), final(values).view(), count as nat, intersect),
)]
fn interpret_set<G: KernelStore>(
    store: &mut G,
    count: usize,
    intersect: bool,
    values: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    proof_decl! { let ghost before = store.graph(); }
    let start = match values.len().checked_sub(count) {
        Some(v) => v,
        None => return Err(invariant()),
    };
    let children = match values.get(start..) {
        Some(xs) => xs,
        None => return Err(invariant()),
    };
    proof_decl! { let ghost selected = children@; }
    let out = if intersect {
        regex_intersect(store, children)?
    } else {
        regex_union(store, children)?
    };
    proof! { lifted_values_stable(before, store.graph(), old(values).view()); }
    values.truncate(start);
    values.push(out);
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>| model::symbols_wf(sym) implies
            regex_stack_equiv(model::gsem(sym, theta), lifted_values(store.graph(), values.view()),
                lifted_values(store.graph(), old(values).view().take(old(values).view().len() - count)).push(
                    regex_fold(lifted_values(store.graph(), old(values).view().skip(old(values).view().len() - count)), intersect))) by {
            assert forall|word: Seq<Data>| model::regex_lang(store.graph(), sym, theta, out@, word)
                == language::lang(model::gsem(sym, theta), regex_fold(lifted_values(store.graph(), selected), intersect), word) by {
                regex_fold_ids(store.graph(), selected, intersect, sym, theta, word);
            }
            assert(lifted_values(store.graph(), values.view())
                =~= lifted_values(store.graph(), old(values).view().take(start as int)).push(model::lift_regex(store.graph(), out@)));
            assert(selected =~= old(values).view().skip(start as int));
            assert forall|i: int, word: Seq<Data>| 0 <= i < values.view().len() implies
                language::lang(model::gsem(sym, theta), lifted_values(store.graph(), values.view())[i], word)
                    == language::lang(model::gsem(sym, theta), lifted_values(store.graph(), old(values).view().take(start as int)).push(
                        regex_fold(lifted_values(store.graph(), selected), intersect))[i], word) by {
                if i == start {
                    assert(model::regex_lang(store.graph(), sym, theta, out@, word)
                        == language::lang(model::gsem(sym, theta), regex_fold(lifted_values(store.graph(), selected), intersect), word));
                }
            }
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), id@ < old(store).graph().transitions.len(),
        old(store).graph().transitions[id@ as int] == (if intersect { model::TransitionNode::Intersect(transition_children(old(store).graph(), id)) } else { model::TransitionNode::Union(transition_children(old(store).graph(), id)) }),
        count == transition_children(old(store).graph(), id).len(), interp_tasks_wf(old(store).graph(), old(tasks).view()),
        norm::regex_ids_valid(old(store).graph(), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        interp_tasks_wf(final(store).graph(), final(tasks).view()), norm::regex_ids_valid(final(store).graph(), final(values).view()),
        result.is_ok() ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym) ==>
            interp_results_equiv(model::gsem(sym, theta),
                interp_run(old(store).graph(), old(tasks).view().push((id, finish)), lifted_values(old(store).graph(), old(values).view()), sym, theta, event),
                interp_run(final(store).graph(), final(tasks).view(), lifted_values(final(store).graph(), final(values).view()), sym, theta, event)),
        result.is_ok() ==> final(tasks).view() == old(tasks).view()
            || (interp_tasks_wf(old(store).graph(), final(tasks).view())
                && interp_work(old(store).graph(), final(tasks).view())
                    < interp_work(old(store).graph(), old(tasks).view().push((id, finish)))),
)]
fn interpret_branch<G: KernelStore>(
    store: &mut G,
    id: TransitionId,
    count: usize,
    intersect: bool,
    finish: bool,
    tasks: &mut WorkVec<(TransitionId, bool)>,
    values: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    proof_decl! { let ghost before = store.graph(); }
    if finish {
        interpret_set(store, count, intersect, values)?;
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym) implies
                interp_results_equiv(model::gsem(sym, theta),
                    interp_run(before, old(tasks).view().push((id, finish)), lifted_values(before, old(values).view()), sym, theta, event),
                    interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
                let pending = old(tasks).view().push((id, finish));
                interp_same_configuration_extends(before, store.graph(), pending, old(values).view(), sym, theta, event);
                assert(pending.drop_last() =~= old(tasks).view());
                interp_run_unfold(store.graph(), pending, lifted_values(store.graph(), old(values).view()), sym, theta, event);
                let reduced = lifted_values(store.graph(), old(values).view()).take(old(values).view().len() - count).push(
                    regex_fold(lifted_values(store.graph(), old(values).view()).skip(old(values).view().len() - count), intersect));
                assert(lifted_values(store.graph(), old(values).view().take(old(values).view().len() - count))
                    =~= lifted_values(store.graph(), old(values).view()).take(old(values).view().len() - count));
                assert(lifted_values(store.graph(), old(values).view().skip(old(values).view().len() - count))
                    =~= lifted_values(store.graph(), old(values).view()).skip(old(values).view().len() - count));
                interp_run_congruent(store.graph(), tasks.view(), reduced, lifted_values(store.graph(), values.view()), sym, theta, event);
            }
        }
    } else {
        tasks.push((id, true));
        schedule_transition_children(store, id, count, tasks)?;
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym) implies
                interp_results_equiv(model::gsem(sym, theta),
                    interp_run(before, old(tasks).view().push((id, finish)), lifted_values(before, old(values).view()), sym, theta, event),
                    interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
                interp_expand_set(store.graph(), id, old(tasks).view(), lifted_values(store.graph(), old(values).view()), sym, theta, event);
            }
            interp_lemma_work_branch(store.graph(), id, old(tasks).view());
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), id@ < store.graph().transitions.len(), head@ < store.graph().regexes.len(),
        count == transition_suffix(store.graph(), id).len(),
    ensures result matches Ok(xs) ==> norm::regex_ids_valid(store.graph(), xs.view())
        && model::regex_ids(xs.view()) == seq![head@] + transition_suffix(store.graph(), id),
)]
fn append_values<G: KernelStore>(
    store: &G,
    id: TransitionId,
    count: usize,
    head: RegexId,
) -> KernelResult<WorkVec<RegexId>> {
    proof! { model::lemma_graph_transition_wf(store.graph(), id@); }
    let mut xs = WorkVec::new();
    xs.push(head);
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= count, model::graph_wf(store.graph()), id@ < store.graph().transitions.len(), head@ < store.graph().regexes.len(),
            count == transition_suffix(store.graph(), id).len(), norm::regex_ids_valid(store.graph(), xs.view()),
            model::regex_ids(xs.view()) == seq![head@] + transition_suffix(store.graph(), id).take(i as int),
        ensures failure.is_none() ==> i == count,
        decreases count - i,
    ))]
    while i < count {
        let child = loop_try!(suffix_child(store, id, i), failure);
        proof! {
            model::lemma_graph_transition_wf(store.graph(), id@);
            assert(child@ == transition_suffix(store.graph(), id)[i as int]);
            assert(child@ < store.graph().regexes.len());
        }
        proof_decl! { let ghost previous = xs.view(); }
        xs.push(child);
        proof! {
            norm::regex_ids_push(previous, child);
            assert(transition_suffix(store.graph(), id).take(i as int + 1)
                =~= transition_suffix(store.graph(), id).take(i as int).push(child@));
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(xs)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), id@ < old(store).graph().transitions.len(),
        model::atom_ids_wf(old(store).graph(), atoms@), interp_tasks_wf(old(store).graph(), old(tasks).view()),
        norm::regex_ids_valid(old(store).graph(), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        interp_tasks_wf(final(store).graph(), final(tasks).view()), norm::regex_ids_valid(final(store).graph(), final(values).view()),
        result.is_ok() ==> interp_machine_relation(old(store).graph(), final(store).graph(), old(tasks).view().push((id, finish)), final(tasks).view(), old(values).view(), final(values).view(), atoms@, words@),
        result.is_ok() ==> interp_work(final(store).graph(), final(tasks).view())
            < interp_work(old(store).graph(), old(tasks).view().push((id, finish))),
)]
fn interpret_step<G: KernelStore>(
    store: &mut G,
    id: TransitionId,
    finish: bool,
    atoms: &AtomSet,
    words: &[u64],
    tasks: &mut WorkVec<(TransitionId, bool)>,
    values: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    proof_decl! { let ghost before = store.graph(); let ghost pending = tasks.view(); let ghost prior = values.view(); }
    proof! { model::lemma_graph_transition_wf(store.graph(), id@); norm::transition_unfold(store.graph(), id@); }
    store.checkpoint()?;
    match transition_head(store, id)? {
        TransitionHead::Const(r) => {
            values.push(r);
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                    interp_results_equiv(model::gsem(sym, theta),
                        interp_run(store.graph(), pending.push((id, finish)), lifted_values(store.graph(), prior), sym, theta, event),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
                    language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(store.graph(), r@));
                    interp_value_reduction(store.graph(), id, finish, pending, lifted_values(store.graph(), prior), lifted_values(store.graph(), values.view()), sym, theta, event);
                }
            }
        }
        TransitionHead::If(test, a, b) => {
            let chosen = if evaluate_test(store, test, atoms, words)? {
                a
            } else {
                b
            };
            tasks.push((chosen, false));
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                    model::symbols_wf(sym) && truth_words_realize(before, atoms@, words@, sym, theta, event) implies
                        interp_results_equiv(model::gsem(sym, theta),
                            interp_run(before, pending.push((id, finish)), lifted_values(before, prior), sym, theta, event),
                            interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
                    interp_choose(store.graph(), id, finish, test, a, b, chosen, pending, lifted_values(store.graph(), prior), sym, theta, event);
                }
                interp_lemma_work_if(store.graph(), id, finish, pending, chosen);
            }
        }
        TransitionHead::Union(n) => interpret_branch(store, id, n, false, finish, tasks, values)?,
        TransitionHead::Intersect(n) => {
            interpret_branch(store, id, n, true, finish, tasks, values)?
        }
        TransitionHead::Not(inner) => {
            if finish {
                let inner = match values.pop() {
                    Some(v) => v,
                    None => return Err(invariant()),
                };
                values.push(regex_not(store, inner)?);
                proof! {
                    lifted_values_stable(before, store.graph(), prior);
                    assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym) implies
                        interp_results_equiv(model::gsem(sym, theta),
                            interp_run(store.graph(), pending.push((id, finish)), lifted_values(store.graph(), prior), sym, theta, event),
                            interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
                        assert forall|word: Seq<Data>| language::lang(model::gsem(sym, theta), language::Regex::Not(Box::new(model::lift_regex(store.graph(), inner@))), word)
                            == model::regex_lang(store.graph(), sym, theta, values.view().last()@, word) by {
                            regex_not_language(model::gsem(sym, theta), model::lift_regex(store.graph(), inner@), word);
                        }
                        assert(lifted_values(store.graph(), values.view()) =~= lifted_values(store.graph(), prior).drop_last().push(model::lift_regex(store.graph(), values.view().last()@)));
                        interp_value_reduction(store.graph(), id, finish, pending, lifted_values(store.graph(), prior), lifted_values(store.graph(), values.view()), sym, theta, event);
                    }
                }
            } else {
                tasks.push((id, true));
                tasks.push((inner, false));
                proof! {
                    assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                        interp_run(store.graph(), pending.push((id, finish)), lifted_values(store.graph(), prior), sym, theta, event)
                            == interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event) by {
                        interp_expand_unary(store.graph(), id, inner, pending, lifted_values(store.graph(), prior), sym, theta, event);
                    }
                    interp_lemma_work_unary(store.graph(), id, pending, inner);
                }
            }
        }
        TransitionHead::Append(inner, n) => {
            if finish {
                let head = match values.pop() {
                    Some(v) => v,
                    None => return Err(invariant()),
                };
                let xs = append_values(store, id, n, head)?;
                values.push(regex_concat(store, &xs)?);
                proof! {
                    lifted_values_stable(before, store.graph(), prior);
                    interp_append_ids(store.graph(), xs.view(), head, transition_suffix(store.graph(), id));
                    regex_concat_ids(store.graph(), xs.view());
                    assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym) implies
                        interp_results_equiv(model::gsem(sym, theta),
                            interp_run(store.graph(), pending.push((id, finish)), lifted_values(store.graph(), prior), sym, theta, event),
                            interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
                        assert forall|word: Seq<Data>| model::regex_lang(store.graph(), sym, theta, values.view().last()@, word)
                            == language::lang(model::gsem(sym, theta), language::Regex::Concat(seq![model::lift_regex(store.graph(), head@)]
                                + model::lift_regexes(store.graph(), transition_suffix(store.graph(), id))), word) by {
                            reveal(norm::concat_combo);
                        }
                        assert(lifted_values(store.graph(), values.view()) =~= lifted_values(store.graph(), prior).drop_last().push(model::lift_regex(store.graph(), values.view().last()@)));
                        assert(prior.len() > 0 && prior.last() == head);
                        assert(lifted_values(store.graph(), prior).last() == model::lift_regex(store.graph(), head@));
                        assert forall|i: int, word: Seq<Data>| 0 <= i < prior.len() implies
                            language::lang(model::gsem(sym, theta), interp_action(store.graph(), (id, finish), lifted_values(store.graph(), prior), sym, theta, event)->Some_0[i], word)
                                == language::lang(model::gsem(sym, theta), lifted_values(store.graph(), values.view())[i], word) by {
                            if i == prior.len() - 1 {
                                assert(model::regex_lang(store.graph(), sym, theta, values.view().last()@, word)
                                    == language::lang(model::gsem(sym, theta), language::Regex::Concat(seq![model::lift_regex(store.graph(), head@)]
                                        + model::lift_regexes(store.graph(), transition_suffix(store.graph(), id))), word));
                            }
                        }
                        interp_value_reduction(store.graph(), id, finish, pending, lifted_values(store.graph(), prior), lifted_values(store.graph(), values.view()), sym, theta, event);
                    }
                }
            } else {
                tasks.push((id, true));
                tasks.push((inner, false));
                proof! {
                    assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                        interp_run(store.graph(), pending.push((id, finish)), lifted_values(store.graph(), prior), sym, theta, event)
                            == interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event) by {
                        interp_expand_unary(store.graph(), id, inner, pending, lifted_values(store.graph(), prior), sym, theta, event);
                    }
                    interp_lemma_work_unary(store.graph(), id, pending, inner);
                }
            }
        }
    }
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            model::symbols_wf(sym) && truth_words_realize(before, atoms@, words@, sym, theta, event) implies
                interp_results_equiv(model::gsem(sym, theta),
                    interp_run(before, pending.push((id, finish)), lifted_values(before, prior), sym, theta, event),
                    interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event)) by {
            interp_same_configuration_extends(before, store.graph(), pending.push((id, finish)), prior, sym, theta, event);
        }
        interp_lemma_step_post(before, store.graph(), id, finish, pending, tasks.view());
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        model::atom_ids_wf(old(store).graph(), atoms@), interp_tasks_wf(old(store).graph(), old(tasks).view()),
        norm::regex_ids_valid(old(store).graph(), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        interp_tasks_wf(final(store).graph(), final(tasks).view()), norm::regex_ids_valid(final(store).graph(), final(values).view()),
        result.is_ok() ==> interp_machine_relation(old(store).graph(), final(store).graph(), old(tasks).view(), final(tasks).view(), old(values).view(), final(values).view(), atoms@, words@),
        result.is_ok() ==> interp_work(final(store).graph(), final(tasks).view()) < interp_work(old(store).graph(), old(tasks).view()),
)]
fn interpret_next<G: KernelStore>(
    store: &mut G,
    atoms: &AtomSet,
    words: &[u64],
    tasks: &mut WorkVec<(TransitionId, bool)>,
    values: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    let (id, finish) = match tasks.pop() {
        Some(v) => v,
        None => return Err(invariant()),
    };
    proof! { assert(old(tasks).view() =~= tasks.view().push((id, finish))); }
    interpret_step(store, id, finish, atoms, words, tasks, values)
}
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition@ < old(store).graph().transitions.len(),
        model::atom_ids_wf(old(store).graph(), atoms@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        result matches Ok(id) ==> id@ < final(store).graph().regexes.len()
            && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                model::symbols_wf(sym) && truth_words_realize(old(store).graph(), atoms@, truth_words@, sym, theta, event) ==>
                    model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == norm::transition_lang(final(store).graph(), sym, theta, transition, event, word),
)]
pub(crate) fn interpret_transition<G: KernelStore>(
    store: &mut G,
    transition: TransitionId,
    atoms: &AtomSet,
    truth_words: &[u64],
) -> KernelResult<RegexId> {
    proof_decl! { let ghost entry = store.graph(); }
    validate_assignment(atoms, truth_words)?;
    let mut tasks = WorkVec::new();
    let mut values = WorkVec::new();
    tasks.push((transition, false));
    let mut state = Ok(());
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            interp_results_equiv(model::gsem(sym, theta),
                interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event),
                Some(seq![interpreted(entry, transition, sym, theta, event)])) by {
            interp_run_unfold(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event);
            interp_run_unfold(store.graph(), Seq::empty(), seq![interpreted(entry, transition, sym, theta, event)], sym, theta, event);
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant model::graph_extends(entry, store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            model::graph_wf(entry), model::atom_ids_wf(entry, atoms@), transition@ < entry.transitions.len(),
            model::atom_ids_wf(store.graph(), atoms@), interp_tasks_wf(store.graph(), tasks.view()), norm::regex_ids_valid(store.graph(), values.view()),
            state.is_ok() ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                model::symbols_wf(sym) && truth_words_realize(entry, atoms@, truth_words@, sym, theta, event) ==>
                    interp_results_equiv(model::gsem(sym, theta),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event),
                        Some(seq![interpreted(entry, transition, sym, theta, event)])),
        decreases if state is Ok { interp_work(store.graph(), tasks.view()) + 1 } else { 0 },
    ))]
    while !tasks.is_empty() && state.is_ok() {
        proof_decl! { let ghost before = store.graph(); let ghost pending = tasks.view(); let ghost prior = values.view(); }
        state = interpret_next(store, atoms, truth_words, &mut tasks, &mut values);
        proof! {
            norm::transition_lemma_extends_transitive(entry, before, store.graph());
            truth_words_realize_extends(entry, store.graph(), atoms@, truth_words@);
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                state.is_ok() && model::symbols_wf(sym) && truth_words_realize(entry, atoms@, truth_words@, sym, theta, event) implies
                    interp_results_equiv(model::gsem(sym, theta),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event),
                        Some(seq![interpreted(entry, transition, sym, theta, event)])) by {
                truth_words_realize_extends(entry, before, atoms@, truth_words@);
                interp_results_equiv_trans(model::gsem(sym, theta),
                    interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), sym, theta, event),
                    interp_run(before, pending, lifted_values(before, prior), sym, theta, event),
                    Some(seq![interpreted(entry, transition, sym, theta, event)]));
            }
        }
    }
    state?;
    proof! {
        interp_root_stable(entry, store.graph(), transition);
    }
    match values.pop() {
        Some(v) => Ok(v),
        None => Err(invariant()),
    }
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    verus! {
            pub open spec fn truth_word_bit(words: Seq<u64>, index: nat) -> bool {
                index / 64 < words.len()
                    && ((words[(index / 64) as int] >> ((index % 64) as u32)) & 1u64) != 0
            }

            pub open spec fn truth_words_realize(
                g: model::Graph, atoms: Seq<TestId>, words: Seq<u64>, sym: model::Symbols, theta: Seq<Data>, event: Data,
            ) -> bool {
                forall|i: int| 0 <= i < atoms.len() ==> #[trigger] truth_word_bit(words, i as nat)
                    == model::test_holds(sym, theta, model::lift_test(g, atoms[i]@), event)
            }

            pub proof fn truth_words_realize_extends(
                before: model::Graph, after: model::Graph, atoms: Seq<TestId>, words: Seq<u64>,
            )
                requires model::graph_extends(before, after), model::atom_ids_wf(before, atoms),
                ensures model::atom_ids_wf(after, atoms),
                    forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                        truth_words_realize(before, atoms, words, sym, theta, event)
                            == truth_words_realize(after, atoms, words, sym, theta, event),
            {
                assert forall|i: int| 0 <= i < atoms.len() implies atoms[i]@ < after.tests.len()
                    && #[trigger] after.tests[atoms[i]@ as int] matches model::TestNode::Atom(_, true) by {
                    assert(after.tests[atoms[i]@ as int] == before.tests[atoms[i]@ as int]);
                }
                assert forall|i: int| 0 <= i < atoms.len() implies
                    model::lift_test(before, atoms[i]@) == model::lift_test(after, atoms[i]@) by {
                    model::lemma_lift_test_stable(before, after, atoms[i]@);
                }
            }

    pub proof fn symbolic_not_result(g: model::Graph, root: TransitionId, out: TransitionId)
        requires norm::transition_result(g, norm::ActionShape::Not(root@), out),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> norm::transition_lang(g, sym, theta, out, event, word) == !norm::transition_lang(g, sym, theta, root, event, word),
    {
        let task = norm::ActionShape::Not(root@);
        let expected = norm::transition_initial_value(g, task).unwrap();
        norm::transition_lemma_result_refines(g, task, out);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies norm::transition_lang(g, sym, theta, out, event, word) == !norm::transition_lang(g, sym, theta, root, event, word) by {
            let ctx = norm::TransitionContext { symbols: sym, bindings: theta };
            norm::transition_lemma_context_sem(ctx);
            language::lemma_interp_not(model::gsem(sym, theta), event, model::lift_transition(g, root@));
            assert((expected.guard)(ctx, event));
            assert(norm::guarded_language(norm::transition_context_sem(), ctx, event, expected, word)
                == norm::guarded_language(norm::transition_context_sem(), ctx, event, norm::transition_known(g, out), word));
            norm::transition_lemma_known_language(g, out, ctx, event, word);
        }
    }

    pub proof fn symbolic_intersect_result(g: model::Graph, ids: Seq<TransitionId>, out: TransitionId)
        requires norm::transition_result(g, norm::ActionShape::Fold(model::transition_ids(ids), 0), out),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> norm::transition_lang(g, sym, theta, out, event, word) == norm::transition_combo(g, sym, theta, ids, event, word, true),
    {
        let task = norm::ActionShape::Fold(model::transition_ids(ids), 0);
        let expected = norm::transition_initial_value(g, task).unwrap();
        let terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
        norm::transition_lemma_result_refines(g, task, out);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies norm::transition_lang(g, sym, theta, out, event, word) == norm::transition_combo(g, sym, theta, ids, event, word, true) by {
            let ctx = norm::TransitionContext { symbols: sym, bindings: theta };
            norm::transition_lemma_context_sem(ctx);
            language::lemma_interp_intersect(model::gsem(sym, theta), event, terms, word);
            assert forall|i: int| 0 <= i < ids.len() implies language::lang(model::gsem(sym, theta),
                language::interp_transition(model::gsem(sym, theta), event, terms[i]), word)
                    == norm::transition_lang(g, sym, theta, ids[i], event, word) by {
                assert(terms[i] == model::lift_transition(g, ids[i]@));
            }
            assert((expected.guard)(ctx, event));
            assert(norm::guarded_language(norm::transition_context_sem(), ctx, event, expected, word)
                == norm::guarded_language(norm::transition_context_sem(), ctx, event, norm::transition_known(g, out), word));
            norm::transition_lemma_known_language(g, out, ctx, event, word);
        }
    }


    pub open spec fn derivative_correct(g: model::Graph, root: nat, out: TransitionId) -> bool {
        root < g.regexes.len() && out@ < g.transitions.len()
        && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            model::symbols_wf(sym) ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                == model::regex_lang(g, sym, theta, root, seq![event] + word)
    }

    /// The runtime derivative agrees, modulo language, with the independent δ.
    pub proof fn lemma_derivative_correct_is_symbolic_derivative(g: model::Graph, root: nat, out: TransitionId, sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>)
        requires derivative_correct(g, root, out), model::symbols_wf(sym),
        ensures norm::transition_lang(g, sym, theta, out, event, word)
            == language::lang(model::gsem(sym, theta), language::interp_transition(model::gsem(sym, theta), event, algebra::symbolic_derivative(model::lift_regex(g, root))), word),
    {
        algebra::theorem_symbolic_derivative_correct(model::gsem(sym, theta), event, model::lift_regex(g, root), word);
    }

    pub open spec fn derivative_cache_wf(g: model::Graph, cache: Seq<Option<TransitionId>>) -> bool {
        forall|i: int| 0 <= i < cache.len() ==> match #[trigger] cache[i] {
            Some(out) => derivative_correct(g, i as nat, out), None => true,
        }
    }

    pub open spec fn derivative_tasks_wf(g: model::Graph, tasks: Seq<(RegexId, bool)>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].0@ < g.regexes.len()
    }

    pub open spec fn derivative_node_work(g: model::Graph, id: nat) -> nat
        decreases id, 1nat,
    {
        if id >= g.regexes.len() { 0 } else {
            match g.regexes[id as int].kind {
                model::RegexKindNode::Union(cs) | model::RegexKindNode::Intersect(cs) | model::RegexKindNode::Concat(cs) =>
                    2 + derivative_children_work(g, cs, id),
                model::RegexKindNode::Star(c) | model::RegexKindNode::Not(c) =>
                    2 + if c < id { derivative_node_work(g, c) } else { 0 },
                _ => 1,
            }
        }
    }

    pub open spec fn derivative_children_work(g: model::Graph, children: Seq<nat>, bound: nat) -> nat
        decreases bound, 0nat, children.len(),
    {
        if children.len() == 0 { 0 } else {
            derivative_children_work(g, children.skip(1), bound)
                + if children[0] < bound { derivative_node_work(g, children[0]) } else { 0 }
        }
    }

    pub open spec fn derivative_work(g: model::Graph, tasks: Seq<(RegexId, bool)>) -> nat
        decreases tasks.len(),
    {
        if tasks.len() == 0 { 0 } else {
            derivative_work(g, tasks.drop_last())
                + if tasks.last().1 { 1 } else { derivative_node_work(g, tasks.last().0@) }
        }
    }

    pub proof fn derivative_lemma_node_work_extends(a: model::Graph, b: model::Graph, id: nat)
        requires model::graph_extends(a, b), id < a.regexes.len(),
        ensures derivative_node_work(a, id) == derivative_node_work(b, id),
        decreases id, 1nat,
    {
        assert(a.regexes[id as int] == b.regexes[id as int]);
        match a.regexes[id as int].kind {
            model::RegexKindNode::Union(cs) => { derivative_lemma_children_work_extends(a, b, cs, id); },
            model::RegexKindNode::Intersect(cs) => { derivative_lemma_children_work_extends(a, b, cs, id); },
            model::RegexKindNode::Concat(cs) => { derivative_lemma_children_work_extends(a, b, cs, id); },
            model::RegexKindNode::Star(c) => { if c < id { derivative_lemma_node_work_extends(a, b, c); } },
            model::RegexKindNode::Not(c) => { if c < id { derivative_lemma_node_work_extends(a, b, c); } },
            _ => {},
        }
    }

    pub proof fn derivative_lemma_children_work_extends(a: model::Graph, b: model::Graph, children: Seq<nat>, bound: nat)
        requires model::graph_extends(a, b), bound <= a.regexes.len(),
        ensures derivative_children_work(a, children, bound) == derivative_children_work(b, children, bound),
        decreases bound, 0nat, children.len(),
    {
        if children.len() > 0 {
            if children[0] < bound { derivative_lemma_node_work_extends(a, b, children[0]); }
            derivative_lemma_children_work_extends(a, b, children.skip(1), bound);
        }
    }

    pub proof fn derivative_lemma_work_extends(a: model::Graph, b: model::Graph, tasks: Seq<(RegexId, bool)>)
        requires model::graph_extends(a, b), derivative_tasks_wf(a, tasks),
        ensures derivative_work(a, tasks) == derivative_work(b, tasks),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            assert(tasks.last() == tasks[tasks.len() - 1]);
            if !tasks.last().1 { derivative_lemma_node_work_extends(a, b, tasks.last().0@); }
            assert forall|i: int| 0 <= i < tasks.drop_last().len() implies #[trigger] tasks.drop_last()[i].0@ < a.regexes.len() by {
                assert(tasks.drop_last()[i] == tasks[i]);
            }
            derivative_lemma_work_extends(a, b, tasks.drop_last());
        }
    }

    pub proof fn derivative_lemma_work_push(g: model::Graph, tasks: Seq<(RegexId, bool)>, task: (RegexId, bool))
        ensures derivative_work(g, tasks.push(task))
            == derivative_work(g, tasks) + if task.1 { 1 } else { derivative_node_work(g, task.0@) },
    {
        assert(tasks.push(task).drop_last() =~= tasks);
    }

    /// Concat schedules only its nullable prefix, so the scheduled tasks are a prefix of the children.
    pub proof fn derivative_lemma_work_schedule_prefix(g: model::Graph, tasks: Seq<(RegexId, bool)>,
        scheduled: Seq<(RegexId, bool)>, children: Seq<nat>, bound: nat)
        requires scheduled.len() <= children.len(), model::bounded(children, bound),
            forall|i: int| 0 <= i < scheduled.len() ==> #[trigger] scheduled[i].0@ == children[i] && !scheduled[i].1,
        ensures derivative_work(g, tasks + scheduled) <= derivative_work(g, tasks) + derivative_children_work(g, children, bound),
        decreases scheduled.len(),
    {
        if scheduled.len() == 0 {
            assert(tasks + scheduled =~= tasks);
        } else {
            let rest = scheduled.skip(1);
            assert(tasks + scheduled =~= tasks.push(scheduled[0]) + rest);
            assert(children[0] < bound);
            assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i].0@ == children.skip(1)[i] && !rest[i].1 by {
                assert(rest[i] == scheduled[i + 1]);
            }
            assert forall|i: int| 0 <= i < children.skip(1).len() implies #[trigger] children.skip(1)[i] < bound by {
                assert(children.skip(1)[i] == children[i + 1]);
            }
            derivative_lemma_work_schedule_prefix(g, tasks.push(scheduled[0]), rest, children.skip(1), bound);
            derivative_lemma_work_push(g, tasks, scheduled[0]);
        }
    }

    pub proof fn derivative_lemma_work_unary(g: model::Graph, id: RegexId, pending: Seq<(RegexId, bool)>, inner: RegexId)
        requires model::graph_wf(g), id@ < g.regexes.len(), derivative_tasks_wf(g, pending),
            g.regexes[id@ as int].kind == model::RegexKindNode::Star(inner@)
                || g.regexes[id@ as int].kind == model::RegexKindNode::Not(inner@),
        ensures derivative_tasks_wf(g, pending.push((id, true)).push((inner, false))),
            derivative_work(g, pending.push((id, true)).push((inner, false))) < derivative_work(g, pending.push((id, false))),
    {
        model::lemma_graph_regex_wf(g, id@);
        derivative_lemma_work_push(g, pending, (id, true));
        derivative_lemma_work_push(g, pending.push((id, true)), (inner, false));
        derivative_lemma_work_push(g, pending, (id, false));
        let all = pending.push((id, true)).push((inner, false));
        assert forall|i: int| 0 <= i < all.len() implies #[trigger] all[i].0@ < g.regexes.len() by {
            if i < pending.len() { assert(all[i] == pending[i]); }
        }
    }

    pub proof fn derivative_lemma_work_branch(g: model::Graph, id: RegexId, pending: Seq<(RegexId, bool)>, tasks: Seq<(RegexId, bool)>)
        requires model::graph_wf(g), id@ < g.regexes.len(), derivative_tasks_wf(g, pending),
            g.regexes[id@ as int].kind is Union || g.regexes[id@ as int].kind is Intersect
                || g.regexes[id@ as int].kind is Concat,
            pending.push((id, true)).is_prefix_of(tasks),
            tasks.len() <= pending.len() + 1 + derivative_children_ids(g, id).len(),
            forall|j: int| pending.len() + 1 <= j < tasks.len() ==> #[trigger] tasks[j].0@
                == derivative_children_ids(g, id)[j - pending.len() - 1] && !tasks[j].1,
        ensures derivative_tasks_wf(g, tasks),
            derivative_work(g, tasks) < derivative_work(g, pending.push((id, false))),
    {
        model::lemma_graph_regex_wf(g, id@);
        let cs = derivative_children_ids(g, id);
        let base = pending.push((id, true));
        let scheduled = tasks.subrange(base.len() as int, tasks.len() as int);
        assert(tasks =~= base + scheduled);
        assert forall|i: int| 0 <= i < scheduled.len() implies #[trigger] scheduled[i].0@ == cs[i] && !scheduled[i].1 by {
            assert(scheduled[i] == tasks[base.len() + i]);
        }
        derivative_lemma_work_schedule_prefix(g, base, scheduled, cs, id@);
        derivative_lemma_work_push(g, pending, (id, true));
        derivative_lemma_work_push(g, pending, (id, false));
        assert forall|i: int| 0 <= i < tasks.len() implies #[trigger] tasks[i].0@ < g.regexes.len() by {
            if i < pending.len() { assert(tasks[i] == base[i]); assert(base[i] == pending[i]); }
            else if i > pending.len() { assert(tasks[i].0@ == cs[i - pending.len() - 1]); }
            else { assert(tasks[i] == base[i]); }
        }
    }

    pub proof fn derivative_lemma_step_post(before: model::Graph, after: model::Graph, id: RegexId, finish: bool,
        pending: Seq<(RegexId, bool)>, tasks: Seq<(RegexId, bool)>)
        requires model::graph_extends(before, after), id@ < before.regexes.len(), derivative_tasks_wf(before, pending),
            tasks == pending || (derivative_tasks_wf(before, tasks)
                && derivative_work(before, tasks) < derivative_work(before, pending.push((id, finish)))),
        ensures derivative_work(after, tasks) < derivative_work(before, pending.push((id, finish))),
    {
        derivative_lemma_work_push(before, pending, (id, finish));
        derivative_lemma_work_extends(before, after, tasks);
    }

    pub open spec fn derivative_children_ids(g: model::Graph, root: RegexId) -> Seq<nat> {
        match g.regexes[root@ as int].kind {
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Intersect(cs) | model::RegexKindNode::Concat(cs) => cs,
            _ => Seq::empty(),
        }
    }

    pub open spec fn derivative_factors_wf(g: model::Graph, root: RegexId, count: nat, concat: bool) -> bool {
        root@ < g.regexes.len() && match g.regexes[root@ as int].kind {
            model::RegexKindNode::Concat(cs) => concat && cs.len() == count,
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Intersect(cs) => !concat && cs.len() == count,
            _ => false,
        }
    }

    pub open spec fn derivative_prefix(g: model::Graph, root: RegexId, index: nat) -> bool {
        forall|i: int| 0 <= i < index ==> language::nullable(model::lift_regex(g, derivative_children_ids(g, root)[i]))
    }

    pub open spec fn derivative_factor_language(
        g: model::Graph, root: RegexId, concat: bool, index: int,
        sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>,
    ) -> bool {
        let cs = derivative_children_ids(g, root);
        let sem = model::gsem(sym, theta);
        if concat {
            language::lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, model::lift_regex(g, cs[index]))]
                + model::lift_regexes(g, cs.subrange(index + 1, cs.len() as int))), word)
        } else { model::regex_lang(g, sym, theta, cs[index], seq![event] + word) }
    }

    pub open spec fn derivative_factor_combo(
        g: model::Graph, root: RegexId, concat: bool, count: nat, intersect: bool,
        sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>,
    ) -> bool {
        if intersect {
            forall|i: int| 0 <= i < count && (!concat || derivative_prefix(g, root, i as nat))
                ==> derivative_factor_language(g, root, concat, i, sym, theta, event, word)
        } else {
            exists|i: int| 0 <= i < count && (!concat || derivative_prefix(g, root, i as nat))
                && derivative_factor_language(g, root, concat, i, sym, theta, event, word)
        }
    }

    pub open spec fn derivative_results(
        g: model::Graph, root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>,
    ) -> bool {
        super::super::normalize::verify::transition_ids_valid(g, results)
        && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>, intersect: bool|
            model::symbols_wf(sym) ==> super::super::normalize::verify::transition_combo(g, sym, theta, results, event, word, intersect)
                == derivative_factor_combo(g, root, concat, count, intersect, sym, theta, event, word)
    }

    pub proof fn derivative_factor_stable(a: model::Graph, b: model::Graph, root: RegexId)
        requires model::graph_wf(a), model::graph_extends(a, b), root@ < a.regexes.len(),
        ensures derivative_children_ids(a, root) == derivative_children_ids(b, root),
            forall|n: nat| n <= derivative_children_ids(a, root).len() ==> derivative_prefix(a, root, n) == derivative_prefix(b, root, n),
            forall|concat: bool, i: int, sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                0 <= i < derivative_children_ids(a, root).len()
                    ==> derivative_factor_language(a, root, concat, i, sym, theta, event, word)
                        == derivative_factor_language(b, root, concat, i, sym, theta, event, word),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        model::lemma_graph_wf_elim(a);
        model::lemma_graph_regex_wf(a, root@);
        model::lemma_lift_stable_under_extends(a, b);
        let cs = derivative_children_ids(a, root);
        assert forall|i: int| 0 <= i < cs.len() implies cs[i] < a.regexes.len() by {}
        assert forall|i: int| 0 <= i < cs.len() implies
            #[trigger] model::lift_regexes(a, cs.subrange(i + 1, cs.len() as int)) == model::lift_regexes(b, cs.subrange(i + 1, cs.len() as int)) by {
            assert(model::lift_regexes(a, cs.subrange(i + 1, cs.len() as int)) =~= model::lift_regexes(b, cs.subrange(i + 1, cs.len() as int)));
        }
    }

    pub proof fn derivative_results_stable(a: model::Graph, b: model::Graph, root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>)
        requires model::graph_wf(a), model::graph_extends(a, b), root@ < a.regexes.len(),
            count <= derivative_children_ids(a, root).len(), derivative_results(a, root, concat, count, results),
        ensures derivative_results(b, root, concat, count, results),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        hide(derivative_factor_language); hide(derivative_prefix);
        derivative_factor_stable(a, b, root);
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>, intersect: bool|
            model::symbols_wf(sym) implies super::super::normalize::verify::transition_combo(b, sym, theta, results, event, word, intersect)
                == derivative_factor_combo(b, root, concat, count, intersect, sym, theta, event, word) by {
            assert forall|i: int| 0 <= i < results.len() implies
                super::super::normalize::verify::transition_lang(a, sym, theta, results[i], event, word)
                    == super::super::normalize::verify::transition_lang(b, sym, theta, results[i], event, word) by {}
            assert(super::super::normalize::verify::transition_combo(a, sym, theta, results, event, word, intersect)
                == super::super::normalize::verify::transition_combo(b, sym, theta, results, event, word, intersect));
            assert(derivative_factor_combo(a, root, concat, count, intersect, sym, theta, event, word)
                == derivative_factor_combo(b, root, concat, count, intersect, sym, theta, event, word));
        }
    }

    pub proof fn derivative_correct_stable(a: model::Graph, b: model::Graph, root: nat, out: TransitionId)
        requires model::graph_wf(a), model::graph_extends(a, b), derivative_correct(a, root, out),
        ensures derivative_correct(b, root, out),
    {
        hide(language::lang); hide(language::interp_transition); hide(model::lift_regex); hide(model::lift_transition);
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_regex_stable(a, b, root);
        model::lemma_lift_transition_stable(a, b, out@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies super::super::normalize::verify::transition_lang(b, sym, theta, out, event, word)
                == model::regex_lang(b, sym, theta, root, seq![event] + word) by {
            assert(super::super::normalize::verify::transition_lang(a, sym, theta, out, event, word)
                == model::regex_lang(a, sym, theta, root, seq![event] + word));
        }
    }

    pub proof fn derivative_extends(a: model::Graph, b: model::Graph)
        requires model::graph_wf(a), model::graph_extends(a, b),
        ensures
            forall|c: model::Graph| model::graph_extends(b, c) ==> model::graph_extends(a, c),
            forall|root: nat, out: TransitionId| derivative_correct(a, root, out) ==> derivative_correct(b, root, out),
            forall|cache: Seq<Option<TransitionId>>| derivative_cache_wf(a, cache) ==> derivative_cache_wf(b, cache),
            forall|tasks: Seq<(RegexId, bool)>| derivative_tasks_wf(a, tasks) ==> derivative_tasks_wf(b, tasks),
            forall|root: RegexId, count: nat, concat: bool| derivative_factors_wf(a, root, count, concat) ==> derivative_factors_wf(b, root, count, concat),
            forall|root: RegexId, index: nat| root@ < a.regexes.len() && index <= derivative_children_ids(a, root).len()
                ==> derivative_prefix(a, root, index) == derivative_prefix(b, root, index),
            forall|root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>|
                root@ < a.regexes.len() && count <= derivative_children_ids(a, root).len() && derivative_results(a, root, concat, count, results)
                    ==> derivative_results(b, root, concat, count, results),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        hide(model::test_holds); hide(model::lift_regex); hide(model::lift_transition);
        hide(derivative_correct); hide(derivative_results); hide(derivative_prefix); hide(derivative_factor_language);
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
        assert forall|c: model::Graph| model::graph_extends(b, c) implies model::graph_extends(a, c) by {
            assert(a.tests.is_prefix_of(c.tests));
            assert(a.regexes.is_prefix_of(c.regexes));
            assert(a.transitions.is_prefix_of(c.transitions));
        }
        assert forall|root: nat, out: TransitionId| derivative_correct(a, root, out) implies derivative_correct(b, root, out) by {
            derivative_correct_stable(a, b, root, out);
        }
        assert forall|cache: Seq<Option<TransitionId>>| derivative_cache_wf(a, cache) implies derivative_cache_wf(b, cache) by {
            assert forall|i: int| 0 <= i < cache.len() implies match #[trigger] cache[i] {
                Some(out) => derivative_correct(b, i as nat, out), None => true,
            } by {}
        }
        assert forall|root: RegexId, index: nat| root@ < a.regexes.len() && index <= derivative_children_ids(a, root).len()
            implies derivative_prefix(a, root, index) == derivative_prefix(b, root, index) by {
            derivative_factor_stable(a, b, root);
        }
        assert forall|root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>|
            root@ < a.regexes.len() && count <= derivative_children_ids(a, root).len() && derivative_results(a, root, concat, count, results)
                implies derivative_results(b, root, concat, count, results) by {
            derivative_results_stable(a, b, root, concat, count, results);
        }
    }

    pub proof fn derivative_frame(g: model::Graph)
        requires model::graph_wf(g),
        ensures forall|next: model::Graph| model::graph_extends(g, next) ==> (
            (forall|cache: Seq<Option<TransitionId>>| derivative_cache_wf(g, cache) ==> derivative_cache_wf(next, cache))
            && (forall|tasks: Seq<(RegexId, bool)>| derivative_tasks_wf(g, tasks) ==> derivative_tasks_wf(next, tasks))
            && (forall|root: nat, out: TransitionId| derivative_correct(g, root, out) ==> derivative_correct(next, root, out))
            && (forall|root: RegexId, count: nat, concat: bool| derivative_factors_wf(g, root, count, concat) ==> derivative_factors_wf(next, root, count, concat))
            && (forall|root: RegexId, index: nat| root@ < g.regexes.len() && index <= derivative_children_ids(g, root).len()
                ==> derivative_prefix(g, root, index) == derivative_prefix(next, root, index))
            && (forall|root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>|
                root@ < g.regexes.len() && count <= derivative_children_ids(g, root).len() && derivative_results(g, root, concat, count, results)
                    ==> derivative_results(next, root, concat, count, results))
            && (forall|after: model::Graph| model::graph_extends(next, after) ==> model::graph_extends(g, after))),
    {
        hide(derivative_correct); hide(derivative_results); hide(derivative_prefix); hide(derivative_factor_language);
        hide(derivative_cache_wf); hide(derivative_factors_wf); hide(derivative_tasks_wf);
        assert forall|next: model::Graph| model::graph_extends(g, next) implies (
            (forall|cache: Seq<Option<TransitionId>>| derivative_cache_wf(g, cache) ==> derivative_cache_wf(next, cache))
            && (forall|tasks: Seq<(RegexId, bool)>| derivative_tasks_wf(g, tasks) ==> derivative_tasks_wf(next, tasks))
            && (forall|root: nat, out: TransitionId| derivative_correct(g, root, out) ==> derivative_correct(next, root, out))
            && (forall|root: RegexId, count: nat, concat: bool| derivative_factors_wf(g, root, count, concat) ==> derivative_factors_wf(next, root, count, concat))
            && (forall|root: RegexId, index: nat| root@ < g.regexes.len() && index <= derivative_children_ids(g, root).len()
                ==> derivative_prefix(g, root, index) == derivative_prefix(next, root, index))
            && (forall|root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>|
                root@ < g.regexes.len() && count <= derivative_children_ids(g, root).len() && derivative_results(g, root, concat, count, results)
                    ==> derivative_results(next, root, concat, count, results))
            && (forall|after: model::Graph| model::graph_extends(next, after) ==> model::graph_extends(g, after))) by {
            derivative_extends(g, next);
        }
    }

    pub proof fn derivative_results_push(
        g: model::Graph, root: RegexId, concat: bool, index: nat, prior: Seq<TransitionId>, out: TransitionId,
    )
        requires derivative_results(g, root, concat, index, prior), out@ < g.transitions.len(),
            !concat || derivative_prefix(g, root, index),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == derivative_factor_language(g, root, concat, index as int, sym, theta, event, word),
        ensures derivative_results(g, root, concat, index + 1, prior.push(out)),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        hide(super::super::normalize::verify::transition_lang); hide(derivative_factor_language);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>, intersect: bool|
            model::symbols_wf(sym) implies super::super::normalize::verify::transition_combo(g, sym, theta, prior.push(out), event, word, intersect)
                == derivative_factor_combo(g, root, concat, index + 1, intersect, sym, theta, event, word) by {
            if intersect {
                assert forall|i: int| 0 <= i < prior.push(out).len() implies
                    super::super::normalize::verify::transition_lang(g, sym, theta, prior.push(out)[i], event, word)
                        == if i < prior.len() { super::super::normalize::verify::transition_lang(g, sym, theta, prior[i], event, word) }
                            else { super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word) } by {}
                assert(prior.push(out)[prior.len() as int] == out);
                if super::super::normalize::verify::transition_combo(g, sym, theta, prior.push(out), event, word, true) {
                    assert forall|i: int| 0 <= i < prior.len() implies
                        super::super::normalize::verify::transition_lang(g, sym, theta, prior[i], event, word) by {
                        assert(prior.push(out)[i] == prior[i]);
                    }
                }
                if super::super::normalize::verify::transition_combo(g, sym, theta, prior, event, word, true)
                    && super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word) {
                    assert forall|i: int| 0 <= i < prior.push(out).len() implies
                        super::super::normalize::verify::transition_lang(g, sym, theta, prior.push(out)[i], event, word) by {
                        if i < prior.len() { assert(prior.push(out)[i] == prior[i]); } else { assert(prior.push(out)[i] == out); }
                    }
                }
                assert(super::super::normalize::verify::transition_combo(g, sym, theta, prior.push(out), event, word, true)
                    == (super::super::normalize::verify::transition_combo(g, sym, theta, prior, event, word, true)
                        && super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)));
            } else {
                if super::super::normalize::verify::transition_combo(g, sym, theta, prior.push(out), event, word, false) {
                    let i = choose|i: int| 0 <= i < prior.push(out).len()
                        && super::super::normalize::verify::transition_lang(g, sym, theta, prior.push(out)[i], event, word);
                    if i < prior.len() { assert(super::super::normalize::verify::transition_combo(g, sym, theta, prior, event, word, false)); }
                }
                if super::super::normalize::verify::transition_combo(g, sym, theta, prior, event, word, false) {
                    let i = choose|i: int| 0 <= i < prior.len()
                        && super::super::normalize::verify::transition_lang(g, sym, theta, prior[i], event, word);
                    assert(prior.push(out)[i] == prior[i]);
                }
                assert(prior.push(out)[prior.len() as int] == out);
                assert(super::super::normalize::verify::transition_combo(g, sym, theta, prior.push(out), event, word, false)
                    == (super::super::normalize::verify::transition_combo(g, sym, theta, prior, event, word, false)
                        || super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)));
            }
        }
    }

    pub proof fn derivative_results_skip(g: model::Graph, root: RegexId, index: nat, results: Seq<TransitionId>)
        requires derivative_results(g, root, true, index, results), !derivative_prefix(g, root, index),
        ensures derivative_results(g, root, true, index + 1, results),
    {}

    pub proof fn derivative_append_factor(
        g: model::Graph, root: RegexId, index: int, d: TransitionId, suffix: Seq<RegexId>, out: TransitionId,
    )
        requires 0 <= index < derivative_children_ids(g, root).len(),
            derivative_correct(g, derivative_children_ids(g, root)[index], d),
            model::regex_ids(suffix) == derivative_children_ids(g, root).subrange(index + 1, derivative_children_ids(g, root).len() as int),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == super::super::normalize::verify::transition_append_combo(g, sym, theta, d, suffix, event, word),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                == derivative_factor_language(g, root, true, index, sym, theta, event, word),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                == derivative_factor_language(g, root, true, index, sym, theta, event, word) by {
            let sem = model::gsem(sym, theta);
            let child = model::lift_regex(g, derivative_children_ids(g, root)[index]);
            let actual = language::interp_transition(sem, event, model::lift_transition(g, d@));
            let expected = language::derivative(sem, event, child);
            let tail = model::lift_regexes(g, model::regex_ids(suffix));
            language::lemma_concat_prepend(sem, actual, tail, word);
            language::lemma_concat_prepend(sem, expected, tail, word);
            assert forall|w: Seq<Data>| language::lang(sem, actual, w) == language::lang(sem, expected, w) by {
                language::lemma_derivative_correct(sem, event, child, w);
                assert(super::super::normalize::verify::transition_lang(g, sym, theta, d, event, w)
                    == model::regex_lang(g, sym, theta, derivative_children_ids(g, root)[index], seq![event] + w));
            }
        }
    }

    pub open spec fn derivative_sum<L>(sem: spec_fn(L, Data) -> bool, event: Data, cs: Seq<language::Regex<L>>, word: Seq<Data>) -> bool {
        exists|i: int| 0 <= i < cs.len()
            && (forall|j: int| 0 <= j < i ==> language::nullable(cs[j]))
            && language::lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, cs[i])]
                + cs.subrange(i + 1, cs.len() as int)), word)
    }

    pub proof fn derivative_concat_sum<L>(sem: spec_fn(L, Data) -> bool, event: Data, bound: language::Regex<L>, cs: Seq<language::Regex<L>>, word: Seq<Data>)
        requires forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        ensures language::lang(sem, language::derivative_concat(sem, event, bound, cs), word) == derivative_sum(sem, event, cs, word),
        decreases cs.len(),
    {
        if cs.len() > 0 {
            let rest = cs.drop_first();
            assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], bound) by { assert(rest[i] == cs[i + 1]); }
            derivative_concat_sum(sem, event, bound, rest, word);
            let head = language::Regex::Concat(seq![language::derivative(sem, event, cs[0])] + rest);
            language::lemma_union_optional(sem, head, language::derivative_concat(sem, event, bound, rest), language::nullable(cs[0]), word);
            assert(cs.subrange(1, cs.len() as int) =~= rest);
            if derivative_sum(sem, event, cs, word) {
                let i = choose|i: int| 0 <= i < cs.len()
                    && (forall|j: int| 0 <= j < i ==> language::nullable(cs[j]))
                    && language::lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, cs[i])]
                        + cs.subrange(i + 1, cs.len() as int)), word);
                if i > 0 {
                    assert(rest[i - 1] == cs[i]);
                    assert(rest.subrange(i, rest.len() as int) =~= cs.subrange(i + 1, cs.len() as int));
                    assert forall|j: int| 0 <= j < i - 1 implies language::nullable(rest[j]) by { assert(rest[j] == cs[j + 1]); }
                    assert(derivative_sum(sem, event, rest, word));
                }
            }
            if language::lang(sem, head, word) { assert(derivative_sum(sem, event, cs, word)); }
            if language::nullable(cs[0]) && derivative_sum(sem, event, rest, word) {
                let i = choose|i: int| 0 <= i < rest.len()
                    && (forall|j: int| 0 <= j < i ==> language::nullable(rest[j]))
                    && language::lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, rest[i])]
                        + rest.subrange(i + 1, rest.len() as int)), word);
                assert(cs[i + 1] == rest[i]);
                assert(cs.subrange(i + 2, cs.len() as int) =~= rest.subrange(i + 1, rest.len() as int));
                assert forall|j: int| 0 <= j < i + 1 implies language::nullable(cs[j]) by { if j > 0 { assert(cs[j] == rest[j - 1]); } }
                assert(derivative_sum(sem, event, cs, word));
            }
        }
    }

    pub proof fn derivative_sum_correct<L>(sem: spec_fn(L, Data) -> bool, event: Data, root: language::Regex<L>, word: Seq<Data>)
        requires root is Concat,
        ensures derivative_sum(sem, event, root->Concat_0, word) == language::lang(sem, root, seq![event] + word),
    {
        hide(language::lang);
        match root {
            language::Regex::Concat(cs) => {
                assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], root) by {}
                derivative_concat_sum(sem, event, root, cs, word);
                language::lemma_derivative_correct(sem, event, root, word);
            },
            _ => {},
        }
    }

    pub proof fn derivative_children_complete(g: model::Graph, root: RegexId, concat: bool, intersect: bool, out: TransitionId)
        requires model::graph_wf(g), root@ < g.regexes.len(),
            match g.regexes[root@ as int].kind {
                model::RegexKindNode::Union(_) => !concat && !intersect,
                model::RegexKindNode::Intersect(_) => !concat && intersect,
                model::RegexKindNode::Concat(_) => concat && !intersect,
                _ => false,
            }, out@ < g.transitions.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == derivative_factor_combo(g, root, concat, derivative_children_ids(g, root).len(), intersect, sym, theta, event, word),
        ensures derivative_correct(g, root@, out),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        hide(model::lift_regex); hide(model::lift_transition);
        hide(language::nullable);
        super::super::normalize::verify::regex_unfold(g, root@);
        let cs = derivative_children_ids(g, root);
        let rs = model::lift_regexes(g, cs);
        assert(rs.len() == cs.len());
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                == model::regex_lang(g, sym, theta, root@, seq![event] + word) by {
            let sem = model::gsem(sym, theta);
            assert(super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                == derivative_factor_combo(g, root, concat, cs.len(), intersect, sym, theta, event, word));
            assert forall|i: int| 0 <= i < cs.len() implies
                #[trigger] derivative_factor_language(g, root, false, i, sym, theta, event, word)
                    == language::lang(sem, rs[i], seq![event] + word) by {
                assert(rs[i] == model::lift_regex(g, cs[i]));
            }
            if concat {
                assert(!intersect);
                derivative_sum_correct(sem, event, language::Regex::Concat(rs), word);
                assert(model::lift_regex(g, root@) == language::Regex::Concat(rs));
                assert forall|i: int| 0 <= i < cs.len() implies
                    #[trigger] model::lift_regexes(g, cs.subrange(i + 1, cs.len() as int)) == rs.subrange(i + 1, rs.len() as int) by {
                    assert(model::lift_regexes(g, cs.subrange(i + 1, cs.len() as int)) =~= rs.subrange(i + 1, rs.len() as int));
                }
                assert forall|i: int| 0 <= i < cs.len() implies
                    #[trigger] derivative_prefix(g, root, i as nat) == (forall|j: int| 0 <= j < i ==> language::nullable(rs[j])) by {
                    assert forall|j: int| 0 <= j < i implies rs[j] == model::lift_regex(g, cs[j]) by {}
                    if derivative_prefix(g, root, i as nat) {
                        assert forall|j: int| 0 <= j < i implies language::nullable(rs[j]) by {
                            assert(rs[j] == model::lift_regex(g, cs[j]));
                        }
                    }
                    if forall|j: int| 0 <= j < i ==> language::nullable(rs[j]) {
                        assert forall|j: int| 0 <= j < i implies language::nullable(model::lift_regex(g, cs[j])) by {
                            assert(rs[j] == model::lift_regex(g, cs[j]));
                        }
                    }
                }
                assert forall|i: int| 0 <= i < cs.len() implies
                    #[trigger] derivative_factor_language(g, root, true, i, sym, theta, event, word)
                        == language::lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, rs[i])]
                            + rs.subrange(i + 1, rs.len() as int)), word) by {
                    assert(rs[i] == model::lift_regex(g, cs[i]));
                    assert(model::lift_regexes(g, cs.subrange(i + 1, cs.len() as int)) == rs.subrange(i + 1, rs.len() as int));
                }
                if derivative_factor_combo(g, root, concat, cs.len(), intersect, sym, theta, event, word) {
                    let i = choose|i: int| 0 <= i < cs.len() && derivative_prefix(g, root, i as nat)
                        && derivative_factor_language(g, root, true, i, sym, theta, event, word);
                    assert(0 <= i < rs.len());
                    assert(derivative_sum(sem, event, rs, word));
                }
                if derivative_sum(sem, event, rs, word) {
                    let i = choose|i: int| 0 <= i < rs.len()
                        && (forall|j: int| 0 <= j < i ==> language::nullable(rs[j]))
                        && language::lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, rs[i])]
                            + rs.subrange(i + 1, rs.len() as int)), word);
                    assert(0 <= i < cs.len());
                    assert(derivative_prefix(g, root, i as nat));
                    assert(derivative_factor_language(g, root, true, i, sym, theta, event, word));
                    assert(derivative_factor_combo(g, root, concat, cs.len(), intersect, sym, theta, event, word));
                }
                assert(derivative_factor_combo(g, root, concat, cs.len(), intersect, sym, theta, event, word)
                    == derivative_sum(sem, event, rs, word));
                assert(super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == model::regex_lang(g, sym, theta, root@, seq![event] + word));
            } else if intersect {
                language::lemma_lang_intersect(sem, rs, seq![event] + word);
                assert(model::lift_regex(g, root@) == language::Regex::Intersect(rs));
                assert(derivative_factor_combo(g, root, false, cs.len(), true, sym, theta, event, word)
                    == (forall|i: int| 0 <= i < cs.len() ==> derivative_factor_language(g, root, false, i, sym, theta, event, word)));
                if derivative_factor_combo(g, root, false, cs.len(), true, sym, theta, event, word) {
                    assert forall|i: int| 0 <= i < rs.len() implies language::lang(sem, rs[i], seq![event] + word) by {
                        assert(derivative_factor_language(g, root, false, i, sym, theta, event, word));
                    }
                }
                if forall|i: int| 0 <= i < rs.len() ==> language::lang(sem, rs[i], seq![event] + word) {
                    assert forall|i: int| 0 <= i < cs.len() implies derivative_factor_language(g, root, false, i, sym, theta, event, word) by {
                        assert(language::lang(sem, rs[i], seq![event] + word));
                    }
                }
                assert(derivative_factor_combo(g, root, false, cs.len(), true, sym, theta, event, word)
                    == (forall|i: int| 0 <= i < rs.len() ==> language::lang(sem, rs[i], seq![event] + word)));
                assert(super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == model::regex_lang(g, sym, theta, root@, seq![event] + word));
            } else {
                language::lemma_lang_union(sem, rs, seq![event] + word);
                assert(model::lift_regex(g, root@) == language::Regex::Union(rs));
                if derivative_factor_combo(g, root, false, cs.len(), false, sym, theta, event, word) {
                    let i = choose|i: int| 0 <= i < cs.len() && derivative_factor_language(g, root, false, i, sym, theta, event, word);
                    assert(language::lang(sem, rs[i], seq![event] + word));
                }
                if exists|i: int| 0 <= i < rs.len() && language::lang(sem, rs[i], seq![event] + word) {
                    let i = choose|i: int| 0 <= i < rs.len() && language::lang(sem, rs[i], seq![event] + word);
                    assert(derivative_factor_language(g, root, false, i, sym, theta, event, word));
                    assert(derivative_factor_combo(g, root, false, cs.len(), false, sym, theta, event, word));
                }
                assert(derivative_factor_combo(g, root, false, cs.len(), false, sym, theta, event, word)
                    == (exists|i: int| 0 <= i < rs.len() && language::lang(sem, rs[i], seq![event] + word)));
                assert(super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == model::regex_lang(g, sym, theta, root@, seq![event] + word));
            }
        }
    }

    pub proof fn derivative_constants(g: model::Graph)
        requires model::graph_wf(g),
        ensures g.constants.transition_empty < g.transitions.len(),
            g.constants.transition_all < g.transitions.len(), g.constants.transition_epsilon < g.transitions.len(),
            model::lift_transition(g, g.constants.transition_empty) == language::Transition::Const(language::Regex::Empty),
            model::lift_transition(g, g.constants.transition_all) == language::Transition::Const(language::Regex::All),
            model::lift_transition(g, g.constants.transition_epsilon) == language::Transition::Const(language::Regex::Epsilon),
    {
        model::lemma_graph_wf_elim(g);
    }

    pub open spec fn derivative_native_result(g: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>, out: TransitionId) -> bool {
        match g.regexes[root@ as int].kind {
            model::RegexKindNode::Empty | model::RegexKindNode::Epsilon => out@ == g.constants.transition_empty,
            model::RegexKindNode::All => out@ == g.constants.transition_all,
            model::RegexKindNode::Test(test) => forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                model::symbols_wf(sym) ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                    == if model::test_holds(sym, theta, model::lift_test(g, test), event) { word.len() == 0 } else { false },
            model::RegexKindNode::Star(inner) => exists|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                        == super::super::normalize::verify::transition_append_combo(g, sym, theta, d, seq![root], event, word),
            model::RegexKindNode::Not(inner) => exists|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                && super::super::normalize::verify::transition_result(g, super::super::normalize::verify::ActionShape::Not(d@), out),
            _ => derivative_correct(g, root@, out),
        }
    }

    pub proof fn derivative_native_correct(g: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>, out: TransitionId)
        requires model::graph_wf(g), root@ < g.regexes.len(), derivative_cache_wf(g, cache),
            out@ < g.transitions.len(), derivative_native_result(g, root, cache, out),
        ensures derivative_correct(g, root@, out),
    {
        hide(language::lang); hide(language::derivative); hide(language::interp_transition);
        hide(model::lift_regex); hide(model::lift_transition);
        super::super::normalize::verify::regex_unfold(g, root@);
        derivative_constants(g);
        match g.regexes[root@ as int].kind {
            model::RegexKindNode::Star(inner) => {
                assert(model::lift_regex(g, root@) == language::Regex::Star(alloc::boxed::Box::new(model::lift_regex(g, inner))));
                let d = choose|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                    && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                        ==> super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                            == super::super::normalize::verify::transition_append_combo(g, sym, theta, d, seq![root], event, word);
                assert(derivative_correct(g, inner, d));
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    implies super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                        == model::regex_lang(g, sym, theta, root@, seq![event] + word) by {
                    let sem = model::gsem(sym, theta);
                    let actual = language::interp_transition(sem, event, model::lift_transition(g, d@));
                    let expected = language::derivative(sem, event, model::lift_regex(g, inner));
                    let tail = seq![model::lift_regex(g, root@)];
                    assert(model::lift_regexes(g, model::regex_ids(seq![root])) =~= tail);
                    language::lemma_concat_prepend(sem, actual, tail, word);
                    language::lemma_concat_prepend(sem, expected, tail, word);
                    assert forall|w: Seq<Data>| language::lang(sem, actual, w) == language::lang(sem, expected, w) by {
                        language::lemma_derivative_correct(sem, event, model::lift_regex(g, inner), w);
                        assert(super::super::normalize::verify::transition_lang(g, sym, theta, d, event, w)
                            == model::regex_lang(g, sym, theta, inner, seq![event] + w));
                    }
                    language::lemma_derivative_correct(sem, event, model::lift_regex(g, root@), word);
                    reveal(language::derivative);
                    assert(seq![expected] + tail =~= seq![expected, model::lift_regex(g, root@)]);
                    assert(language::derivative(sem, event, model::lift_regex(g, root@))
                        == language::Regex::Concat(seq![expected] + tail));
                }
            },
            model::RegexKindNode::Not(inner) => {
                let d = choose|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                    && super::super::normalize::verify::transition_result(g, super::super::normalize::verify::ActionShape::Not(d@), out);
                symbolic_not_result(g, d, out);
                assert(derivative_correct(g, inner, d));
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    implies super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                        == model::regex_lang(g, sym, theta, root@, seq![event] + word) by {
                    reveal(language::lang);
                }
            },
            model::RegexKindNode::Empty | model::RegexKindNode::All | model::RegexKindNode::Epsilon | model::RegexKindNode::Test(_) => {
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    implies super::super::normalize::verify::transition_lang(g, sym, theta, out, event, word)
                        == model::regex_lang(g, sym, theta, root@, seq![event] + word) by {
                    reveal(language::lang); reveal(language::interp_transition);
                    assert((seq![event] + word).len() == 1 + word.len());
                    assert((seq![event] + word)[0] == event);
                }
            },
            _ => {},
        }
    }

    pub proof fn derivative_step_future(g: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>)
        requires model::graph_wf(g), root@ < g.regexes.len(), derivative_cache_wf(g, cache),
        ensures forall|next: model::Graph, out: TransitionId| model::graph_extends(g, next) && model::graph_wf(next)
            && out@ < next.transitions.len() && derivative_native_result(next, root, cache, out) ==> derivative_correct(next, root@, out),
    {
        assert forall|next: model::Graph, out: TransitionId| model::graph_extends(g, next) && model::graph_wf(next)
            && out@ < next.transitions.len() && derivative_native_result(next, root, cache, out) implies derivative_correct(next, root@, out) by {
            derivative_extends(g, next);
            derivative_native_correct(next, root, cache, out);
        }
    }

    pub proof fn derivative_result_future(g: model::Graph, root: RegexId, concat: bool, intersect: bool, results: Seq<TransitionId>)
        requires model::graph_wf(g), derivative_results(g, root, concat, derivative_children_ids(g, root).len(), results), root@ < g.regexes.len(),
            match g.regexes[root@ as int].kind {
                model::RegexKindNode::Union(_) => !concat && !intersect,
                model::RegexKindNode::Intersect(_) => !concat && intersect,
                model::RegexKindNode::Concat(_) => concat && !intersect,
                _ => false,
            },
        ensures forall|next: model::Graph, out: TransitionId| model::graph_extends(g, next) && model::graph_wf(next)
            && out@ < next.transitions.len()
            && (if intersect { super::super::normalize::verify::transition_result(next, super::super::normalize::verify::ActionShape::Fold(model::transition_ids(results), 0), out) }
                else { forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> super::super::normalize::verify::transition_lang(next, sym, theta, out, event, word)
                        == super::super::normalize::verify::transition_combo(next, sym, theta, results, event, word, false) })
            ==> derivative_correct(next, root@, out),
    {
        assert forall|next: model::Graph, out: TransitionId| model::graph_extends(g, next) && model::graph_wf(next)
            && out@ < next.transitions.len()
            && (if intersect { super::super::normalize::verify::transition_result(next, super::super::normalize::verify::ActionShape::Fold(model::transition_ids(results), 0), out) }
                else { forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> super::super::normalize::verify::transition_lang(next, sym, theta, out, event, word)
                        == super::super::normalize::verify::transition_combo(next, sym, theta, results, event, word, false) })
            implies derivative_correct(next, root@, out) by {
            derivative_extends(g, next);
            if intersect { symbolic_intersect_result(next, results, out); }
            derivative_children_complete(next, root, concat, intersect, out);
        }
    }

    pub open spec fn assignment_valid(count: nat, words: Seq<u64>) -> bool {
        count + 63 <= usize::MAX
            && words.len() == (count + 63) / 64
            && (count % 64 != 0 ==> words.len() > 0
                && (words.last() >> ((count % 64) as u32)) == 0u64)
    }

    pub open spec fn positive_atom_at(g: model::Graph, atoms: Seq<TestId>, primitive: model::Primitive, index: usize) -> bool {
        index < atoms.len() && atoms[index as int]@ < g.tests.len()
            && g.tests[atoms[index as int]@ as int] == model::TestNode::Atom(primitive, true)
    }

    pub open spec fn bool_fold(values: Seq<bool>, and: bool) -> bool {
        if and { forall|i: int| 0 <= i < values.len() ==> values[i] }
        else { exists|i: int| 0 <= i < values.len() && values[i] }
    }

    pub proof fn bool_fold_push(values: Seq<bool>, value: bool, and: bool)
        ensures bool_fold(values.push(value), and) == (if and { bool_fold(values, and) && value } else { bool_fold(values, and) || value }),
    {
        if and {
            if bool_fold(values.push(value), true) {
                assert(values.push(value)[values.len() as int]);
                assert forall|i: int| 0 <= i < values.len() implies values[i] by {
                    assert(values.push(value)[i]);
                }
            }
            if bool_fold(values, true) && value {
                assert forall|i: int| 0 <= i < values.push(value).len() implies values.push(value)[i] by {
                    if i < values.len() { assert(values[i]); }
                }
            }
        } else {
            if bool_fold(values.push(value), false) {
                let i = choose|i: int| 0 <= i < values.push(value).len() && values.push(value)[i];
                if i != values.len() { assert(i < values.len()); assert(values[i]); }
            }
            if bool_fold(values, false) {
                let i = choose|i: int| 0 <= i < values.len() && values[i];
                assert(values.push(value)[i]);
            }
            if value { assert(values.push(value)[values.len() as int]); }
        }
    }

    pub open spec fn test_children(g: model::Graph, id: TestId) -> Seq<nat> {
        match g.tests[id@ as int] { model::TestNode::And(cs) | model::TestNode::Or(cs) => cs, _ => Seq::empty() }
    }

    pub open spec fn test_tasks_wf(g: model::Graph, tasks: Seq<(TestId, bool)>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> tasks[i].0@ < g.tests.len()
    }

    /// `evaluate_test` reuses the `test_not` measure: both worklists schedule the same nodes.
    pub proof fn test_lemma_eval_branch_work(g: model::Graph, id: TestId, pending: Seq<(TestId, bool)>)
        requires model::graph_wf(g), id@ < g.tests.len(),
            g.tests[id@ as int] is And || g.tests[id@ as int] is Or,
        ensures norm::test_not_work(g, pending.push((id, true)) + child_test_tasks(g, id, 0))
            < norm::test_not_work(g, pending.push((id, false))),
    {
        model::lemma_graph_test_wf(g, id@);
        let cs = test_children(g, id);
        let scheduled = child_test_tasks(g, id, 0);
        assert forall|i: int| 0 <= i < scheduled.len()
            implies #[trigger] scheduled[i].0@ == cs[cs.len() as int - 1 - i] && !scheduled[i].1 by {
            assert(cs[cs.len() as int - 1 - i] < id@);
        }
        norm::test_lemma_not_work_schedule(g, pending.push((id, true)), scheduled, cs, id@);
        assert(pending.push((id, true)).drop_last() =~= pending);
        assert(pending.push((id, false)).drop_last() =~= pending);
    }

    pub proof fn test_lemma_eval_step_work(g: model::Graph, id: TestId, finish: bool,
        pending: Seq<(TestId, bool)>, tasks: Seq<(TestId, bool)>)
        requires id@ < g.tests.len(),
            tasks == pending || norm::test_not_work(g, tasks) < norm::test_not_work(g, pending.push((id, finish))),
        ensures norm::test_not_work(g, tasks) < norm::test_not_work(g, pending.push((id, finish))),
    {
        assert(pending.push((id, finish)).drop_last() =~= pending);
    }

    pub open(crate) spec fn child_test_tasks(g: model::Graph, id: TestId, remaining: nat) -> Seq<(TestId, bool)> {
        Seq::new((test_children(g, id).len() - remaining) as nat, |i: int| (TestId(test_children(g, id)[test_children(g, id).len() - 1 - i] as u32), false))
    }

    pub open spec fn test_action(g: model::Graph, task: (TestId, bool), values: Seq<bool>, sym: model::Symbols, theta: Seq<Data>, event: Data) -> Option<Seq<bool>> {
        if task.1 {
            match g.tests[task.0@ as int] {
                model::TestNode::And(cs) | model::TestNode::Or(cs) => {
                    if cs.len() > values.len() { None }
                    else { Some(values.take(values.len() - cs.len()).push(bool_fold(values.skip(values.len() - cs.len()), g.tests[task.0@ as int] is And))) }
                },
                _ => Some(values.push(model::test_holds(sym, theta, model::lift_test(g, task.0@), event))),
            }
        } else { Some(values.push(model::test_holds(sym, theta, model::lift_test(g, task.0@), event))) }
    }

    pub open spec fn test_run(g: model::Graph, tasks: Seq<(TestId, bool)>, values: Seq<bool>, sym: model::Symbols, theta: Seq<Data>, event: Data) -> Option<Seq<bool>>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(values) }
        else { match test_action(g, tasks.last(), values, sym, theta, event) {
            Some(next) => test_run(g, tasks.drop_last(), next, sym, theta, event), None => None,
        } }
    }

    pub proof fn test_run_concat(g: model::Graph, prefix: Seq<(TestId, bool)>, suffix: Seq<(TestId, bool)>, values: Seq<bool>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        ensures test_run(g, prefix + suffix, values, sym, theta, event) == match test_run(g, suffix, values, sym, theta, event) {
            Some(next) => test_run(g, prefix, next, sym, theta, event), None => None,
        },
        decreases suffix.len(),
    {
        if suffix.len() > 0 {
            assert((prefix + suffix).last() == suffix.last());
            assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
            if let Some(next) = test_action(g, suffix.last(), values, sym, theta, event) {
                test_run_concat(g, prefix, suffix.drop_last(), next, sym, theta, event);
            }
        } else { assert(prefix + suffix =~= prefix); }
    }

    pub open spec fn child_test_values(g: model::Graph, id: TestId, count: nat, sym: model::Symbols, theta: Seq<Data>, event: Data) -> Seq<bool> {
        Seq::new(count, |i: int| model::test_holds(sym, theta, model::lift_test(g, test_children(g, id)[i]), event))
    }

    pub proof fn child_test_run(g: model::Graph, id: TestId, remaining: nat, values: Seq<bool>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.tests.len(), remaining <= test_children(g, id).len(),
        ensures test_run(g, child_test_tasks(g, id, remaining), values, sym, theta, event)
            == Some(values + child_test_values(g, id, test_children(g, id).len(), sym, theta, event).skip(remaining as int)),
        decreases test_children(g, id).len() - remaining,
    {
        model::lemma_graph_test_wf(g, id@);
        let tasks = child_test_tasks(g, id, remaining);
        let vals = child_test_values(g, id, test_children(g, id).len(), sym, theta, event);
        if remaining < test_children(g, id).len() {
            let child = TestId(test_children(g, id)[remaining as int] as u32);
            assert(child@ == test_children(g, id)[remaining as int]);
            assert(tasks.last() == (child, false));
            assert(tasks.drop_last() =~= child_test_tasks(g, id, remaining + 1));
            child_test_run(g, id, remaining + 1, values.push(vals[remaining as int]), sym, theta, event);
            assert(values.push(vals[remaining as int]) + vals.skip(remaining as int + 1)
                =~= values + vals.skip(remaining as int));
        } else {
            assert(tasks =~= Seq::empty());
            assert(vals.skip(remaining as int) =~= Seq::empty());
            assert(values + vals.skip(remaining as int) =~= values);
        }
    }

    pub proof fn test_expand(g: model::Graph, id: TestId, tasks: Seq<(TestId, bool)>, values: Seq<bool>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.tests.len(),
            g.tests[id@ as int] is And || g.tests[id@ as int] is Or,
        ensures test_run(g, tasks.push((id, true)) + child_test_tasks(g, id, 0), values, sym, theta, event)
            == test_run(g, tasks.push((id, false)), values, sym, theta, event),
    {
        reveal_with_fuel(model::test_holds, 2);
        reveal_with_fuel(model::lift_test, 2);
        reveal_with_fuel(test_run, 2);
        model::lemma_graph_test_wf(g, id@);
        let vals = child_test_values(g, id, test_children(g, id).len(), sym, theta, event);
        child_test_run(g, id, 0, values, sym, theta, event);
        test_run_concat(g, tasks.push((id, true)), child_test_tasks(g, id, 0), values, sym, theta, event);
        assert(vals.skip(0) =~= vals);
        assert((values + vals).take(values.len() as int) =~= values);
        assert((values + vals).skip(values.len() as int) =~= vals);
        assert(bool_fold(vals, g.tests[id@ as int] is And)
            == model::test_holds(sym, theta, model::lift_test(g, id@), event)) by {
            match g.tests[id@ as int] {
                model::TestNode::And(cs) => {
                    assert(model::lift_test(g, id@) == model::Test::And(model::lift_tests(g, cs, id@)));
                    assert forall|i: int| 0 <= i < cs.len() implies
                        vals[i] == model::test_holds(sym, theta, model::lift_tests(g, cs, id@)[i], event) by {
                        assert(model::lift_tests(g, cs, id@)[i] == model::lift_test(g, cs[i]));
                    }
                    bool_fold_tests(vals, model::lift_tests(g, cs, id@), true, sym, theta, event);
                },
                model::TestNode::Or(cs) => {
                    assert(model::lift_test(g, id@) == model::Test::Or(model::lift_tests(g, cs, id@)));
                    assert forall|i: int| 0 <= i < cs.len() implies
                        vals[i] == model::test_holds(sym, theta, model::lift_tests(g, cs, id@)[i], event) by {
                        assert(model::lift_tests(g, cs, id@)[i] == model::lift_test(g, cs[i]));
                    }
                    bool_fold_tests(vals, model::lift_tests(g, cs, id@), false, sym, theta, event);
                },
                _ => {},
            }
        }
        assert(test_action(g, (id, true), values + vals, sym, theta, event)
            == Some(values.push(model::test_holds(sym, theta, model::lift_test(g, id@), event))));
        assert(tasks.push((id, true)).drop_last() =~= tasks);
        assert(tasks.push((id, false)).drop_last() =~= tasks);
    }

    pub proof fn bool_fold_tests(vals: Seq<bool>, tests: Seq<model::Test>, and: bool, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires vals.len() == tests.len(), forall|i: int| 0 <= i < vals.len() ==> vals[i] == model::test_holds(sym, theta, tests[i], event),
        ensures bool_fold(vals, and) == model::test_holds(sym, theta, if and { model::Test::And(tests) } else { model::Test::Or(tests) }, event),
    {
        norm::test_lemma_semantics_unfold(sym, theta, event, model::Test::And(tests));
        norm::test_lemma_semantics_unfold(sym, theta, event, model::Test::Or(tests));
        if and {
            if bool_fold(vals, true) {
                assert forall|i: int| 0 <= i < tests.len() implies model::test_holds(sym, theta, tests[i], event) by { assert(vals[i]); }
            }
            if model::test_holds(sym, theta, model::Test::And(tests), event) {
                assert forall|i: int| 0 <= i < vals.len() implies vals[i] by { assert(model::test_holds(sym, theta, tests[i], event)); }
            }
        } else {
            if bool_fold(vals, false) {
                let i = choose|i: int| 0 <= i < vals.len() && vals[i];
                assert(model::test_holds(sym, theta, tests[i], event));
            }
            if model::test_holds(sym, theta, model::Test::Or(tests), event) {
                let i = choose|i: int| 0 <= i < tests.len() && model::test_holds(sym, theta, tests[i], event);
                assert(vals[i]);
            }
        }
    }

    pub proof fn bool_fold_prepend(value: bool, values: Seq<bool>, and: bool)
        ensures bool_fold(seq![value] + values, and) == (if and { value && bool_fold(values, and) } else { value || bool_fold(values, and) }),
    {
        if and {
            if bool_fold(seq![value] + values, true) {
                assert((seq![value] + values)[0]);
                assert forall|i: int| 0 <= i < values.len() implies values[i] by { assert((seq![value] + values)[i + 1]); }
            }
            if value && bool_fold(values, true) {
                assert forall|i: int| 0 <= i < (seq![value] + values).len() implies (seq![value] + values)[i] by {
                    if i > 0 { assert(values[i - 1]); }
                }
            }
        } else {
            if bool_fold(seq![value] + values, false) {
                let i = choose|i: int| 0 <= i < (seq![value] + values).len() && (seq![value] + values)[i];
                if i > 0 { assert(values[i - 1]); }
            }
            if bool_fold(values, false) {
                let i = choose|i: int| 0 <= i < values.len() && values[i];
                assert((seq![value] + values)[i + 1]);
            }
            if value { assert((seq![value] + values)[0]); }
        }
    }

    pub proof fn test_run_unfold(g: model::Graph, tasks: Seq<(TestId, bool)>, values: Seq<bool>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        ensures test_run(g, tasks, values, sym, theta, event) == if tasks.len() == 0 { Some(values) }
            else { match test_action(g, tasks.last(), values, sym, theta, event) {
                Some(next) => test_run(g, tasks.drop_last(), next, sym, theta, event), None => None,
            } },
    {
        if tasks.len() == 0 {} else {}
    }

    pub proof fn realized_atom_value(g: model::Graph, atoms: Seq<TestId>, words: Seq<u64>, id: TestId, primitive: model::Primitive, positive: bool, index: usize, value: bool)
        requires id@ < g.tests.len(), g.tests[id@ as int] == model::TestNode::Atom(primitive, positive),
            positive_atom_at(g, atoms, primitive, index), value == truth_word_bit(words, index as nat),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            truth_words_realize(g, atoms, words, sym, theta, event) ==>
                (if positive { value } else { !value }) == model::test_holds(sym, theta, model::lift_test(g, id@), event),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            truth_words_realize(g, atoms, words, sym, theta, event) implies
                (if positive { value } else { !value }) == model::test_holds(sym, theta, model::lift_test(g, id@), event) by {
            assert(0 <= (index as int) < atoms.len());
            reveal(truth_words_realize);
            assert forall|i: int| 0 <= i < atoms.len() implies
                truth_word_bit(words, i as nat) == model::test_holds(sym, theta, model::lift_test(g, atoms[i]@), event) by {}
            assert(truth_word_bit(words, (index as int) as nat)
                == model::test_holds(sym, theta, model::lift_test(g, atoms[index as int]@), event));
            assert(model::lift_test(g, atoms[index as int]@) == model::Test::Atom(primitive, true));
            assert(model::lift_test(g, id@) == model::Test::Atom(primitive, positive));
        }
    }

    pub type InterpRegex = language::Regex<model::Test>;

    pub open spec fn interpreted(g: model::Graph, id: TransitionId, sym: model::Symbols, theta: Seq<Data>, event: Data) -> InterpRegex {
        language::interp_transition(model::gsem(sym, theta), event, model::lift_transition(g, id@))
    }

    pub open spec fn lifted_values(g: model::Graph, ids: Seq<RegexId>) -> Seq<InterpRegex> {
        Seq::new(ids.len(), |i: int| model::lift_regex(g, ids[i]@))
    }

    pub open spec fn interp_tasks_wf(g: model::Graph, tasks: Seq<(TransitionId, bool)>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> tasks[i].0@ < g.transitions.len()
    }

    pub open spec fn interp_node_work(g: model::Graph, id: nat) -> nat
        decreases id, 1nat,
    {
        if id >= g.transitions.len() { 0 } else {
            match g.transitions[id as int] {
                model::TransitionNode::Const(_) => 1,
                model::TransitionNode::If(_, a, b) => 1 + (if a < id { interp_node_work(g, a) } else { 0 })
                    + (if b < id { interp_node_work(g, b) } else { 0 }),
                model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => 2 + interp_children_work(g, cs, id),
                model::TransitionNode::Not(c) | model::TransitionNode::Append(c, _) =>
                    2 + if c < id { interp_node_work(g, c) } else { 0 },
            }
        }
    }

    pub open spec fn interp_children_work(g: model::Graph, children: Seq<nat>, bound: nat) -> nat
        decreases bound, 0nat, children.len(),
    {
        if children.len() == 0 { 0 } else {
            interp_children_work(g, children.skip(1), bound)
                + if children[0] < bound { interp_node_work(g, children[0]) } else { 0 }
        }
    }

    /// `interpret_step` ignores `finish` on `If` nodes, so an `If` task always weighs its whole node.
    pub open spec fn interp_task_work(g: model::Graph, task: (TransitionId, bool)) -> nat {
        if task.1 && !(task.0@ < g.transitions.len() && g.transitions[task.0@ as int] is If) { 1 }
        else { interp_node_work(g, task.0@) }
    }

    pub open spec fn interp_work(g: model::Graph, tasks: Seq<(TransitionId, bool)>) -> nat
        decreases tasks.len(),
    {
        if tasks.len() == 0 { 0 } else { interp_work(g, tasks.drop_last()) + interp_task_work(g, tasks.last()) }
    }

    pub proof fn interp_lemma_node_work_extends(a: model::Graph, b: model::Graph, id: nat)
        requires model::graph_extends(a, b), id < a.transitions.len(),
        ensures interp_node_work(a, id) == interp_node_work(b, id),
        decreases id, 1nat,
    {
        assert(a.transitions[id as int] == b.transitions[id as int]);
        match a.transitions[id as int] {
            model::TransitionNode::If(_, x, y) => {
                if x < id { interp_lemma_node_work_extends(a, b, x); }
                if y < id { interp_lemma_node_work_extends(a, b, y); }
            },
            model::TransitionNode::Union(cs) => { interp_lemma_children_work_extends(a, b, cs, id); },
            model::TransitionNode::Intersect(cs) => { interp_lemma_children_work_extends(a, b, cs, id); },
            model::TransitionNode::Not(c) => { if c < id { interp_lemma_node_work_extends(a, b, c); } },
            model::TransitionNode::Append(c, _) => { if c < id { interp_lemma_node_work_extends(a, b, c); } },
            _ => {},
        }
    }

    pub proof fn interp_lemma_children_work_extends(a: model::Graph, b: model::Graph, children: Seq<nat>, bound: nat)
        requires model::graph_extends(a, b), bound <= a.transitions.len(),
        ensures interp_children_work(a, children, bound) == interp_children_work(b, children, bound),
        decreases bound, 0nat, children.len(),
    {
        if children.len() > 0 {
            if children[0] < bound { interp_lemma_node_work_extends(a, b, children[0]); }
            interp_lemma_children_work_extends(a, b, children.skip(1), bound);
        }
    }

    pub proof fn interp_lemma_work_extends(a: model::Graph, b: model::Graph, tasks: Seq<(TransitionId, bool)>)
        requires model::graph_extends(a, b), interp_tasks_wf(a, tasks),
        ensures interp_work(a, tasks) == interp_work(b, tasks),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            let last = tasks.last();
            assert(last.0@ < a.transitions.len());
            assert(a.transitions[last.0@ as int] == b.transitions[last.0@ as int]);
            interp_lemma_node_work_extends(a, b, last.0@);
            assert forall|i: int| 0 <= i < tasks.drop_last().len() implies tasks.drop_last()[i].0@ < a.transitions.len() by {
                assert(tasks.drop_last()[i] == tasks[i]);
            }
            interp_lemma_work_extends(a, b, tasks.drop_last());
        }
    }

    pub proof fn interp_lemma_work_schedule(g: model::Graph, tasks: Seq<(TransitionId, bool)>,
        scheduled: Seq<(TransitionId, bool)>, children: Seq<nat>, bound: nat)
        requires scheduled.len() == children.len(), model::bounded(children, bound),
            forall|i: int| 0 <= i < scheduled.len()
                ==> #[trigger] scheduled[i].0@ == children[children.len() as int - 1 - i] && !scheduled[i].1,
        ensures interp_work(g, tasks + scheduled) == interp_work(g, tasks) + interp_children_work(g, children, bound),
        decreases scheduled.len(),
    {
        if scheduled.len() == 0 {
            assert(tasks + scheduled =~= tasks);
        } else {
            assert((tasks + scheduled).drop_last() =~= tasks + scheduled.drop_last());
            assert((tasks + scheduled).last() == scheduled.last());
            interp_lemma_work_schedule(g, tasks, scheduled.drop_last(), children.skip(1), bound);
        }
    }

    pub proof fn interp_lemma_work_push(g: model::Graph, tasks: Seq<(TransitionId, bool)>, task: (TransitionId, bool))
        ensures interp_work(g, tasks.push(task)) == interp_work(g, tasks) + interp_task_work(g, task),
    {
        assert(tasks.push(task).drop_last() =~= tasks);
    }

    pub proof fn interp_lemma_work_if(g: model::Graph, id: TransitionId, finish: bool,
        pending: Seq<(TransitionId, bool)>, chosen: TransitionId)
        requires model::graph_wf(g), id@ < g.transitions.len(), interp_tasks_wf(g, pending),
            match g.transitions[id@ as int] { model::TransitionNode::If(_, a, b) => chosen@ == a || chosen@ == b, _ => false },
        ensures interp_tasks_wf(g, pending.push((chosen, false))),
            interp_work(g, pending.push((chosen, false))) < interp_work(g, pending.push((id, finish))),
    {
        model::lemma_graph_transition_wf(g, id@);
        interp_lemma_work_push(g, pending, (chosen, false));
        interp_lemma_work_push(g, pending, (id, finish));
    }

    pub proof fn interp_lemma_work_unary(g: model::Graph, id: TransitionId, pending: Seq<(TransitionId, bool)>, inner: TransitionId)
        requires model::graph_wf(g), id@ < g.transitions.len(), interp_tasks_wf(g, pending),
            match g.transitions[id@ as int] {
                model::TransitionNode::Not(c) => inner@ == c,
                model::TransitionNode::Append(c, _) => inner@ == c,
                _ => false,
            },
        ensures interp_tasks_wf(g, pending.push((id, true)).push((inner, false))),
            interp_work(g, pending.push((id, true)).push((inner, false))) < interp_work(g, pending.push((id, false))),
    {
        model::lemma_graph_transition_wf(g, id@);
        interp_lemma_work_push(g, pending, (id, true));
        interp_lemma_work_push(g, pending.push((id, true)), (inner, false));
        interp_lemma_work_push(g, pending, (id, false));
    }

    pub proof fn interp_lemma_work_branch(g: model::Graph, id: TransitionId, pending: Seq<(TransitionId, bool)>)
        requires model::graph_wf(g), id@ < g.transitions.len(), interp_tasks_wf(g, pending),
            g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect,
        ensures interp_tasks_wf(g, pending.push((id, true)) + child_interp_tasks(g, id, 0)),
            interp_work(g, pending.push((id, true)) + child_interp_tasks(g, id, 0)) < interp_work(g, pending.push((id, false))),
    {
        model::lemma_graph_transition_wf(g, id@);
        let cs = transition_children(g, id);
        let scheduled = child_interp_tasks(g, id, 0);
        assert forall|i: int| 0 <= i < scheduled.len()
            implies #[trigger] scheduled[i].0@ == cs[cs.len() as int - 1 - i] && !scheduled[i].1 by {
            assert(cs[cs.len() as int - 1 - i] < id@);
        }
        interp_lemma_work_schedule(g, pending.push((id, true)), scheduled, cs, id@);
        interp_lemma_work_push(g, pending, (id, true));
        interp_lemma_work_push(g, pending, (id, false));
        let all = pending.push((id, true)) + scheduled;
        assert forall|i: int| 0 <= i < all.len() implies all[i].0@ < g.transitions.len() by {
            if i < pending.len() { assert(all[i] == pending[i]); }
            else if i > pending.len() { assert(all[i] == scheduled[i - pending.len() - 1]); }
        }
    }

    pub proof fn interp_lemma_step_post(before: model::Graph, after: model::Graph, id: TransitionId, finish: bool,
        pending: Seq<(TransitionId, bool)>, tasks: Seq<(TransitionId, bool)>)
        requires model::graph_extends(before, after), id@ < before.transitions.len(), interp_tasks_wf(before, pending),
            tasks == pending || (interp_tasks_wf(before, tasks)
                && interp_work(before, tasks) < interp_work(before, pending.push((id, finish)))),
        ensures interp_work(after, tasks) < interp_work(before, pending.push((id, finish))),
    {
        interp_lemma_work_push(before, pending, (id, finish));
        interp_lemma_work_extends(before, after, tasks);
    }

    pub open spec fn transition_children(g: model::Graph, id: TransitionId) -> Seq<nat> {
        match g.transitions[id@ as int] { model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => cs, _ => Seq::empty() }
    }

    pub open spec fn transition_suffix(g: model::Graph, id: TransitionId) -> Seq<nat> {
        match g.transitions[id@ as int] { model::TransitionNode::Append(_, cs) => cs, _ => Seq::empty() }
    }

    pub open(crate) spec fn child_interp_tasks(g: model::Graph, id: TransitionId, remaining: nat) -> Seq<(TransitionId, bool)> {
        Seq::new((transition_children(g, id).len() - remaining) as nat, |i: int| (TransitionId(transition_children(g, id)[transition_children(g, id).len() - 1 - i] as u32), false))
    }

    pub open spec fn regex_stack_equiv(sem: spec_fn(model::Test, Data) -> bool, left: Seq<InterpRegex>, right: Seq<InterpRegex>) -> bool {
        left.len() == right.len() && forall|i: int, word: Seq<Data>| 0 <= i < left.len() ==>
            language::lang(sem, left[i], word) == language::lang(sem, right[i], word)
    }

    pub open spec fn interp_results_equiv(sem: spec_fn(model::Test, Data) -> bool, left: Option<Seq<InterpRegex>>, right: Option<Seq<InterpRegex>>) -> bool {
        match (left, right) { (Some(a), Some(b)) => regex_stack_equiv(sem, a, b), (None, None) => true, _ => false }
    }

    pub open spec fn interp_action(g: model::Graph, task: (TransitionId, bool), values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data) -> Option<Seq<InterpRegex>> {
        if !task.1 { Some(values.push(interpreted(g, task.0, sym, theta, event))) }
        else {
            match g.transitions[task.0@ as int] {
                model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => {
                    if cs.len() > values.len() { None }
                    else { Some(values.take(values.len() - cs.len()).push(
                        if g.transitions[task.0@ as int] is Intersect { language::Regex::Intersect(values.skip(values.len() - cs.len())) }
                        else { language::Regex::Union(values.skip(values.len() - cs.len())) })) }
                },
                model::TransitionNode::Not(_) => if values.len() == 0 { None }
                    else { Some(values.drop_last().push(language::Regex::Not(Box::new(values.last())))) },
                model::TransitionNode::Append(_, cs) => if values.len() == 0 { None }
                    else { Some(values.drop_last().push(language::Regex::Concat(seq![values.last()] + model::lift_regexes(g, cs)))) },
                _ => Some(values.push(interpreted(g, task.0, sym, theta, event))),
            }
        }
    }

    pub open spec fn interp_run(g: model::Graph, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data) -> Option<Seq<InterpRegex>>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(values) }
        else { match interp_action(g, tasks.last(), values, sym, theta, event) {
            Some(next) => interp_run(g, tasks.drop_last(), next, sym, theta, event), None => None,
        } }
    }

    pub proof fn interp_run_unfold(g: model::Graph, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        ensures interp_run(g, tasks, values, sym, theta, event) == if tasks.len() == 0 { Some(values) }
            else { match interp_action(g, tasks.last(), values, sym, theta, event) {
                Some(next) => interp_run(g, tasks.drop_last(), next, sym, theta, event), None => None,
            } },
    { if tasks.len() == 0 {} else {} }

    pub proof fn regex_stack_equiv_trans(sem: spec_fn(model::Test, Data) -> bool, a: Seq<InterpRegex>, b: Seq<InterpRegex>, c: Seq<InterpRegex>)
        requires regex_stack_equiv(sem, a, b), regex_stack_equiv(sem, b, c),
        ensures regex_stack_equiv(sem, a, c),
    {}

    pub proof fn interp_results_equiv_trans(sem: spec_fn(model::Test, Data) -> bool, a: Option<Seq<InterpRegex>>, b: Option<Seq<InterpRegex>>, c: Option<Seq<InterpRegex>>)
        requires interp_results_equiv(sem, a, b), interp_results_equiv(sem, b, c),
        ensures interp_results_equiv(sem, a, c),
    {
        match (a,b,c) { (Some(x),Some(y),Some(z)) => regex_stack_equiv_trans(sem,x,y,z), _ => {} }
    }

    pub open spec fn regex_fold(values: Seq<InterpRegex>, intersect: bool) -> InterpRegex {
        if intersect { language::Regex::Intersect(values) } else { language::Regex::Union(values) }
    }

    pub proof fn regex_stack_fold_congruent(sem: spec_fn(model::Test, Data) -> bool, left: Seq<InterpRegex>, right: Seq<InterpRegex>, intersect: bool)
        requires regex_stack_equiv(sem, left, right),
        ensures forall|word: Seq<Data>| language::lang(sem, regex_fold(left, intersect), word)
            == language::lang(sem, regex_fold(right, intersect), word),
    {
        assert forall|word: Seq<Data>| language::lang(sem, regex_fold(left, intersect), word)
            == language::lang(sem, regex_fold(right, intersect), word) by {
            regex_fold_semantics(sem, left, intersect, word);
            regex_fold_semantics(sem, right, intersect, word);
            if !intersect {
                if exists|i: int| 0 <= i < left.len() && language::lang(sem, left[i], word) {
                    let i = choose|i: int| 0 <= i < left.len() && language::lang(sem, left[i], word);
                    assert(language::lang(sem, right[i], word));
                }
                if exists|i: int| 0 <= i < right.len() && language::lang(sem, right[i], word) {
                    let i = choose|i: int| 0 <= i < right.len() && language::lang(sem, right[i], word);
                    assert(language::lang(sem, left[i], word));
                }
            } else {
                if language::lang(sem, regex_fold(left, true), word) {
                    assert forall|i: int| 0 <= i < right.len() implies language::lang(sem, right[i], word) by {
                        assert(language::lang(sem, left[i], word));
                    }
                }
                if language::lang(sem, regex_fold(right, true), word) {
                    assert forall|i: int| 0 <= i < left.len() implies language::lang(sem, left[i], word) by {
                        assert(language::lang(sem, right[i], word));
                    }
                }
            }
        }
    }

    pub proof fn interp_action_congruent(g: model::Graph, task: (TransitionId, bool), left: Seq<InterpRegex>, right: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires regex_stack_equiv(model::gsem(sym, theta), left, right),
        ensures interp_results_equiv(model::gsem(sym, theta), interp_action(g, task, left, sym, theta, event), interp_action(g, task, right, sym, theta, event)),
    {
        let sem = model::gsem(sym, theta);
        if task.1 {
            match g.transitions[task.0@ as int] {
                model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => {
                    if cs.len() <= left.len() {
                        assert(regex_stack_equiv(sem, left.skip(left.len()-cs.len()), right.skip(right.len()-cs.len())));
                        regex_stack_fold_congruent(sem, left.skip(left.len()-cs.len()), right.skip(right.len()-cs.len()), g.transitions[task.0@ as int] is Intersect);
                    }
                },
                model::TransitionNode::Not(_) => {
                    if left.len() > 0 {
                        assert forall|word: Seq<Data>| language::lang(sem, language::Regex::Not(Box::new(left.last())), word)
                            == language::lang(sem, language::Regex::Not(Box::new(right.last())), word) by {
                            norm::regex_language_unfold(sem, language::Regex::Not(Box::new(left.last())), word);
                            norm::regex_language_unfold(sem, language::Regex::Not(Box::new(right.last())), word);
                        }
                    }
                },
                model::TransitionNode::Append(_, cs) => {
                    if left.len() > 0 {
                        norm::regex_concat_congruent(sem, seq![left.last()] + model::lift_regexes(g, cs), seq![right.last()] + model::lift_regexes(g, cs));
                    }
                },
                _ => {},
            }
        }
    }

    pub proof fn interp_run_congruent(g: model::Graph, tasks: Seq<(TransitionId, bool)>, left: Seq<InterpRegex>, right: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires regex_stack_equiv(model::gsem(sym, theta), left, right),
        ensures interp_results_equiv(model::gsem(sym, theta), interp_run(g, tasks, left, sym, theta, event), interp_run(g, tasks, right, sym, theta, event)),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            interp_action_congruent(g, tasks.last(), left, right, sym, theta, event);
            match (interp_action(g, tasks.last(), left, sym, theta, event), interp_action(g, tasks.last(), right, sym, theta, event)) {
                (Some(a),Some(b)) => interp_run_congruent(g, tasks.drop_last(), a, b, sym, theta, event), _ => {},
            }
        }
    }

    pub proof fn interp_run_concat(g: model::Graph, prefix: Seq<(TransitionId, bool)>, suffix: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        ensures interp_run(g, prefix + suffix, values, sym, theta, event) == match interp_run(g, suffix, values, sym, theta, event) {
            Some(next) => interp_run(g, prefix, next, sym, theta, event), None => None,
        },
        decreases suffix.len(),
    {
        if suffix.len() > 0 {
            assert((prefix + suffix).last() == suffix.last());
            assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
            if let Some(next) = interp_action(g, suffix.last(), values, sym, theta, event) {
                interp_run_concat(g, prefix, suffix.drop_last(), next, sym, theta, event);
            }
        } else { assert(prefix + suffix =~= prefix); }
    }

    pub proof fn regex_fold_semantics(sem: spec_fn(model::Test, Data) -> bool, values: Seq<InterpRegex>, intersect: bool, word: Seq<Data>)
        ensures language::lang(sem, regex_fold(values, intersect), word) == if intersect {
            forall|i: int| 0 <= i < values.len() ==> language::lang(sem, values[i], word)
        } else { exists|i: int| 0 <= i < values.len() && language::lang(sem, values[i], word) },
    {
        reveal(regex_fold);
        if intersect {
            regex_intersect_language(sem, values, word);
            assert(language::lang(sem, language::Regex::Intersect(values), word)
                == (forall|i: int| 0 <= i < values.len() ==> language::lang(sem, values[i], word)));
            assert(regex_fold(values, intersect) == language::Regex::Intersect(values));
        } else {
            regex_union_language(sem, values, word);
            assert(language::lang(sem, language::Regex::Union(values), word)
                == (exists|i: int| 0 <= i < values.len() && language::lang(sem, values[i], word)));
            assert(regex_fold(values, intersect) == language::Regex::Union(values));
        }
    }

    pub proof fn regex_intersect_language(sem: spec_fn(model::Test, Data) -> bool, cs: Seq<InterpRegex>, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Intersect(cs), word)
            == (forall|i: int| 0 <= i < cs.len() ==> language::lang(sem, cs[i], word)),
    { norm::regex_language_unfold(sem, language::Regex::Intersect(cs), word); }

    pub proof fn regex_union_language(sem: spec_fn(model::Test, Data) -> bool, cs: Seq<InterpRegex>, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Union(cs), word)
            == (exists|i: int| 0 <= i < cs.len() && language::lang(sem, cs[i], word)),
    { norm::regex_language_unfold(sem, language::Regex::Union(cs), word); }

    pub open(crate) spec fn child_interp_values(g: model::Graph, id: TransitionId, sym: model::Symbols, theta: Seq<Data>, event: Data) -> Seq<InterpRegex> {
        Seq::new(transition_children(g, id).len(), |i: int| interpreted(g, TransitionId(transition_children(g, id)[i] as u32), sym, theta, event))
    }

    pub proof fn child_interp_run(g: model::Graph, id: TransitionId, remaining: nat, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.transitions.len(), remaining <= transition_children(g, id).len(),
        ensures interp_run(g, child_interp_tasks(g, id, remaining), values, sym, theta, event)
            == Some(values + child_interp_values(g, id, sym, theta, event).skip(remaining as int)),
        decreases transition_children(g, id).len() - remaining,
    {
        model::lemma_graph_transition_wf(g, id@);
        let tasks = child_interp_tasks(g, id, remaining);
        let vals = child_interp_values(g, id, sym, theta, event);
        if remaining < transition_children(g, id).len() {
            let child = TransitionId(transition_children(g, id)[remaining as int] as u32);
            assert(child@ == transition_children(g, id)[remaining as int]);
            assert(tasks.last() == (child, false));
            assert(tasks.drop_last() =~= child_interp_tasks(g, id, remaining + 1));
            child_interp_run(g, id, remaining + 1, values.push(vals[remaining as int]), sym, theta, event);
            assert(values.push(vals[remaining as int]) + vals.skip(remaining as int + 1) =~= values + vals.skip(remaining as int));
        } else {
            assert(tasks =~= Seq::empty());
            assert(vals.skip(remaining as int) =~= Seq::empty());
            assert(values + vals.skip(remaining as int) =~= values);
        }
    }

    pub proof fn interpreted_fold(g: model::Graph, id: TransitionId, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect,
        ensures forall|word: Seq<Data>| language::lang(model::gsem(sym, theta), interpreted(g, id, sym, theta, event), word)
            == language::lang(model::gsem(sym, theta), regex_fold(child_interp_values(g, id, sym, theta, event), g.transitions[id@ as int] is Intersect), word),
    {
        model::lemma_graph_transition_wf(g, id@);
        let children = Seq::new(transition_children(g, id).len(), |i: int| TransitionId(transition_children(g, id)[i] as u32));
        assert(model::transition_ids(children) =~= transition_children(g, id));
        norm::transition_lemma_children_language(g, id, children, g.transitions[id@ as int] is Intersect);
        let vals = child_interp_values(g, id, sym, theta, event);
        assert forall|word: Seq<Data>| language::lang(model::gsem(sym, theta), interpreted(g, id, sym, theta, event), word)
            == language::lang(model::gsem(sym, theta), regex_fold(vals, g.transitions[id@ as int] is Intersect), word) by {
            let sem = model::gsem(sym, theta);
            reveal(norm::transition_combo);
            assert(norm::transition_lang(g, sym, theta, id, event, word)
                == language::lang(sem, interpreted(g, id, sym, theta, event), word));
            assert forall|i: int| 0 <= i < children.len() implies
                norm::transition_lang(g, sym, theta, children[i], event, word) == language::lang(sem, vals[i], word) by {}
            regex_fold_semantics(sem, vals, g.transitions[id@ as int] is Intersect, word);
            if !(g.transitions[id@ as int] is Intersect) {
                if norm::transition_lang(g, sym, theta, id, event, word) {
                    let i = choose|i: int| 0 <= i < children.len() && norm::transition_lang(g, sym, theta, children[i], event, word);
                    assert(language::lang(sem, vals[i], word));
                }
                if language::lang(sem, regex_fold(vals, false), word) {
                    let i = choose|i: int| 0 <= i < vals.len() && language::lang(sem, vals[i], word);
                    assert(norm::transition_lang(g, sym, theta, children[i], event, word));
                }
            } else {
                if norm::transition_lang(g, sym, theta, id, event, word) {
                    assert forall|i: int| 0 <= i < vals.len() implies language::lang(sem, vals[i], word) by {
                        assert(norm::transition_lang(g, sym, theta, children[i], event, word));
                    }
                }
                if language::lang(sem, regex_fold(vals, true), word) {
                    assert forall|i: int| 0 <= i < children.len() implies norm::transition_lang(g, sym, theta, children[i], event, word) by {
                        assert(language::lang(sem, vals[i], word));
                    }
                }
            }
        }
    }

    pub proof fn interp_expand_set(g: model::Graph, id: TransitionId, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect,
        ensures interp_results_equiv(model::gsem(sym, theta),
            interp_run(g, tasks.push((id, false)), values, sym, theta, event),
            interp_run(g, tasks.push((id, true)) + child_interp_tasks(g, id, 0), values, sym, theta, event)),
    {
        let vals = child_interp_values(g, id, sym, theta, event);
        child_interp_run(g, id, 0, values, sym, theta, event);
        interp_run_concat(g, tasks.push((id, true)), child_interp_tasks(g, id, 0), values, sym, theta, event);
        interpreted_fold(g, id, sym, theta, event);
        assert(vals.skip(0) =~= vals);
        assert((values + vals).take(values.len() as int) =~= values);
        assert((values + vals).skip(values.len() as int) =~= vals);
        assert(tasks.push((id, true)).drop_last() =~= tasks);
        assert(tasks.push((id, false)).drop_last() =~= tasks);
        interp_run_unfold(g, tasks.push((id, true)), values + vals, sym, theta, event);
        interp_run_unfold(g, tasks.push((id, false)), values, sym, theta, event);
        interp_run_congruent(g, tasks, values.push(interpreted(g, id, sym, theta, event)), values.push(regex_fold(vals, g.transitions[id@ as int] is Intersect)), sym, theta, event);
    }

    pub proof fn interp_action_stable(before: model::Graph, after: model::Graph, task: (TransitionId, bool), values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(before), model::graph_extends(before, after), task.0@ < before.transitions.len(),
        ensures interp_action(before, task, values, sym, theta, event) == interp_action(after, task, values, sym, theta, event),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_transition_stable(before, after, task.0@);
        assert(before.transitions[task.0@ as int] == after.transitions[task.0@ as int]);
        if let model::TransitionNode::Append(_, cs) = before.transitions[task.0@ as int] {
            model::lemma_graph_transition_wf(before, task.0@);
            assert(model::lift_regexes(before, cs) =~= model::lift_regexes(after, cs)) by {
                assert forall|i: int| 0 <= i < cs.len() implies
                    model::lift_regexes(before, cs)[i] == model::lift_regexes(after, cs)[i] by {
                    model::lemma_lift_regex_stable(before, after, cs[i]);
                }
            }
        }
    }

    pub proof fn interp_run_stable(before: model::Graph, after: model::Graph, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(before), model::graph_extends(before, after), interp_tasks_wf(before, tasks),
        ensures interp_run(before, tasks, values, sym, theta, event) == interp_run(after, tasks, values, sym, theta, event),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            interp_action_stable(before, after, tasks.last(), values, sym, theta, event);
            if let Some(next) = interp_action(before, tasks.last(), values, sym, theta, event) {
                interp_run_stable(before, after, tasks.drop_last(), next, sym, theta, event);
            }
        }
    }

    pub proof fn lifted_values_stable(before: model::Graph, after: model::Graph, ids: Seq<RegexId>)
        requires model::graph_wf(before), model::graph_extends(before, after), norm::regex_ids_valid(before, ids),
        ensures norm::regex_ids_valid(after, ids), lifted_values(before, ids) == lifted_values(after, ids),
    {
        model::lemma_graph_wf_elim(before);
        assert(lifted_values(before, ids) =~= lifted_values(after, ids)) by {
            assert forall|i: int| 0 <= i < ids.len() implies model::lift_regex(before, ids[i]@) == model::lift_regex(after, ids[i]@) by {
                model::lemma_lift_regex_stable(before, after, ids[i]@);
            }
        }
    }

    pub open spec fn interp_set_result(g: model::Graph, before: Seq<RegexId>, after: Seq<RegexId>, count: nat, intersect: bool) -> bool {
        count <= before.len() && forall|sym: model::Symbols, theta: Seq<Data>| model::symbols_wf(sym) ==>
            regex_stack_equiv(model::gsem(sym, theta), lifted_values(g, after),
                lifted_values(g, before.take(before.len() - count)).push(regex_fold(lifted_values(g, before.skip(before.len() - count)), intersect)))
    }

    pub open spec fn interp_machine_relation(before: model::Graph, after: model::Graph,
        tasks0: Seq<(TransitionId, bool)>, tasks1: Seq<(TransitionId, bool)>, values0: Seq<RegexId>, values1: Seq<RegexId>, atoms: Seq<TestId>, words: Seq<u64>) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            model::symbols_wf(sym) && truth_words_realize(before, atoms, words, sym, theta, event) ==>
                interp_results_equiv(model::gsem(sym, theta),
                    interp_run(before, tasks0, lifted_values(before, values0), sym, theta, event),
                    interp_run(after, tasks1, lifted_values(after, values1), sym, theta, event))
    }

    pub proof fn interp_same_configuration_extends(before: model::Graph, after: model::Graph,
        tasks: Seq<(TransitionId, bool)>, values: Seq<RegexId>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(before), model::graph_extends(before, after), interp_tasks_wf(before, tasks), norm::regex_ids_valid(before, values),
        ensures interp_tasks_wf(after, tasks),
            interp_run(before, tasks, lifted_values(before, values), sym, theta, event)
                == interp_run(after, tasks, lifted_values(after, values), sym, theta, event),
    {
        lifted_values_stable(before, after, values);
        interp_run_stable(before, after, tasks, lifted_values(before, values), sym, theta, event);
    }

    pub proof fn regex_fold_ids(g: model::Graph, ids: Seq<RegexId>, intersect: bool, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>)
        ensures norm::regex_combo(g, sym, theta, ids, word, intersect)
            == language::lang(model::gsem(sym, theta), regex_fold(lifted_values(g, ids), intersect), word),
    {
        let sem = model::gsem(sym, theta);
        let vals = lifted_values(g, ids);
        reveal(norm::regex_combo);
        regex_fold_semantics(sem, vals, intersect, word);
        assert forall|i: int| 0 <= i < ids.len() implies
            model::regex_lang(g, sym, theta, ids[i]@, word) == language::lang(sem, vals[i], word) by {}
        if !intersect {
            if norm::regex_combo(g, sym, theta, ids, word, false) {
                let i = choose|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, ids[i]@, word);
                assert(language::lang(sem, vals[i], word));
            }
            if language::lang(sem, regex_fold(vals, false), word) {
                let i = choose|i: int| 0 <= i < vals.len() && language::lang(sem, vals[i], word);
                assert(model::regex_lang(g, sym, theta, ids[i]@, word));
            }
        } else {
            if norm::regex_combo(g, sym, theta, ids, word, true) {
                assert forall|i: int| 0 <= i < vals.len() implies language::lang(sem, vals[i], word) by {
                    assert(model::regex_lang(g, sym, theta, ids[i]@, word));
                }
            }
            if language::lang(sem, regex_fold(vals, true), word) {
                assert forall|i: int| 0 <= i < ids.len() implies model::regex_lang(g, sym, theta, ids[i]@, word) by {
                    assert(language::lang(sem, vals[i], word));
                }
            }
        }
    }

    pub proof fn interp_value_reduction(g: model::Graph, id: TransitionId, finish: bool, tasks: Seq<(TransitionId, bool)>, before: Seq<InterpRegex>, after: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires interp_action(g, (id, finish), before, sym, theta, event) is Some,
            regex_stack_equiv(model::gsem(sym, theta), interp_action(g, (id, finish), before, sym, theta, event)->Some_0, after),
        ensures interp_results_equiv(model::gsem(sym, theta),
            interp_run(g, tasks.push((id, finish)), before, sym, theta, event), interp_run(g, tasks, after, sym, theta, event)),
    {
        assert(tasks.push((id, finish)).drop_last() =~= tasks);
        interp_run_unfold(g, tasks.push((id, finish)), before, sym, theta, event);
        interp_run_congruent(g, tasks, interp_action(g, (id, finish), before, sym, theta, event)->Some_0, after, sym, theta, event);
    }

    pub proof fn interp_expand_unary(g: model::Graph, id: TransitionId, inner: TransitionId, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::Not(inner@)
                || g.transitions[id@ as int] == model::TransitionNode::Append(inner@, transition_suffix(g, id)),
        ensures interp_run(g, tasks.push((id, false)), values, sym, theta, event)
            == interp_run(g, tasks.push((id, true)).push((inner, false)), values, sym, theta, event),
    {
        norm::transition_unfold(g, id@);
        let sem = model::gsem(sym, theta);
        let term = model::lift_transition(g, inner@);
        match g.transitions[id@ as int] {
            model::TransitionNode::Not(_) => language::lemma_interp_not(sem, event, term),
            model::TransitionNode::Append(_, cs) => language::lemma_interp_append(sem, event, term, model::lift_regexes(g, cs)),
            _ => {},
        }
        assert(tasks.push((id, false)).drop_last() =~= tasks);
        assert(tasks.push((id, true)).push((inner, false)).drop_last() =~= tasks.push((id, true)));
        assert(tasks.push((id, true)).drop_last() =~= tasks);
        assert(values.push(interpreted(g, inner, sym, theta, event)).drop_last() =~= values);
        interp_run_unfold(g, tasks.push((id, false)), values, sym, theta, event);
        interp_run_unfold(g, tasks.push((id, true)).push((inner, false)), values, sym, theta, event);
        interp_run_unfold(g, tasks.push((id, true)), values.push(interpreted(g, inner, sym, theta, event)), sym, theta, event);
    }

    pub proof fn interp_choose(g: model::Graph, id: TransitionId, finish: bool, test: TestId, a: TransitionId, b: TransitionId, chosen: TransitionId, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), id@ < g.transitions.len(), g.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
            chosen == if model::test_holds(sym, theta, model::lift_test(g, test@), event) { a } else { b },
        ensures interp_run(g, tasks.push((id, finish)), values, sym, theta, event)
            == interp_run(g, tasks.push((chosen, false)), values, sym, theta, event),
    {
        norm::transition_unfold(g, id@);
        language::lemma_interp_if(model::gsem(sym, theta), event, model::lift_test(g, test@), model::lift_transition(g, a@), model::lift_transition(g, b@));
        assert(tasks.push((id, finish)).drop_last() =~= tasks);
        assert(tasks.push((chosen, false)).drop_last() =~= tasks);
        interp_run_unfold(g, tasks.push((id, finish)), values, sym, theta, event);
        interp_run_unfold(g, tasks.push((chosen, false)), values, sym, theta, event);
    }

    pub proof fn interp_append_ids(g: model::Graph, ids: Seq<RegexId>, head: RegexId, suffix: Seq<nat>)
        requires model::regex_ids(ids) == seq![head@] + suffix,
        ensures lifted_values(g, ids) == seq![model::lift_regex(g, head@)] + model::lift_regexes(g, suffix),
    {
        reveal(model::regex_ids);
        assert(model::regex_ids(ids).len() == ids.len());
        assert(ids.len() == 1 + suffix.len());
        assert forall|i: int| 0 <= i < ids.len() implies lifted_values(g, ids)[i]
            == (seq![model::lift_regex(g, head@)] + model::lift_regexes(g, suffix))[i] by {
            assert(model::regex_ids(ids)[i] == ids[i]@);
            if i == 0 { assert(ids[i]@ == head@); }
            else { assert(ids[i]@ == suffix[i - 1]); }
        }
        assert(lifted_values(g, ids) =~= seq![model::lift_regex(g, head@)] + model::lift_regexes(g, suffix));
    }

    pub proof fn regex_not_language(sem: spec_fn(model::Test, Data) -> bool, child: InterpRegex, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Not(Box::new(child)), word) == !language::lang(sem, child, word),
    { norm::regex_language_unfold(sem, language::Regex::Not(Box::new(child)), word); }

    pub proof fn regex_concat_ids(g: model::Graph, ids: Seq<RegexId>)
        ensures model::lift_regexes(g, model::regex_ids(ids)) == lifted_values(g, ids),
    { assert(model::lift_regexes(g, model::regex_ids(ids)) =~= lifted_values(g, ids)); }


    pub proof fn interp_root_stable(before: model::Graph, after: model::Graph, root: TransitionId)
        requires model::graph_wf(before), model::graph_extends(before, after), root@ < before.transitions.len(),
        ensures model::lift_transition(before, root@) == model::lift_transition(after, root@),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_transition_stable(before, after, root@);
    }
        }
}

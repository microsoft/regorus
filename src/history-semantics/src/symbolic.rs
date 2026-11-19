// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Exact numeric symbolic derivatives and iterative transition-DAG interpretation.
//! Existing ID extension traits own cache lookup and branch execution; finish tasks
//! precede reverse child scheduling so each LIFO traversal preserves source order.
//! Error provenance is conditional on store capabilities; finishing tasks require completed dependencies.

use crate::WorkVec;
#[cfg(verus_keep_ghost)]
use crate::normalize::verify as norm;
use crate::normalize::{RegexNormalize, TransitionNormalize};
#[cfg(verus_keep_ghost)]
use crate::progress::verify as reach;
#[cfg(verus_keep_ghost)]
use crate::verify::finite_deriv as fder;
#[cfg(verus_keep_ghost)]
use crate::verify::finite_interp as fint;
#[cfg(verus_keep_ghost)]
use crate::verify::finite_trans as ftr;
#[cfg(verus_keep_ghost)]
use crate::verify::history_algebra as algebra;
#[cfg(verus_keep_ghost)]
use alloc::boxed::Box;
use alloc::vec::Vec;
use junco_core::bits::checked_shr;
use junco_core::errors::HistoryError;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::kernel::*;
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics::resource_error;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::KernelStoreSpec;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{EventView, Subst};
use junco_core::{loop_try, scan};
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;
}

#[verus_verify]
#[verus_spec(result => ensures language::no_invariant_failure(result), !(result matches Err(HistoryError::InvalidPolicy { .. })),
    result matches Err(error) ==> resource_error(error),
    match result {
        Ok(bytes) => bytes as int == count * vstd::layout::size_of::<Option<TransitionId>>(),
        Err(error) => error is AllocationFailed && count * vstd::layout::size_of::<Option<TransitionId>>() > usize::MAX,
    })]
fn derivative_cache_bytes(count: usize) -> KernelResult<usize> {
    vstd::layout::layout_for_type_is_valid::<Option<TransitionId>>();
    match count.checked_mul(core::mem::size_of::<Option<TransitionId>>()) {
        Some(bytes) => Ok(bytes),
        None => Err(HistoryError::AllocationFailed),
    }
}

#[cfg(test)]
#[test]
fn derivative_cache_byte_overflow_is_allocation_failure() {
    let width = core::mem::size_of::<Option<TransitionId>>();
    assert!(width > 1);
    let largest = usize::MAX / width;
    assert_eq!(derivative_cache_bytes(largest), Ok(largest * width));
    assert_eq!(
        derivative_cache_bytes(largest + 1),
        Err(HistoryError::AllocationFailed)
    );
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
struct DerivativeFactors {
    root: RegexId,
    count: usize,
    concat: bool,
}
impl DerivativeFactors {
    #[verus_verify]
    #[verus_spec(result =>
        requires model::graph_wf(store.graph()), derivative_factors_wf(store.graph(), self.root, self.count as nat, self.concat),
            derivative_tasks_wf(store.graph(), old(tasks).view()),
        ensures derivative_tasks_wf(store.graph(), final(tasks).view()),
            store.errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            store.errors_are_non_invariant() && store.valid_store() ==> language::no_invariant_failure(result),
            store.errors_are_resource() && store.valid_store() ==> (result matches Err(error) ==> resource_error(error)),
            store.errors_are_non_invalid_policy() && store.valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(tasks).view().is_prefix_of(final(tasks).view()),
            final(tasks).view().len() <= old(tasks).view().len() + self.count,
            result is Ok && !self.concat ==> final(tasks).view().len() == old(tasks).view().len() + self.count,
            result is Ok ==> forall|i: nat| i < self.count && (!self.concat || #[trigger] derivative_prefix(store.graph(), self.root, i))
                ==> old(tasks).view().len() + i < final(tasks).view().len(),
            forall|j: int| #![trigger final(tasks).view()[j]] old(tasks).view().len() <= j < final(tasks).view().len() ==> final(tasks).view()[j].0@
                == derivative_children_ids(store.graph(), self.root)[j - old(tasks).view().len()] && !final(tasks).view()[j].1,
    )]
    fn schedule<G: KernelStore>(
        self,
        store: &G,
        tasks: &mut WorkVec<(RegexId, bool)>,
    ) -> KernelResult<()> {
        proof! { model::lemma_graph_regex_wf(store.graph(), self.root@); }
        let mut prefix = true;
        let mut failure = None;
        let mut i = 0;
        proof_decl! { let ghost start = tasks.view(); }
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant i <= self.count, derivative_tasks_wf(store.graph(), tasks.view()),
            model::graph_wf(store.graph()), derivative_factors_wf(store.graph(), self.root, self.count as nat, self.concat),
            store.errors_are_non_owner() ==> failure != Some(HistoryError::WrongHistoryOwner),
            store.errors_are_non_invariant() && store.valid_store() ==> (failure matches Some(error) ==> language::no_invariant_failure::<()>(Err(error))),
            store.errors_are_resource() && store.valid_store() ==> (failure matches Some(error) ==> resource_error(error)),
            store.errors_are_non_invalid_policy() && store.valid_store() ==> !(failure matches Some(HistoryError::InvalidPolicy { .. })),
            model::regex_node_wf_at(store.graph(), store.graph().regexes[self.root@ as int], self.root@),
            prefix == derivative_prefix(store.graph(), self.root, i as nat),
            start == old(tasks).view(), start.is_prefix_of(tasks.view()),
            tasks.view().len() <= start.len() + self.count,
            forall|j: int| #![trigger tasks.view()[j]] start.len() <= j < tasks.view().len() ==> tasks.view()[j].0@
                == derivative_children_ids(store.graph(), self.root)[j - start.len()] && !tasks.view()[j].1,
            forall|j: nat| j < i && (!self.concat || #[trigger] derivative_prefix(store.graph(), self.root, j))
                ==> start.len() + j < tasks.view().len(),
            invariant_except_break failure is None, tasks.view().len() <= start.len() + i,
                (!self.concat || prefix) ==> tasks.view().len() == start.len() + i,
            ensures failure is None ==> i == self.count
                && tasks.view().len() <= start.len() + self.count,
            failure is None && !self.concat ==> tasks.view().len() == start.len() + self.count,
            failure is None ==> forall|j: nat| j < self.count
                && (!self.concat || #[trigger] derivative_prefix(store.graph(), self.root, j))
                ==> start.len() + j < tasks.view().len(),
            decreases self.count - i))]
        while i < self.count {
            let child = loop_try!(self.root.child(store, i), failure);
            proof_decl! { let ghost prior = tasks.view(); }
            if !self.concat || prefix {
                tasks.push((child, false));
            }
            proof! {
                assert forall|j: int| #![trigger tasks.view()[j]] start.len() <= j < tasks.view().len() implies tasks.view()[j].0@
                    == derivative_children_ids(store.graph(), self.root)[j - start.len()] && !tasks.view()[j].1 by {
                    if j < prior.len() { assert(tasks.view()[j] == prior[j]); } else {
                        assert(j == start.len() + i);
                        assert(child@ == derivative_children_ids(store.graph(), self.root)[i as int]);
                    }
                }
            }
            let n = loop_try!(RegexId::nullable(child, store), failure);
            prefix &= n;
            i = i.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        proof! {
            assert(start == old(tasks).view());
            assert(i == self.count);
            if !self.concat { assert(tasks.view().len() == start.len() + self.count); }
            assert forall|j: nat| j < self.count
                && (!self.concat || #[trigger] derivative_prefix(store.graph(), self.root, j))
                implies old(tasks).view().len() + j < tasks.view().len() by {}
        }
        Ok(())
    }
    #[verus_verify]
    #[verus_spec(result =>
        requires model::graph_wf(store.graph()), start <= self.count,
            self.root@ < store.graph().regexes.len(), self.count == derivative_children_ids(store.graph(), self.root).len(),
        ensures store.errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            store.errors_are_non_invariant() && store.valid_store() ==> language::no_invariant_failure(result),
            store.errors_are_resource() && store.valid_store() ==> (result matches Err(error) ==> resource_error(error)),
            store.errors_are_non_invalid_policy() && store.valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            match result { Ok(suffix) =>
            norm::regex_ids_valid(store.graph(), suffix.view())
            && model::regex_ids(suffix.view()) == derivative_children_ids(store.graph(), self.root).subrange(start as int, self.count as int),
            Err(_) => true },
    )]
    fn suffix<G: KernelStore>(self, store: &G, start: usize) -> KernelResult<WorkVec<RegexId>> {
        proof! { model::lemma_graph_regex_wf(store.graph(), self.root@); }
        let mut suffix = WorkVec::new();
        let mut failure = None;
        let mut i = start;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant start <= i <= self.count,
            model::graph_wf(store.graph()), self.root@ < store.graph().regexes.len(),
            store.errors_are_non_owner() ==> failure != Some(HistoryError::WrongHistoryOwner),
            store.errors_are_non_invariant() && store.valid_store() ==> (failure matches Some(error) ==> language::no_invariant_failure::<()>(Err(error))),
            store.errors_are_resource() && store.valid_store() ==> (failure matches Some(error) ==> resource_error(error)),
            store.errors_are_non_invalid_policy() && store.valid_store() ==> !(failure matches Some(HistoryError::InvalidPolicy { .. })),
            self.count == derivative_children_ids(store.graph(), self.root).len(),
            model::regex_node_wf_at(store.graph(), store.graph().regexes[self.root@ as int], self.root@),
            norm::regex_ids_valid(store.graph(), suffix.view()),
            suffix.view().len() == i - start,
            forall|j: int| 0 <= j < suffix.view().len() ==> suffix.view()[j]@ == derivative_children_ids(store.graph(), self.root)[start as int + j],
            ensures failure.is_none() ==> i == self.count, decreases self.count - i))]
        while i < self.count {
            proof_decl! { let ghost prior_suffix = suffix.view(); }
            let child = loop_try!(self.root.child(store, i), failure);
            suffix.push(child);
            proof! {
                assert(child@ == derivative_children_ids(store.graph(), self.root)[i as int]);
                assert(suffix.view() == prior_suffix.push(child));
                assert forall|j: int| 0 <= j < suffix.view().len() implies
                    model::regex_ids(suffix.view())[j] == derivative_children_ids(store.graph(), self.root)[start as int + j] by {
                    if j < prior_suffix.len() {
                        assert(suffix.view()[j] == prior_suffix[j]);
                        assert(prior_suffix[j]@ == derivative_children_ids(store.graph(), self.root)[start as int + j]);
                    } else { assert(suffix.view()[j] == child); assert(start + j == i); }
                }
                assert(model::regex_ids(suffix.view()) =~= derivative_children_ids(store.graph(), self.root).subrange(start as int, i as int + 1));
            }
            i = i.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        proof! {
            assert(model::regex_ids(suffix.view()) =~= derivative_children_ids(store.graph(), self.root).subrange(start as int, self.count as int));
        }
        Ok(suffix)
    }
    #[verus_verify]
    #[verus_spec(result =>
        requires model::graph_wf(old(store).graph()), old(store).valid_store(),
            derivative_cache_wf(old(store).graph(), cache@),
            derivative_factors_wf(old(store).graph(), self.root, self.count as nat, self.concat), index < self.count,
            derivative_results(old(store).graph(), self.root, self.concat, index as nat, old(results).view()),
            prefix == derivative_prefix(old(store).graph(), self.root, index as nat),
            fder::results_bound(old(store).graph(), self.root@, old(results).view()),
            derivative_results_vocab(old(store).graph(), self.root@, old(results).view()),
        ensures model::graph_extends(old(store).graph(), final(store).graph()),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && derivative_dependencies_complete(old(store).graph(), self.root, cache@) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store()
                && derivative_dependencies_complete(old(store).graph(), self.root, cache@)
                ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            model::graph_wf(final(store).graph()), final(store).valid_store(),
            derivative_cache_wf(final(store).graph(), cache@),
            derivative_dependencies_complete(old(store).graph(), self.root, cache@)
                == derivative_dependencies_complete(final(store).graph(), self.root, cache@),
            match result { Ok(next) => next == derivative_prefix(final(store).graph(), self.root, index as nat + 1)
                && derivative_results(final(store).graph(), self.root, self.concat, index as nat + 1, final(results).view())
                && fder::results_bound(final(store).graph(), self.root@, final(results).view()), Err(_) => true },
            result is Ok ==> derivative_results_vocab(final(store).graph(), self.root@, final(results).view()),
    )]
    fn child_step<G: KernelStore>(
        self,
        store: &mut G,
        cache: &[Option<TransitionId>],
        index: usize,
        results: &mut WorkVec<TransitionId>,
        prefix: bool,
    ) -> KernelResult<bool> {
        proof_decl! { let ghost before = store.graph(); let ghost prior_results = results.view(); }
        proof! { derivative_frame(store.graph()); model::lemma_graph_regex_wf(store.graph(), self.root@); }
        proof! { derivative_dependency_frame(store.graph(), self.root); }
        store.checkpoint()?;
        let child = self.root.child(store, index)?;
        if !self.concat || prefix {
            proof! {
                assert(derivative_children_ids(store.graph(), self.root)[index as int] == child@);
                assert(derivative_dependency(store.graph(), self.root, child@));
            }
            let d = RegexId::cached(cache, child)?;
            proof! {
                derivative_cached_bound(store.graph(), cache@, child, d);
                lemma_regex_graph_child_vocab(store.graph(), self.root@, child@);
            }
            if self.concat {
                let start = match index.checked_add(1) {
                    Some(v) => v,
                    None => return Err(HistoryError::symbolic_invariant()),
                };
                let suffix = self.suffix(store, start)?;
                proof_decl! { let ghost mid = store.graph(); }
                results.push(TransitionId::append(d, store, &suffix)?);
                proof! {
                    derivative_append_factor(store.graph(), self.root, index as int, d, suffix.view(), results.view().last());
                    derivative_results_push(store.graph(), self.root, true, index as nat, prior_results, results.view().last());
                    fder::lemma_factor_concat2(mid, store.graph(), self.root@, index as int, d@, suffix.view(), results.view().last()@);
                    fder::lemma_results_stable(before, store.graph(), self.root@, prior_results);
                    fder::lemma_results_push(store.graph(), self.root@, prior_results, results.view().last());
                    lemma_derivative_vocab_stable(mid, store.graph(), child@, d@);
                    lemma_regex_graph_child_vocab(store.graph(), self.root@, child@);
                    norm::lemma_guard_definition(store.graph(), d@);
                    norm::lemma_guard_definition(store.graph(), results.view().last()@);
                    assert(derivative_vocab(store.graph(), self.root@, results.view().last()@));
                    lemma_derivative_results_vocab_stable(before, store.graph(), self.root@, prior_results);
                    assert(derivative_results_vocab(store.graph(), self.root@, results.view()));
                }
            } else {
                results.push(d);
                proof! {
                    derivative_results_push(store.graph(), self.root, false, index as nat, prior_results, d);
                    fder::lemma_factor_set(store.graph(), self.root@, index as int, d@);
                    fder::lemma_results_stable(before, store.graph(), self.root@, prior_results);
                    fder::lemma_results_push(store.graph(), self.root@, prior_results, d);
                    assert(derivative_vocab(store.graph(), self.root@, d@));
                    assert(derivative_results_vocab(store.graph(), self.root@, results.view()));
                }
            }
        }
        proof! {
            if self.concat && !prefix {
                derivative_results_skip(store.graph(), self.root, index as nat, results.view());
                fder::lemma_results_stable(before, store.graph(), self.root@, results.view());
                lemma_derivative_results_vocab_stable(before, store.graph(), self.root@, results.view());
            }
        }
        let n = RegexId::nullable(child, store)?;
        Ok(prefix && n)
    }
    verus! {
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(120))]
    #[verus_spec(result =>
        requires model::graph_wf(old(store).graph()), old(store).valid_store(),
            derivative_cache_wf(old(store).graph(), cache@),
            derivative_factors_wf(old(store).graph(), self.root, self.count as nat, self.concat),
            match old(store).graph().regexes[self.root@ as int].kind {
                model::RegexKindNode::Union(_) => !self.concat && !intersect,
                model::RegexKindNode::Intersect(_) => !self.concat && intersect,
                model::RegexKindNode::Concat(_) => self.concat && !intersect,
                _ => false,
            },
        ensures model::graph_extends(old(store).graph(), final(store).graph()),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && derivative_dependencies_complete(old(store).graph(), self.root, cache@) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store()
                && derivative_dependencies_complete(old(store).graph(), self.root, cache@)
                ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            model::graph_wf(final(store).graph()), final(store).valid_store(),
            derivative_cache_wf(final(store).graph(), cache@),
            match result { Ok(out) => derivative_correct(final(store).graph(), self.root@, out)
                && fder::dbound(final(store).graph(), self.root@, out@)
                && derivative_vocab(final(store).graph(), self.root@, out@), Err(_) => true },
    )]
    fn derive<G: KernelStore>(
        self,
        store: &mut G,
        cache: &[Option<TransitionId>],
        intersect: bool,
    ) -> KernelResult<TransitionId> {
        hide(Seq::<_>::no_duplicates);
        hide(model::unique_nodes);
        hide(model::tables_wf);
        proof_decl! { let ghost entry = store.graph(); }
        proof! { derivative_frame(store.graph()); fder::lemma_results_empty(store.graph(), self.root@); }
        proof! { derivative_dependency_frame(entry, self.root); }
        let mut results = WorkVec::new();
        let mut state = Ok(true);
        scan!(state,index,self.count,state.is_ok(),prior=>self.child_step(store,cache,index,&mut results,prior);
            invariant index <= self.count, model::graph_extends(entry, store.graph()), model::graph_wf(store.graph()), store.valid_store(),
                store.restoration() == old(store).restoration(),
                store.errors_are_non_owner() == old(store).errors_are_non_owner(),
                store.errors_are_non_invariant() == old(store).errors_are_non_invariant(),
                store.errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
                store.errors_are_resource() == old(store).errors_are_resource(),
                old(store).errors_are_non_invalid_policy() ==> !(state matches Err(HistoryError::InvalidPolicy { .. })),
                old(store).errors_are_non_invariant() && derivative_dependencies_complete(entry, self.root, cache@) ==> language::no_invariant_failure(state),
                old(store).errors_are_resource() && old(store).valid_store()
                    && derivative_dependencies_complete(entry, self.root, cache@)
                    ==> (state matches Err(error) ==> resource_error(error)),
                old(store).errors_are_non_owner() ==> state != Err(HistoryError::WrongHistoryOwner),
                model::graph_wf(entry), self.root@ < entry.regexes.len(),
                derivative_cache_wf(store.graph(), cache@), derivative_factors_wf(store.graph(), self.root, self.count as nat, self.concat),
                store.graph().regexes[self.root@ as int] == entry.regexes[self.root@ as int],
                derivative_dependencies_complete(entry, self.root, cache@) == derivative_dependencies_complete(store.graph(), self.root, cache@),
                match state { Ok(prefix) => prefix == derivative_prefix(store.graph(), self.root, index as nat)
                    && derivative_results(store.graph(), self.root, self.concat, index as nat, results.view())
                    && fder::results_bound(store.graph(), self.root@, results.view()), Err(_) => true },
                state is Ok ==> derivative_results_vocab(store.graph(), self.root@, results.view()),
            decreases self.count - index);
        state?;
        proof! {
            derivative_frame(store.graph());
            derivative_result_future(store.graph(), self.root, self.concat, intersect, results.view());
            fder::lemma_derive_future(store.graph(), self.root@, results.view(), intersect);
        }
        proof! {
            assert forall|i: int| 0 <= i < results.view().len() implies norm::guard_vocab(store.graph(), results.view()[i]@).subset_of(
                regex_primitives(model::lift_regex(store.graph(), self.root@))) by {
                norm::lemma_guard_definition(store.graph(), results.view()[i]@);
            }
            norm::lemma_guard_union(store.graph(), model::transition_ids(results.view()), regex_primitives(model::lift_regex(store.graph(), self.root@)));
        }
        proof_decl! { let ghost before_collect = store.graph(); }
        let out = if intersect {
            TransitionId::intersect(store, &results)
        } else {
            TransitionId::collect(store, &results, false)
        }?;
        proof! {
            model::lemma_graph_wf_elim(entry);
            model::lemma_lift_regex_stable(entry, store.graph(), self.root@);
            model::lemma_graph_wf_elim(before_collect);
            model::lemma_lift_regex_stable(before_collect, store.graph(), self.root@);
            norm::lemma_guard_task_stable(before_collect, store.graph(),
                norm::ActionShape::Fold(model::transition_ids(results.view()), 0));
            norm::lemma_guard_subset(store.graph(), out@, regex_primitives(model::lift_regex(store.graph(), self.root@)));
        }
        Ok(out)
    }
    }
    // `cache@` is specified as a `Vec` view; a slice parameter would change every caller's contract.
    #[allow(clippy::ptr_arg)]
    #[verus_verify]
    #[verus_spec(result =>
        requires model::graph_wf(old(store).graph()), old(store).valid_store(),
            derivative_cache_wf(old(store).graph(), old(cache)@), derivative_tasks_wf(old(store).graph(), old(tasks).view()),
            self.root@ < old(store).graph().regexes.len(),
            match old(store).graph().regexes[self.root@ as int].kind {
                model::RegexKindNode::Union(cs) => !self.concat && !intersect && cs.len() == self.count,
                model::RegexKindNode::Intersect(cs) => !self.concat && intersect && cs.len() == self.count,
                model::RegexKindNode::Concat(cs) => self.concat && !intersect && cs.len() == self.count,
                _ => false,
            },
        ensures model::graph_extends(old(store).graph(), final(store).graph()),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && (!finish || derivative_dependencies_complete(old(store).graph(), self.root, old(cache)@)) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store()
                && (!finish || derivative_dependencies_complete(old(store).graph(), self.root, old(cache)@))
                ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            model::graph_wf(final(store).graph()), final(store).valid_store(), final(cache)@ == old(cache)@,
            derivative_cache_wf(final(store).graph(), final(cache)@), derivative_tasks_wf(final(store).graph(), final(tasks).view()),
            match result { Ok(Some(out)) => derivative_correct(final(store).graph(), self.root@, out)
                && out@ < final(store).graph().transitions.len()
                && fder::dbound(final(store).graph(), self.root@, out@)
                && derivative_vocab(final(store).graph(), self.root@, out@), _ => true },
            result matches Ok(Some(_)) ==> final(tasks).view() == old(tasks).view(),
            old(tasks).view().is_prefix_of(final(tasks).view()),
            forall|bound: nat| self.root@ <= bound && derivative_tasks_bounded(old(tasks).view(), bound)
                ==> derivative_tasks_bounded(final(tasks).view(), bound),
            result == Ok(None) ==> derivative_scheduled(old(store).graph(), self.root, old(tasks).view(), final(tasks).view()),
            result is Ok ==> final(tasks).view() == old(tasks).view()
                || (derivative_tasks_wf(old(store).graph(), final(tasks).view())
                    && derivative_work(old(store).graph(), final(tasks).view())
                        < derivative_work(old(store).graph(), old(tasks).view().push((self.root, finish)))),
    )]
    fn branch<G: KernelStore>(
        self,
        store: &mut G,
        cache: &mut Vec<Option<TransitionId>>,
        intersect: bool,
        finish: bool,
        tasks: &mut WorkVec<(RegexId, bool)>,
    ) -> KernelResult<Option<TransitionId>> {
        proof! { derivative_frame(store.graph()); model::lemma_graph_regex_wf(store.graph(), self.root@); }
        if finish {
            Ok(Some(self.derive(store, cache, intersect)?))
        } else {
            tasks.push((self.root, true));
            proof_decl! { let ghost scheduled_from = tasks.view(); }
            proof! { assert(scheduled_from == old(tasks).view().push((self.root, true))); }
            let scheduled = self.schedule(store, tasks);
            proof! {
                broadcast use vstd::seq::group_seq_lemmas;
                assert(scheduled_from.is_prefix_of(tasks.view()));
                assert forall|j: int| 0 <= j < scheduled_from.len()
                    implies tasks.view()[j] == scheduled_from[j] by {}
                assert forall|bound: nat| self.root@ <= bound && derivative_tasks_bounded(old(tasks).view(), bound)
                    implies derivative_tasks_bounded(tasks.view(), bound) by {
                    assert forall|j: int| 0 <= j < tasks.view().len() implies tasks.view()[j].0@ <= bound by {
                        if j < old(tasks).view().len() {
                            assert(scheduled_from[j] == old(tasks).view()[j]);
                            assert(tasks.view()[j] == scheduled_from[j]);
                            assert(tasks.view()[j] == old(tasks).view()[j]);
                        } else if j == old(tasks).view().len() {
                            assert(scheduled_from[j] == (self.root, true));
                            assert(tasks.view()[j] == scheduled_from[j]);
                            assert(tasks.view()[j].0 == self.root);
                        } else {
                            let i = j - old(tasks).view().len() - 1;
                            assert(0 <= i < self.count);
                            assert(i < derivative_children_ids(store.graph(), self.root).len());
                            assert(tasks.view()[j].0@ == derivative_children_ids(store.graph(), self.root)[i]);
                        }
                    }
                }
            }
            scheduled?;
            proof! {
                broadcast use vstd::seq::group_seq_lemmas;
                derivative_lemma_work_branch(store.graph(), self.root, old(tasks).view(), tasks.view());
                assert(old(tasks).view() =~= tasks.view().take(old(tasks).view().len() as int));
                assert(scheduled_from[old(tasks).view().len() as int] == (self.root, true));
                assert(tasks.view()[old(tasks).view().len() as int]
                    == scheduled_from[old(tasks).view().len() as int]);
                assert(tasks.view()[old(tasks).view().len() as int] == (self.root, true));
                assert forall|i: int| old(tasks).view().len() < i < tasks.view().len()
                    implies !tasks.view()[i].1 by {}
                assert forall|child: nat| derivative_dependency(store.graph(), self.root, child)
                    implies exists|j: int| old(tasks).view().len() < j < tasks.view().len() && tasks.view()[j].0@ == child by {
                    let i = choose|i: int| 0 <= i < self.count && derivative_children_ids(store.graph(), self.root)[i] == child
                        && (!self.concat || derivative_prefix(store.graph(), self.root, i as nat));
                    let j = old(tasks).view().len() + 1 + i;
                    if self.concat {
                        assert(derivative_prefix(store.graph(), self.root, i as nat));
                        assert(scheduled_from.len() + (i as nat) < tasks.view().len());
                    } else {
                        assert(tasks.view().len() == scheduled_from.len() + self.count);
                    }
                    assert(scheduled_from.len() + i < tasks.view().len());
                    assert(tasks.view()[j].0@ == derivative_children_ids(store.graph(), self.root)[i]);
                    assert(tasks.view()[j].0@ == child);
                }
            }
            Ok(None)
        }
    }
}
verus! {
pub(crate) trait RegexDerivative: Sized {
    fn cached(cache: &[Option<TransitionId>], id: RegexId) -> (result: KernelResult<TransitionId>)
        ensures match result {
            Ok(out) => id@ < cache@.len() && cache@[id@ as int] == Some(out), Err(_) => true,
        },
            result != Err(HistoryError::WrongHistoryOwner),
            cache_complete(cache@, id@) ==> language::no_invariant_failure(result),
            cache_complete(cache@, id@) ==> (result matches Err(error) ==> resource_error(error)),
            !(result matches Err(HistoryError::InvalidPolicy { .. })),
    {
        match cache.get(id.index()?) {
            Some(Some(value)) => Ok(*value),
            _ => Err(HistoryError::symbolic_invariant()),
        }
    }

    fn derivative_step<G: KernelStore>(
        this: RegexId,
        store: &mut G,
        cache: &mut Vec<Option<TransitionId>>,
        finish: bool,
        tasks: &mut WorkVec<(RegexId, bool)>,
    ) -> (result: KernelResult<()>)
        requires model::graph_wf(old(store).graph()), old(store).valid_store(), this@ < old(store).graph().regexes.len(),
            derivative_cache_wf(old(store).graph(), old(cache)@), derivative_tasks_wf(old(store).graph(), old(tasks).view()),
        ensures model::graph_extends(old(store).graph(), final(store).graph()),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && this@ < usize::MAX && (!finish || derivative_dependencies_complete(old(store).graph(), this, old(cache)@)) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && this@ < usize::MAX
                && (!finish || derivative_dependencies_complete(old(store).graph(), this, old(cache)@))
                ==> (result matches Err(error) ==> resource_error(error)),
            cache_completions_preserved(old(cache)@, final(cache)@),
            old(cache)@.len() <= final(cache)@.len(),
            forall|i: int| #![trigger final(cache)@[i]]
                0 <= i < old(cache)@.len() && old(cache)@[i] is Some
                ==> i < final(cache)@.len() && final(cache)@[i] == old(cache)@[i],
            old(tasks).view().is_prefix_of(final(tasks).view()),
            forall|bound: nat| this@ <= bound && derivative_tasks_bounded(old(tasks).view(), bound)
                ==> derivative_tasks_bounded(final(tasks).view(), bound),
            result is Ok ==> cache_complete(final(cache)@, this@) || tasks_contain(final(tasks).view(), this@),
            derivative_tasks_ready(old(store).graph(), old(tasks).view().push((this, finish)), old(cache)@) && result is Ok
                ==> derivative_tasks_ready(final(store).graph(), final(tasks).view(), final(cache)@),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            model::graph_wf(final(store).graph()), final(store).valid_store(),
            derivative_cache_wf(final(store).graph(), final(cache)@), derivative_tasks_wf(final(store).graph(), final(tasks).view()),
            result is Ok ==> derivative_work(final(store).graph(), final(tasks).view())
                < derivative_work(old(store).graph(), old(tasks).view().push((this, finish)));

    fn derivative<G: KernelStore>(
        this: RegexId,
        store: &mut G,
        cache: &mut Vec<Option<TransitionId>>,
    ) -> (result: KernelResult<TransitionId>)
        requires model::graph_wf(old(store).graph()), old(store).valid_store(), this@ < old(store).graph().regexes.len(),
            derivative_cache_wf(old(store).graph(), old(cache)@),
        ensures model::graph_extends(old(store).graph(), final(store).graph()),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && this@ < usize::MAX ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && this@ < usize::MAX
                ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            model::graph_wf(final(store).graph()), final(store).valid_store(),
            derivative_cache_wf(final(store).graph(), final(cache)@),
            old(cache)@.len() <= final(cache)@.len(),
            forall|i: int| #![trigger final(cache)@[i]]
                0 <= i < old(cache)@.len() && old(cache)@[i] is Some
                ==> i < final(cache)@.len() && final(cache)@[i] == old(cache)@[i],
            result matches Ok(out) ==> this@ < final(cache)@.len() && final(cache)@[this@ as int] == Some(out),
            match result { Ok(out) => derivative_correct(final(store).graph(), this@, out)
                && fder::dbound(final(store).graph(), this@, out@), Err(_) => true };
}
}

verus! {
fn grow_derivative_cache<G: KernelStore>(
    this: RegexId, store: &mut G, cache: &mut Vec<Option<TransitionId>>,
) -> (result: KernelResult<()>)
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        derivative_cache_wf(old(store).graph(), old(cache)@),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
        final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
        final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
        final(store).errors_are_resource() == old(store).errors_are_resource(),
        old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
        old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
        old(store).errors_are_non_invariant() && this@ < usize::MAX ==> language::no_invariant_failure(result),
        old(store).errors_are_resource() && old(store).valid_store() && this@ < usize::MAX
            ==> (result matches Err(error) ==> resource_error(error)),
        derivative_cache_wf(final(store).graph(), final(cache)@),
        old(cache)@.is_prefix_of(final(cache)@),
        forall|i: int| 0 <= i < old(cache)@.len() ==> final(cache)@[i] == old(cache)@[i],
        forall|i: int| old(cache)@.len() <= i < final(cache)@.len() ==> final(cache)@[i] is None,
        result is Err ==> final(cache)@ == old(cache)@,
        result is Ok ==> this@ < final(cache)@.len()
            && final(cache)@.len() == if old(cache)@.len() > this@ { old(cache)@.len() } else { this@ + 1 },
{
    hide(derivative_cache_wf); hide(derivative_correct);
    let ghost before = cache@;
    store.checkpoint()?;
    let required = match this.index()?.checked_add(1) {
        Some(value) => value,
        None => return Err(HistoryError::symbolic_invariant()),
    };
    if required > cache.len() {
        let extra = match required.checked_sub(cache.len()) {
            Some(value) => value,
            None => return Err(HistoryError::symbolic_invariant()),
        };
        let bytes = derivative_cache_bytes(extra)?;
        store.reserve_derivatives(cache, extra)?;
        store.charge_aux(bytes)?;
        cache.resize(required, None);
    }
    proof {
        derivative_cache_prefix_facts(before, cache@);
        reveal(derivative_cache_wf);
        assert forall|i: int| 0 <= i < cache@.len() implies match #[trigger] cache@[i] {
            Some(out) => derivative_correct(store.graph(), i as nat, out) && fder::dbound(store.graph(), i as nat, out@)
                && derivative_vocab(store.graph(), i as nat, out@), None => true,
        } by {
            if i < before.len() { assert(cache@[i] == before[i]); }
            else { assert(cache@[i] is None); }
        }
    }
    Ok(())
}

impl RegexDerivative for RegexId {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(160))]
    fn derivative_step<G: KernelStore>(
        this: RegexId,
        store: &mut G,
        cache: &mut Vec<Option<TransitionId>>,
        finish: bool,
        tasks: &mut WorkVec<(RegexId, bool)>,
    ) -> KernelResult<()> {
        hide(Seq::<_>::no_duplicates);
        hide(resource_error);
        hide(derivative_cache_wf); hide(derivative_tasks_wf);
        hide(derivative_correct);
        hide(derivative_tasks_ready); hide(derivative_scheduled);
        hide(derivative_dependencies_complete); hide(derivative_dependency);
        hide(vstd::seq::lemma_seq_subrange_index);
        hide(vstd::seq::lemma_seq_two_subranges_index);
        proof_decl! { let ghost before = store.graph(); let ghost prior_tasks = tasks.view(); }
        proof! {
            assert forall|i: int| 0 <= i < prior_tasks.len() implies prior_tasks.subrange(0, prior_tasks.len() as int)[i] == prior_tasks[i] by {
                vstd::seq::lemma_seq_subrange_index(prior_tasks, 0, prior_tasks.len() as int, i);
            }
            assert(prior_tasks =~= prior_tasks.subrange(0, prior_tasks.len() as int));
            assert(prior_tasks.is_prefix_of(prior_tasks));
        }
        proof! { norm::graph_lemma_extends_refl(store.graph()); }
        proof! {
            derivative_frame(store.graph()); model::lemma_graph_regex_wf(store.graph(), this@); derivative_constants(store.graph());
        }
        proof_decl! { let ghost cache_before = cache@; let ghost growth_graph = store.graph(); }
        grow_derivative_cache(this, store, cache)?;
        proof! {
            if derivative_dependencies_complete(before, this, cache_before) {
                derivative_cache_extend_dependencies(before, this, cache_before, cache@);
            }
        }
        let index = this.index()?;
        let pending = match cache.get(index) {
            Some(None) => true,
            Some(Some(_)) => false,
            None => return Err(HistoryError::symbolic_invariant()),
        };
        if pending {
            let c = store.constants();
            proof! {
                fder::lemma_native_future(store.graph(), this, cache@);
            }
            let out = match this.head(store)? {
                RegexHead::Empty | RegexHead::Epsilon => {
                    proof! {
                        norm::lemma_guard_constants(store.graph());
                        norm::lemma_guard_definition(store.graph(), c.transition_empty@);
                        assert(derivative_vocab(store.graph(), this@, c.transition_empty@));
                    }
                    proof! { derivative_native_correct(store.graph(), this, cache@, c.transition_empty); }
                    Some(c.transition_empty)
                }
                RegexHead::All => {
                    proof! {
                        norm::lemma_guard_constants(store.graph());
                        norm::lemma_guard_definition(store.graph(), c.transition_all@);
                        assert(derivative_vocab(store.graph(), this@, c.transition_all@));
                    }
                    proof! { derivative_native_correct(store.graph(), this, cache@, c.transition_all); }
                    Some(c.transition_all)
                }
                RegexHead::Test(test) => {
                    let out = TransitionId::if_then_else(store, test, c.transition_epsilon, c.transition_empty)?;
                    proof! { derivative_graph_frame(growth_graph, store.graph(), this); }
                    proof! {
                        norm::lemma_guard_constants(store.graph());
                        norm::lemma_test_definition(store.graph(), test@);
                        norm::lemma_guard_definition(store.graph(), out@);
                        norm::regex_unfold(store.graph(), this@);
                        assert(derivative_vocab(store.graph(), this@, out@));
                    }
                    proof! { derivative_test_correct(store.graph(), this, test, cache@, out, c.transition_epsilon, c.transition_empty); }
                    Some(out)
                }
                RegexHead::Star(inner) => {
                    if finish {
                        proof! {
                            if derivative_dependencies_complete(before, this, cache_before) {
                                derivative_unary_complete(before, this, inner, cache@);
                            }
                        }
                        let d = Self::cached(cache, inner)?;
                        proof_decl! { let ghost before_append = store.graph(); }
                        proof! { derivative_cached_bound(store.graph(), cache@, inner, d); }
                        let out = TransitionId::append(d, store, &[this])?;
                        proof! { derivative_graph_frame(growth_graph, store.graph(), this); }
                        proof! {
                            lemma_derivative_vocab_stable(before_append, store.graph(), inner@, d@);
                            lemma_regex_graph_child_vocab(store.graph(), this@, inner@);
                            norm::lemma_guard_definition(store.graph(), d@);
                            norm::lemma_guard_definition(store.graph(), out@);
                            assert(derivative_vocab(store.graph(), this@, out@));
                        }
                        proof! { derivative_native_correct(store.graph(), this, cache@, out); }
                        Some(out)
                    } else {
                        tasks.push((this, true));
                        proof! { derivative_unary_scheduled(before, this, prior_tasks, inner); }
                        tasks.push((inner, false));
                        proof! { derivative_lemma_work_unary(store.graph(), this, prior_tasks, inner); }
                        None
                    }
                }
                RegexHead::Not(inner) => {
                    if finish {
                        proof! {
                            if derivative_dependencies_complete(before, this, cache_before) {
                                derivative_unary_complete(before, this, inner, cache@);
                            }
                        }
                        let d = Self::cached(cache, inner)?;
                        proof_decl! { let ghost before_not = store.graph(); }
                        proof! { derivative_cached_bound(store.graph(), cache@, inner, d); }
                        let out = TransitionId::not(d, store)?;
                        proof! { derivative_graph_frame(growth_graph, store.graph(), this); }
                        proof! {
                            lemma_derivative_vocab_stable(before_not, store.graph(), inner@, d@);
                            lemma_regex_graph_child_vocab(store.graph(), this@, inner@);
                            norm::lemma_guard_definition(store.graph(), d@);
                            norm::lemma_guard_definition(store.graph(), out@);
                            assert(derivative_vocab(store.graph(), this@, out@));
                        }
                        proof! { derivative_native_correct(store.graph(), this, cache@, out); }
                        Some(out)
                    } else {
                        tasks.push((this, true));
                        proof! { derivative_unary_scheduled(before, this, prior_tasks, inner); }
                        tasks.push((inner, false));
                        proof! { derivative_lemma_work_unary(store.graph(), this, prior_tasks, inner); }
                        None
                    }
                }
                RegexHead::Union(n) => DerivativeFactors {
                    root: this,
                    count: n,
                    concat: false,
                }
                .branch(store, cache, false, finish, tasks)?,
                RegexHead::Intersect(n) => DerivativeFactors {
                    root: this,
                    count: n,
                    concat: false,
                }
                .branch(store, cache, true, finish, tasks)?,
                RegexHead::Concat(n) => DerivativeFactors {
                    root: this,
                    count: n,
                    concat: true,
                }
                .branch(store, cache, false, finish, tasks)?,
            };
            if let Some(out) = out {
                proof! {
                    assert(derivative_correct(store.graph(), this@, out));
                    derivative_graph_frame(growth_graph, store.graph(), this);
                    match growth_graph.regexes[this@ as int].kind {
                        model::RegexKindNode::Star(inner) => {
                            assert(inner < cache@.len() && cache@[inner as int] is Some);
                            assert(vstd::array::spec_array_as_slice(&[this])@ =~= seq![this]);
                            assert(fder::native_bound(growth_graph, store.graph(), this, cache@, out@));
                        },
                        model::RegexKindNode::Not(inner) => {
                            assert(inner < cache@.len() && cache@[inner as int] is Some);
                            assert(fder::native_bound(growth_graph, store.graph(), this, cache@, out@));
                        },
                        model::RegexKindNode::Test(_) => {
                            assert(fder::native_bound(growth_graph, store.graph(), this, cache@, out@));
                        },
                        _ => {
                            assert(fder::native_bound(growth_graph, store.graph(), this, cache@, out@));
                        },
                    }
                    assert(fder::dbound(store.graph(), this@, out@));
                    assert(derivative_vocab(store.graph(), this@, out@));
                }
                let slots = cache.as_mut_slice();
                match slots.get_mut(index) {
                    Some(slot) => *slot = Some(out),
                    None => return Err(HistoryError::symbolic_invariant()),
                }
                proof! {
                    assert(derivative_cache_wf(store.graph(), cache@)) by {
                        reveal(derivative_cache_wf);
                        assert forall|i: int| 0 <= i < cache@.len() implies match #[trigger] cache@[i] {
                            Some(t) => derivative_correct(store.graph(), i as nat, t) && fder::dbound(store.graph(), i as nat, t@)
                                && derivative_vocab(store.graph(), i as nat, t@), None => true,
                        } by { if i == index { assert(cache@[i] == Some(out)); } }
                    }
                }
            }
        }
        proof! {
            derivative_lemma_step_post(before, store.graph(), this, finish, prior_tasks, tasks.view());
            assert(cache_completions_preserved(cache_before, cache@));
            assert forall|i: int| #![trigger cache@[i]]
                0 <= i < cache_before.len() && cache_before[i] is Some implies
                i < cache@.len() && cache@[i] == cache_before[i] by {}
            assert(tasks.view() == prior_tasks && cache_complete(cache@, this@) || derivative_scheduled(before, this, prior_tasks, tasks.view()));
            if derivative_scheduled(before, this, prior_tasks, tasks.view()) {
                derivative_scheduled_facts(before, this, prior_tasks, tasks.view());
            }
            if derivative_tasks_ready(before, prior_tasks.push((this, finish)), cache_before) {
                derivative_ready_after_step(before, store.graph(), this, finish, prior_tasks, tasks.view(), cache_before, cache@);
            }
        }
        Ok(())
    }

    fn derivative<G: KernelStore>(
        this: RegexId,
        store: &mut G,
        cache: &mut Vec<Option<TransitionId>>,
    ) -> KernelResult<TransitionId> {
        proof_decl! { let ghost entry = store.graph(); }
        let mut tasks = WorkVec::new();
        tasks.push((this, false));
        let mut state = Ok(());
        proof! { assert(tasks.view()[0].0 == this); assert(tasks_contain(tasks.view(), this@)); }
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant model::graph_extends(entry, store.graph()), model::graph_wf(entry),
            store.restoration() == old(store).restoration(),
            store.errors_are_non_owner() == old(store).errors_are_non_owner(),
            store.errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            store.errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            store.errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(state matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && this@ < usize::MAX ==> language::no_invariant_failure(state),
            old(store).errors_are_resource() && old(store).valid_store() && this@ < usize::MAX
                ==> (state matches Err(error) ==> resource_error(error)),
            state is Ok ==> derivative_tasks_ready(store.graph(), tasks.view(), cache@),
            state is Ok ==> cache_complete(cache@, this@) || tasks_contain(tasks.view(), this@),
            old(store).errors_are_non_owner() ==> state != Err(HistoryError::WrongHistoryOwner),
            model::graph_wf(store.graph()), store.valid_store(), this@ < store.graph().regexes.len(),
            derivative_cache_wf(store.graph(), cache@), derivative_tasks_wf(store.graph(), tasks.view()),
            old(cache)@.len() <= cache@.len(),
            forall|i: int| 0 <= i < old(cache)@.len() && old(cache)@[i] is Some
                ==> i < cache@.len() && cache@[i] == old(cache)@[i],
            derivative_tasks_bounded(tasks.view(), this@),
            decreases if state is Ok { derivative_work(store.graph(), tasks.view()) + 1 } else { 0 }))]
        while !tasks.is_empty() && state.is_ok() {
            proof! { derivative_extends(entry, store.graph()); }
            proof_decl! { let ghost pending = tasks.view(); }
            state = match tasks.pop() {
                Some((id, finish)) => {
                    proof! {
                        assert(pending =~= tasks.view().push((id, finish)));
                        derivative_ready_top(store.graph(), pending, cache@);
                    }
                    RegexId::derivative_step(id, store, cache, finish, &mut tasks)
                }
                None => Err(HistoryError::symbolic_invariant()),
            };
        }
        state?;
        Self::cached(cache, this)
    }
}
}
#[verus_verify]
pub(crate) trait AtomTruth: Sized {
    #[verus_spec(result => ensures result.is_ok() == assignment_valid(this@.len(), words@),
        result != Err(HistoryError::WrongHistoryOwner), assignment_valid(this@.len(), words@) ==> language::no_invariant_failure(result),
        assignment_valid(this@.len(), words@) ==> (result matches Err(error) ==> resource_error(error)),
        !(result matches Err(HistoryError::InvalidPolicy { .. })))]
    fn validate_assignment(this: &AtomSet, words: &[u64]) -> KernelResult<()>;

    #[verus_spec(result =>
        requires model::atom_ids_wf(old(store).graph(), this@),
            match previous { Some(i) => positive_atom_at(old(store).graph(), this@, primitive@, i), None => true },
        ensures final(store).graph() == old(store).graph(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() && old(store).valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && old(store).valid_store() && index < this@.len() ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && index < this@.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result == Ok(None) ==> previous is None && !positive_atom_at(final(store).graph(), this@, primitive@, index),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            final(store).valid_store() == old(store).valid_store(),
            match result { Ok(Some(i)) => positive_atom_at(final(store).graph(), this@, primitive@, i), _ => true },
    )]
    fn positive_step<G: KernelStore>(
        this: &AtomSet,
        store: &mut G,
        primitive: Primitive,
        index: usize,
        previous: Option<usize>,
    ) -> KernelResult<Option<usize>>;

    #[verus_spec(result =>
        requires model::atom_ids_wf(old(store).graph(), this@),
            id@ < old(store).graph().tests.len(),
            old(store).graph().tests[id@ as int] == model::TestNode::Atom(primitive@, positive),
        ensures final(store).graph() == old(store).graph(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() && old(store).valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && old(store).valid_store() && model::graph_wf(old(store).graph())
                && reach::has_positive(old(store).graph(), this@, primitive@) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && model::graph_wf(old(store).graph())
                && reach::has_positive(old(store).graph(), this@, primitive@)
                ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            final(store).valid_store() == old(store).valid_store(),
            match result { Ok(i) => positive_atom_at(final(store).graph(), this@, primitive@, i), Err(_) => true },
    )]
    fn positive_index<G: KernelStore>(
        this: &AtomSet,
        store: &mut G,
        id: TestId,
        primitive: Primitive,
        positive: bool,
    ) -> KernelResult<usize>;

    #[verus_spec(result => ensures match result {
        Ok(value) => index / 64 < words@.len() && value == truth_word_bit(words@, index as nat),
        Err(_) => index / 64 >= words@.len(),
    }, result != Err(HistoryError::WrongHistoryOwner), index / 64 < words@.len() ==> language::no_invariant_failure(result),
        index / 64 < words@.len() ==> (result matches Err(error) ==> resource_error(error)),
        !(result matches Err(HistoryError::InvalidPolicy { .. })))]
    fn truth(words: &[u64], index: usize) -> KernelResult<bool>;
}

#[verus_verify]
impl AtomTruth for AtomSet {
    #[verus_verify]

    fn validate_assignment(this: &AtomSet, words: &[u64]) -> KernelResult<()> {
        let count = this.ids().len();
        let rounded = match count.checked_add(63) {
            Some(v) => v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        let required = match rounded.checked_div(64) {
            Some(v) => v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        if words.len() != required {
            return Err(HistoryError::invalid_truth_assignment());
        }
        let remainder = match count.checked_rem(64) {
            Some(v) => v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        if remainder != 0 {
            let shift = match u32::try_from(remainder) {
                Ok(v) => v,
                Err(_) => return Err(HistoryError::invalid_truth_assignment()),
            };
            let last = match words.last() {
                Some(v) => *v,
                None => return Err(HistoryError::invalid_truth_assignment()),
            };
            let high = match checked_shr(last, shift) {
                Some(v) => v,
                None => return Err(HistoryError::invalid_truth_assignment()),
            };
            if high != 0 {
                return Err(HistoryError::invalid_truth_assignment());
            }
        }
        Ok(())
    }
    #[verus_verify]

    fn positive_step<G: KernelStore>(
        this: &AtomSet,
        store: &mut G,
        primitive: Primitive,
        index: usize,
        previous: Option<usize>,
    ) -> KernelResult<Option<usize>> {
        store.checkpoint()?;
        let base = match this.ids().get(index) {
            Some(v) => *v,
            None => return Err(HistoryError::missing_transition_atom()),
        };
        let head = base.head(store)?;
        if matches!(head,TestHead::Atom(p,true) if p==primitive) {
            Ok(Some(index))
        } else {
            Ok(previous)
        }
    }
    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure."
    )]
    #[verus_verify]

    fn positive_index<G: KernelStore>(
        this: &AtomSet,
        store: &mut G,
        id: TestId,
        primitive: Primitive,
        positive: bool,
    ) -> KernelResult<usize> {
        if positive {
            proof! {
                assert forall|i: int, j: int| 0 <= i < j < this@.len()
                    implies vstd::std_specs::cmp::OrdSpec::cmp_spec(&this@[i], &this@[j]) is Less by {
                    assert(model::test_ids(this@)[i] == this@[i]@);
                    assert(model::test_ids(this@)[j] == this@[j]@);
                }
                if model::graph_wf(store.graph()) && reach::has_positive(store.graph(), this@, primitive@) {
                    model::lemma_graph_wf_elim(store.graph());
                    let i = choose|i: int| 0 <= i < this@.len() && this@[i]@ < store.graph().tests.len()
                        && store.graph().tests[this@[i]@ as int] == model::TestNode::Atom(primitive@, true);
                    assert(store.graph().tests[this@[i]@ as int] == store.graph().tests[id@ as int]);
                    assert(this@[i]@ == id@);
                    assert(this@[i] == id);
                    assert(this@.contains(id));
                }
            }
            proof! { junco_core::kernel::TestId::lemma_obeys_cmp(); }
            return match this.ids().binary_search(&id) {
                Ok(index) => Ok(index),
                Err(_) => Err(HistoryError::missing_transition_atom()),
            };
        }
        let mut state = Ok(None);
        let count = this.ids().len();
        scan!(state,index,count,state.is_ok(),previous=>AtomSet::positive_step(this,store,primitive,index,previous);
            invariant count == this@.len(), store.graph() == old(store).graph(),
                store.restoration() == old(store).restoration(),
                store.errors_are_non_owner() == old(store).errors_are_non_owner(),
                store.errors_are_non_invariant() == old(store).errors_are_non_invariant(),
                store.errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
                store.errors_are_resource() == old(store).errors_are_resource(),
                old(store).errors_are_non_invalid_policy() && old(store).valid_store() ==> !(state matches Err(HistoryError::InvalidPolicy { .. })),
                old(store).errors_are_non_invariant() && old(store).valid_store() ==> language::no_invariant_failure(state),
                old(store).errors_are_resource() && old(store).valid_store()
                    ==> (state matches Err(error) ==> resource_error(error)),
                index <= this@.len(), state == Ok(None) ==> forall|j: usize| j < index ==> !positive_atom_at(store.graph(), this@, primitive@, j),
                old(store).errors_are_non_owner() ==> state != Err(HistoryError::WrongHistoryOwner),
                store.valid_store() == old(store).valid_store(), model::atom_ids_wf(store.graph(), this@),
                match state { Ok(Some(i)) => positive_atom_at(store.graph(), this@, primitive@, i), _ => true },
                ensures state == Ok(None) ==> forall|j: usize| j < this@.len() ==> !positive_atom_at(store.graph(), this@, primitive@, j),
                decreases this@.len() - index,
        );
        let selected = state?;
        proof! {
            if selected is None && reach::has_positive(store.graph(), this@, primitive@) {
                let i = choose|i: int| 0 <= i < this@.len() && this@[i]@ < store.graph().tests.len()
                    && store.graph().tests[this@[i]@ as int] == model::TestNode::Atom(primitive@, true);
                assert(i <= usize::MAX);
                let index = i as usize;
                assert(index as int == i);
                assert(positive_atom_at(store.graph(), this@, primitive@, index));
                assert(state == Ok(None));
                assert(false);
            }
        }
        match selected {
            Some(index) => Ok(index),
            None => Err(HistoryError::missing_transition_atom()),
        }
    }
    #[verus_verify]

    fn truth(words: &[u64], index: usize) -> KernelResult<bool> {
        let word = match index.checked_div(64) {
            Some(v) => v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        let bit = match index.checked_rem(64) {
            Some(v) => v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        let shift = match u32::try_from(bit) {
            Ok(v) => v,
            Err(_) => return Err(HistoryError::invalid_truth_assignment()),
        };
        let value = match words.get(word) {
            Some(v) => *v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        let shifted = match checked_shr(value, shift) {
            Some(v) => v,
            None => return Err(HistoryError::invalid_truth_assignment()),
        };
        Ok(shifted & 1 != 0)
    }
}
verus! {
pub(crate) trait TestEvaluate: Sized {
    #[allow(
        clippy::option_if_let_else,
        clippy::semicolon_if_nothing_returned,
        reason = "Preserve the existing Verus-verified matches and mutation branches."
    )]
    fn evaluate_branch<G: KernelStore>(
        store: &G,
        id: TestId,
        count: usize,
        and: bool,
        finish: bool,
        tasks: &mut WorkVec<(TestId, bool)>,
        values: &mut WorkVec<bool>,
    ) -> (result: KernelResult<()>)
        requires model::graph_wf(store.graph()), id@ < store.graph().tests.len(),
            store.graph().tests[id@ as int] == (if and { model::TestNode::And(test_children(store.graph(), id)) } else { model::TestNode::Or(test_children(store.graph(), id)) }),
            count == test_children(store.graph(), id).len(), test_tasks_wf(store.graph(), old(tasks).view()),
        ensures test_tasks_wf(store.graph(), final(tasks).view()),
            store.errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            store.errors_are_non_invariant() && store.valid_store() && (!finish || count <= old(values).view().len()) ==> language::no_invariant_failure(result),
            store.errors_are_resource() && store.valid_store() && (!finish || count <= old(values).view().len())
                ==> (result matches Err(error) ==> resource_error(error)),
            store.errors_are_non_invalid_policy() && store.valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            result is Ok ==> test_stack_result(store.graph(), old(tasks).view().push((id, finish)), old(values).view().len())
                == test_stack_result(store.graph(), final(tasks).view(), final(values).view().len()),
            forall|atoms: Seq<TestId>| test_tasks_covered(store.graph(), old(tasks).view().push((id, finish)), atoms) && result is Ok
                ==> test_tasks_covered(store.graph(), final(tasks).view(), atoms),
            result.is_ok() ==> forall|theta: Subst, event: EventView|
                test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), theta, event)
                    == test_run(store.graph(), final(tasks).view(), final(values).view(), theta, event),
            result.is_ok() ==> final(tasks).view() == old(tasks).view()
                || norm::test_not_work(store.graph(), final(tasks).view())
                    < norm::test_not_work(store.graph(), old(tasks).view().push((id, finish))),
    {
        if finish {
            let mut out = and;
            let mut failure = None;
            let mut i = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant i <= count, i <= old(values).view().len(),
                    store.errors_are_non_owner() ==> failure != Some(HistoryError::WrongHistoryOwner),
                    store.errors_are_non_invariant() && store.valid_store() && count <= old(values).view().len()
                        ==> (failure matches Some(error) ==> language::no_invariant_failure::<()>(Err(error))),
                    store.errors_are_resource() && store.valid_store() && count <= old(values).view().len()
                        ==> (failure matches Some(error) ==> resource_error(error)),
                    store.errors_are_non_invalid_policy() && store.valid_store() ==> !(failure matches Some(HistoryError::InvalidPolicy { .. })),
                    values.view() == old(values).view().take(old(values).view().len() - i),
                    out == bool_fold(old(values).view().skip(old(values).view().len() - i), and),
                ensures failure.is_none() ==> i == count,
                decreases count - i,
            ))]
            while i < count {
                let value = loop_try!(
                    match values.pop() {
                        Some(v) => Ok(v),
                        None => Err(HistoryError::symbolic_invariant()),
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
            values.push(out);
            proof! {
                test_stack_task(store.graph(), old(tasks).view(), (id, true), old(values).view().len());
                assert(values.view().len() == old(values).view().len() - count + 1);
                assert(old(tasks).view().push((id, finish)).drop_last() =~= old(tasks).view());
                assert forall|theta: Subst, event: EventView|
                    test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), theta, event)
                        == test_run(store.graph(), tasks.view(), values.view(), theta, event) by {
                    test_run_unfold(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), theta, event);
                }
            }
        } else {
            tasks.push((id, true));
            proof_decl! { let ghost scheduled_base = tasks.view(); }
            proof! { model::lemma_graph_test_wf(store.graph(), id@); }
            let mut failure = None;
            let mut remaining = count;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant remaining <= count, model::graph_wf(store.graph()), id@ < store.graph().tests.len(),
                    store.errors_are_non_owner() ==> failure != Some(HistoryError::WrongHistoryOwner),
                    store.errors_are_non_invariant() && store.valid_store() ==> (failure matches Some(error) ==> language::no_invariant_failure::<()>(Err(error))),
                    store.errors_are_resource() && store.valid_store() ==> (failure matches Some(error) ==> resource_error(error)),
                    store.errors_are_non_invalid_policy() && store.valid_store() ==> !(failure matches Some(HistoryError::InvalidPolicy { .. })),
                    count == test_children(store.graph(), id).len(), test_tasks_wf(store.graph(), scheduled_base),
                    test_tasks_wf(store.graph(), tasks.view()),
                    failure.is_none() ==> tasks.view() == scheduled_base + child_test_tasks(store.graph(), id, remaining as nat),
                ensures failure.is_none() ==> remaining == 0,
                decreases remaining,
            ))]
            // Reverse pushes preserve source order when the LIFO task stack executes children.
            while remaining != 0 {
                let i = loop_try!(
                    match remaining.checked_sub(1) {
                        Some(value) => Ok(value),
                        None => Err(HistoryError::symbolic_invariant()),
                    },
                    failure
                );
                remaining = i;
                let child = loop_try!(id.child(store, i), failure);
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
            proof! {
                test_stack_children(store.graph(), id, 0, old(tasks).view().push((id, true)), old(values).view().len());
                test_stack_task(store.graph(), old(tasks).view(), (id, false), old(values).view().len());
                test_stack_task(store.graph(), old(tasks).view(), (id, true), (old(values).view().len() + count) as nat);
                assert(tasks.view() == old(tasks).view().push((id, true)) + child_test_tasks(store.graph(), id, 0));
                assert forall|theta: Subst, event: EventView|
                    test_run(store.graph(), old(tasks).view().push((id, finish)), old(values).view(), theta, event)
                        == test_run(store.graph(), tasks.view(), values.view(), theta, event) by {
                    test_expand(store.graph(), id, old(tasks).view(), old(values).view(), theta, event);
                }
                test_lemma_eval_branch_work(store.graph(), id, old(tasks).view());
            }
        }
        proof! {
            assert forall|atoms: Seq<TestId>| test_tasks_covered(store.graph(), old(tasks).view().push((id, finish)), atoms)
                implies test_tasks_covered(store.graph(), tasks.view(), atoms) by {
                assert(old(tasks).view().push((id, finish))[old(tasks).view().len() as int] == (id, finish));
                assert(test_atoms_covered(store.graph(), id@, atoms));
                test_coverage_children(store.graph(), id, atoms);
                assert forall|i: int| 0 <= i < tasks.view().len() implies test_atoms_covered(store.graph(), tasks.view()[i].0@, atoms) by {
                    if i < old(tasks).view().len() {
                        assert(tasks.view()[i] == old(tasks).view()[i]);
                        assert(old(tasks).view().push((id, finish))[i] == old(tasks).view()[i]);
                    } else if i == old(tasks).view().len() {
                        assert(tasks.view()[i].0 == id);
                    } else {
                        let j = test_children(store.graph(), id).len() - 1 - (i - old(tasks).view().len() - 1);
                        assert(tasks.view()[i].0@ == test_children(store.graph(), id)[j]);
                    }
                }
            }
        }
        Ok(())
    }

    fn evaluate_step<G: KernelStore>(
        this: TestId,
        store: &mut G,
        finish: bool,
        atoms: &AtomSet,
        words: &[u64],
        tasks: &mut WorkVec<(TestId, bool)>,
        values: &mut WorkVec<bool>,
    ) -> (result: KernelResult<()>)
        requires model::graph_wf(old(store).graph()), this@ < old(store).graph().tests.len(),
            model::atom_ids_wf(old(store).graph(), atoms@), test_tasks_wf(old(store).graph(), old(tasks).view()),
        ensures final(store).graph() == old(store).graph(), final(store).valid_store() == old(store).valid_store(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() && old(store).valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && old(store).valid_store() && test_atoms_covered(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), words@)
                && test_stack_result(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view().len()) is Some
                ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && test_atoms_covered(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), words@)
                && test_stack_result(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view().len()) is Some
                ==> (result matches Err(error) ==> resource_error(error)),
            result is Ok ==> test_stack_result(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view().len())
                == test_stack_result(final(store).graph(), final(tasks).view(), final(values).view().len()),
            test_tasks_covered(old(store).graph(), old(tasks).view().push((this, finish)), atoms@) && result is Ok
                ==> test_tasks_covered(final(store).graph(), final(tasks).view(), atoms@),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            test_tasks_wf(final(store).graph(), final(tasks).view()),
            result.is_ok() ==> forall|theta: Subst, event: EventView|
                truth_words_realize(final(store).graph(), atoms@, words@, theta, event) ==>
                    test_run(final(store).graph(), old(tasks).view().push((this, finish)), old(values).view(), theta, event)
                        == test_run(final(store).graph(), final(tasks).view(), final(values).view(), theta, event),
            result.is_ok() ==> norm::test_not_work(final(store).graph(), final(tasks).view())
                < norm::test_not_work(old(store).graph(), old(tasks).view().push((this, finish)));

    fn evaluate<G: KernelStore>(
        this: TestId,
        store: &mut G,
        atoms: &AtomSet,
        words: &[u64],
    ) -> (result: KernelResult<bool>)
        requires model::graph_wf(old(store).graph()), this@ < old(store).graph().tests.len(),
            model::atom_ids_wf(old(store).graph(), atoms@),
        ensures final(store).graph() == old(store).graph(), final(store).valid_store() == old(store).valid_store(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() && old(store).valid_store() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && old(store).valid_store() && test_atoms_covered(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), words@) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && test_atoms_covered(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), words@) ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            result matches Ok(value) ==> forall|theta: Subst, event: EventView|
                truth_words_realize(final(store).graph(), atoms@, words@, theta, event) ==>
                    value == model::test_holds(theta, model::lift_test(final(store).graph(), this@), event);
}
}

#[verus_verify]
impl TestEvaluate for TestId {
    #[verus_verify]

    fn evaluate_step<G: KernelStore>(
        this: TestId,
        store: &mut G,
        finish: bool,
        atoms: &AtomSet,
        words: &[u64],
        tasks: &mut WorkVec<(TestId, bool)>,
        values: &mut WorkVec<bool>,
    ) -> KernelResult<()> {
        store.checkpoint()?;
        match this.head(store)? {
            TestHead::True => values.push(true),
            TestHead::False => values.push(false),
            TestHead::Atom(primitive, positive) => {
                proof! {
                    if test_atoms_covered(store.graph(), this@, atoms@) {
                        assert(reach::test_reaches_primitive(store.graph(), this@, primitive@));
                        assert(reach::has_positive(store.graph(), atoms@, primitive@));
                    }
                }
                let index = AtomSet::positive_index(atoms, store, this, primitive, positive)?;
                proof! {
                    if assignment_valid(atoms@.len(), words@) { assignment_index_bound(atoms@.len(), words@, index); }
                }
                let value = AtomSet::truth(words, index)?;
                values.push(if positive { value } else { !value });
                proof! {
                    realized_atom_value(store.graph(), atoms@, words@, this, primitive@, positive, index, value);
                }
            }
            TestHead::And(n) => Self::evaluate_branch(store, this, n, true, finish, tasks, values)?,
            TestHead::Or(n) => Self::evaluate_branch(store, this, n, false, finish, tasks, values)?,
        }
        proof! {
            assert(old(tasks).view().push((this, finish)).drop_last() =~= old(tasks).view());
            assert forall|theta: Subst, event: EventView|
                truth_words_realize(store.graph(), atoms@, words@, theta, event) implies
                    test_run(store.graph(), old(tasks).view().push((this, finish)), old(values).view(), theta, event)
                        == test_run(store.graph(), tasks.view(), values.view(), theta, event) by {
                test_run_unfold(store.graph(), old(tasks).view().push((this, finish)), old(values).view(), theta, event);
            }
            test_lemma_eval_step_work(store.graph(), this, finish, old(tasks).view(), tasks.view());
        }
        Ok(())
    }
    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure."
    )]
    #[verus_verify]

    fn evaluate<G: KernelStore>(
        this: TestId,
        store: &mut G,
        atoms: &AtomSet,
        words: &[u64],
    ) -> KernelResult<bool> {
        let mut tasks = WorkVec::new();
        let mut values = WorkVec::new();
        tasks.push((this, false));
        let mut state = Ok(());
        proof! {
            test_stack_task(store.graph(), Seq::empty(), (this, false), 0);
            assert(test_stack_result(store.graph(), Seq::empty(), 1) == Some(1));
            assert(tasks.view() == seq![(this, false)]);
            assert(test_stack_result(store.graph(), tasks.view(), 0) == Some(1));
            assert forall|theta: Subst, event: EventView|
                test_run(store.graph(), tasks.view(), values.view(), theta, event)
                    == Some(seq![model::test_holds(theta, model::lift_test(store.graph(), this@), event)]) by {
                test_run_unfold(store.graph(), tasks.view(), values.view(), theta, event);
                test_run_unfold(store.graph(), Seq::empty(), seq![model::test_holds(theta, model::lift_test(store.graph(), this@), event)], theta, event);
            }
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant store.graph() == old(store).graph(), store.valid_store() == old(store).valid_store(),
                store.restoration() == old(store).restoration(),
                store.errors_are_non_owner() == old(store).errors_are_non_owner(),
                store.errors_are_non_invariant() == old(store).errors_are_non_invariant(),
                store.errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
                store.errors_are_resource() == old(store).errors_are_resource(),
                old(store).errors_are_non_invalid_policy() && old(store).valid_store() ==> !(state matches Err(HistoryError::InvalidPolicy { .. })),
                old(store).errors_are_non_invariant() && old(store).valid_store() && test_atoms_covered(store.graph(), this@, atoms@)
                    && assignment_valid(atoms@.len(), words@) ==> language::no_invariant_failure(state),
                old(store).errors_are_resource() && old(store).valid_store() && test_atoms_covered(store.graph(), this@, atoms@)
                    && assignment_valid(atoms@.len(), words@) ==> (state matches Err(error) ==> resource_error(error)),
                state is Ok ==> test_stack_result(store.graph(), tasks.view(), values.view().len()) == Some(1),
                test_atoms_covered(store.graph(), this@, atoms@) && state is Ok ==> test_tasks_covered(store.graph(), tasks.view(), atoms@),
                old(store).errors_are_non_owner() ==> state != Err(HistoryError::WrongHistoryOwner),
                model::graph_wf(store.graph()), model::atom_ids_wf(store.graph(), atoms@), test_tasks_wf(store.graph(), tasks.view()),
                this@ < store.graph().tests.len(),
                state.is_ok() ==> forall|theta: Subst, event: EventView|
                    truth_words_realize(store.graph(), atoms@, words@, theta, event) ==>
                        test_run(store.graph(), tasks.view(), values.view(), theta, event)
                            == Some(seq![model::test_holds(theta, model::lift_test(store.graph(), this@), event)]),
            decreases if state is Ok { norm::test_not_work(store.graph(), tasks.view()) + 1 } else { 0 },
        ))]
        while !tasks.is_empty() && state.is_ok() {
            proof_decl! { let ghost pending = tasks.view(); }
            state = match tasks.pop() {
                Some((id, finish)) => {
                    proof! { assert(pending =~= tasks.view().push((id, finish))); }
                    TestId::evaluate_step(id, store, finish, atoms, words, &mut tasks, &mut values)
                }
                None => Err(HistoryError::symbolic_invariant()),
            };
        }
        state?;
        match values.pop() {
            Some(v) => Ok(v),
            None => Err(HistoryError::symbolic_invariant()),
        }
    }
}
verus! {
fn collect_append_factors<G: KernelStore>(
    store: &G, root: TransitionId, head: RegexId, count: usize, xs: &mut WorkVec<RegexId>,
) -> (result: KernelResult<()>)
    requires model::graph_wf(store.graph()), store.valid_store(), root@ < store.graph().transitions.len(),
        store.graph().transitions[root@ as int] is Append, head@ < store.graph().regexes.len(),
        count == transition_suffix(store.graph(), root).len(), old(xs).view().len() == 0,
    ensures norm::regex_ids_valid(store.graph(), final(xs).view()),
        store.errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
        store.errors_are_non_invariant() ==> language::no_invariant_failure(result),
        store.errors_are_resource() && store.valid_store() ==> (result matches Err(error) ==> resource_error(error)),
        store.errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
        result is Ok ==> model::regex_ids(final(xs).view()) == seq![head@] + transition_suffix(store.graph(), root),
{
    proof { model::lemma_graph_transition_wf(store.graph(), root@); }
    xs.push(head);
    let mut failure = None;
    let mut i = 0;
    while i < count
        invariant i <= count, model::graph_wf(store.graph()), store.valid_store(),
            root@ < store.graph().transitions.len(), store.graph().transitions[root@ as int] is Append,
            head@ < store.graph().regexes.len(), count == transition_suffix(store.graph(), root).len(),
            model::transition_node_wf_at(store.graph(), store.graph().transitions[root@ as int], root@),
            store.errors_are_non_owner() ==> failure != Some(HistoryError::WrongHistoryOwner),
            store.errors_are_non_invariant() ==> (failure matches Some(error) ==> language::no_invariant_failure::<()>(Err(error))),
            store.errors_are_resource() && store.valid_store() ==> (failure matches Some(error) ==> resource_error(error)),
            store.errors_are_non_invalid_policy() ==> !(failure matches Some(HistoryError::InvalidPolicy { .. })),
            norm::regex_ids_valid(store.graph(), xs.view()),
            model::regex_ids(xs.view()) == seq![head@] + transition_suffix(store.graph(), root).take(i as int),
        ensures failure is None ==> i == count,
        decreases count - i,
    {
        let child = loop_try!(root.suffix_child(store, i), failure);
        proof {
            assert(child@ == transition_suffix(store.graph(), root)[i as int]);
            assert(child@ < store.graph().regexes.len());
        }
        let ghost previous = xs.view();
        xs.push(child);
        proof {
            norm::regex_ids_push(previous, child);
            assert(transition_suffix(store.graph(), root).take(i as int + 1)
                =~= transition_suffix(store.graph(), root).take(i as int).push(child@));
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure { return Err(error); }
    proof { assert(transition_suffix(store.graph(), root).take(count as int) =~= transition_suffix(store.graph(), root)); }
    Ok(())
}

#[verifier::spinoff_prover]
fn interpret_not<G: KernelStore>(
    store: &mut G, root: TransitionId, inner: TransitionId, finish: bool,
    tasks: &mut WorkVec<(TransitionId, bool)>, values: &mut WorkVec<RegexId>,
) -> (result: KernelResult<()>)
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), root@ < old(store).graph().transitions.len(),
        old(store).graph().transitions[root@ as int] == model::TransitionNode::Not(inner@),
        interp_tasks_wf(old(store).graph(), old(tasks).view()), norm::regex_ids_valid(old(store).graph(), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
        final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
        final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
        final(store).errors_are_resource() == old(store).errors_are_resource(),
        old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
        old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
        old(store).errors_are_non_invariant() && (!finish || old(values).view().len() > 0) ==> language::no_invariant_failure(result),
        old(store).errors_are_resource() && old(store).valid_store() && (!finish || old(values).view().len() > 0)
            ==> (result matches Err(error) ==> resource_error(error)),
        interp_tasks_wf(final(store).graph(), final(tasks).view()), norm::regex_ids_valid(final(store).graph(), final(values).view()),
        result is Ok ==> (if finish {
            final(tasks).view() == old(tasks).view() && final(values).view().len() == old(values).view().len()
        } else {
            final(tasks).view() == old(tasks).view().push((root, true)).push((inner, false)) && final(values).view() == old(values).view()
        }),
        result is Ok ==> interp_work(final(store).graph(), final(tasks).view())
            < interp_work(old(store).graph(), old(tasks).view().push((root, finish))),
        result is Ok ==> final(tasks).view() == old(tasks).view()
            || (interp_tasks_wf(old(store).graph(), final(tasks).view())
                && interp_work(old(store).graph(), final(tasks).view())
                    < interp_work(old(store).graph(), old(tasks).view().push((root, finish)))),
        result is Ok ==> interp_stack_result(old(store).graph(), old(tasks).view().push((root, finish)), old(values).view().len())
            == interp_stack_result(final(store).graph(), final(tasks).view(), final(values).view().len()),
        forall|atoms: Seq<TestId>| interp_tasks_covered(old(store).graph(), old(tasks).view().push((root, finish)), atoms) && result is Ok
            ==> interp_tasks_covered(final(store).graph(), final(tasks).view(), atoms),
        result is Ok ==> forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len())
            ==> interp_results_equiv(model::gsem(theta),
                interp_run(old(store).graph(), old(tasks).view().push((root, finish)), lifted_values(old(store).graph(), old(values).view()), theta, event),
                interp_run(final(store).graph(), final(tasks).view(), lifted_values(final(store).graph(), final(values).view()), theta, event)),
        result is Ok ==> (fint::ipre(old(store).graph(), old(tasks).view().push((root, finish)), old(values).view())
            ==> fint::istep(final(store).graph(), old(tasks).view().push((root, finish)), final(tasks).view(), old(values).view(), final(values).view())),
{
    hide(interp_run); hide(interp_stack_result); hide(interp_tasks_covered);
    hide(reach::atoms_wf); hide(test_atoms_covered);
    hide(language::numeric_lang); hide(language::interp_transition);
    hide(model::test_holds); hide(model::lift_transition); hide(model::lift_regex);
    let ghost before = store.graph();
    let ghost pending = tasks.view();
    let ghost prior = values.view();
    proof {
        norm::graph_lemma_extends_refl(before);
        model::lemma_graph_transition_wf(before, root@);
        interp_stack_task(before, pending, (root, finish), prior.len());
    }
    if finish {
        let value = match values.pop() {
            Some(value) => value,
            None => return Err(HistoryError::symbolic_invariant()),
        };
        values.push(RegexId::not(value, store)?);
        proof {
            lifted_values_stable(before, store.graph(), prior);
            store.graph().transitions.lemma_prefix_index_eq(before.transitions);
            assert forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len()) implies
                interp_results_equiv(model::gsem(theta),
                    interp_run(store.graph(), pending.push((root, finish)), lifted_values(store.graph(), prior), theta, event),
                    interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
                assert forall|word: Seq<EventView>| language::numeric_lang(model::gsem(theta), language::Regex::Not(Box::new(model::lift_regex(store.graph(), value@))), word)
                    == model::regex_lang(store.graph(), theta, values.view().last()@, word) by {
                    norm::regex_language_unfold(model::gsem(theta), language::Regex::Not(Box::new(model::lift_regex(store.graph(), value@))), word);
                }
                assert(lifted_values(store.graph(), values.view()) =~= lifted_values(store.graph(), prior).drop_last().push(model::lift_regex(store.graph(), values.view().last()@)));
                interp_value_reduction(store.graph(), root, finish, pending, lifted_values(store.graph(), prior), lifted_values(store.graph(), values.view()), theta, event);
            }
            assert(before.transitions[root@ as int] == store.graph().transitions[root@ as int]);
            if fint::ipre(before, pending.push((root, finish)), prior) {
                fint::lemma_istep_not(before, store.graph(), root, pending, prior, values.view().last());
            }
        }
    } else {
        tasks.push((root, true));
        tasks.push((inner, false));
        proof {
            interp_stack_task(store.graph(), pending.push((root, true)), (inner, false), prior.len());
            interp_stack_task(store.graph(), pending, (root, true), prior.len() + 1);
            assert forall|theta: Subst, event: EventView| interp_run(store.graph(), pending.push((root, finish)), lifted_values(store.graph(), prior), theta, event)
                == interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event) by {
                interp_expand_unary(store.graph(), root, inner, pending, lifted_values(store.graph(), prior), theta, event);
            }
            interp_lemma_work_unary(store.graph(), root, pending, inner);
            assert(before.transitions[root@ as int] == store.graph().transitions[root@ as int]);
            if fint::ipre(before, pending.push((root, finish)), prior) {
                fint::lemma_istep_unary(before, store.graph(), root, finish, pending, prior, inner);
            }
        }
    }
    proof {
        interp_lemma_step_post(before, store.graph(), root, finish, pending, tasks.view());
        interp_stack_stable(before, store.graph(), pending.push((root, finish)), prior.len());
        interp_stack_task(store.graph(), pending, (root, finish), prior.len());
        assert forall|atoms: Seq<TestId>| interp_tasks_covered(before, pending.push((root, finish)), atoms)
            implies interp_tasks_covered(store.graph(), tasks.view(), atoms) by {
            interp_coverage_pop(before, pending, (root, finish), atoms);
            interp_coverage_stable(before, store.graph(), pending, atoms);
            if !finish {
                transition_coverage_children(before, root, atoms);
                assert(reach::transition_edges(before, root@) == seq![inner@]);
                assert(reach::transition_edges(before, root@)[0] == inner@);
                assert(reach::atoms_wf(before, inner@, atoms));
                interp_coverage_push(before, pending, (root, true), atoms);
                interp_coverage_push(before, pending.push((root, true)), (inner, false), atoms);
            }
        }
        assert forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len()) implies
            interp_results_equiv(model::gsem(theta),
                interp_run(before, pending.push((root, finish)), lifted_values(before, prior), theta, event),
                interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
            interp_same_configuration_extends(before, store.graph(), pending.push((root, finish)), prior, theta, event);
        }
    }
    Ok(())
}

pub(crate) trait TransitionInterpret: Sized {
    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure."
    )]
    fn interpret_branch<G: KernelStore>(
        store: &mut G,
        id: TransitionId,
        count: usize,
        intersect: bool,
        finish: bool,
        tasks: &mut WorkVec<(TransitionId, bool)>,
        values: &mut WorkVec<RegexId>,
    ) -> (result: KernelResult<()>)
        requires model::graph_wf(old(store).graph()), old(store).valid_store(), id@ < old(store).graph().transitions.len(),
            old(store).graph().transitions[id@ as int] == (if intersect { model::TransitionNode::Intersect(transition_children(old(store).graph(), id)) } else { model::TransitionNode::Union(transition_children(old(store).graph(), id)) }),
            count == transition_children(old(store).graph(), id).len(), interp_tasks_wf(old(store).graph(), old(tasks).view()),
            norm::regex_ids_valid(old(store).graph(), old(values).view()),
        ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && (!finish || count <= old(values).view().len()) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && (!finish || count <= old(values).view().len())
                ==> (result matches Err(error) ==> resource_error(error)),
            result is Ok ==> interp_stack_result(old(store).graph(), old(tasks).view().push((id, finish)), old(values).view().len())
                == interp_stack_result(final(store).graph(), final(tasks).view(), final(values).view().len()),
            forall|atoms: Seq<TestId>| interp_tasks_covered(old(store).graph(), old(tasks).view().push((id, finish)), atoms) && result is Ok
                ==> interp_tasks_covered(final(store).graph(), final(tasks).view(), atoms),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            interp_tasks_wf(final(store).graph(), final(tasks).view()), norm::regex_ids_valid(final(store).graph(), final(values).view()),
            result.is_ok() ==> forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len()) ==>
                interp_results_equiv(model::gsem(theta),
                    interp_run(old(store).graph(), old(tasks).view().push((id, finish)), lifted_values(old(store).graph(), old(values).view()), theta, event),
                    interp_run(final(store).graph(), final(tasks).view(), lifted_values(final(store).graph(), final(values).view()), theta, event)),
            result.is_ok() ==> final(tasks).view() == old(tasks).view()
                || (interp_tasks_wf(old(store).graph(), final(tasks).view())
                    && interp_work(old(store).graph(), final(tasks).view())
                        < interp_work(old(store).graph(), old(tasks).view().push((id, finish)))),
            result.is_ok() ==> (fint::ipre(old(store).graph(), old(tasks).view().push((id, finish)), old(values).view())
                ==> fint::istep(final(store).graph(), old(tasks).view().push((id, finish)), final(tasks).view(), old(values).view(), final(values).view())),
    {
        proof_decl! { let ghost before = store.graph(); }
        if finish {
            let start = match values.len().checked_sub(count) {
                Some(v) => v,
                None => return Err(HistoryError::symbolic_invariant()),
            };
            let children = match values.get(start..) {
                Some(xs) => xs,
                None => return Err(HistoryError::symbolic_invariant()),
            };
            proof_decl! { let ghost selected = children@; }
            let out = RegexId::set(store, children, intersect)?;
            proof! { lifted_values_stable(before, store.graph(), old(values).view()); }
            values.truncate(start);
            values.push(out);
            proof! {
                interp_stack_task(store.graph(), old(tasks).view(), (id, true), old(values).view().len());
                assert(values.view().len() == old(values).view().len() - count + 1);
                assert forall|theta: Subst| language::event_wf(theta, theta.len()) implies
                    regex_stack_equiv(model::gsem(theta), lifted_values(store.graph(), values.view()),
                        lifted_values(store.graph(), old(values).view().take(old(values).view().len() - count)).push(
                            regex_fold(lifted_values(store.graph(), old(values).view().skip(old(values).view().len() - count)), intersect))) by {
                    assert forall|word: Seq<EventView>| model::regex_lang(store.graph(), theta, out@, word)
                        == language::numeric_lang(model::gsem(theta), regex_fold(lifted_values(store.graph(), selected), intersect), word) by {
                        regex_fold_ids(store.graph(), selected, intersect, theta, word);
                    }
                    assert(lifted_values(store.graph(), values.view())
                        =~= lifted_values(store.graph(), old(values).view().take(start as int)).push(model::lift_regex(store.graph(), out@)));
                    assert(selected =~= old(values).view().skip(start as int));
                    assert forall|i: int, word: Seq<EventView>| 0 <= i < values.view().len() implies
                        language::numeric_lang(model::gsem(theta), lifted_values(store.graph(), values.view())[i], word)
                            == language::numeric_lang(model::gsem(theta), lifted_values(store.graph(), old(values).view().take(start as int)).push(
                                regex_fold(lifted_values(store.graph(), selected), intersect))[i], word) by {
                        if i == start {
                            assert(model::regex_lang(store.graph(), theta, out@, word)
                                == language::numeric_lang(model::gsem(theta), regex_fold(lifted_values(store.graph(), selected), intersect), word));
                        }
                    }
                }
                assert(interp_set_result(store.graph(), old(values).view(), values.view(), count as nat, intersect));
                assert forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len()) implies
                    interp_results_equiv(model::gsem(theta),
                        interp_run(before, old(tasks).view().push((id, finish)), lifted_values(before, old(values).view()), theta, event),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
                    let pending = old(tasks).view().push((id, finish));
                    interp_same_configuration_extends(before, store.graph(), pending, old(values).view(), theta, event);
                    assert(pending.drop_last() =~= old(tasks).view());
                    interp_run_unfold(store.graph(), pending, lifted_values(store.graph(), old(values).view()), theta, event);
                    let reduced = lifted_values(store.graph(), old(values).view()).take(old(values).view().len() - count).push(
                        regex_fold(lifted_values(store.graph(), old(values).view()).skip(old(values).view().len() - count), intersect));
                    assert(lifted_values(store.graph(), old(values).view().take(old(values).view().len() - count))
                        =~= lifted_values(store.graph(), old(values).view()).take(old(values).view().len() - count));
                    assert(lifted_values(store.graph(), old(values).view().skip(old(values).view().len() - count))
                        =~= lifted_values(store.graph(), old(values).view()).skip(old(values).view().len() - count));
                    interp_run_congruent(store.graph(), tasks.view(), reduced, lifted_values(store.graph(), values.view()), theta, event);
                }
                assert(values.view() =~= old(values).view().take(start as int).push(out));
                if fint::ipre(before, old(tasks).view().push((id, finish)), old(values).view()) {
                    fint::lemma_istep_set(before, store.graph(), id, intersect, old(tasks).view(), old(values).view(), start as int, out);
                }
            }
        } else {
            tasks.push((id, true));
            proof_decl! { let ghost scheduled_base = tasks.view(); }
            proof! { model::lemma_graph_transition_wf(store.graph(), id@); }
            let mut failure = None;
            let mut remaining = count;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant remaining <= count, model::graph_wf(store.graph()), id@ < store.graph().transitions.len(),
                    store.graph() == before, store.valid_store(), store.restoration() == old(store).restoration(),
                    store.errors_are_non_owner() == old(store).errors_are_non_owner(),
                    store.errors_are_non_invariant() == old(store).errors_are_non_invariant(),
                    store.errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
                    store.errors_are_resource() == old(store).errors_are_resource(),
                    old(store).errors_are_non_invalid_policy() ==> !(failure matches Some(HistoryError::InvalidPolicy { .. })),
                    old(store).errors_are_non_invariant() ==> (failure matches Some(error) ==> language::no_invariant_failure::<()>(Err(error))),
                    old(store).errors_are_resource() && old(store).valid_store()
                        ==> (failure matches Some(error) ==> resource_error(error)),
                    old(store).errors_are_non_owner() ==> failure != Some(HistoryError::WrongHistoryOwner),
                    norm::regex_ids_valid(store.graph(), values.view()),
                    count == transition_children(store.graph(), id).len(), interp_tasks_wf(store.graph(), scheduled_base),
                    interp_tasks_wf(store.graph(), tasks.view()),
                    failure.is_none() ==> tasks.view() == scheduled_base + child_interp_tasks(store.graph(), id, remaining as nat),
                ensures failure.is_none() ==> remaining == 0,
                decreases remaining,
            ))]
            // Reverse pushes preserve source order when the LIFO task stack executes children.
            while remaining != 0 {
                let i = loop_try!(
                    match remaining.checked_sub(1) {
                        Some(value) => Ok(value),
                        None => Err(HistoryError::symbolic_invariant()),
                    },
                    failure
                );
                remaining = i;
                let child = loop_try!(id.child(store, i), failure);
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
            proof! {
                interp_stack_children(store.graph(), id, 0, old(tasks).view().push((id, true)), old(values).view().len());
                interp_stack_task(store.graph(), old(tasks).view(), (id, false), old(values).view().len());
                interp_stack_task(store.graph(), old(tasks).view(), (id, true), (old(values).view().len() + count) as nat);
                assert(tasks.view() == old(tasks).view().push((id, true)) + child_interp_tasks(store.graph(), id, 0));
                assert forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len()) implies
                    interp_results_equiv(model::gsem(theta),
                        interp_run(before, old(tasks).view().push((id, finish)), lifted_values(before, old(values).view()), theta, event),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
                    interp_expand_set(store.graph(), id, old(tasks).view(), lifted_values(store.graph(), old(values).view()), theta, event);
                }
                interp_lemma_work_branch(store.graph(), id, old(tasks).view());
                if fint::ipre(before, old(tasks).view().push((id, finish)), old(values).view()) {
                    fint::lemma_istep_expand(before, store.graph(), id, finish, old(tasks).view(), old(values).view());
                }
            }
        }
        proof! {
            interp_stack_stable(before, store.graph(), old(tasks).view().push((id, finish)), old(values).view().len());
            assert forall|atoms: Seq<TestId>| interp_tasks_covered(before, old(tasks).view().push((id, finish)), atoms)
                implies interp_tasks_covered(store.graph(), tasks.view(), atoms) by {
                interp_coverage_stable(before, store.graph(), old(tasks).view().push((id, finish)), atoms);
                assert(old(tasks).view().push((id, finish))[old(tasks).view().len() as int] == (id, finish));
                assert(reach::atoms_wf(store.graph(), id@, atoms));
                transition_coverage_children(store.graph(), id, atoms);
                assert forall|i: int| 0 <= i < tasks.view().len() implies reach::atoms_wf(store.graph(), tasks.view()[i].0@, atoms) by {
                    if i < old(tasks).view().len() {
                        assert(tasks.view()[i] == old(tasks).view()[i]);
                        assert(old(tasks).view().push((id, finish))[i] == old(tasks).view()[i]);
                    } else if i == old(tasks).view().len() {
                        assert(tasks.view()[i].0 == id);
                    } else {
                        let j = transition_children(store.graph(), id).len() - 1 - (i - old(tasks).view().len() - 1);
                        assert(tasks.view()[i].0@ == transition_children(store.graph(), id)[j]);
                    }
                }
            }
        }
        Ok(())
    }

    fn interpret_step<G: KernelStore>(
        this: TransitionId,
        store: &mut G,
        finish: bool,
        atoms: &AtomSet,
        words: &[u64],
        tasks: &mut WorkVec<(TransitionId, bool)>,
        values: &mut WorkVec<RegexId>,
    ) -> (result: KernelResult<()>)
        requires model::graph_wf(old(store).graph()), old(store).valid_store(), this@ < old(store).graph().transitions.len(),
            model::atom_ids_wf(old(store).graph(), atoms@), interp_tasks_wf(old(store).graph(), old(tasks).view()),
            norm::regex_ids_valid(old(store).graph(), old(values).view()),
        ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && reach::atoms_wf(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), words@)
                && interp_stack_result(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view().len()) is Some
                ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && reach::atoms_wf(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), words@)
                && interp_stack_result(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view().len()) is Some
                ==> (result matches Err(error) ==> resource_error(error)),
            result is Ok ==> interp_stack_result(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view().len())
                == interp_stack_result(final(store).graph(), final(tasks).view(), final(values).view().len()),
            interp_tasks_covered(old(store).graph(), old(tasks).view().push((this, finish)), atoms@) && result is Ok
                ==> interp_tasks_covered(final(store).graph(), final(tasks).view(), atoms@),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            interp_tasks_wf(final(store).graph(), final(tasks).view()), norm::regex_ids_valid(final(store).graph(), final(values).view()),
            result.is_ok() ==> interp_machine_relation(old(store).graph(), final(store).graph(), old(tasks).view().push((this, finish)), final(tasks).view(), old(values).view(), final(values).view(), atoms@, words@),
            result.is_ok() ==> interp_work(final(store).graph(), final(tasks).view())
                < interp_work(old(store).graph(), old(tasks).view().push((this, finish))),
            result.is_ok() ==> (fint::ipre(old(store).graph(), old(tasks).view().push((this, finish)), old(values).view())
                ==> fint::istep(final(store).graph(), old(tasks).view().push((this, finish)), final(tasks).view(), old(values).view(), final(values).view()));

    fn interpret<G: KernelStore>(
        this: TransitionId,
        store: &mut G,
        atoms: &AtomSet,
        truth_words: &[u64],
    ) -> (result: KernelResult<RegexId>)
        requires model::graph_wf(old(store).graph()), old(store).valid_store(), this@ < old(store).graph().transitions.len(),
            model::atom_ids_wf(old(store).graph(), atoms@),
        ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
            final(store).restoration() == old(store).restoration(),
            final(store).errors_are_non_owner() == old(store).errors_are_non_owner(),
            final(store).errors_are_non_invariant() == old(store).errors_are_non_invariant(),
            final(store).errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
            final(store).errors_are_resource() == old(store).errors_are_resource(),
            old(store).errors_are_non_invalid_policy() ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            old(store).errors_are_non_invariant() && reach::atoms_wf(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), truth_words@) ==> language::no_invariant_failure(result),
            old(store).errors_are_resource() && old(store).valid_store() && reach::atoms_wf(old(store).graph(), this@, atoms@)
                && assignment_valid(atoms@.len(), truth_words@) ==> (result matches Err(error) ==> resource_error(error)),
            old(store).errors_are_non_owner() ==> result != Err(HistoryError::WrongHistoryOwner),
            result matches Ok(id) ==> id@ < final(store).graph().regexes.len()
                && forall|theta: Subst, event: EventView, word: Seq<EventView>|
                    language::event_wf(theta, theta.len()) && truth_words_realize(old(store).graph(), atoms@, truth_words@, theta, event) ==>
                        model::regex_lang(final(store).graph(), theta, id@, word)
                            == norm::transition_lang(final(store).graph(), theta, this, event, word),
            result matches Ok(id) ==> (ftr::nf_sum(old(store).graph(), this@)
                ==> ftr::tval(final(store).graph(), this@, model::lift_regex(final(store).graph(), id@)));
}
}

#[verus_verify]
impl TransitionInterpret for TransitionId {
    verus! {
    #[verifier::spinoff_prover]
    fn interpret_step<G: KernelStore>(
        this: TransitionId,
        store: &mut G,
        finish: bool,
        atoms: &AtomSet,
        words: &[u64],
        tasks: &mut WorkVec<(TransitionId, bool)>,
        values: &mut WorkVec<RegexId>,
    ) -> KernelResult<()> {
        hide(interp_stack_result); hide(interp_tasks_covered);
        hide(interp_run);
        hide(reach::atoms_wf); hide(test_atoms_covered);
        hide(language::numeric_lang); hide(language::interp_transition);
        hide(model::test_holds); hide(model::lift_transition); hide(model::lift_regex);
        proof_decl! { let ghost before = store.graph(); let ghost pending = tasks.view(); let ghost prior = values.view(); }
        proof! { model::lemma_graph_transition_wf(store.graph(), this@); }
        proof! {
            interp_stack_task(before, pending, (this, finish), prior.len());
            if interp_tasks_covered(before, pending.push((this, finish)), atoms@) {
                interp_coverage_pop(before, pending, (this, finish), atoms@);
            }
            if reach::atoms_wf(store.graph(), this@, atoms@) { transition_coverage_children(store.graph(), this, atoms@); }
        }
        store.checkpoint()?;
        match this.head(store)? {
            TransitionHead::Const(r) => {
                values.push(r);
                proof! {
                    assert forall|theta: Subst, event: EventView|
                        interp_results_equiv(model::gsem(theta),
                            interp_run(store.graph(), pending.push((this, finish)), lifted_values(store.graph(), prior), theta, event),
                            interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
                        norm::transition_unfold(store.graph(), this@);
                        language::lemma_interp_const(model::gsem(theta), event, model::lift_regex(store.graph(), r@));
                        interp_value_reduction(store.graph(), this, finish, pending, lifted_values(store.graph(), prior), lifted_values(store.graph(), values.view()), theta, event);
                    }
                    assert(before.transitions[this@ as int] == store.graph().transitions[this@ as int]);
                    if fint::ipre(before, pending.push((this, finish)), prior) {
                        fint::lemma_istep_const(before, store.graph(), this, finish, pending, prior, r);
                    }
                }
            }
            TransitionHead::If(test, a, b) => {
                proof! {
                    if reach::atoms_wf(before, this@, atoms@) {
                        assert(reach::transition_tests(before, this@) == seq![test@]);
                        assert(reach::transition_tests(before, this@)[0] == test@);
                        assert(test_atoms_covered(before, test@, atoms@));
                    }
                }
                let chosen = if TestId::evaluate(test, store, atoms, words)? {
                    a
                } else {
                    b
                };
                tasks.push((chosen, false));
                proof! {
                    interp_stack_task(store.graph(), pending, (chosen, false), prior.len());
                    if interp_tasks_covered(before, pending.push((this, finish)), atoms@) {
                        assert(reach::transition_edges(before, this@) == seq![a@, b@]);
                        if chosen == a { assert(reach::transition_edges(before, this@)[0] == chosen@); }
                        else { assert(reach::transition_edges(before, this@)[1] == chosen@); }
                        assert(reach::atoms_wf(before, chosen@, atoms@));
                        interp_coverage_push(before, pending, (chosen, false), atoms@);
                    }
                    assert forall|theta: Subst, event: EventView|
                        language::event_wf(theta, theta.len()) && truth_words_realize(before, atoms@, words@, theta, event) implies
                            interp_results_equiv(model::gsem(theta),
                                interp_run(before, pending.push((this, finish)), lifted_values(before, prior), theta, event),
                                interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
                        interp_choose(store.graph(), this, finish, test, a, b, chosen, pending, lifted_values(store.graph(), prior), theta, event);
                    }
                    interp_lemma_work_if(store.graph(), this, finish, pending, chosen);
                    assert(before.transitions[this@ as int] == store.graph().transitions[this@ as int]);
                    if fint::ipre(before, pending.push((this, finish)), prior) {
                        fint::lemma_istep_if(before, store.graph(), this, finish, pending, prior, test@, a, b, chosen);
                    }
                }
            }
            TransitionHead::Union(n) => {
                Self::interpret_branch(store, this, n, false, finish, tasks, values)?
            }
            TransitionHead::Intersect(n) => {
                Self::interpret_branch(store, this, n, true, finish, tasks, values)?
            }
            TransitionHead::Not(inner) => interpret_not(store, this, inner, finish, tasks, values)?,
            TransitionHead::Append(inner, n) => {
                if finish {
                    let head = match values.pop() {
                        Some(v) => v,
                        None => return Err(HistoryError::symbolic_invariant()),
                    };
                    proof! { model::lemma_graph_transition_wf(store.graph(), this@); }
                    let mut xs = WorkVec::new();
                    collect_append_factors(store, this, head, n, &mut xs)?;
                    values.push(RegexId::concat(store, &xs)?);
                    proof! {
                        interp_append_finish(before, store.graph(), this, pending, prior, head, xs.view(), values.view());
                        if fint::ipre(before, pending.push((this, finish)), prior) {
                            fint::lemma_istep_append(before, store.graph(), this, pending, prior, xs.view(), values.view().last());
                        }
                    }
                } else {
                    tasks.push((this, true));
                    tasks.push((inner, false));
                    proof! {
                        interp_stack_task(store.graph(), pending.push((this, true)), (inner, false), prior.len());
                        interp_stack_task(store.graph(), pending, (this, true), prior.len() + 1);
                        if interp_tasks_covered(before, pending.push((this, finish)), atoms@) {
                            assert(reach::transition_edges(before, this@) == seq![inner@]);
                            assert(reach::transition_edges(before, this@)[0] == inner@);
                            assert(reach::atoms_wf(before, inner@, atoms@));
                            interp_coverage_push(before, pending, (this, true), atoms@);
                            interp_coverage_push(before, pending.push((this, true)), (inner, false), atoms@);
                        }
                        assert forall|theta: Subst, event: EventView|
                            interp_run(store.graph(), pending.push((this, finish)), lifted_values(store.graph(), prior), theta, event)
                                == interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event) by {
                            interp_expand_unary(store.graph(), this, inner, pending, lifted_values(store.graph(), prior), theta, event);
                        }
                        interp_lemma_work_unary(store.graph(), this, pending, inner);
                        assert(before.transitions[this@ as int] == store.graph().transitions[this@ as int]);
                        if fint::ipre(before, pending.push((this, finish)), prior) {
                            fint::lemma_istep_unary(before, store.graph(), this, finish, pending, prior, inner);
                        }
                    }
                }
            }
        }
        proof! {
            assert forall|theta: Subst, event: EventView|
                language::event_wf(theta, theta.len()) && truth_words_realize(before, atoms@, words@, theta, event) implies
                    interp_results_equiv(model::gsem(theta),
                        interp_run(before, pending.push((this, finish)), lifted_values(before, prior), theta, event),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event)) by {
                interp_same_configuration_extends(before, store.graph(), pending.push((this, finish)), prior, theta, event);
            }
            interp_lemma_step_post(before, store.graph(), this, finish, pending, tasks.view());
            interp_stack_stable(before, store.graph(), pending.push((this, finish)), prior.len());
            interp_stack_task(store.graph(), pending, (this, finish), prior.len());
            if interp_tasks_covered(before, pending.push((this, finish)), atoms@) {
                interp_coverage_stable(before, store.graph(), pending.push((this, finish)), atoms@);
                interp_coverage_stable(before, store.graph(), pending, atoms@);
                assert(interp_tasks_covered(store.graph(), tasks.view(), atoms@));
            }
        }
        Ok(())
    }
    }
    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure."
    )]
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]

    fn interpret<G: KernelStore>(
        this: TransitionId,
        store: &mut G,
        atoms: &AtomSet,
        truth_words: &[u64],
    ) -> KernelResult<RegexId> {
        proof_decl! { let ghost entry = store.graph(); }
        AtomSet::validate_assignment(atoms, truth_words)?;
        let mut tasks = WorkVec::new();
        let mut values = WorkVec::new();
        tasks.push((this, false));
        let mut state = Ok(());
        proof! {
            assert(tasks.view() == seq![(this, false)]);
            assert(values.view().len() == 0);
            assert(interp_stack_needed(store.graph(), (this, false)) == 0);
            assert(interp_stack_result(store.graph(), Seq::empty(), 1) == Some(1));
            interp_stack_task(store.graph(), Seq::empty(), (this, false), 0);
            assert(interp_stack_result(store.graph(), tasks.view(), 0) == Some(1));
            assert forall|theta: Subst, event: EventView|
                interp_results_equiv(model::gsem(theta),
                    interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event),
                    Some(seq![interpreted(entry, this, theta, event)])) by {
                interp_run_unfold(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event);
                interp_run_unfold(store.graph(), Seq::empty(), seq![interpreted(entry, this, theta, event)], theta, event);
            }
            if ftr::nf_sum(entry, this@) {
                assert(values.view() =~= Seq::<RegexId>::empty());
                assert(tasks.view() =~= seq![(this, false)]);
                fint::lemma_iinit(store.graph(), this);
            }
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant model::graph_extends(entry, store.graph()), model::graph_wf(store.graph()), store.valid_store(),
                store.restoration() == old(store).restoration(),
                store.errors_are_non_owner() == old(store).errors_are_non_owner(),
                store.errors_are_non_invariant() == old(store).errors_are_non_invariant(),
                store.errors_are_non_invalid_policy() == old(store).errors_are_non_invalid_policy(),
                store.errors_are_resource() == old(store).errors_are_resource(),
                old(store).errors_are_non_invalid_policy() ==> !(state matches Err(HistoryError::InvalidPolicy { .. })),
                old(store).errors_are_non_invariant() && reach::atoms_wf(entry, this@, atoms@) ==> language::no_invariant_failure(state),
                old(store).errors_are_resource() && old(store).valid_store() && reach::atoms_wf(entry, this@, atoms@)
                    ==> (state matches Err(error) ==> resource_error(error)),
                assignment_valid(atoms@.len(), truth_words@),
                state is Ok ==> interp_stack_result(store.graph(), tasks.view(), values.view().len()) == Some(1),
                reach::atoms_wf(entry, this@, atoms@) && state is Ok ==> interp_tasks_covered(store.graph(), tasks.view(), atoms@),
                old(store).errors_are_non_owner() ==> state != Err(HistoryError::WrongHistoryOwner),
                model::graph_wf(entry), model::atom_ids_wf(entry, atoms@), this@ < entry.transitions.len(),
                model::atom_ids_wf(store.graph(), atoms@), interp_tasks_wf(store.graph(), tasks.view()), norm::regex_ids_valid(store.graph(), values.view()),
                state.is_ok() ==> forall|theta: Subst, event: EventView|
                    language::event_wf(theta, theta.len()) && truth_words_realize(entry, atoms@, truth_words@, theta, event) ==>
                        interp_results_equiv(model::gsem(theta),
                            interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event),
                            Some(seq![interpreted(entry, this, theta, event)])),
                state.is_ok() && ftr::nf_sum(entry, this@) ==> fint::iinv(store.graph(), this@, tasks.view(), values.view()),
            decreases if state is Ok { interp_work(store.graph(), tasks.view()) + 1 } else { 0 },
        ))]
        while !tasks.is_empty() && state.is_ok() {
            proof_decl! { let ghost before = store.graph(); let ghost pending = tasks.view(); let ghost prior = values.view(); }
            state = match tasks.pop() {
                Some((id, finish)) => {
                    proof! { assert(pending =~= tasks.view().push((id, finish))); }
                    TransitionId::interpret_step(
                        id,
                        store,
                        finish,
                        atoms,
                        truth_words,
                        &mut tasks,
                        &mut values,
                    )
                }
                None => Err(HistoryError::symbolic_invariant()),
            };
            proof! {
                norm::transition_lemma_extends_transitive(entry, before, store.graph());
                truth_words_realize_extends(entry, store.graph(), atoms@, truth_words@);
                assert forall|theta: Subst, event: EventView|
                    state.is_ok() && language::event_wf(theta, theta.len()) && truth_words_realize(entry, atoms@, truth_words@, theta, event) implies
                        interp_results_equiv(model::gsem(theta),
                            interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event),
                            Some(seq![interpreted(entry, this, theta, event)])) by {
                    truth_words_realize_extends(entry, before, atoms@, truth_words@);
                    interp_results_equiv_trans(model::gsem(theta),
                        interp_run(store.graph(), tasks.view(), lifted_values(store.graph(), values.view()), theta, event),
                        interp_run(before, pending, lifted_values(before, prior), theta, event),
                        Some(seq![interpreted(entry, this, theta, event)]));
                }
                if state.is_ok() && ftr::nf_sum(entry, this@) {
                    fint::lemma_iloop(before, store.graph(), this@, pending, prior, tasks.view(), values.view());
                }
            }
        }
        state?;
        proof! {
            interp_root_stable(entry, store.graph(), this);
            if ftr::nf_sum(entry, this@) {
                assert(tasks.view() =~= Seq::<(TransitionId, bool)>::empty());
                fint::lemma_ifinal(store.graph(), this@, values.view());
                assert(values.view().last() == values.view()[0]);
            }
        }
        match values.pop() {
            Some(v) => Ok(v),
            None => Err(HistoryError::symbolic_invariant()),
        }
    }
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    verus! {
    broadcast use {junco_core::kernel::verify::group_kernel_views, vstd::set::group_set_lemmas};

    pub open spec fn test_primitives(t: model::Test) -> Set<model::Primitive>
        decreases t, 1nat, 0nat,
    {
        match t {
            model::Test::Atom(p, _) => Set::empty().insert(p),
            model::Test::And(cs) | model::Test::Or(cs) => test_primitive_prefix(t, cs.len()),
            _ => Set::empty(),
        }
    }

    pub open spec fn test_primitive_prefix(t: model::Test, n: nat) -> Set<model::Primitive>
        decreases t, 0nat, n,
    {
        match t {
            model::Test::And(cs) | model::Test::Or(cs) => if 0 < n <= cs.len() {
                test_primitive_prefix(t, (n - 1) as nat).union(test_primitives(cs[n - 1]))
            } else { Set::empty() },
            _ => Set::empty(),
        }
    }

    pub open spec fn regex_primitives(r: language::Regex<model::Test>) -> Set<model::Primitive>
        decreases r, 1nat, 0nat,
    {
        match r {
            language::Regex::Test(t) => test_primitives(t),
            language::Regex::Union(cs) | language::Regex::Intersect(cs)
                | language::Regex::Concat(cs) => regex_primitive_prefix(r, cs.len()),
            language::Regex::Star(b) | language::Regex::Not(b) => regex_primitives(*b),
            _ => Set::empty(),
        }
    }

    pub open spec fn regex_primitive_prefix(r: language::Regex<model::Test>, n: nat) -> Set<model::Primitive>
        decreases r, 0nat, n,
    {
        match r {
            language::Regex::Union(cs) | language::Regex::Intersect(cs)
                | language::Regex::Concat(cs) => if 0 < n <= cs.len() {
                    regex_primitive_prefix(r, (n - 1) as nat).union(regex_primitives(cs[n - 1]))
                } else { Set::empty() },
            _ => Set::empty(),
        }
    }

    pub proof fn lemma_test_primitive_prefix(t: model::Test, n: nat, p: model::Primitive)
        requires t is And || t is Or, n <= crate::verify::finite_impl::test_kids(t).len(),
        ensures test_primitive_prefix(t, n).contains(p)
            == (exists|i: int| 0 <= i < n && test_primitives(crate::verify::finite_impl::test_kids(t)[i]).contains(p)),
        decreases n,
    {
        let cs = crate::verify::finite_impl::test_kids(t);
        reveal_with_fuel(test_primitive_prefix, 1);
        if n > 0 {
            lemma_test_primitive_prefix(t, (n - 1) as nat, p);
            assert(test_primitive_prefix(t, (n - 1) as nat).contains(p)
                == (exists|i: int| 0 <= i < n - 1 && test_primitives(cs[i]).contains(p)));
            if exists|i: int| 0 <= i < n && test_primitives(cs[i]).contains(p) {
                let i = choose|i: int| 0 <= i < n && test_primitives(cs[i]).contains(p);
                if i < n - 1 {
                    assert(exists|j: int| 0 <= j < n - 1 && test_primitives(cs[j]).contains(p));
                } else { assert(i == n - 1); }
            }
            if test_primitive_prefix(t, (n - 1) as nat).contains(p) {
                let j = choose|j: int| 0 <= j < n - 1 && test_primitives(cs[j]).contains(p);
                assert(exists|i: int| 0 <= i < n && test_primitives(cs[i]).contains(p));
            }
            if test_primitives(cs[n - 1]).contains(p) {
                assert(exists|i: int| 0 <= i < n && test_primitives(cs[i]).contains(p));
            }
        }
    }

    pub proof fn lemma_test_pair_vocab(a: model::Test, b: model::Test)
        ensures test_primitives(model::Test::And(seq![a, b])) == test_primitives(a).union(test_primitives(b)),
    {
        reveal_with_fuel(test_primitive_prefix, 3);
        reveal_with_fuel(test_primitives, 3);
        assert(test_primitives(model::Test::And(seq![a, b])) =~= test_primitives(a).union(test_primitives(b)));
    }

    pub open spec fn regex_kids(r: language::Regex<model::Test>) -> Seq<language::Regex<model::Test>> {
        match r {
            language::Regex::Union(cs) | language::Regex::Intersect(cs) | language::Regex::Concat(cs) => cs,
            _ => Seq::empty(),
        }
    }

    pub proof fn lemma_regex_primitive_prefix(r: language::Regex<model::Test>, n: nat, p: model::Primitive)
        requires r is Union || r is Intersect || r is Concat, n <= regex_kids(r).len(),
        ensures regex_primitive_prefix(r, n).contains(p)
            == (exists|i: int| 0 <= i < n && regex_primitives(regex_kids(r)[i]).contains(p)),
        decreases n,
    {
        let cs = regex_kids(r);
        reveal_with_fuel(regex_primitive_prefix, 1);
        if n > 0 {
            lemma_regex_primitive_prefix(r, (n - 1) as nat, p);
            assert(regex_primitive_prefix(r, (n - 1) as nat).contains(p)
                == (exists|i: int| 0 <= i < n - 1 && regex_primitives(cs[i]).contains(p)));
            if exists|i: int| 0 <= i < n && regex_primitives(cs[i]).contains(p) {
                let i = choose|i: int| 0 <= i < n && regex_primitives(cs[i]).contains(p);
                if i < n - 1 { assert(exists|j: int| 0 <= j < n - 1 && regex_primitives(cs[j]).contains(p)); }
                else { assert(i == n - 1); }
            }
            if regex_primitive_prefix(r, (n - 1) as nat).contains(p) {
                let j = choose|j: int| 0 <= j < n - 1 && regex_primitives(cs[j]).contains(p);
                assert(exists|i: int| 0 <= i < n && regex_primitives(cs[i]).contains(p));
            }
            if regex_primitives(cs[n - 1]).contains(p) {
                assert(exists|i: int| 0 <= i < n && regex_primitives(cs[i]).contains(p));
            }
        }
    }

    pub proof fn lemma_test_primitives_lift(g: model::Graph, id: nat, p: model::Primitive)
        requires model::graph_wf(g), id < g.tests.len(),
        ensures test_primitives(model::lift_test(g, id)).contains(p)
            == reach::test_reaches_primitive(g, id, p),
        decreases id,
    {
        model::lemma_graph_test_wf(g, id);
        reveal_with_fuel(model::lift_test, 1);
        reveal_with_fuel(model::lift_tests, 1);
        reveal_with_fuel(test_primitives, 1);
        reveal_with_fuel(reach::test_reaches_primitive, 1);
        match g.tests[id as int] {
            model::TestNode::And(cs) | model::TestNode::Or(cs) => {
                let t = model::lift_test(g, id);
                lemma_test_primitive_prefix(t, cs.len(), p);
                assert forall|i: int| 0 <= i < cs.len() implies
                    test_primitives(model::lift_tests(g, cs, id)[i]).contains(p)
                        == reach::test_reaches_primitive(g, cs[i], p) by {
                    lemma_test_primitives_lift(g, cs[i], p);
                }
                if test_primitives(t).contains(p) {
                    let i = choose|i: int| 0 <= i < cs.len() && test_primitives(model::lift_tests(g, cs, id)[i]).contains(p);
                    assert(reach::test_edges(g, id)[i] == cs[i]);
                    assert(cs[i] < id);
                    assert(reach::test_reaches_primitive(g, id, p));
                }
                if reach::test_reaches_primitive(g, id, p) {
                    let i = choose|i: int| 0 <= i < cs.len() && cs[i] < id && reach::test_reaches_primitive(g, cs[i], p);
                    assert(test_primitives(model::lift_tests(g, cs, id)[i]).contains(p));
                    assert(test_primitives(crate::verify::finite_impl::test_kids(t)[i]).contains(p));
                }
            },
            _ => {},
        }
    }

    pub proof fn lemma_regex_primitives_stable(a: model::Graph, b: model::Graph, q: nat)
        requires model::graph_wf(a), model::graph_extends(a, b), q < a.regexes.len(),
        ensures regex_primitives(model::lift_regex(a, q)) == regex_primitives(model::lift_regex(b, q)),
    {
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_regex_stable(a, b, q);
    }

    pub proof fn lemma_test_primitive_code(t: model::Test, c: history_syntax::Component, v: nat)
        ensures test_primitives(t).contains(model::Primitive::Eq(c, model::GTerm::Constant(v)))
            == crate::verify::refinement::encoding::test_mentions(t, c, v),
        decreases t,
    {
        reveal_with_fuel(test_primitives, 1);
        reveal_with_fuel(crate::verify::refinement::encoding::test_mentions, 1);
        reveal(crate::verify::refinement::encoding::test_mention_child);
        let p = model::Primitive::Eq(c, model::GTerm::Constant(v));
        match t {
            model::Test::And(cs) => {
                lemma_test_primitive_prefix(t, cs.len(), p);
                assert forall|i: int| #![trigger cs[i]] 0 <= i < cs.len() implies
                    test_primitives(cs[i]).contains(p) == crate::verify::refinement::encoding::test_mentions(cs[i], c, v) by {
                    lemma_test_primitive_code(cs[i], c, v);
                }
                if test_primitives(t).contains(p) {
                    let i = choose|i: int| 0 <= i < cs.len() && test_primitives(cs[i]).contains(p);
                    lemma_test_primitive_code(cs[i], c, v);
                    assert(crate::verify::refinement::encoding::test_mention_child(t, i) == Some(cs[i]));
                    assert(exists|j: int| #![trigger crate::verify::refinement::encoding::test_mention_child(t, j)]
                        0 <= j < cs.len() && crate::verify::refinement::encoding::test_mentions(cs[j], c, v));
                }
                if crate::verify::refinement::encoding::test_mentions(t, c, v) {
                    let i = choose|i: int| #![trigger crate::verify::refinement::encoding::test_mention_child(t, i)]
                        0 <= i < cs.len() && crate::verify::refinement::encoding::test_mentions(cs[i], c, v);
                    lemma_test_primitive_code(cs[i], c, v);
                    assert(test_primitives(cs[i]).contains(p));
                }
            },
            model::Test::Or(cs) => {
                lemma_test_primitive_prefix(t, cs.len(), p);
                assert forall|i: int| #![trigger cs[i]] 0 <= i < cs.len() implies
                    test_primitives(cs[i]).contains(p) == crate::verify::refinement::encoding::test_mentions(cs[i], c, v) by {
                    lemma_test_primitive_code(cs[i], c, v);
                }
                if test_primitives(t).contains(p) {
                    let i = choose|i: int| 0 <= i < cs.len() && test_primitives(cs[i]).contains(p);
                    lemma_test_primitive_code(cs[i], c, v);
                    assert(crate::verify::refinement::encoding::test_mention_child(t, i) == Some(cs[i]));
                    assert(exists|j: int| #![trigger crate::verify::refinement::encoding::test_mention_child(t, j)]
                        0 <= j < cs.len() && crate::verify::refinement::encoding::test_mentions(cs[j], c, v));
                }
                if crate::verify::refinement::encoding::test_mentions(t, c, v) {
                    let i = choose|i: int| #![trigger crate::verify::refinement::encoding::test_mention_child(t, i)]
                        0 <= i < cs.len() && crate::verify::refinement::encoding::test_mentions(cs[i], c, v);
                    lemma_test_primitive_code(cs[i], c, v);
                    assert(test_primitives(cs[i]).contains(p));
                }
            },
            _ => {},
        }
    }

    pub proof fn lemma_regex_primitive_code(r: language::Regex<model::Test>, c: history_syntax::Component, v: nat)
        ensures regex_primitives(r).contains(model::Primitive::Eq(c, model::GTerm::Constant(v)))
            == crate::verify::refinement::encoding::regex_mentions(r, c, v),
        decreases r,
    {
        reveal_with_fuel(regex_primitives, 1);
        reveal_with_fuel(crate::verify::refinement::encoding::regex_mentions, 2);
        reveal(crate::verify::refinement::encoding::regex_mention_child);
        let p = model::Primitive::Eq(c, model::GTerm::Constant(v));
        match r {
            language::Regex::Test(t) => { lemma_test_primitive_code(t, c, v); },
            language::Regex::Star(b) | language::Regex::Not(b) => {
                lemma_regex_primitive_code(*b, c, v);
            },
            language::Regex::Union(cs) | language::Regex::Intersect(cs) | language::Regex::Concat(cs) => {
                lemma_regex_primitive_prefix(r, cs.len(), p);
                assert forall|i: int| 0 <= i < cs.len() implies
                    regex_primitives(cs[i]).contains(p)
                        == crate::verify::refinement::encoding::regex_mentions(cs[i], c, v) by {
                    lemma_regex_primitive_code(cs[i], c, v);
                }
                if regex_primitives(r).contains(p) {
                    let i = choose|i: int| 0 <= i < cs.len() && regex_primitives(cs[i]).contains(p);
                    lemma_regex_primitive_code(cs[i], c, v);
                    assert(crate::verify::refinement::encoding::regex_mentions(cs[i], c, v));
                    assert(crate::verify::refinement::encoding::regex_mention_child(r, i) == Some(cs[i]));
                    assert(exists|j: int| #![trigger crate::verify::refinement::encoding::regex_mention_child(r, j)]
                        0 <= j < regex_kids(r).len() && crate::verify::refinement::encoding::regex_mentions(regex_kids(r)[j], c, v));
                    assert(crate::verify::refinement::encoding::regex_mentions(r, c, v));
                }
                if crate::verify::refinement::encoding::regex_mentions(r, c, v) {
                    let i = choose|i: int| 0 <= i < cs.len() && crate::verify::refinement::encoding::regex_mentions(cs[i], c, v);
                    lemma_regex_primitive_code(cs[i], c, v);
                    assert(regex_primitives(regex_kids(r)[i]).contains(p));
                }
            },
            _ => {},
        }
    }

    /// Primitives tested now; tests in constant residuals and append suffixes are tested later.
    pub open spec fn transition_primitives(t: language::Transition<model::Test>) -> Set<model::Primitive>
        decreases t, 1nat, 0nat,
    {
        match t {
            language::Transition::Const(_) => Set::empty(),
            language::Transition::If(test, a, b) => test_primitives(test)
                .union(transition_primitives(*a)).union(transition_primitives(*b)),
            language::Transition::Union(cs) | language::Transition::Intersect(cs) =>
                transition_primitive_prefix(t, cs.len()),
            language::Transition::Not(b) | language::Transition::Append(b, _) => transition_primitives(*b),
        }
    }

    pub open spec fn transition_primitive_prefix(t: language::Transition<model::Test>, n: nat) -> Set<model::Primitive>
        decreases t, 0nat, n,
    {
        match t {
            language::Transition::Union(cs) | language::Transition::Intersect(cs) => if 0 < n <= cs.len() {
                transition_primitive_prefix(t, (n - 1) as nat).union(transition_primitives(cs[n - 1]))
            } else { Set::empty() },
            _ => Set::empty(),
        }
    }

    pub open spec fn transition_kids(t: language::Transition<model::Test>) -> Seq<language::Transition<model::Test>> {
        match t { language::Transition::Union(cs) | language::Transition::Intersect(cs) => cs, _ => Seq::empty() }
    }

    pub proof fn lemma_transition_primitive_prefix(t: language::Transition<model::Test>, n: nat, p: model::Primitive)
        requires t is Union || t is Intersect, n <= transition_kids(t).len(),
        ensures transition_primitive_prefix(t, n).contains(p)
            == (exists|i: int| 0 <= i < n && transition_primitives(transition_kids(t)[i]).contains(p)),
        decreases n,
    {
        let cs = transition_kids(t);
        reveal_with_fuel(transition_primitive_prefix, 1);
        if n > 0 {
            lemma_transition_primitive_prefix(t, (n - 1) as nat, p);
            assert(transition_primitive_prefix(t, (n - 1) as nat).contains(p)
                == (exists|i: int| 0 <= i < n - 1 && transition_primitives(cs[i]).contains(p)));
            if exists|i: int| 0 <= i < n && transition_primitives(cs[i]).contains(p) {
                let i = choose|i: int| 0 <= i < n && transition_primitives(cs[i]).contains(p);
                if i < n - 1 { assert(exists|j: int| 0 <= j < n - 1 && transition_primitives(cs[j]).contains(p)); }
                else { assert(i == n - 1); }
            }
            if transition_primitive_prefix(t, (n - 1) as nat).contains(p) {
                let j = choose|j: int| 0 <= j < n - 1 && transition_primitives(cs[j]).contains(p);
                assert(exists|i: int| 0 <= i < n && transition_primitives(cs[i]).contains(p));
            }
            if transition_primitives(cs[n - 1]).contains(p) {
                assert(exists|i: int| 0 <= i < n && transition_primitives(cs[i]).contains(p));
            }
        }
    }

    pub proof fn lemma_transition_primitives_lift(g: model::Graph, id: nat, p: model::Primitive)
        requires model::graph_wf(g), id < g.transitions.len(),
        ensures transition_primitives(model::lift_transition(g, id)).contains(p)
            == reach::transition_reaches_primitive(g, id, p),
        decreases id,
    {
        model::lemma_graph_transition_wf(g, id);
        norm::transition_unfold(g, id);
        reveal_with_fuel(transition_primitives, 1);
        reveal_with_fuel(reach::transition_reaches_primitive, 1);
        assert forall|j: int| #![trigger reach::transition_edges(g, id)[j]]
            0 <= j < reach::transition_edges(g, id).len() implies
                transition_primitives(model::lift_transition(g, reach::transition_edges(g, id)[j])).contains(p)
                    == reach::transition_reaches_primitive(g, reach::transition_edges(g, id)[j], p) by {
            lemma_transition_primitives_lift(g, reach::transition_edges(g, id)[j], p);
        }
        match g.transitions[id as int] {
            model::TransitionNode::If(t, a, b) => {
                lemma_test_primitives_lift(g, t, p);
                lemma_transition_primitives_lift(g, a, p);
                lemma_transition_primitives_lift(g, b, p);
                assert(reach::transition_tests(g, id) == seq![t]);
                assert(reach::transition_edges(g, id) == seq![a, b]);
                if reach::test_reaches_primitive(g, t, p) || reach::transition_reaches_primitive(g, a, p)
                    || reach::transition_reaches_primitive(g, b, p) {
                    if reach::test_reaches_primitive(g, t, p) {
                        assert(reach::transition_tests(g, id)[0] == t);
                    } else if reach::transition_reaches_primitive(g, a, p) {
                        assert(reach::transition_edges(g, id)[0] == a);
                    } else { assert(reach::transition_edges(g, id)[1] == b); }
                    assert(reach::transition_reaches_primitive(g, id, p));
                }
                assert(reach::transition_reaches_primitive(g, id, p) == (reach::test_reaches_primitive(g, t, p)
                    || reach::transition_reaches_primitive(g, a, p) || reach::transition_reaches_primitive(g, b, p)));
            },
            model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => {
                let lifted = model::lift_transition(g, id);
                lemma_transition_primitive_prefix(lifted, cs.len(), p);
                reveal_with_fuel(model::lift_transitions, 1);
                assert(transition_kids(lifted) == model::lift_transitions(g, cs, id));
                assert forall|j: int| 0 <= j < cs.len() implies
                    model::lift_transitions(g, cs, id)[j] == model::lift_transition(g, cs[j]) by {}
                if transition_primitives(lifted).contains(p) {
                    let i = choose|i: int| 0 <= i < cs.len() && transition_primitives(model::lift_transitions(g, cs, id)[i]).contains(p);
                    assert(reach::transition_edges(g, id)[i] == cs[i]);
                    assert(cs[i] < id);
                    assert(reach::transition_reaches_primitive(g, id, p));
                }
                if reach::transition_reaches_primitive(g, id, p) {
                    let i = choose|i: int| 0 <= i < cs.len() && cs[i] < id && reach::transition_reaches_primitive(g, cs[i], p);
                    assert(transition_primitives(transition_kids(lifted)[i]).contains(p));
                }
            },
            model::TransitionNode::Not(child) | model::TransitionNode::Append(child, _) => {
                lemma_transition_primitives_lift(g, child, p);
                assert(reach::transition_tests(g, id) == Seq::<nat>::empty());
                assert(reach::transition_edges(g, id) == seq![child]);
                assert(reach::transition_edges(g, id)[0] == child);
                assert(reach::transition_reaches_primitive(g, id, p)
                    == reach::transition_reaches_primitive(g, child, p));
            },
            _ => {},
        }
    }

    pub open spec fn derivative_vocab(g: model::Graph, q: nat, t: nat) -> bool {
        transition_primitives(model::lift_transition(g, t)).subset_of(regex_primitives(model::lift_regex(g, q)))
    }

    pub proof fn lemma_derivative_vocab_stable(a: model::Graph, b: model::Graph, q: nat, t: nat)
        requires model::graph_wf(a), model::graph_extends(a, b), q < a.regexes.len(), t < a.transitions.len(),
            derivative_vocab(a, q, t),
        ensures derivative_vocab(b, q, t),
    {
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
    }

    pub proof fn lemma_test_negation_primitives(g: model::Graph, relation: Set<(nat, nat)>, a: nat, b: nat, p: model::Primitive)
        requires model::graph_wf(g), norm::test_negation_witness(g, relation), relation.contains((a, b)),
        ensures reach::test_reaches_primitive(g, a, p) == reach::test_reaches_primitive(g, b, p),
        decreases a,
    {
        norm::test_lemma_negation_witness_elim(g, relation);
        reveal(norm::test_negation_row);
        reveal_with_fuel(reach::test_reaches_primitive, 1);
        match (g.tests[a as int], g.tests[b as int]) {
            (model::TestNode::And(cs), model::TestNode::Or(ds))
                | (model::TestNode::Or(cs), model::TestNode::And(ds)) => {
                if reach::test_reaches_primitive(g, a, p) {
                    let i = choose|i: int| 0 <= i < cs.len() && cs[i] < a && reach::test_reaches_primitive(g, cs[i], p);
                    assert(cs.contains(cs[i]));
                    let d = choose|d: nat| ds.contains(d) && relation.contains((cs[i], d));
                    lemma_test_negation_primitives(g, relation, cs[i], d, p);
                    let j = ds.lemma_contains_to_index(d);
                    assert(d < b);
                    assert(reach::test_edges(g, b) == ds);
                    assert(ds[j] == d);
                    assert(exists|k: int| 0 <= k < reach::test_edges(g, b).len()
                        && reach::test_edges(g, b)[k] < b && reach::test_reaches_primitive(g, reach::test_edges(g, b)[k], p));
                    assert(reach::test_reaches_primitive(g, b, p));
                }
                if reach::test_reaches_primitive(g, b, p) {
                    let j = choose|j: int| 0 <= j < ds.len() && ds[j] < b && reach::test_reaches_primitive(g, ds[j], p);
                    assert(ds.contains(ds[j]));
                    let c = choose|c: nat| cs.contains(c) && relation.contains((c, ds[j]));
                    let i = cs.lemma_contains_to_index(c);
                    assert(c < a);
                    lemma_test_negation_primitives(g, relation, c, ds[j], p);
                    assert(reach::test_edges(g, a) == cs);
                    assert(cs[i] == c);
                    assert(exists|k: int| 0 <= k < reach::test_edges(g, a).len()
                        && reach::test_edges(g, a)[k] < a && reach::test_reaches_primitive(g, reach::test_edges(g, a)[k], p));
                    assert(reach::test_reaches_primitive(g, a, p));
                }
            },
            _ => {},
        }
    }

    pub proof fn lemma_test_not_done_primitives(g: model::Graph, values: Seq<TestId>, root: TestId)
        requires model::graph_wf(g), norm::test_not_state(g, Seq::empty(), values, root),
        ensures values.len() == 1,
            test_primitives(model::lift_test(g, values[0]@)) == test_primitives(model::lift_test(g, root@)),
    {
        let (origins, relation) = choose|origins: Seq<nat>, relation: Set<(nat, nat)>|
            origins.len() == values.len() && norm::test_negation_witness(g, relation)
            && (forall|i: int| 0 <= i < values.len() ==> relation.contains((origins[i], values[i]@)))
            && norm::test_not_plan(g, Seq::empty(), origins) == Some(seq![root@]);
        assert(origins == seq![root@]);
        assert(values.len() == 1);
        assert(0 <= 0 < values.len());
        assert(origins[0] == root@);
        assert(relation.contains((origins[0], values[0]@)));
        assert(relation.contains((root@, values[0]@)));
        norm::test_lemma_negation_witness_elim(g, relation);
        reveal(norm::test_negation_row);
        assert forall|p: model::Primitive| test_primitives(model::lift_test(g, values[0]@)).contains(p)
            == test_primitives(model::lift_test(g, root@)).contains(p) by {
            lemma_test_primitives_lift(g, values[0]@, p);
            lemma_test_primitives_lift(g, root@, p);
            lemma_test_negation_primitives(g, relation, root@, values[0]@, p);
        }
        assert(test_primitives(model::lift_test(g, values[0]@)) =~= test_primitives(model::lift_test(g, root@)));
    }

    pub proof fn lemma_test_member_bound(g: model::Graph, children: Seq<TestId>, and: bool, t: nat)
        requires model::graph_wf(g), norm::test_ids_valid(g, children), norm::test_member(g, children, and, t),
        ensures t < g.tests.len(),
    {
        let i = choose|i: int| 0 <= i < children.len() && norm::test_piece_contains(g, children[i]@, and, t);
        crate::verify::finite_link::lemma_test_piece_link(g, children[i]@, and, t);
    }

    pub proof fn lemma_test_member_primitives(g: model::Graph, children: Seq<TestId>, and: bool, t: nat, p: model::Primitive)
        requires model::graph_wf(g), norm::test_ids_valid(g, children), norm::test_member(g, children, and, t),
            reach::test_reaches_primitive(g, t, p),
        ensures exists|i: int| 0 <= i < children.len() && reach::test_reaches_primitive(g, children[i]@, p),
    {
        let i = choose|i: int| 0 <= i < children.len() && norm::test_piece_contains(g, children[i]@, and, t);
        let c = children[i]@;
        model::lemma_graph_test_wf(g, c);
        match g.tests[c as int] {
            model::TestNode::And(cs) => if and {
                let j = cs.lemma_contains_to_index(t);
                assert(cs[j] < c);
                assert(reach::test_edges(g, c) == cs);
                assert(reach::test_reaches_primitive(g, c, p));
            },
            model::TestNode::Or(cs) => if !and {
                let j = cs.lemma_contains_to_index(t);
                assert(cs[j] < c);
                assert(reach::test_edges(g, c) == cs);
                assert(reach::test_reaches_primitive(g, c, p));
            },
            _ => {},
        }
        assert(reach::test_reaches_primitive(g, children[i]@, p));
    }

    pub proof fn lemma_test_connective_primitives(a: model::Graph, b: model::Graph, children: Seq<TestId>, and: bool, t: nat, p: model::Primitive)
        requires model::graph_wf(a), model::graph_wf(b), model::graph_extends(a, b),
            norm::test_ids_valid(a, children), t < b.tests.len(),
            norm::test_connective_result(a, b, children, and, t),
            test_primitives(model::lift_test(b, t)).contains(p),
        ensures exists|i: int| 0 <= i < children.len()
            && test_primitives(model::lift_test(a, children[i]@)).contains(p),
    {
        lemma_test_primitives_lift(b, t, p);
        model::lemma_graph_wf_elim(a);
        if t == a.constants.test_true || t == a.constants.test_false {
            assert(b.tests[t as int] == a.tests[t as int]);
            assert(!reach::test_reaches_primitive(b, t, p));
        } else if norm::test_member(a, children, and, t) {
            lemma_test_member_bound(a, children, and, t);
            reach::lemma_test_reaches_stable(a, b, t, p);
            lemma_test_member_primitives(a, children, and, t, p);
            let i = choose|i: int| 0 <= i < children.len() && reach::test_reaches_primitive(a, children[i]@, p);
            lemma_test_primitives_lift(a, children[i]@, p);
        } else {
            model::lemma_graph_test_wf(b, t);
            let j = choose|j: int| 0 <= j < reach::test_edges(b, t).len()
                && reach::test_edges(b, t)[j] < t && reach::test_reaches_primitive(b, reach::test_edges(b, t)[j], p);
            let c = reach::test_edges(b, t)[j];
            assert(norm::test_member(a, children, and, c));
            lemma_test_member_bound(a, children, and, c);
            reach::lemma_test_reaches_stable(a, b, c, p);
            lemma_test_member_primitives(a, children, and, c, p);
            let i = choose|i: int| 0 <= i < children.len() && reach::test_reaches_primitive(a, children[i]@, p);
            lemma_test_primitives_lift(a, children[i]@, p);
        }
    }

    pub proof fn lemma_test_piece_vocab(inter: bool, psi: model::Test, phi: model::Test)
        requires crate::verify::finite_impl::test_piece(inter, psi, phi),
        ensures test_primitives(phi).subset_of(test_primitives(psi)),
    {
        assert forall|p: model::Primitive| test_primitives(phi).contains(p) implies
            test_primitives(psi).contains(p) by {
            match psi {
                model::Test::And(cs) | model::Test::Or(cs) => {
                    if phi != psi {
                        let i = cs.lemma_contains_to_index(phi);
                        lemma_test_primitive_prefix(psi, cs.len(), p);
                        assert(test_primitives(cs[i]).contains(p));
                    }
                },
                _ => {},
            }
        }
    }

    pub proof fn lemma_test_combo_vocab(inter: bool, xs: Set<language::Regex<model::Test>>, phi: model::Test, allowed: Set<model::Primitive>)
        requires crate::verify::finite_impl::test_combo(inter, xs, phi),
            forall|r: language::Regex<model::Test>| xs.contains(r) ==> regex_primitives(r).subset_of(allowed),
        ensures test_primitives(phi).subset_of(allowed),
    {
        assert forall|psi: model::Test| crate::verify::finite_impl::piece_of(inter, xs, psi) implies
            test_primitives(psi).subset_of(allowed) by {
            let parent = choose|parent: model::Test| xs.contains(language::Regex::Test(parent))
                && crate::verify::finite_impl::test_piece(inter, parent, psi);
            lemma_test_piece_vocab(inter, parent, psi);
            assert(regex_primitives(language::Regex::Test(parent)) == test_primitives(parent));
        }
        assert forall|p: model::Primitive| test_primitives(phi).contains(p) implies allowed.contains(p) by {
            if !crate::verify::finite_impl::piece_of(inter, xs, phi) {
                match phi {
                    model::Test::And(cs) | model::Test::Or(cs) => {
                        lemma_test_primitive_prefix(phi, cs.len(), p);
                        let i = choose|i: int| 0 <= i < cs.len() && test_primitives(cs[i]).contains(p);
                        assert(crate::verify::finite_impl::test_kids(phi)[i] == cs[i]);
                        assert(crate::verify::finite_impl::piece_of(inter, xs, cs[i]));
                        assert(test_primitives(cs[i]).subset_of(allowed));
                    },
                    _ => {},
                }
            }
        }
    }

    pub proof fn lemma_sops_vocab(inter: bool, r: language::Regex<model::Test>, allowed: Set<model::Primitive>)
        requires regex_primitives(r).subset_of(allowed),
        ensures forall|o: language::Regex<model::Test>|
            crate::verify::finite_impl::pre().sops(inter, r).contains(o) ==> regex_primitives(o).subset_of(allowed),
    {
        assert forall|o: language::Regex<model::Test>|
            crate::verify::finite_impl::pre().sops(inter, r).contains(o) implies regex_primitives(o).subset_of(allowed) by {
            match r {
                language::Regex::Union(cs) | language::Regex::Intersect(cs) => {
                    if o != r {
                        let i = cs.lemma_contains_to_index(o);
                        assert forall|p: model::Primitive| regex_primitives(o).contains(p) implies allowed.contains(p) by {
                            lemma_regex_primitive_prefix(r, cs.len(), p);
                            assert(regex_primitives(cs[i]).contains(p));
                            assert(regex_primitives(r).contains(p));
                        }
                    }
                },
                _ => {},
            }
        }
    }

    pub proof fn lemma_nset_vocab(inter: bool, xs: Set<language::Regex<model::Test>>, out: language::Regex<model::Test>, allowed: Set<model::Primitive>)
        requires (crate::verify::finite_impl::core().nset)(inter, xs, out),
            forall|r: language::Regex<model::Test>| xs.contains(r) ==> regex_primitives(r).subset_of(allowed),
        ensures regex_primitives(out).subset_of(allowed),
    {
        reveal(crate::verify::finite_states::Model::combo_from);
        reveal(crate::verify::finite_states::Model::in_sops_of);
        let m = crate::verify::finite_impl::pre();
        assert(m.nset_shape(inter, xs, out));
        assert forall|r: language::Regex<model::Test>| xs.contains(r) implies
            forall|o: language::Regex<model::Test>| m.sops(inter, r).contains(o) ==> regex_primitives(o).subset_of(allowed) by {
            lemma_sops_vocab(inter, r, allowed);
        }
        assert forall|o: language::Regex<model::Test>| m.sops(inter, out).contains(o) implies
            regex_primitives(o).subset_of(allowed) by {
            if m.in_sops_of(inter, xs, o) {
                let r = choose|r: language::Regex<model::Test>| xs.contains(r) && m.sops(inter, r).contains(o);
            } else if !m.is_const(out) {
                let ts = choose|ts: Set<language::Regex<model::Test>>| m.combo_from(inter, xs, ts, o);
                assert(m.combo_from(inter, xs, ts, o));
                assert(forall|r: language::Regex<model::Test>| #![trigger ts.contains(r)] ts.contains(r) ==> m.is_test(r) && m.in_sops_of(inter, xs, r));
                assert forall|r: language::Regex<model::Test>| ts.contains(r) implies regex_primitives(r).subset_of(allowed) by {
                    assert(m.in_sops_of(inter, xs, r));
                    let parent = choose|parent: language::Regex<model::Test>| xs.contains(parent) && m.sops(inter, parent).contains(r);
                }
                match o {
                    language::Regex::Test(phi) => { lemma_test_combo_vocab(inter, ts, phi, allowed); },
                    _ => {},
                }
            }
        }
        assert forall|p: model::Primitive| regex_primitives(out).contains(p) implies allowed.contains(p) by {
            match out {
                language::Regex::Union(cs) | language::Regex::Intersect(cs) => {
                    if m.is_set(inter, out) {
                        lemma_regex_primitive_prefix(out, cs.len(), p);
                        let i = choose|i: int| 0 <= i < cs.len() && regex_primitives(cs[i]).contains(p);
                        assert(m.sops(inter, out).contains(cs[i]));
                    }
                },
                _ => {},
            }
            if !m.is_set(inter, out) { assert(m.sops(inter, out).contains(out)); }
        }
    }

    pub proof fn lemma_built_vocab(inter: bool, base: spec_fn(language::Regex<model::Test>) -> bool,
        out: language::Regex<model::Test>, allowed: Set<model::Primitive>)
        requires crate::verify::finite_impl::m_impl().built(inter, base, out),
            forall|r: language::Regex<model::Test>| base(r) ==> regex_primitives(r).subset_of(allowed),
        ensures regex_primitives(out).subset_of(allowed),
    {
        broadcast use vstd::iset::lemma_iset_new;
        crate::verify::finite_impl::lemma_models_agree();
        let m = crate::verify::finite_impl::m_impl();
        let carrier = ISet::new(|r: language::Regex<model::Test>| regex_primitives(r).subset_of(allowed));
        assert(m.has_consts(carrier));
        assert(m.nset_closed(inter, carrier)) by {
            assert forall|xs: Set<language::Regex<model::Test>>, r: language::Regex<model::Test>|
                (forall|x: language::Regex<model::Test>| xs.contains(x) ==> carrier.contains(x))
                    && #[trigger] (m.nset)(inter, xs, r) implies carrier.contains(r) by {
                assert forall|x: language::Regex<model::Test>| xs.contains(x) implies regex_primitives(x).subset_of(allowed) by {
                    assert(carrier.contains(x));
                }
                lemma_nset_vocab(inter, xs, r, allowed);
            }
        }
        assert(carrier.contains(out));
    }

    pub proof fn lemma_not_vocab(r: language::Regex<model::Test>)
        ensures regex_primitives(crate::verify::finite_impl::r_not(r)).subset_of(regex_primitives(r)),
    {
        match r { language::Regex::Not(b) => {}, _ => {} }
    }

    pub proof fn lemma_flat_vocab(xs: Seq<language::Regex<model::Test>>, allowed: Set<model::Primitive>)
        requires forall|i: int| 0 <= i < xs.len() ==> regex_primitives(xs[i]).subset_of(allowed),
        ensures forall|r: language::Regex<model::Test>| crate::verify::finite_impl::pre().flat(xs).contains(r)
            ==> regex_primitives(r).subset_of(allowed),
        decreases xs.len(),
    {
        if xs.len() > 0 {
            let m = crate::verify::finite_impl::pre();
            lemma_flat_vocab(xs.drop_last(), allowed);
            assert forall|r: language::Regex<model::Test>| m.flat(xs).contains(r) implies
                regex_primitives(r).subset_of(allowed) by {
                if !m.flat(xs.drop_last()).contains(r) {
                    assert(m.piece(xs.last()).contains(r));
                    match xs.last() {
                        language::Regex::Concat(cs) => {
                            let i = cs.lemma_contains_to_index(r);
                            assert forall|p: model::Primitive| regex_primitives(r).contains(p) implies allowed.contains(p) by {
                                lemma_regex_primitive_prefix(xs.last(), cs.len(), p);
                                assert(regex_primitives(cs[i]).contains(p));
                                assert(exists|j: int| 0 <= j < cs.len() && regex_primitives(regex_kids(xs.last())[j]).contains(p));
                                assert(regex_primitives(xs.last()).contains(p));
                            }
                        },
                        _ => {},
                    }
                }
            }
        }
    }

    pub proof fn lemma_cat_vocab(xs: Seq<language::Regex<model::Test>>, allowed: Set<model::Primitive>)
        requires forall|i: int| 0 <= i < xs.len() ==> regex_primitives(xs[i]).subset_of(allowed),
        ensures regex_primitives(crate::verify::finite_impl::r_cat(xs)).subset_of(allowed),
    {
        let m = crate::verify::finite_impl::pre();
        let f = m.flat(xs);
        lemma_flat_vocab(xs, allowed);
        if !m.has_empty(xs) && f.len() > 1 {
            let out = language::Regex::Concat(f);
            assert forall|p: model::Primitive| regex_primitives(out).contains(p) implies allowed.contains(p) by {
                lemma_regex_primitive_prefix(out, f.len(), p);
                let i = choose|i: int| 0 <= i < f.len() && regex_primitives(f[i]).contains(p);
                assert(f.contains(f[i]));
            }
        }
        if !m.has_empty(xs) && f.len() == 1 { assert(f.contains(f[0])); }
    }

    pub proof fn lemma_regex_child_vocab(r: language::Regex<model::Test>, i: int)
        requires r is Union || r is Intersect || r is Concat, 0 <= i < regex_kids(r).len(),
        ensures regex_primitives(regex_kids(r)[i]).subset_of(regex_primitives(r)),
    {
        assert forall|p: model::Primitive| regex_primitives(regex_kids(r)[i]).contains(p) implies regex_primitives(r).contains(p) by {
            lemma_regex_primitive_prefix(r, regex_kids(r).len(), p);
            assert(exists|j: int| 0 <= j < regex_kids(r).len() && regex_primitives(regex_kids(r)[j]).contains(p));
        }
    }

    pub proof fn lemma_model_constant_vocab(r: language::Regex<model::Test>)
        requires crate::verify::finite_impl::m_impl().is_const(r),
        ensures regex_primitives(r) == Set::empty(),
    {
        crate::verify::finite_impl::lemma_models_agree();
        match r { language::Regex::Empty | language::Regex::Epsilon | language::Regex::All => {}, _ => {} }
    }

    pub proof fn lemma_model_literal_vocab(r: language::Regex<model::Test>, out: language::Regex<model::Test>)
        requires crate::verify::finite_impl::regex_nf(r), (crate::verify::finite_impl::m_impl().lit)(r, out),
        ensures regex_primitives(out).subset_of(regex_primitives(r)),
        decreases crate::verify::finite_impl::r_size(r), 0nat,
    {
        let m = crate::verify::finite_impl::m_impl();
        let allowed = regex_primitives(r);
        crate::verify::finite_impl::theorem_impl_contract();
        crate::verify::finite_impl::lemma_models_agree();
        if !m.base_kind(r) {
            match r {
                language::Regex::Union(cs) | language::Regex::Intersect(cs) => {
                    lemma_sops_vocab(r is Intersect, r, allowed);
                    assert forall|w: language::Regex<model::Test>| m.ops_lit(r, w) implies regex_primitives(w).subset_of(allowed) by {
                        let o = choose|o: language::Regex<model::Test>| (m.ops)(r).contains(o) && #[trigger] (m.lit)(o, w);
                        cs.to_set_ensures();
                        assert(cs.contains(o));
                        let i = cs.lemma_contains_to_index(o);
                        lemma_regex_child_vocab(r, i);
                        assert(m.st(o));
                        assert((m.size)(o) < (m.size)(r));
                        lemma_model_literal_vocab(o, w);
                        assert(m.sops(r is Intersect, r).contains(o));
                    }
                    lemma_built_vocab(r is Intersect, |w: language::Regex<model::Test>| m.ops_lit(r, w), out, allowed);
                },
                language::Regex::Not(b) => {
                    assert forall|w: language::Regex<model::Test>| m.not_lit(r, w) implies regex_primitives(w).subset_of(allowed) by {
                        let v = choose|v: language::Regex<model::Test>| #[trigger] (m.lit)(*b, v) && w == (m.nnot)(v);
                        lemma_model_literal_vocab(*b, v);
                        lemma_not_vocab(v);
                    }
                    lemma_built_vocab(true, |w: language::Regex<model::Test>| m.not_lit(r, w), out, allowed);
                },
                language::Regex::Star(b) => {
                    assert forall|w: language::Regex<model::Test>| m.star_lit(r, w) implies regex_primitives(w).subset_of(allowed) by {
                        let v = choose|v: language::Regex<model::Test>| #[trigger] (m.prod)(*b, v) && w == m.cat2(v, r);
                        lemma_model_product_vocab(*b, v);
                        lemma_cat_vocab(seq![v, r], allowed);
                    }
                    lemma_built_vocab(false, |w: language::Regex<model::Test>| m.star_lit(r, w), out, allowed);
                },
                language::Regex::Concat(cs) => {
                    assert forall|i: int| 0 <= i < cs.len() implies regex_primitives(cs[i]).subset_of(allowed) by {
                        lemma_regex_child_vocab(r, i);
                    }
                    assert forall|w: language::Regex<model::Test>| m.list_lit(r, w) implies regex_primitives(w).subset_of(allowed) by {
                        if exists|i: int, v: language::Regex<model::Test>| 0 <= i < cs.len() - 1 && #[trigger] (m.prod)(cs[i], v)
                            && w == (m.ncat)(seq![v] + cs.skip(i + 1)) {
                            let (i, v) = choose|i: int, v: language::Regex<model::Test>| 0 <= i < cs.len() - 1
                                && #[trigger] (m.prod)(cs[i], v) && w == (m.ncat)(seq![v] + cs.skip(i + 1));
                            lemma_model_product_vocab(cs[i], v);
                            let inputs = seq![v] + cs.skip(i + 1);
                            assert forall|j: int| 0 <= j < inputs.len() implies regex_primitives(inputs[j]).subset_of(allowed) by {
                                if j == 0 { assert(inputs[j] == v); }
                                else { assert(inputs[j] == cs[i + j]); }
                            }
                            lemma_cat_vocab(inputs, allowed);
                        } else {
                            assert((m.lit)(cs.last(), w));
                            lemma_model_literal_vocab(cs.last(), w);
                            assert(regex_primitives(cs.last()).subset_of(allowed));
                        }
                    }
                    lemma_built_vocab(false, |w: language::Regex<model::Test>| m.list_lit(r, w), out, allowed);
                },
                _ => {},
            }
        } else { lemma_model_constant_vocab(out); }
    }

    pub proof fn lemma_model_product_vocab(r: language::Regex<model::Test>, out: language::Regex<model::Test>)
        requires crate::verify::finite_impl::regex_nf(r), (crate::verify::finite_impl::m_impl().prod)(r, out),
        ensures regex_primitives(out).subset_of(regex_primitives(r)),
        decreases crate::verify::finite_impl::r_size(r), 1nat,
    {
        let m = crate::verify::finite_impl::m_impl();
        let allowed = regex_primitives(r);
        crate::verify::finite_impl::theorem_impl_contract();
        crate::verify::finite_impl::lemma_models_agree();
        if !m.base_kind(r) {
            match r {
                language::Regex::Union(cs) => {
                    if exists|o: language::Regex<model::Test>| (m.ops)(r).contains(o) && #[trigger] (m.prod)(o, out) {
                        let o = choose|o: language::Regex<model::Test>| (m.ops)(r).contains(o) && #[trigger] (m.prod)(o, out);
                        cs.to_set_ensures();
                        assert(cs.contains(o));
                        let i = cs.lemma_contains_to_index(o);
                        lemma_regex_child_vocab(r, i);
                        lemma_model_product_vocab(o, out);
                        lemma_sops_vocab(false, r, allowed);
                    } else { lemma_model_literal_vocab(r, out); }
                },
                language::Regex::Intersect(_) | language::Regex::Not(_) => {
                    assert forall|w: language::Regex<model::Test>| (m.lit)(r, w) implies regex_primitives(w).subset_of(allowed) by {
                        lemma_model_literal_vocab(r, w);
                    }
                    lemma_built_vocab(true, |w: language::Regex<model::Test>| (m.lit)(r, w), out, allowed);
                },
                language::Regex::Star(_) => { lemma_model_literal_vocab(r, out); },
                language::Regex::Concat(cs) => {
                    if (m.lit)(r, out) { lemma_model_literal_vocab(r, out); }
                    else {
                        lemma_model_product_vocab(cs.last(), out);
                        lemma_regex_child_vocab(r, cs.len() as int - 1);
                    }
                },
                _ => {},
            }
        } else { lemma_model_constant_vocab(out); }
    }

    pub proof fn lemma_model_successor_vocab(r: language::Regex<model::Test>, out: language::Regex<model::Test>)
        requires crate::verify::finite_impl::regex_nf(r), (crate::verify::finite_impl::m_impl().succ)(r, out),
        ensures regex_primitives(out).subset_of(regex_primitives(r)),
    {
        let m = crate::verify::finite_impl::m_impl();
        let allowed = regex_primitives(r);
        crate::verify::finite_impl::theorem_impl_contract();
        crate::verify::finite_impl::lemma_models_agree();
        if !m.base_kind(r) {
            assert forall|w: language::Regex<model::Test>| (m.prod)(r, w) implies regex_primitives(w).subset_of(allowed) by {
                lemma_model_product_vocab(r, w);
            }
            lemma_built_vocab(false, |w: language::Regex<model::Test>| (m.prod)(r, w), out, allowed);
        } else { lemma_model_constant_vocab(out); }
    }

    /// Stack availability is independent of whether a truth word has a realizing event.
    pub open spec fn test_stack_result(g: model::Graph, tasks: Seq<(TestId, bool)>, depth: nat) -> Option<nat>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(depth) } else {
            let task = tasks.last();
            let needed = if task.1 { test_children(g, task.0).len() } else { 0 };
            if depth < needed { None }
            else { test_stack_result(g, tasks.drop_last(), (depth - needed + 1) as nat) }
        }
    }

    pub proof fn test_stack_task(g: model::Graph, pending: Seq<(TestId, bool)>, task: (TestId, bool), depth: nat)
        ensures test_stack_result(g, pending.push(task), depth) == {
            let needed = if task.1 { test_children(g, task.0).len() } else { 0 };
            if depth < needed { None } else { test_stack_result(g, pending, (depth - needed + 1) as nat) }
        },
    {
        assert(pending.push(task).drop_last() =~= pending);
    }

    pub open spec fn interp_stack_needed(g: model::Graph, task: (TransitionId, bool)) -> nat {
        if !task.1 { 0 } else {
            match g.transitions[task.0@ as int] {
                model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => cs.len(),
                model::TransitionNode::Not(_) | model::TransitionNode::Append(_, _) => 1,
                _ => 0,
            }
        }
    }

    pub open spec fn interp_stack_result(g: model::Graph, tasks: Seq<(TransitionId, bool)>, depth: nat) -> Option<nat>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(depth) } else {
            let needed = interp_stack_needed(g, tasks.last());
            if depth < needed { None }
            else { interp_stack_result(g, tasks.drop_last(), (depth - needed + 1) as nat) }
        }
    }

    pub proof fn interp_stack_task(g: model::Graph, pending: Seq<(TransitionId, bool)>, task: (TransitionId, bool), depth: nat)
        ensures interp_stack_result(g, pending.push(task), depth) == {
            let needed = interp_stack_needed(g, task);
            if depth < needed { None } else { interp_stack_result(g, pending, (depth - needed + 1) as nat) }
        },
    {
        assert(pending.push(task).drop_last() =~= pending);
    }

    pub proof fn test_stack_children(g: model::Graph, id: TestId, remaining: nat, pending: Seq<(TestId, bool)>, depth: nat)
        requires remaining <= test_children(g, id).len(),
        ensures test_stack_result(g, pending + child_test_tasks(g, id, remaining), depth)
            == test_stack_result(g, pending, (depth + test_children(g, id).len() - remaining) as nat),
        decreases test_children(g, id).len() - remaining,
    {
        let children = child_test_tasks(g, id, remaining);
        if remaining < test_children(g, id).len() {
            assert(children.drop_last() =~= child_test_tasks(g, id, remaining + 1));
            assert(!children.last().1);
            assert((pending + children).drop_last() =~= pending + children.drop_last());
            test_stack_children(g, id, remaining + 1, pending, depth + 1);
        } else { assert(children =~= Seq::empty()); }
    }

    pub proof fn interp_stack_children(g: model::Graph, id: TransitionId, remaining: nat, pending: Seq<(TransitionId, bool)>, depth: nat)
        requires remaining <= transition_children(g, id).len(),
        ensures interp_stack_result(g, pending + child_interp_tasks(g, id, remaining), depth)
            == interp_stack_result(g, pending, (depth + transition_children(g, id).len() - remaining) as nat),
        decreases transition_children(g, id).len() - remaining,
    {
        let children = child_interp_tasks(g, id, remaining);
        if remaining < transition_children(g, id).len() {
            assert(children.drop_last() =~= child_interp_tasks(g, id, remaining + 1));
            assert(!children.last().1);
            assert((pending + children).drop_last() =~= pending + children.drop_last());
            interp_stack_children(g, id, remaining + 1, pending, depth + 1);
        } else { assert(children =~= Seq::empty()); }
    }

    pub proof fn interp_stack_stable(before: model::Graph, after: model::Graph, tasks: Seq<(TransitionId, bool)>, depth: nat)
        requires model::graph_extends(before, after), interp_tasks_wf(before, tasks),
        ensures interp_stack_result(before, tasks, depth) == interp_stack_result(after, tasks, depth),
            tasks.len() > 0 ==> interp_stack_needed(before, tasks.last()) == interp_stack_needed(after, tasks.last()),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            let needed = interp_stack_needed(before, tasks.last());
            assert(before.transitions[tasks.last().0@ as int] == after.transitions[tasks.last().0@ as int]);
            if needed <= depth { interp_stack_stable(before, after, tasks.drop_last(), (depth - needed + 1) as nat); }
        }
    }

    pub open spec fn test_atoms_covered(g: model::Graph, root: nat, atoms: Seq<TestId>) -> bool {
        forall|p: model::Primitive| reach::test_reaches_primitive(g, root, p) ==> reach::has_positive(g, atoms, p)
    }

    pub open spec fn test_tasks_covered(g: model::Graph, tasks: Seq<(TestId, bool)>, atoms: Seq<TestId>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> test_atoms_covered(g, tasks[i].0@, atoms)
    }

    pub open spec fn interp_tasks_covered(g: model::Graph, tasks: Seq<(TransitionId, bool)>, atoms: Seq<TestId>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> reach::atoms_wf(g, tasks[i].0@, atoms)
    }

    pub proof fn test_coverage_children(g: model::Graph, root: TestId, atoms: Seq<TestId>)
        requires model::graph_wf(g), root@ < g.tests.len(), test_atoms_covered(g, root@, atoms),
        ensures forall|i: int| 0 <= i < test_children(g, root).len()
            ==> test_atoms_covered(g, test_children(g, root)[i], atoms),
    {
        model::lemma_graph_test_wf(g, root@);
        assert forall|i: int| 0 <= i < test_children(g, root).len()
            implies test_atoms_covered(g, test_children(g, root)[i], atoms) by {
            assert forall|p: model::Primitive| reach::test_reaches_primitive(g, test_children(g, root)[i], p)
                implies reach::has_positive(g, atoms, p) by {
                assert(reach::test_edges(g, root@)[i] == test_children(g, root)[i]);
                assert(reach::test_reaches_primitive(g, root@, p));
            }
        }
    }

    pub proof fn transition_coverage_children(g: model::Graph, root: TransitionId, atoms: Seq<TestId>)
        requires model::graph_wf(g), root@ < g.transitions.len(), reach::atoms_wf(g, root@, atoms),
        ensures (forall|i: int| 0 <= i < reach::transition_edges(g, root@).len()
                ==> reach::atoms_wf(g, reach::transition_edges(g, root@)[i], atoms)),
            forall|i: int| 0 <= i < reach::transition_tests(g, root@).len()
                ==> test_atoms_covered(g, reach::transition_tests(g, root@)[i], atoms),
    {
        model::lemma_graph_transition_wf(g, root@);
        assert forall|i: int| 0 <= i < reach::transition_edges(g, root@).len()
            implies reach::atoms_wf(g, reach::transition_edges(g, root@)[i], atoms) by {
            assert forall|p: model::Primitive| reach::transition_reaches_primitive(g, reach::transition_edges(g, root@)[i], p)
                implies reach::has_positive(g, atoms, p) by {
                assert(reach::transition_reaches_primitive(g, root@, p));
            }
        }
        assert forall|i: int| 0 <= i < reach::transition_tests(g, root@).len()
            implies test_atoms_covered(g, reach::transition_tests(g, root@)[i], atoms) by {
            assert forall|p: model::Primitive| reach::test_reaches_primitive(g, reach::transition_tests(g, root@)[i], p)
                implies reach::has_positive(g, atoms, p) by {
                assert(reach::transition_reaches_primitive(g, root@, p));
            }
        }
    }

    pub proof fn interp_coverage_stable(before: model::Graph, after: model::Graph, tasks: Seq<(TransitionId, bool)>, atoms: Seq<TestId>)
        requires model::graph_wf(before), model::graph_extends(before, after), interp_tasks_wf(before, tasks),
            interp_tasks_covered(before, tasks, atoms),
        ensures interp_tasks_covered(after, tasks, atoms),
    {
        assert forall|i: int| 0 <= i < tasks.len() implies reach::atoms_wf(after, tasks[i].0@, atoms) by {
            reach::lemma_atoms_wf_extends(before, after, tasks[i].0@, atoms);
        }
    }

    pub proof fn interp_coverage_push(g: model::Graph, tasks: Seq<(TransitionId, bool)>, task: (TransitionId, bool), atoms: Seq<TestId>)
        requires interp_tasks_covered(g, tasks, atoms), reach::atoms_wf(g, task.0@, atoms),
        ensures interp_tasks_covered(g, tasks.push(task), atoms),
    {
        assert forall|i: int| 0 <= i < tasks.push(task).len() implies reach::atoms_wf(g, tasks.push(task)[i].0@, atoms) by {
            if i < tasks.len() { assert(tasks.push(task)[i] == tasks[i]); }
            else { assert(tasks.push(task)[i] == task); }
        }
    }

    pub proof fn interp_coverage_pop(g: model::Graph, tasks: Seq<(TransitionId, bool)>, task: (TransitionId, bool), atoms: Seq<TestId>)
        requires interp_tasks_covered(g, tasks.push(task), atoms),
        ensures interp_tasks_covered(g, tasks, atoms), reach::atoms_wf(g, task.0@, atoms),
    {
        assert(tasks.push(task)[tasks.len() as int] == task);
        assert forall|i: int| 0 <= i < tasks.len() implies reach::atoms_wf(g, tasks[i].0@, atoms) by {
            assert(tasks.push(task)[i] == tasks[i]);
        }
    }

    pub proof fn assignment_index_bound(count: nat, words: Seq<u64>, index: usize)
        requires assignment_valid(count, words), index < count,
        ensures index / 64 < words.len(),
    {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(index as int, 64);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((count + 63) as int, 64);
        assert(index / 64 * 64 <= index);
        assert((count + 63) / 64 * 64 > count - 1);
    }
            pub open spec fn truth_word_bit(words: Seq<u64>, index: nat) -> bool {
                index / 64 < words.len()
                    && ((words[(index / 64) as int] >> ((index % 64) as u32)) & 1u64) != 0
            }

            pub open spec fn truth_words_realize(
                g: model::Graph, atoms: Seq<TestId>, words: Seq<u64>, theta: Subst, event: EventView,
            ) -> bool {
                forall|i: int| 0 <= i < atoms.len() ==> #[trigger] truth_word_bit(words, i as nat)
                    == model::test_holds(theta, model::lift_test(g, atoms[i]@), event)
            }

            pub proof fn truth_words_realize_extends(
                before: model::Graph, after: model::Graph, atoms: Seq<TestId>, words: Seq<u64>,
            )
                requires model::graph_extends(before, after), model::atom_ids_wf(before, atoms),
                ensures model::atom_ids_wf(after, atoms),
                    forall|theta: Subst, event: EventView|
                        truth_words_realize(before, atoms, words, theta, event)
                            == truth_words_realize(after, atoms, words, theta, event),
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
        ensures forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            ==> norm::transition_lang(g, theta, out, event, word) == !norm::transition_lang(g, theta, root, event, word),
    {
        let task = norm::ActionShape::Not(root@);
        let expected = norm::transition_initial_value(g, task).unwrap();
        norm::transition_lemma_result_refines(g, task, out);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            implies norm::transition_lang(g, theta, out, event, word) == !norm::transition_lang(g, theta, root, event, word) by {
            let ctx = norm::TransitionContext { bindings: theta };
            norm::transition_lemma_context_sem(ctx);
            language::lemma_interp_not(model::gsem(theta), event, model::lift_transition(g, root@));
            assert((expected.guard)(ctx, event));
            assert(norm::guarded_language(norm::transition_context_sem(), ctx, event, expected, word)
                == norm::guarded_language(norm::transition_context_sem(), ctx, event, norm::transition_known(g, out), word));
            norm::transition_lemma_known_language(g, out, ctx, event, word);
        }
    }

    pub proof fn symbolic_intersect_result(g: model::Graph, ids: Seq<TransitionId>, out: TransitionId)
        requires norm::transition_result(g, norm::ActionShape::Fold(model::transition_ids(ids), 0), out),
        ensures forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            ==> norm::transition_lang(g, theta, out, event, word) == norm::transition_combo(g, theta, ids, event, word, true),
    {
        let task = norm::ActionShape::Fold(model::transition_ids(ids), 0);
        let expected = norm::transition_initial_value(g, task).unwrap();
        let terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
        norm::transition_lemma_result_refines(g, task, out);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            implies norm::transition_lang(g, theta, out, event, word) == norm::transition_combo(g, theta, ids, event, word, true) by {
            let ctx = norm::TransitionContext { bindings: theta };
            norm::transition_lemma_context_sem(ctx);
            language::lemma_interp_intersect(model::gsem(theta), event, terms, word);
            assert forall|i: int| 0 <= i < ids.len() implies language::numeric_lang(model::gsem(theta),
                language::interp_transition(model::gsem(theta), event, terms[i]), word)
                    == norm::transition_lang(g, theta, ids[i], event, word) by {
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
        && forall|theta: Subst, event: EventView, word: Seq<EventView>|
            language::event_wf(theta, theta.len()) ==> norm::transition_lang(g, theta, out, event, word)
                == model::regex_lang(g, theta, root, seq![event] + word)
    }

    /// The runtime derivative agrees, modulo language, with the independent δ.
    pub proof fn lemma_derivative_correct_is_symbolic_derivative(g: model::Graph, root: nat, out: TransitionId, theta: Subst, event: EventView, word: Seq<EventView>)
        requires derivative_correct(g, root, out), language::event_wf(theta, theta.len()),
        ensures norm::transition_lang(g, theta, out, event, word)
            == language::numeric_lang(model::gsem(theta), language::interp_transition(model::gsem(theta), event, algebra::symbolic_derivative(model::lift_regex(g, root))), word),
    {
        algebra::lemma_symbolic_derivative_correct(model::gsem(theta), event, model::lift_regex(g, root), word);
    }

    pub proof fn lemma_regex_graph_child_vocab(g: model::Graph, root: nat, child: nat)
        requires model::graph_wf(g), root < g.regexes.len(),
            match g.regexes[root as int].kind {
                model::RegexKindNode::Star(c) | model::RegexKindNode::Not(c) => child == c,
                model::RegexKindNode::Union(cs) | model::RegexKindNode::Intersect(cs) | model::RegexKindNode::Concat(cs) => cs.contains(child),
                _ => false,
            },
        ensures child < g.regexes.len(), regex_primitives(model::lift_regex(g, child)).subset_of(regex_primitives(model::lift_regex(g, root))),
    {
        model::lemma_graph_regex_wf(g, root);
        norm::regex_unfold(g, root);
        match g.regexes[root as int].kind {
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Intersect(cs) | model::RegexKindNode::Concat(cs) => {
                let i = cs.lemma_contains_to_index(child);
                lemma_regex_child_vocab(model::lift_regex(g, root), i);
            },
            _ => {},
        }
    }

    pub open spec fn derivative_results_vocab(g: model::Graph, root: nat, results: Seq<TransitionId>) -> bool {
        forall|i: int| 0 <= i < results.len() ==> derivative_vocab(g, root, results[i]@)
    }

    pub proof fn lemma_derivative_results_vocab_stable(a: model::Graph, b: model::Graph, root: nat, results: Seq<TransitionId>)
        requires model::graph_wf(a), model::graph_extends(a, b), root < a.regexes.len(),
            norm::transition_ids_valid(a, results), derivative_results_vocab(a, root, results),
        ensures derivative_results_vocab(b, root, results),
    {
        assert forall|i: int| 0 <= i < results.len() implies derivative_vocab(b, root, results[i]@) by {
            lemma_derivative_vocab_stable(a, b, root, results[i]@);
        }
    }

    /// Every cached derivative is correct and has the class bound of its state
    /// (`verify::finite_deriv::dbound`).
    pub open spec fn derivative_cache_wf(g: model::Graph, cache: Seq<Option<TransitionId>>) -> bool {
        forall|i: int| 0 <= i < cache.len() ==> match #[trigger] cache[i] {
            Some(out) => derivative_correct(g, i as nat, out) && fder::dbound(g, i as nat, out@)
                && derivative_vocab(g, i as nat, out@), None => true,
        }
    }

    pub proof fn derivative_cached_bound(g: model::Graph, cache: Seq<Option<TransitionId>>, id: RegexId, out: TransitionId)
        requires derivative_cache_wf(g, cache), id@ < cache.len(), cache[id@ as int] == Some(out),
        ensures out@ < g.transitions.len(), derivative_vocab(g, id@, out@),
    {}

    pub proof fn derivative_cache_prefix_facts(before: Seq<Option<TransitionId>>, after: Seq<Option<TransitionId>>)
        requires before.len() <= after.len(), before == after || before == after.subrange(0, before.len() as int),
        ensures before.is_prefix_of(after),
            forall|i: int| 0 <= i < before.len() ==> after[i] == before[i],
    {}

    pub proof fn derivative_test_correct(g: model::Graph, root: RegexId, test: TestId, cache: Seq<Option<TransitionId>>, out: TransitionId,
        then_id: TransitionId, else_id: TransitionId)
        requires model::graph_wf(g), root@ < g.regexes.len(), derivative_cache_wf(g, cache), out@ < g.transitions.len(),
            g.regexes[root@ as int].kind == model::RegexKindNode::Test(test@),
            then_id@ == g.constants.transition_epsilon, else_id@ == g.constants.transition_empty,
            forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                ==> norm::transition_lang(g, theta, out, event, word) == norm::transition_if_combo(g, theta, test,
                    then_id, else_id, event, word),
        ensures derivative_correct(g, root@, out),
    {
        derivative_constants(g);
        assert(derivative_native_result(g, root, cache, out));
        derivative_native_correct(g, root, cache, out);
    }

    pub proof fn derivative_graph_frame(before: model::Graph, after: model::Graph, root: RegexId)
        requires model::graph_extends(before, after), root@ < before.regexes.len(),
        ensures root@ < after.regexes.len(), after.regexes[root@ as int] == before.regexes[root@ as int],
            after.constants == before.constants,
    {}

    pub proof fn derivative_correct_bounds(g: model::Graph, root: nat, out: TransitionId)
        requires derivative_correct(g, root, out),
        ensures root < g.regexes.len(), out@ < g.transitions.len(),
    {}

    pub open spec fn derivative_tasks_wf(g: model::Graph, tasks: Seq<(RegexId, bool)>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].0@ < g.regexes.len()
    }

    pub open spec fn derivative_tasks_bounded(tasks: Seq<(RegexId, bool)>, bound: nat) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> tasks[i].0@ <= bound
    }

    pub open spec fn cache_complete(cache: Seq<Option<TransitionId>>, id: nat) -> bool {
        id < cache.len() && cache[id as int] is Some
    }

    pub open spec fn cache_completions_preserved(before: Seq<Option<TransitionId>>, after: Seq<Option<TransitionId>>) -> bool {
        forall|id: nat| cache_complete(before, id) ==> cache_complete(after, id)
    }

    pub open spec fn tasks_contain(tasks: Seq<(RegexId, bool)>, id: nat) -> bool {
        exists|i: int| 0 <= i < tasks.len() && tasks[i].0@ == id
    }

    pub open spec fn derivative_dependency(g: model::Graph, root: RegexId, child: nat) -> bool {
        match g.regexes[root@ as int].kind {
            model::RegexKindNode::Star(id) | model::RegexKindNode::Not(id) => child == id,
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Intersect(cs) => cs.contains(child),
            model::RegexKindNode::Concat(cs) => exists|i: int| 0 <= i < cs.len() && cs[i] == child
                && derivative_prefix(g, root, i as nat),
            _ => false,
        }
    }

    pub open spec fn derivative_dependencies_complete(g: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>) -> bool {
        forall|child: nat| derivative_dependency(g, root, child) ==> cache_complete(cache, child)
    }

    pub proof fn derivative_cache_extend_dependencies(g: model::Graph, root: RegexId,
        before: Seq<Option<TransitionId>>, after: Seq<Option<TransitionId>>)
        requires before.is_prefix_of(after), derivative_dependencies_complete(g, root, before),
        ensures derivative_dependencies_complete(g, root, after),
    {
        after.lemma_prefix_index_eq(before);
        assert forall|child: nat| derivative_dependency(g, root, child) implies cache_complete(after, child) by {
            assert(cache_complete(before, child));
            assert(after[child as int] == before[child as int]);
        }
    }

    pub proof fn derivative_unary_complete(g: model::Graph, root: RegexId, inner: RegexId, cache: Seq<Option<TransitionId>>)
        requires derivative_dependencies_complete(g, root, cache),
            g.regexes[root@ as int].kind == model::RegexKindNode::Star(inner@)
                || g.regexes[root@ as int].kind == model::RegexKindNode::Not(inner@),
        ensures cache_complete(cache, inner@),
    {
        assert(derivative_dependency(g, root, inner@));
    }

    pub proof fn derivative_unary_scheduled(g: model::Graph, root: RegexId, pending: Seq<(RegexId, bool)>, inner: RegexId)
        requires g.regexes[root@ as int].kind == model::RegexKindNode::Star(inner@)
            || g.regexes[root@ as int].kind == model::RegexKindNode::Not(inner@),
        ensures derivative_scheduled(g, root, pending, pending.push((root, true)).push((inner, false))),
    {
        let tasks = pending.push((root, true)).push((inner, false));
        assert(pending =~= tasks.subrange(0, pending.len() as int));
        assert forall|child: nat| derivative_dependency(g, root, child)
            implies exists|j: int| pending.len() < j < tasks.len() && tasks[j].0@ == child by {
            assert(child == inner@);
            assert(tasks[pending.len() as int + 1].0@ == child);
        }
    }

    pub proof fn derivative_scheduled_facts(g: model::Graph, root: RegexId, pending: Seq<(RegexId, bool)>, tasks: Seq<(RegexId, bool)>)
        requires derivative_scheduled(g, root, pending, tasks),
        ensures pending.is_prefix_of(tasks), tasks_contain(tasks, root@),
    {
        assert(tasks[pending.len() as int] == (root, true));
    }

    /// A finishing task may rely only on a completed cache entry or work above it.
    pub open spec fn derivative_tasks_ready(g: model::Graph, tasks: Seq<(RegexId, bool)>, cache: Seq<Option<TransitionId>>) -> bool {
        forall|i: int, child: nat| 0 <= i < tasks.len() && tasks[i].1
            && derivative_dependency(g, tasks[i].0, child) ==> cache_complete(cache, child)
                || exists|j: int| i < j < tasks.len() && tasks[j].0@ == child
    }

    pub open spec fn derivative_scheduled(g: model::Graph, root: RegexId,
        pending: Seq<(RegexId, bool)>, tasks: Seq<(RegexId, bool)>) -> bool {
        pending.is_prefix_of(tasks) && pending.len() < tasks.len() && tasks[pending.len() as int] == (root, true)
            && (forall|i: int| pending.len() < i < tasks.len() ==> !tasks[i].1)
            && forall|child: nat| derivative_dependency(g, root, child)
                ==> exists|j: int| pending.len() < j < tasks.len() && tasks[j].0@ == child
    }

    pub proof fn derivative_ready_top(g: model::Graph, tasks: Seq<(RegexId, bool)>, cache: Seq<Option<TransitionId>>)
        requires tasks.len() > 0, derivative_tasks_ready(g, tasks, cache),
        ensures tasks.last().1 ==> derivative_dependencies_complete(g, tasks.last().0, cache),
    {
        assert forall|child: nat| tasks.last().1 && derivative_dependency(g, tasks.last().0, child)
            implies cache_complete(cache, child) by {
            assert(tasks[tasks.len() - 1] == tasks.last());
        }
    }

    pub proof fn derivative_ready_after_step(before: model::Graph, after: model::Graph, root: RegexId, finish: bool,
        pending: Seq<(RegexId, bool)>, tasks: Seq<(RegexId, bool)>, cache0: Seq<Option<TransitionId>>, cache1: Seq<Option<TransitionId>>)
        requires model::graph_wf(before), model::graph_extends(before, after), root@ < before.regexes.len(),
            derivative_tasks_wf(before, pending), derivative_tasks_ready(before, pending.push((root, finish)), cache0),
            cache_completions_preserved(cache0, cache1),
            tasks == pending && cache_complete(cache1, root@) || derivative_scheduled(before, root, pending, tasks),
        ensures derivative_tasks_ready(after, tasks, cache1),
    {
        let queued = pending.push((root, finish));
        after.regexes.lemma_prefix_index_eq(before.regexes);
        if tasks != pending { tasks.lemma_prefix_index_eq(pending); }
        assert forall|i: int, child: nat| 0 <= i < tasks.len() && tasks[i].1
            && derivative_dependency(after, tasks[i].0, child) implies cache_complete(cache1, child)
                || exists|j: int| i < j < tasks.len() && tasks[j].0@ == child by {
            if i < pending.len() {
                assert(tasks[i] == pending[i]);
                assert(queued[i] == pending[i]);
                assert(queued[i].1);
                derivative_factor_stable(before, after, pending[i].0);
                assert(before.regexes[pending[i].0@ as int] == after.regexes[pending[i].0@ as int]);
                assert(derivative_dependency(before, queued[i].0, child));
                if cache_complete(cache0, child) {
                    assert(cache_complete(cache1, child));
                } else {
                    assert(exists|j: int| i < j < queued.len() && queued[j].0@ == child);
                    let j = choose|j: int| i < j < queued.len() && queued[j].0@ == child;
                    if j < pending.len() {
                        assert(queued[j] == pending[j]);
                        assert(tasks[j] == pending[j]);
                        assert(exists|k: int| i < k < tasks.len() && tasks[k].0@ == child);
                    } else {
                        assert(j == pending.len());
                        assert(child == root@);
                        if tasks == pending { assert(cache_complete(cache1, child)); }
                        else {
                            assert(tasks[pending.len() as int] == (root, true));
                            assert(exists|k: int| i < k < tasks.len() && tasks[k].0@ == child);
                        }
                    }
                }
            } else {
                assert(tasks != pending);
                assert(i == pending.len());
                assert(tasks[i] == (root, true));
                derivative_factor_stable(before, after, root);
                assert(before.regexes[root@ as int] == after.regexes[root@ as int]);
                assert(derivative_dependency(before, root, child));
                let j = choose|j: int| pending.len() < j < tasks.len() && tasks[j].0@ == child;
                assert(i < j);
            }
        }
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
        theta: Subst, event: EventView, word: Seq<EventView>,
    ) -> bool {
        let cs = derivative_children_ids(g, root);
        let sem = model::gsem(theta);
        if concat {
            language::numeric_lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, model::lift_regex(g, cs[index]))]
                + model::lift_regexes(g, cs.subrange(index + 1, cs.len() as int))), word)
        } else { model::regex_lang(g, theta, cs[index], seq![event] + word) }
    }

    pub open spec fn derivative_factor_combo(
        g: model::Graph, root: RegexId, concat: bool, count: nat, intersect: bool,
        theta: Subst, event: EventView, word: Seq<EventView>,
    ) -> bool {
        if intersect {
            forall|i: int| 0 <= i < count && (!concat || derivative_prefix(g, root, i as nat))
                ==> derivative_factor_language(g, root, concat, i, theta, event, word)
        } else {
            exists|i: int| 0 <= i < count && (!concat || derivative_prefix(g, root, i as nat))
                && derivative_factor_language(g, root, concat, i, theta, event, word)
        }
    }

    pub open spec fn derivative_results(
        g: model::Graph, root: RegexId, concat: bool, count: nat, results: Seq<TransitionId>,
    ) -> bool {
        norm::transition_ids_valid(g, results)
        && forall|theta: Subst, event: EventView, word: Seq<EventView>, intersect: bool|
            language::event_wf(theta, theta.len()) ==> norm::transition_combo(g, theta, results, event, word, intersect)
                == derivative_factor_combo(g, root, concat, count, intersect, theta, event, word)
    }

    pub proof fn derivative_factor_stable(a: model::Graph, b: model::Graph, root: RegexId)
        requires model::graph_wf(a), model::graph_extends(a, b), root@ < a.regexes.len(),
        ensures derivative_children_ids(a, root) == derivative_children_ids(b, root),
            forall|n: nat| n <= derivative_children_ids(a, root).len() ==> derivative_prefix(a, root, n) == derivative_prefix(b, root, n),
            forall|concat: bool, i: int, theta: Subst, event: EventView, word: Seq<EventView>|
                0 <= i < derivative_children_ids(a, root).len()
                    ==> derivative_factor_language(a, root, concat, i, theta, event, word)
                        == derivative_factor_language(b, root, concat, i, theta, event, word),
    {
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
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
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
        hide(derivative_factor_language); hide(derivative_prefix);
        derivative_factor_stable(a, b, root);
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>, intersect: bool|
            language::event_wf(theta, theta.len()) implies norm::transition_combo(b, theta, results, event, word, intersect)
                == derivative_factor_combo(b, root, concat, count, intersect, theta, event, word) by {
            assert forall|i: int| 0 <= i < results.len() implies
                norm::transition_lang(a, theta, results[i], event, word)
                    == norm::transition_lang(b, theta, results[i], event, word) by {}
            assert(norm::transition_combo(a, theta, results, event, word, intersect)
                == norm::transition_combo(b, theta, results, event, word, intersect));
            assert(derivative_factor_combo(a, root, concat, count, intersect, theta, event, word)
                == derivative_factor_combo(b, root, concat, count, intersect, theta, event, word));
        }
    }

    pub proof fn derivative_correct_stable(a: model::Graph, b: model::Graph, root: nat, out: TransitionId)
        requires model::graph_wf(a), model::graph_extends(a, b), derivative_correct(a, root, out),
        ensures derivative_correct(b, root, out),
    {
        hide(language::numeric_lang); hide(language::interp_transition); hide(model::lift_regex); hide(model::lift_transition);
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_regex_stable(a, b, root);
        model::lemma_lift_transition_stable(a, b, out@);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            implies norm::transition_lang(b, theta, out, event, word)
                == model::regex_lang(b, theta, root, seq![event] + word) by {
            assert(norm::transition_lang(a, theta, out, event, word)
                == model::regex_lang(a, theta, root, seq![event] + word));
        }
    }

    #[verifier::spinoff_prover]
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
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
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
                Some(out) => derivative_correct(b, i as nat, out) && fder::dbound(b, i as nat, out@)
                    && derivative_vocab(b, i as nat, out@), None => true,
            } by {
                if let Some(out) = cache[i] {
                    derivative_correct_bounds(a, i as nat, out);
                    fder::lemma_dbound_stable(a, b, i as nat, out@);
                    lemma_derivative_vocab_stable(a, b, i as nat, out@);
                }
            }
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

    pub proof fn derivative_dependency_frame(g: model::Graph, root: RegexId)
        requires model::graph_wf(g), root@ < g.regexes.len(),
        ensures forall|next: model::Graph, cache: Seq<Option<TransitionId>>| model::graph_extends(g, next)
            ==> derivative_dependencies_complete(g, root, cache) == derivative_dependencies_complete(next, root, cache),
    {
        assert forall|next: model::Graph, cache: Seq<Option<TransitionId>>| model::graph_extends(g, next)
            implies derivative_dependencies_complete(g, root, cache) == derivative_dependencies_complete(next, root, cache) by {
            derivative_factor_stable(g, next, root);
            assert(g.regexes[root@ as int] == next.regexes[root@ as int]);
            assert forall|child: nat| derivative_dependency(g, root, child) == derivative_dependency(next, root, child) by {}
        }
    }

    pub proof fn derivative_results_push(
        g: model::Graph, root: RegexId, concat: bool, index: nat, prior: Seq<TransitionId>, out: TransitionId,
    )
        requires derivative_results(g, root, concat, index, prior), out@ < g.transitions.len(),
            !concat || derivative_prefix(g, root, index),
            forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                ==> norm::transition_lang(g, theta, out, event, word)
                    == derivative_factor_language(g, root, concat, index as int, theta, event, word),
        ensures derivative_results(g, root, concat, index + 1, prior.push(out)),
    {
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
        hide(norm::transition_lang); hide(derivative_factor_language);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>, intersect: bool|
            language::event_wf(theta, theta.len()) implies norm::transition_combo(g, theta, prior.push(out), event, word, intersect)
                == derivative_factor_combo(g, root, concat, index + 1, intersect, theta, event, word) by {
            if intersect {
                assert forall|i: int| 0 <= i < prior.push(out).len() implies
                    norm::transition_lang(g, theta, prior.push(out)[i], event, word)
                        == if i < prior.len() { norm::transition_lang(g, theta, prior[i], event, word) }
                            else { norm::transition_lang(g, theta, out, event, word) } by {}
                assert(prior.push(out)[prior.len() as int] == out);
                if norm::transition_combo(g, theta, prior.push(out), event, word, true) {
                    assert forall|i: int| 0 <= i < prior.len() implies
                        norm::transition_lang(g, theta, prior[i], event, word) by {
                        assert(prior.push(out)[i] == prior[i]);
                    }
                }
                if norm::transition_combo(g, theta, prior, event, word, true)
                    && norm::transition_lang(g, theta, out, event, word) {
                    assert forall|i: int| 0 <= i < prior.push(out).len() implies
                        norm::transition_lang(g, theta, prior.push(out)[i], event, word) by {
                        if i < prior.len() { assert(prior.push(out)[i] == prior[i]); } else { assert(prior.push(out)[i] == out); }
                    }
                }
                assert(norm::transition_combo(g, theta, prior.push(out), event, word, true)
                    == (norm::transition_combo(g, theta, prior, event, word, true)
                        && norm::transition_lang(g, theta, out, event, word)));
            } else {
                if norm::transition_combo(g, theta, prior.push(out), event, word, false) {
                    let i = choose|i: int| 0 <= i < prior.push(out).len()
                        && norm::transition_lang(g, theta, prior.push(out)[i], event, word);
                    if i < prior.len() { assert(norm::transition_combo(g, theta, prior, event, word, false)); }
                }
                if norm::transition_combo(g, theta, prior, event, word, false) {
                    let i = choose|i: int| 0 <= i < prior.len()
                        && norm::transition_lang(g, theta, prior[i], event, word);
                    assert(prior.push(out)[i] == prior[i]);
                }
                assert(prior.push(out)[prior.len() as int] == out);
                assert(norm::transition_combo(g, theta, prior.push(out), event, word, false)
                    == (norm::transition_combo(g, theta, prior, event, word, false)
                        || norm::transition_lang(g, theta, out, event, word)));
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
            forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                ==> norm::transition_lang(g, theta, out, event, word)
                    == norm::transition_append_combo(g, theta, d, suffix, event, word),
        ensures forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            ==> norm::transition_lang(g, theta, out, event, word)
                == derivative_factor_language(g, root, true, index, theta, event, word),
    {
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            implies norm::transition_lang(g, theta, out, event, word)
                == derivative_factor_language(g, root, true, index, theta, event, word) by {
            let sem = model::gsem(theta);
            let child = model::lift_regex(g, derivative_children_ids(g, root)[index]);
            let actual = language::interp_transition(sem, event, model::lift_transition(g, d@));
            let expected = language::derivative(sem, event, child);
            let tail = model::lift_regexes(g, model::regex_ids(suffix));
            language::lemma_concat_prepend(sem, actual, tail, word);
            language::lemma_concat_prepend(sem, expected, tail, word);
            assert forall|w: Seq<EventView>| language::numeric_lang(sem, actual, w) == language::numeric_lang(sem, expected, w) by {
                language::lemma_derivative_correct(sem, event, child, w);
                assert(norm::transition_lang(g, theta, d, event, w)
                    == model::regex_lang(g, theta, derivative_children_ids(g, root)[index], seq![event] + w));
            }
        }
    }

    pub open spec fn derivative_sum<L>(sem: spec_fn(L, EventView) -> bool, event: EventView, cs: Seq<language::Regex<L>>, word: Seq<EventView>) -> bool {
        exists|i: int| 0 <= i < cs.len()
            && (forall|j: int| 0 <= j < i ==> language::nullable(cs[j]))
            && language::numeric_lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, cs[i])]
                + cs.subrange(i + 1, cs.len() as int)), word)
    }

    pub proof fn derivative_concat_sum<L>(sem: spec_fn(L, EventView) -> bool, event: EventView, bound: language::Regex<L>, cs: Seq<language::Regex<L>>, word: Seq<EventView>)
        requires forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        ensures language::numeric_lang(sem, language::derivative_concat(sem, event, bound, cs), word) == derivative_sum(sem, event, cs, word),
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
                    && language::numeric_lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, cs[i])]
                        + cs.subrange(i + 1, cs.len() as int)), word);
                if i > 0 {
                    assert(rest[i - 1] == cs[i]);
                    assert(rest.subrange(i, rest.len() as int) =~= cs.subrange(i + 1, cs.len() as int));
                    assert forall|j: int| 0 <= j < i - 1 implies language::nullable(rest[j]) by { assert(rest[j] == cs[j + 1]); }
                    assert(derivative_sum(sem, event, rest, word));
                }
            }
            if language::numeric_lang(sem, head, word) { assert(derivative_sum(sem, event, cs, word)); }
            if language::nullable(cs[0]) && derivative_sum(sem, event, rest, word) {
                let i = choose|i: int| 0 <= i < rest.len()
                    && (forall|j: int| 0 <= j < i ==> language::nullable(rest[j]))
                    && language::numeric_lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, rest[i])]
                        + rest.subrange(i + 1, rest.len() as int)), word);
                assert(cs[i + 1] == rest[i]);
                assert(cs.subrange(i + 2, cs.len() as int) =~= rest.subrange(i + 1, rest.len() as int));
                assert forall|j: int| 0 <= j < i + 1 implies language::nullable(cs[j]) by { if j > 0 { assert(cs[j] == rest[j - 1]); } }
                assert(derivative_sum(sem, event, cs, word));
            }
        }
    }

    pub proof fn derivative_sum_correct<L>(sem: spec_fn(L, EventView) -> bool, event: EventView, root: language::Regex<L>, word: Seq<EventView>)
        requires root is Concat,
        ensures derivative_sum(sem, event, root->Concat_0, word) == language::numeric_lang(sem, root, seq![event] + word),
    {
        hide(language::numeric_lang);
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
            forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                ==> norm::transition_lang(g, theta, out, event, word)
                    == derivative_factor_combo(g, root, concat, derivative_children_ids(g, root).len(), intersect, theta, event, word),
        ensures derivative_correct(g, root@, out),
    {
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
        hide(model::lift_regex); hide(model::lift_transition);
        hide(language::nullable);
        norm::regex_unfold(g, root@);
        let cs = derivative_children_ids(g, root);
        let rs = model::lift_regexes(g, cs);
        assert(rs.len() == cs.len());
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
            implies norm::transition_lang(g, theta, out, event, word)
                == model::regex_lang(g, theta, root@, seq![event] + word) by {
            let sem = model::gsem(theta);
            assert(norm::transition_lang(g, theta, out, event, word)
                == derivative_factor_combo(g, root, concat, cs.len(), intersect, theta, event, word));
            assert forall|i: int| 0 <= i < cs.len() implies
                #[trigger] derivative_factor_language(g, root, false, i, theta, event, word)
                    == language::numeric_lang(sem, rs[i], seq![event] + word) by {
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
                    #[trigger] derivative_factor_language(g, root, true, i, theta, event, word)
                        == language::numeric_lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, rs[i])]
                            + rs.subrange(i + 1, rs.len() as int)), word) by {
                    assert(rs[i] == model::lift_regex(g, cs[i]));
                    assert(model::lift_regexes(g, cs.subrange(i + 1, cs.len() as int)) == rs.subrange(i + 1, rs.len() as int));
                }
                if derivative_factor_combo(g, root, concat, cs.len(), intersect, theta, event, word) {
                    let i = choose|i: int| 0 <= i < cs.len() && derivative_prefix(g, root, i as nat)
                        && derivative_factor_language(g, root, true, i, theta, event, word);
                    assert(0 <= i < rs.len());
                    assert(derivative_sum(sem, event, rs, word));
                }
                if derivative_sum(sem, event, rs, word) {
                    let i = choose|i: int| 0 <= i < rs.len()
                        && (forall|j: int| 0 <= j < i ==> language::nullable(rs[j]))
                        && language::numeric_lang(sem, language::Regex::Concat(seq![language::derivative(sem, event, rs[i])]
                            + rs.subrange(i + 1, rs.len() as int)), word);
                    assert(0 <= i < cs.len());
                    assert(derivative_prefix(g, root, i as nat));
                    assert(derivative_factor_language(g, root, true, i, theta, event, word));
                    assert(derivative_factor_combo(g, root, concat, cs.len(), intersect, theta, event, word));
                }
                assert(derivative_factor_combo(g, root, concat, cs.len(), intersect, theta, event, word)
                    == derivative_sum(sem, event, rs, word));
                assert(norm::transition_lang(g, theta, out, event, word)
                    == model::regex_lang(g, theta, root@, seq![event] + word));
            } else if intersect {
                language::lemma_lang_intersect(sem, rs, seq![event] + word);
                assert(model::lift_regex(g, root@) == language::Regex::Intersect(rs));
                assert(derivative_factor_combo(g, root, false, cs.len(), true, theta, event, word)
                    == (forall|i: int| 0 <= i < cs.len() ==> derivative_factor_language(g, root, false, i, theta, event, word)));
                if derivative_factor_combo(g, root, false, cs.len(), true, theta, event, word) {
                    assert forall|i: int| 0 <= i < rs.len() implies language::numeric_lang(sem, rs[i], seq![event] + word) by {
                        assert(derivative_factor_language(g, root, false, i, theta, event, word));
                    }
                }
                if forall|i: int| 0 <= i < rs.len() ==> language::numeric_lang(sem, rs[i], seq![event] + word) {
                    assert forall|i: int| 0 <= i < cs.len() implies derivative_factor_language(g, root, false, i, theta, event, word) by {
                        assert(language::numeric_lang(sem, rs[i], seq![event] + word));
                    }
                }
                assert(derivative_factor_combo(g, root, false, cs.len(), true, theta, event, word)
                    == (forall|i: int| 0 <= i < rs.len() ==> language::numeric_lang(sem, rs[i], seq![event] + word)));
                assert(norm::transition_lang(g, theta, out, event, word)
                    == model::regex_lang(g, theta, root@, seq![event] + word));
            } else {
                language::lemma_lang_union(sem, rs, seq![event] + word);
                assert(model::lift_regex(g, root@) == language::Regex::Union(rs));
                if derivative_factor_combo(g, root, false, cs.len(), false, theta, event, word) {
                    let i = choose|i: int| 0 <= i < cs.len() && derivative_factor_language(g, root, false, i, theta, event, word);
                    assert(language::numeric_lang(sem, rs[i], seq![event] + word));
                }
                if exists|i: int| 0 <= i < rs.len() && language::numeric_lang(sem, rs[i], seq![event] + word) {
                    let i = choose|i: int| 0 <= i < rs.len() && language::numeric_lang(sem, rs[i], seq![event] + word);
                    assert(derivative_factor_language(g, root, false, i, theta, event, word));
                    assert(derivative_factor_combo(g, root, false, cs.len(), false, theta, event, word));
                }
                assert(derivative_factor_combo(g, root, false, cs.len(), false, theta, event, word)
                    == (exists|i: int| 0 <= i < rs.len() && language::numeric_lang(sem, rs[i], seq![event] + word)));
                assert(norm::transition_lang(g, theta, out, event, word)
                    == model::regex_lang(g, theta, root@, seq![event] + word));
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
            model::RegexKindNode::Test(test) => forall|theta: Subst, event: EventView, word: Seq<EventView>|
                language::event_wf(theta, theta.len()) ==> norm::transition_lang(g, theta, out, event, word)
                    == if model::test_holds(theta, model::lift_test(g, test), event) { word.len() == 0 } else { false },
            model::RegexKindNode::Star(inner) => exists|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                && forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                    ==> norm::transition_lang(g, theta, out, event, word)
                        == norm::transition_append_combo(g, theta, d, seq![root], event, word),
            model::RegexKindNode::Not(inner) => exists|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                && norm::transition_result(g, norm::ActionShape::Not(d@), out),
            _ => derivative_correct(g, root@, out),
        }
    }

    pub proof fn derivative_native_correct(g: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>, out: TransitionId)
        requires model::graph_wf(g), root@ < g.regexes.len(), derivative_cache_wf(g, cache),
            out@ < g.transitions.len(), derivative_native_result(g, root, cache, out),
        ensures derivative_correct(g, root@, out),
    {
        hide(language::numeric_lang); hide(language::derivative); hide(language::interp_transition);
        hide(model::lift_regex); hide(model::lift_transition);
        norm::regex_unfold(g, root@);
        derivative_constants(g);
        match g.regexes[root@ as int].kind {
            model::RegexKindNode::Star(inner) => {
                assert(model::lift_regex(g, root@) == language::Regex::Star(alloc::boxed::Box::new(model::lift_regex(g, inner))));
                let d = choose|d: TransitionId| inner < cache.len() && cache[inner as int] == Some(d)
                    && forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                        ==> norm::transition_lang(g, theta, out, event, word)
                            == norm::transition_append_combo(g, theta, d, seq![root], event, word);
                assert(derivative_correct(g, inner, d));
                assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                    implies norm::transition_lang(g, theta, out, event, word)
                        == model::regex_lang(g, theta, root@, seq![event] + word) by {
                    let sem = model::gsem(theta);
                    let actual = language::interp_transition(sem, event, model::lift_transition(g, d@));
                    let expected = language::derivative(sem, event, model::lift_regex(g, inner));
                    let tail = seq![model::lift_regex(g, root@)];
                    assert(model::lift_regexes(g, model::regex_ids(seq![root])) =~= tail);
                    language::lemma_concat_prepend(sem, actual, tail, word);
                    language::lemma_concat_prepend(sem, expected, tail, word);
                    assert forall|w: Seq<EventView>| language::numeric_lang(sem, actual, w) == language::numeric_lang(sem, expected, w) by {
                        language::lemma_derivative_correct(sem, event, model::lift_regex(g, inner), w);
                        assert(norm::transition_lang(g, theta, d, event, w)
                            == model::regex_lang(g, theta, inner, seq![event] + w));
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
                    && norm::transition_result(g, norm::ActionShape::Not(d@), out);
                symbolic_not_result(g, d, out);
                assert(derivative_correct(g, inner, d));
                assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                    implies norm::transition_lang(g, theta, out, event, word)
                        == model::regex_lang(g, theta, root@, seq![event] + word) by {
                    reveal(language::numeric_lang);
                }
            },
            model::RegexKindNode::Empty | model::RegexKindNode::All | model::RegexKindNode::Epsilon | model::RegexKindNode::Test(_) => {
                assert forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                    implies norm::transition_lang(g, theta, out, event, word)
                        == model::regex_lang(g, theta, root@, seq![event] + word) by {
                    reveal(language::numeric_lang); reveal(language::interp_transition);
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
            && (if intersect { norm::transition_result(next, norm::ActionShape::Fold(model::transition_ids(results), 0), out) }
                else { forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                    ==> norm::transition_lang(next, theta, out, event, word)
                        == norm::transition_combo(next, theta, results, event, word, false) })
            ==> derivative_correct(next, root@, out),
    {
        assert forall|next: model::Graph, out: TransitionId| model::graph_extends(g, next) && model::graph_wf(next)
            && out@ < next.transitions.len()
            && (if intersect { norm::transition_result(next, norm::ActionShape::Fold(model::transition_ids(results), 0), out) }
                else { forall|theta: Subst, event: EventView, word: Seq<EventView>| language::event_wf(theta, theta.len())
                    ==> norm::transition_lang(next, theta, out, event, word)
                        == norm::transition_combo(next, theta, results, event, word, false) })
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

    pub open spec fn test_children(g: model::Graph, id: TestId) -> Seq<nat> {
        match g.tests[id@ as int] { model::TestNode::And(cs) | model::TestNode::Or(cs) => cs, _ => Seq::empty() }
    }

    pub open spec fn test_tasks_wf(g: model::Graph, tasks: Seq<(TestId, bool)>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> tasks[i].0@ < g.tests.len()
    }

    /// `TestId::evaluate` reuses the `TestId::not` measure: both worklists schedule the same nodes.
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
        Seq::new((test_children(g, id).len() - remaining) as nat, |i: int| (TestId::from_view(test_children(g, id)[test_children(g, id).len() - 1 - i] as u32), false))
    }

    pub open spec fn test_action(g: model::Graph, task: (TestId, bool), values: Seq<bool>, theta: Subst, event: EventView) -> Option<Seq<bool>> {
        if task.1 {
            match g.tests[task.0@ as int] {
                model::TestNode::And(cs) | model::TestNode::Or(cs) => {
                    if cs.len() > values.len() { None }
                    else { Some(values.take(values.len() - cs.len()).push(bool_fold(values.skip(values.len() - cs.len()), g.tests[task.0@ as int] is And))) }
                },
                _ => Some(values.push(model::test_holds(theta, model::lift_test(g, task.0@), event))),
            }
        } else { Some(values.push(model::test_holds(theta, model::lift_test(g, task.0@), event))) }
    }

    pub open spec fn test_run(g: model::Graph, tasks: Seq<(TestId, bool)>, values: Seq<bool>, theta: Subst, event: EventView) -> Option<Seq<bool>>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(values) }
        else { match test_action(g, tasks.last(), values, theta, event) {
            Some(next) => test_run(g, tasks.drop_last(), next, theta, event), None => None,
        } }
    }

    pub proof fn test_run_concat(g: model::Graph, prefix: Seq<(TestId, bool)>, suffix: Seq<(TestId, bool)>, values: Seq<bool>, theta: Subst, event: EventView)
        ensures test_run(g, prefix + suffix, values, theta, event) == match test_run(g, suffix, values, theta, event) {
            Some(next) => test_run(g, prefix, next, theta, event), None => None,
        },
        decreases suffix.len(),
    {
        if suffix.len() > 0 {
            assert((prefix + suffix).last() == suffix.last());
            assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
            if let Some(next) = test_action(g, suffix.last(), values, theta, event) {
                test_run_concat(g, prefix, suffix.drop_last(), next, theta, event);
            }
        } else { assert(prefix + suffix =~= prefix); }
    }

    pub open spec fn child_test_values(g: model::Graph, id: TestId, count: nat, theta: Subst, event: EventView) -> Seq<bool> {
        Seq::new(count, |i: int| model::test_holds(theta, model::lift_test(g, test_children(g, id)[i]), event))
    }

    pub proof fn child_test_run(g: model::Graph, id: TestId, remaining: nat, values: Seq<bool>, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.tests.len(), remaining <= test_children(g, id).len(),
        ensures test_run(g, child_test_tasks(g, id, remaining), values, theta, event)
            == Some(values + child_test_values(g, id, test_children(g, id).len(), theta, event).skip(remaining as int)),
        decreases test_children(g, id).len() - remaining,
    {
        model::lemma_graph_test_wf(g, id@);
        let tasks = child_test_tasks(g, id, remaining);
        let vals = child_test_values(g, id, test_children(g, id).len(), theta, event);
        if remaining < test_children(g, id).len() {
            let child = TestId::from_view(test_children(g, id)[remaining as int] as u32);
            assert(child@ == test_children(g, id)[remaining as int]);
            assert(tasks.last() == (child, false));
            assert(tasks.drop_last() =~= child_test_tasks(g, id, remaining + 1));
            child_test_run(g, id, remaining + 1, values.push(vals[remaining as int]), theta, event);
            assert(values.push(vals[remaining as int]) + vals.skip(remaining as int + 1)
                =~= values + vals.skip(remaining as int));
        } else {
            assert(tasks =~= Seq::empty());
            assert(vals.skip(remaining as int) =~= Seq::empty());
            assert(values + vals.skip(remaining as int) =~= values);
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub proof fn test_expand(g: model::Graph, id: TestId, tasks: Seq<(TestId, bool)>, values: Seq<bool>, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.tests.len(),
            g.tests[id@ as int] is And || g.tests[id@ as int] is Or,
        ensures test_run(g, tasks.push((id, true)) + child_test_tasks(g, id, 0), values, theta, event)
            == test_run(g, tasks.push((id, false)), values, theta, event),
    {
        reveal_with_fuel(model::test_holds, 2);
        reveal_with_fuel(model::lift_test, 2);
        reveal_with_fuel(test_run, 2);
        model::lemma_graph_test_wf(g, id@);
        let vals = child_test_values(g, id, test_children(g, id).len(), theta, event);
        child_test_run(g, id, 0, values, theta, event);
        test_run_concat(g, tasks.push((id, true)), child_test_tasks(g, id, 0), values, theta, event);
        assert(vals.skip(0) =~= vals);
        assert((values + vals).take(values.len() as int) =~= values);
        assert((values + vals).skip(values.len() as int) =~= vals);
        assert(bool_fold(vals, g.tests[id@ as int] is And)
            == model::test_holds(theta, model::lift_test(g, id@), event)) by {
            match g.tests[id@ as int] {
                model::TestNode::And(cs) => {
                    assert(model::lift_test(g, id@) == model::Test::And(model::lift_tests(g, cs, id@)));
                    assert forall|i: int| 0 <= i < cs.len() implies
                        vals[i] == model::test_holds(theta, model::lift_tests(g, cs, id@)[i], event) by {
                        assert(model::lift_tests(g, cs, id@)[i] == model::lift_test(g, cs[i]));
                    }
                    bool_fold_tests(vals, model::lift_tests(g, cs, id@), true, theta, event);
                },
                model::TestNode::Or(cs) => {
                    assert(model::lift_test(g, id@) == model::Test::Or(model::lift_tests(g, cs, id@)));
                    assert forall|i: int| 0 <= i < cs.len() implies
                        vals[i] == model::test_holds(theta, model::lift_tests(g, cs, id@)[i], event) by {
                        assert(model::lift_tests(g, cs, id@)[i] == model::lift_test(g, cs[i]));
                    }
                    bool_fold_tests(vals, model::lift_tests(g, cs, id@), false, theta, event);
                },
                _ => {},
            }
        }
        assert(test_action(g, (id, true), values + vals, theta, event)
            == Some(values.push(model::test_holds(theta, model::lift_test(g, id@), event))));
        assert(tasks.push((id, true)).drop_last() =~= tasks);
        assert(tasks.push((id, false)).drop_last() =~= tasks);
    }

    pub proof fn bool_fold_tests(vals: Seq<bool>, tests: Seq<model::Test>, and: bool, theta: Subst, event: EventView)
        requires vals.len() == tests.len(), forall|i: int| 0 <= i < vals.len() ==> vals[i] == model::test_holds(theta, tests[i], event),
        ensures bool_fold(vals, and) == model::test_holds(theta, if and { model::Test::And(tests) } else { model::Test::Or(tests) }, event),
    {
        norm::test_lemma_semantics_unfold(theta, event, model::Test::And(tests));
        norm::test_lemma_semantics_unfold(theta, event, model::Test::Or(tests));
        if and {
            if bool_fold(vals, true) {
                assert forall|i: int| 0 <= i < tests.len() implies model::test_holds(theta, tests[i], event) by { assert(vals[i]); }
            }
            if model::test_holds(theta, model::Test::And(tests), event) {
                assert forall|i: int| 0 <= i < vals.len() implies vals[i] by { assert(model::test_holds(theta, tests[i], event)); }
            }
        } else {
            if bool_fold(vals, false) {
                let i = choose|i: int| 0 <= i < vals.len() && vals[i];
                assert(model::test_holds(theta, tests[i], event));
            }
            if model::test_holds(theta, model::Test::Or(tests), event) {
                let i = choose|i: int| 0 <= i < tests.len() && model::test_holds(theta, tests[i], event);
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

    pub proof fn test_run_unfold(g: model::Graph, tasks: Seq<(TestId, bool)>, values: Seq<bool>, theta: Subst, event: EventView)
        ensures test_run(g, tasks, values, theta, event) == if tasks.len() == 0 { Some(values) }
            else { match test_action(g, tasks.last(), values, theta, event) {
                Some(next) => test_run(g, tasks.drop_last(), next, theta, event), None => None,
            } },
    {
        if tasks.len() == 0 {} else {}
    }

    pub proof fn realized_atom_value(g: model::Graph, atoms: Seq<TestId>, words: Seq<u64>, id: TestId, primitive: model::Primitive, positive: bool, index: usize, value: bool)
        requires id@ < g.tests.len(), g.tests[id@ as int] == model::TestNode::Atom(primitive, positive),
            positive_atom_at(g, atoms, primitive, index), value == truth_word_bit(words, index as nat),
        ensures forall|theta: Subst, event: EventView|
            truth_words_realize(g, atoms, words, theta, event) ==>
                (if positive { value } else { !value }) == model::test_holds(theta, model::lift_test(g, id@), event),
    {
        assert forall|theta: Subst, event: EventView|
            truth_words_realize(g, atoms, words, theta, event) implies
                (if positive { value } else { !value }) == model::test_holds(theta, model::lift_test(g, id@), event) by {
            assert(0 <= (index as int) < atoms.len());
            reveal(truth_words_realize);
            assert forall|i: int| 0 <= i < atoms.len() implies
                truth_word_bit(words, i as nat) == model::test_holds(theta, model::lift_test(g, atoms[i]@), event) by {}
            assert(truth_word_bit(words, (index as int) as nat)
                == model::test_holds(theta, model::lift_test(g, atoms[index as int]@), event));
            assert(model::lift_test(g, atoms[index as int]@) == model::Test::Atom(primitive, true));
            assert(model::lift_test(g, id@) == model::Test::Atom(primitive, positive));
        }
    }

    pub type InterpRegex = language::Regex<model::Test>;

    pub open spec fn interpreted(g: model::Graph, id: TransitionId, theta: Subst, event: EventView) -> InterpRegex {
        language::interp_transition(model::gsem(theta), event, model::lift_transition(g, id@))
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
        Seq::new((transition_children(g, id).len() - remaining) as nat, |i: int| (TransitionId::from_view(transition_children(g, id)[transition_children(g, id).len() - 1 - i] as u32), false))
    }

    pub open spec fn regex_stack_equiv(sem: spec_fn(model::Test, EventView) -> bool, left: Seq<InterpRegex>, right: Seq<InterpRegex>) -> bool {
        left.len() == right.len() && forall|i: int, word: Seq<EventView>| 0 <= i < left.len() ==>
            language::numeric_lang(sem, left[i], word) == language::numeric_lang(sem, right[i], word)
    }

    pub open spec fn interp_results_equiv(sem: spec_fn(model::Test, EventView) -> bool, left: Option<Seq<InterpRegex>>, right: Option<Seq<InterpRegex>>) -> bool {
        match (left, right) { (Some(a), Some(b)) => regex_stack_equiv(sem, a, b), (None, None) => true, _ => false }
    }

    pub open spec fn interp_action(g: model::Graph, task: (TransitionId, bool), values: Seq<InterpRegex>, theta: Subst, event: EventView) -> Option<Seq<InterpRegex>> {
        if !task.1 { Some(values.push(interpreted(g, task.0, theta, event))) }
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
                _ => Some(values.push(interpreted(g, task.0, theta, event))),
            }
        }
    }

    pub open spec fn interp_run(g: model::Graph, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView) -> Option<Seq<InterpRegex>>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(values) }
        else { match interp_action(g, tasks.last(), values, theta, event) {
            Some(next) => interp_run(g, tasks.drop_last(), next, theta, event), None => None,
        } }
    }

    pub proof fn interp_run_unfold(g: model::Graph, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        ensures interp_run(g, tasks, values, theta, event) == if tasks.len() == 0 { Some(values) }
            else { match interp_action(g, tasks.last(), values, theta, event) {
                Some(next) => interp_run(g, tasks.drop_last(), next, theta, event), None => None,
            } },
    { if tasks.len() == 0 {} else {} }

    pub proof fn regex_stack_equiv_trans(sem: spec_fn(model::Test, EventView) -> bool, a: Seq<InterpRegex>, b: Seq<InterpRegex>, c: Seq<InterpRegex>)
        requires regex_stack_equiv(sem, a, b), regex_stack_equiv(sem, b, c),
        ensures regex_stack_equiv(sem, a, c),
    {}

    pub proof fn interp_results_equiv_trans(sem: spec_fn(model::Test, EventView) -> bool, a: Option<Seq<InterpRegex>>, b: Option<Seq<InterpRegex>>, c: Option<Seq<InterpRegex>>)
        requires interp_results_equiv(sem, a, b), interp_results_equiv(sem, b, c),
        ensures interp_results_equiv(sem, a, c),
    {
        match (a,b,c) { (Some(x),Some(y),Some(z)) => regex_stack_equiv_trans(sem,x,y,z), _ => {} }
    }

    pub open spec fn regex_fold(values: Seq<InterpRegex>, intersect: bool) -> InterpRegex {
        if intersect { language::Regex::Intersect(values) } else { language::Regex::Union(values) }
    }

    pub proof fn regex_stack_fold_congruent(sem: spec_fn(model::Test, EventView) -> bool, left: Seq<InterpRegex>, right: Seq<InterpRegex>, intersect: bool)
        requires regex_stack_equiv(sem, left, right),
        ensures forall|word: Seq<EventView>| language::numeric_lang(sem, regex_fold(left, intersect), word)
            == language::numeric_lang(sem, regex_fold(right, intersect), word),
    {
        assert forall|word: Seq<EventView>| language::numeric_lang(sem, regex_fold(left, intersect), word)
            == language::numeric_lang(sem, regex_fold(right, intersect), word) by {
            regex_fold_semantics(sem, left, intersect, word);
            regex_fold_semantics(sem, right, intersect, word);
            if !intersect {
                if exists|i: int| 0 <= i < left.len() && language::numeric_lang(sem, left[i], word) {
                    let i = choose|i: int| 0 <= i < left.len() && language::numeric_lang(sem, left[i], word);
                    assert(language::numeric_lang(sem, right[i], word));
                }
                if exists|i: int| 0 <= i < right.len() && language::numeric_lang(sem, right[i], word) {
                    let i = choose|i: int| 0 <= i < right.len() && language::numeric_lang(sem, right[i], word);
                    assert(language::numeric_lang(sem, left[i], word));
                }
            } else {
                if language::numeric_lang(sem, regex_fold(left, true), word) {
                    assert forall|i: int| 0 <= i < right.len() implies language::numeric_lang(sem, right[i], word) by {
                        assert(language::numeric_lang(sem, left[i], word));
                    }
                }
                if language::numeric_lang(sem, regex_fold(right, true), word) {
                    assert forall|i: int| 0 <= i < left.len() implies language::numeric_lang(sem, left[i], word) by {
                        assert(language::numeric_lang(sem, right[i], word));
                    }
                }
            }
        }
    }

    pub proof fn interp_action_congruent(g: model::Graph, task: (TransitionId, bool), left: Seq<InterpRegex>, right: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires regex_stack_equiv(model::gsem(theta), left, right),
        ensures interp_results_equiv(model::gsem(theta), interp_action(g, task, left, theta, event), interp_action(g, task, right, theta, event)),
    {
        let sem = model::gsem(theta);
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
                        assert forall|word: Seq<EventView>| language::numeric_lang(sem, language::Regex::Not(Box::new(left.last())), word)
                            == language::numeric_lang(sem, language::Regex::Not(Box::new(right.last())), word) by {
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

    pub proof fn interp_run_congruent(g: model::Graph, tasks: Seq<(TransitionId, bool)>, left: Seq<InterpRegex>, right: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires regex_stack_equiv(model::gsem(theta), left, right),
        ensures interp_results_equiv(model::gsem(theta), interp_run(g, tasks, left, theta, event), interp_run(g, tasks, right, theta, event)),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            interp_action_congruent(g, tasks.last(), left, right, theta, event);
            match (interp_action(g, tasks.last(), left, theta, event), interp_action(g, tasks.last(), right, theta, event)) {
                (Some(a),Some(b)) => interp_run_congruent(g, tasks.drop_last(), a, b, theta, event), _ => {},
            }
        }
    }

    pub proof fn interp_run_concat(g: model::Graph, prefix: Seq<(TransitionId, bool)>, suffix: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        ensures interp_run(g, prefix + suffix, values, theta, event) == match interp_run(g, suffix, values, theta, event) {
            Some(next) => interp_run(g, prefix, next, theta, event), None => None,
        },
        decreases suffix.len(),
    {
        if suffix.len() > 0 {
            assert((prefix + suffix).last() == suffix.last());
            assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
            if let Some(next) = interp_action(g, suffix.last(), values, theta, event) {
                interp_run_concat(g, prefix, suffix.drop_last(), next, theta, event);
            }
        } else { assert(prefix + suffix =~= prefix); }
    }

    pub proof fn regex_fold_semantics(sem: spec_fn(model::Test, EventView) -> bool, values: Seq<InterpRegex>, intersect: bool, word: Seq<EventView>)
        ensures language::numeric_lang(sem, regex_fold(values, intersect), word) == if intersect {
            forall|i: int| 0 <= i < values.len() ==> language::numeric_lang(sem, values[i], word)
        } else { exists|i: int| 0 <= i < values.len() && language::numeric_lang(sem, values[i], word) },
    {
        reveal(regex_fold);
        if intersect {
            language::lemma_lang_intersect::<model::Test>(sem, values, word);
        } else {
            language::lemma_lang_union::<model::Test>(sem, values, word);
        }
    }


    pub open(crate) spec fn child_interp_values(g: model::Graph, id: TransitionId, theta: Subst, event: EventView) -> Seq<InterpRegex> {
        Seq::new(transition_children(g, id).len(), |i: int| interpreted(g, TransitionId::from_view(transition_children(g, id)[i] as u32), theta, event))
    }

    pub proof fn child_interp_run(g: model::Graph, id: TransitionId, remaining: nat, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.transitions.len(), remaining <= transition_children(g, id).len(),
        ensures interp_run(g, child_interp_tasks(g, id, remaining), values, theta, event)
            == Some(values + child_interp_values(g, id, theta, event).skip(remaining as int)),
        decreases transition_children(g, id).len() - remaining,
    {
        model::lemma_graph_transition_wf(g, id@);
        let tasks = child_interp_tasks(g, id, remaining);
        let vals = child_interp_values(g, id, theta, event);
        if remaining < transition_children(g, id).len() {
            let child = TransitionId::from_view(transition_children(g, id)[remaining as int] as u32);
            assert(child@ == transition_children(g, id)[remaining as int]);
            assert(tasks.last() == (child, false));
            assert(tasks.drop_last() =~= child_interp_tasks(g, id, remaining + 1));
            child_interp_run(g, id, remaining + 1, values.push(vals[remaining as int]), theta, event);
            assert(values.push(vals[remaining as int]) + vals.skip(remaining as int + 1) =~= values + vals.skip(remaining as int));
        } else {
            assert(tasks =~= Seq::empty());
            assert(vals.skip(remaining as int) =~= Seq::empty());
            assert(values + vals.skip(remaining as int) =~= values);
        }
    }

    pub proof fn interpreted_fold(g: model::Graph, id: TransitionId, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect,
        ensures forall|word: Seq<EventView>| language::numeric_lang(model::gsem(theta), interpreted(g, id, theta, event), word)
            == language::numeric_lang(model::gsem(theta), regex_fold(child_interp_values(g, id, theta, event), g.transitions[id@ as int] is Intersect), word),
    {
        model::lemma_graph_transition_wf(g, id@);
        let children = Seq::new(transition_children(g, id).len(), |i: int| TransitionId::from_view(transition_children(g, id)[i] as u32));
        assert(model::transition_ids(children) =~= transition_children(g, id));
        norm::transition_lemma_children_language(g, id, children, g.transitions[id@ as int] is Intersect);
        let vals = child_interp_values(g, id, theta, event);
        assert forall|word: Seq<EventView>| language::numeric_lang(model::gsem(theta), interpreted(g, id, theta, event), word)
            == language::numeric_lang(model::gsem(theta), regex_fold(vals, g.transitions[id@ as int] is Intersect), word) by {
            let sem = model::gsem(theta);
            reveal(norm::transition_combo);
            assert(norm::transition_lang(g, theta, id, event, word)
                == language::numeric_lang(sem, interpreted(g, id, theta, event), word));
            assert forall|i: int| 0 <= i < children.len() implies
                norm::transition_lang(g, theta, children[i], event, word) == language::numeric_lang(sem, vals[i], word) by {}
            regex_fold_semantics(sem, vals, g.transitions[id@ as int] is Intersect, word);
            if !(g.transitions[id@ as int] is Intersect) {
                if norm::transition_lang(g, theta, id, event, word) {
                    let i = choose|i: int| 0 <= i < children.len() && norm::transition_lang(g, theta, children[i], event, word);
                    assert(language::numeric_lang(sem, vals[i], word));
                }
                if language::numeric_lang(sem, regex_fold(vals, false), word) {
                    let i = choose|i: int| 0 <= i < vals.len() && language::numeric_lang(sem, vals[i], word);
                    assert(norm::transition_lang(g, theta, children[i], event, word));
                }
            } else {
                if norm::transition_lang(g, theta, id, event, word) {
                    assert forall|i: int| 0 <= i < vals.len() implies language::numeric_lang(sem, vals[i], word) by {
                        assert(norm::transition_lang(g, theta, children[i], event, word));
                    }
                }
                if language::numeric_lang(sem, regex_fold(vals, true), word) {
                    assert forall|i: int| 0 <= i < children.len() implies norm::transition_lang(g, theta, children[i], event, word) by {
                        assert(language::numeric_lang(sem, vals[i], word));
                    }
                }
            }
        }
    }

    pub proof fn interp_expand_set(g: model::Graph, id: TransitionId, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect,
        ensures interp_results_equiv(model::gsem(theta),
            interp_run(g, tasks.push((id, false)), values, theta, event),
            interp_run(g, tasks.push((id, true)) + child_interp_tasks(g, id, 0), values, theta, event)),
    {
        let vals = child_interp_values(g, id, theta, event);
        child_interp_run(g, id, 0, values, theta, event);
        interp_run_concat(g, tasks.push((id, true)), child_interp_tasks(g, id, 0), values, theta, event);
        interpreted_fold(g, id, theta, event);
        assert(vals.skip(0) =~= vals);
        assert((values + vals).take(values.len() as int) =~= values);
        assert((values + vals).skip(values.len() as int) =~= vals);
        assert(tasks.push((id, true)).drop_last() =~= tasks);
        assert(tasks.push((id, false)).drop_last() =~= tasks);
        interp_run_unfold(g, tasks.push((id, true)), values + vals, theta, event);
        interp_run_unfold(g, tasks.push((id, false)), values, theta, event);
        interp_run_congruent(g, tasks, values.push(interpreted(g, id, theta, event)), values.push(regex_fold(vals, g.transitions[id@ as int] is Intersect)), theta, event);
    }

    pub proof fn interp_action_stable(before: model::Graph, after: model::Graph, task: (TransitionId, bool), values: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires model::graph_wf(before), model::graph_extends(before, after), task.0@ < before.transitions.len(),
        ensures interp_action(before, task, values, theta, event) == interp_action(after, task, values, theta, event),
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

    pub proof fn interp_run_stable(before: model::Graph, after: model::Graph, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires model::graph_wf(before), model::graph_extends(before, after), interp_tasks_wf(before, tasks),
        ensures interp_run(before, tasks, values, theta, event) == interp_run(after, tasks, values, theta, event),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            interp_action_stable(before, after, tasks.last(), values, theta, event);
            if let Some(next) = interp_action(before, tasks.last(), values, theta, event) {
                interp_run_stable(before, after, tasks.drop_last(), next, theta, event);
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
        count <= before.len() && forall|theta: Subst| language::event_wf(theta, theta.len()) ==>
            regex_stack_equiv(model::gsem(theta), lifted_values(g, after),
                lifted_values(g, before.take(before.len() - count)).push(regex_fold(lifted_values(g, before.skip(before.len() - count)), intersect)))
    }

    pub open spec fn interp_machine_relation(before: model::Graph, after: model::Graph,
        tasks0: Seq<(TransitionId, bool)>, tasks1: Seq<(TransitionId, bool)>, values0: Seq<RegexId>, values1: Seq<RegexId>, atoms: Seq<TestId>, words: Seq<u64>) -> bool {
        forall|theta: Subst, event: EventView|
            language::event_wf(theta, theta.len()) && truth_words_realize(before, atoms, words, theta, event) ==>
                interp_results_equiv(model::gsem(theta),
                    interp_run(before, tasks0, lifted_values(before, values0), theta, event),
                    interp_run(after, tasks1, lifted_values(after, values1), theta, event))
    }

    pub proof fn interp_same_configuration_extends(before: model::Graph, after: model::Graph,
        tasks: Seq<(TransitionId, bool)>, values: Seq<RegexId>, theta: Subst, event: EventView)
        requires model::graph_wf(before), model::graph_extends(before, after), interp_tasks_wf(before, tasks), norm::regex_ids_valid(before, values),
        ensures interp_tasks_wf(after, tasks),
            interp_run(before, tasks, lifted_values(before, values), theta, event)
                == interp_run(after, tasks, lifted_values(after, values), theta, event),
    {
        lifted_values_stable(before, after, values);
        interp_run_stable(before, after, tasks, lifted_values(before, values), theta, event);
    }

    pub proof fn regex_fold_ids(g: model::Graph, ids: Seq<RegexId>, intersect: bool, theta: Subst, word: Seq<EventView>)
        ensures norm::regex_combo(g, theta, ids, word, intersect)
            == language::numeric_lang(model::gsem(theta), regex_fold(lifted_values(g, ids), intersect), word),
    {
        let sem = model::gsem(theta);
        let vals = lifted_values(g, ids);
        reveal(norm::regex_combo);
        regex_fold_semantics(sem, vals, intersect, word);
        assert forall|i: int| 0 <= i < ids.len() implies
            model::regex_lang(g, theta, ids[i]@, word) == language::numeric_lang(sem, vals[i], word) by {}
        if !intersect {
            if norm::regex_combo(g, theta, ids, word, false) {
                let i = choose|i: int| 0 <= i < ids.len() && model::regex_lang(g, theta, ids[i]@, word);
                assert(language::numeric_lang(sem, vals[i], word));
            }
            if language::numeric_lang(sem, regex_fold(vals, false), word) {
                let i = choose|i: int| 0 <= i < vals.len() && language::numeric_lang(sem, vals[i], word);
                assert(model::regex_lang(g, theta, ids[i]@, word));
            }
        } else {
            if norm::regex_combo(g, theta, ids, word, true) {
                assert forall|i: int| 0 <= i < vals.len() implies language::numeric_lang(sem, vals[i], word) by {
                    assert(model::regex_lang(g, theta, ids[i]@, word));
                }
            }
            if language::numeric_lang(sem, regex_fold(vals, true), word) {
                assert forall|i: int| 0 <= i < ids.len() implies model::regex_lang(g, theta, ids[i]@, word) by {
                    assert(language::numeric_lang(sem, vals[i], word));
                }
            }
        }
    }

    pub proof fn interp_value_reduction(g: model::Graph, id: TransitionId, finish: bool, tasks: Seq<(TransitionId, bool)>, before: Seq<InterpRegex>, after: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires interp_action(g, (id, finish), before, theta, event) is Some,
            regex_stack_equiv(model::gsem(theta), interp_action(g, (id, finish), before, theta, event)->Some_0, after),
        ensures interp_results_equiv(model::gsem(theta),
            interp_run(g, tasks.push((id, finish)), before, theta, event), interp_run(g, tasks, after, theta, event)),
    {
        assert(tasks.push((id, finish)).drop_last() =~= tasks);
        interp_run_unfold(g, tasks.push((id, finish)), before, theta, event);
        interp_run_congruent(g, tasks, interp_action(g, (id, finish), before, theta, event)->Some_0, after, theta, event);
    }

    pub proof fn interp_expand_unary(g: model::Graph, id: TransitionId, inner: TransitionId, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::Not(inner@)
                || g.transitions[id@ as int] == model::TransitionNode::Append(inner@, transition_suffix(g, id)),
        ensures interp_run(g, tasks.push((id, false)), values, theta, event)
            == interp_run(g, tasks.push((id, true)).push((inner, false)), values, theta, event),
    {
        norm::transition_unfold(g, id@);
        let sem = model::gsem(theta);
        let term = model::lift_transition(g, inner@);
        match g.transitions[id@ as int] {
            model::TransitionNode::Not(_) => language::lemma_interp_not(sem, event, term),
            model::TransitionNode::Append(_, cs) => language::lemma_interp_append(sem, event, term, model::lift_regexes(g, cs)),
            _ => {},
        }
        assert(tasks.push((id, false)).drop_last() =~= tasks);
        assert(tasks.push((id, true)).push((inner, false)).drop_last() =~= tasks.push((id, true)));
        assert(tasks.push((id, true)).drop_last() =~= tasks);
        assert(values.push(interpreted(g, inner, theta, event)).drop_last() =~= values);
        interp_run_unfold(g, tasks.push((id, false)), values, theta, event);
        interp_run_unfold(g, tasks.push((id, true)).push((inner, false)), values, theta, event);
        interp_run_unfold(g, tasks.push((id, true)), values.push(interpreted(g, inner, theta, event)), theta, event);
    }

    pub proof fn interp_choose(g: model::Graph, id: TransitionId, finish: bool, test: TestId, a: TransitionId, b: TransitionId, chosen: TransitionId, tasks: Seq<(TransitionId, bool)>, values: Seq<InterpRegex>, theta: Subst, event: EventView)
        requires model::graph_wf(g), id@ < g.transitions.len(), g.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
            chosen == if model::test_holds(theta, model::lift_test(g, test@), event) { a } else { b },
        ensures interp_run(g, tasks.push((id, finish)), values, theta, event)
            == interp_run(g, tasks.push((chosen, false)), values, theta, event),
    {
        norm::transition_unfold(g, id@);
        language::lemma_interp_if(model::gsem(theta), event, model::lift_test(g, test@), model::lift_transition(g, a@), model::lift_transition(g, b@));
        assert(tasks.push((id, finish)).drop_last() =~= tasks);
        assert(tasks.push((chosen, false)).drop_last() =~= tasks);
        interp_run_unfold(g, tasks.push((id, finish)), values, theta, event);
        interp_run_unfold(g, tasks.push((chosen, false)), values, theta, event);
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


    pub proof fn regex_concat_ids(g: model::Graph, ids: Seq<RegexId>)
        ensures model::lift_regexes(g, model::regex_ids(ids)) == lifted_values(g, ids),
    { assert(model::lift_regexes(g, model::regex_ids(ids)) =~= lifted_values(g, ids)); }

    #[verifier::spinoff_prover]
    pub proof fn interp_append_finish(
        before: model::Graph, after: model::Graph, root: TransitionId,
        pending: Seq<(TransitionId, bool)>, prior: Seq<RegexId>, head: RegexId,
        xs: Seq<RegexId>, values: Seq<RegexId>,
    )
        requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
            root@ < before.transitions.len(), before.transitions[root@ as int] is Append,
            interp_tasks_wf(before, pending), norm::regex_ids_valid(before, prior),
            prior.len() > 0, prior.last() == head, values.len() == prior.len(),
            values == prior.drop_last().push(values.last()), values.last()@ < after.regexes.len(),
            model::regex_ids(xs) == seq![head@] + transition_suffix(before, root),
            forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta, theta.len())
                ==> #[trigger] model::regex_lang(after, theta, values.last()@, word) == norm::concat_combo(after, theta, xs, word),
        ensures norm::regex_ids_valid(after, values),
            interp_stack_result(before, pending.push((root, true)), prior.len())
                == interp_stack_result(after, pending, values.len()),
            forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len())
                ==> interp_results_equiv(model::gsem(theta),
                    interp_run(before, pending.push((root, true)), lifted_values(before, prior), theta, event),
                    interp_run(after, pending, lifted_values(after, values), theta, event)),
    {
        hide(language::numeric_lang); hide(language::interp_transition); hide(interp_run);
        hide(model::test_holds); hide(model::lift_transition); hide(model::lift_regex);
        after.transitions.lemma_prefix_index_eq(before.transitions);
        assert(before.transitions[root@ as int] == after.transitions[root@ as int]);
        assert(transition_suffix(before, root) == transition_suffix(after, root));
        lifted_values_stable(before, after, prior);
        interp_append_ids(after, xs, head, transition_suffix(after, root));
        regex_concat_ids(after, xs);
        assert forall|i: int| 0 <= i < values.len() implies values[i]@ < after.regexes.len() by {
            if i < prior.len() - 1 { assert(values[i] == prior[i]); }
            else { assert(values[i] == values.last()); }
        }
        assert(interp_tasks_wf(before, pending.push((root, true))));
        interp_stack_stable(before, after, pending.push((root, true)), prior.len());
        interp_stack_task(after, pending, (root, true), prior.len());
        assert forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len()) implies
            interp_results_equiv(model::gsem(theta),
                interp_run(before, pending.push((root, true)), lifted_values(before, prior), theta, event),
                interp_run(after, pending, lifted_values(after, values), theta, event)) by {
            interp_same_configuration_extends(before, after, pending.push((root, true)), prior, theta, event);
            assert forall|word: Seq<EventView>| model::regex_lang(after, theta, values.last()@, word)
                == language::numeric_lang(model::gsem(theta), language::Regex::Concat(seq![model::lift_regex(after, head@)]
                    + model::lift_regexes(after, transition_suffix(after, root))), word) by {
                reveal(norm::concat_combo);
                assert(model::regex_lang(after, theta, values.last()@, word) == norm::concat_combo(after, theta, xs, word));
                assert(model::lift_regexes(after, model::regex_ids(xs)) == lifted_values(after, xs));
                assert(lifted_values(after, xs) == seq![model::lift_regex(after, head@)] + model::lift_regexes(after, transition_suffix(after, root)));
            }
            assert(lifted_values(after, values) =~= lifted_values(after, prior).drop_last().push(model::lift_regex(after, values.last()@)));
            assert(lifted_values(after, prior).last() == model::lift_regex(after, head@));
            assert forall|i: int, word: Seq<EventView>| 0 <= i < prior.len() implies
                language::numeric_lang(model::gsem(theta), interp_action(after, (root, true), lifted_values(after, prior), theta, event)->Some_0[i], word)
                    == language::numeric_lang(model::gsem(theta), lifted_values(after, values)[i], word) by {
                if i == prior.len() - 1 {
                    assert(model::regex_lang(after, theta, values.last()@, word)
                        == language::numeric_lang(model::gsem(theta), language::Regex::Concat(seq![model::lift_regex(after, head@)]
                            + model::lift_regexes(after, transition_suffix(after, root))), word));
                }
            }
            interp_value_reduction(after, root, true, pending, lifted_values(after, prior), lifted_values(after, values), theta, event);
        }
    }


    pub proof fn interp_root_stable(before: model::Graph, after: model::Graph, root: TransitionId)
        requires model::graph_wf(before), model::graph_extends(before, after), root@ < before.transitions.len(),
        ensures model::lift_transition(before, root@) == model::lift_transition(after, root@),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_transition_stable(before, after, root@);
    }
        }
}

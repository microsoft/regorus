// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Revision-bound retained cursors and failure-atomic numeric batch evaluation.
//! Graph construction and evaluation never report `WrongHistoryOwner`; typed facades check ownership.

#[cfg(verus_keep_ghost)]
use crate::compiled_rule::verify::numeric_result;
use crate::progress::CompiledPair;
#[cfg(any(test, feature = "test-util"))]
pub use crate::progress::WorkCounters;
#[cfg(verus_keep_ghost)]
use crate::progress::verify as progress;
#[cfg(verus_keep_ghost)]
use crate::verify::history_algebra;
#[cfg(verus_keep_ghost)]
use crate::verify::typed_decision as decision;
use alloc::sync::Arc;
#[cfg(any(test, feature = "test-util"))]
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use history_store::cache::HISTORY_CACHE_CAPACITY;
#[cfg(verus_keep_ghost)]
use history_store::cache::verify::{cursor_key_eq, longer_cached_prefix};
use history_store::cache::{CursorCache, HistoryCursor};
use history_store::history::StoredHistory;
#[cfg(verus_keep_ghost)]
use history_store::history::verify as raw;
use history_store::store::{Event, HistoryStore};
use junco_core::errors::HistoryError;
use junco_core::flat::FlatPair;
use junco_core::kernel::Bindings;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::kernel::{KernelResult, RegexId};
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics::resource_error;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;
}

#[cfg(verus_keep_ghost)]
verus! {
pub mod verify {
    use super::*;
    broadcast use junco_core::kernel::verify::group_kernel_views;
    /// Read-only public predicates keep graph IDs and writable runtime state private.
    pub open(crate) spec fn runtime_wf(runtime: RuleRuntime) -> bool {
        cursor_cache_wf(runtime.pair, runtime.cursors@, runtime.snapshots@)
    }

    pub open(crate) spec fn constructor_result(
        result: Result<RuleRuntime, HistoryError>, store: Arc<HistoryStore>,
        template: junco_core::flat::FlatPair<u64>,
    ) -> bool {
        result != Err(HistoryError::WrongHistoryOwner)
            && (junco_core::flat::verify::structural_wf(template) ==> language::no_invariant_failure(result))
            && (junco_core::flat::verify::structural_wf(template)
                ==> !(result matches Err(HistoryError::InvalidPolicy { .. })))
            && (junco_core::flat::verify::structural_wf(template)
                ==> (result matches Err(error) ==> resource_error(error)))
            && (result matches Ok(runtime) ==> runtime_wf(runtime)
            && runtime.store == store
            && runtime.cursors@ == Seq::<HistoryCursor>::empty()
            && runtime.snapshots@ == HistorySnapshots::empty()
            && crate::compile::verify::regex_correct(
                runtime.pair.store.graph(), template, template.root as nat, runtime.pair.root))
    }

    /// The retained root language, without exposing graph nodes or cache state.
    pub closed spec fn runtime_accepts(
        runtime: RuleRuntime, bindings: language::EventView, events: Seq<language::EventView>,
    ) -> bool {
        model::regex_lang(runtime.pair.store.graph(), bindings, runtime.pair.root@, events)
    }

    pub open(crate) spec fn resume_requires(
        runtime: RuleRuntime, bindings: Bindings, stored: StoredHistory, target_len: usize,
    ) -> bool {
        runtime_wf(runtime)
            && snapshot_compatible(runtime.snapshots@, stored.id(), stored.revision(), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && language::event_wf(bindings@, bindings@.len()) && target_len <= history_store::history::verify::stored_events(&stored).len()
    }

    pub open(crate) spec fn resume_ensures(
        before: RuleRuntime, after: RuleRuntime, result: BatchCursor,
        bindings: Bindings, stored: StoredHistory, target_len: usize,
    ) -> bool {
        after.store == before.store && after.pair == before.pair && after.cursors@ == before.cursors@
            && after.snapshots@ == before.snapshots@.insert((stored.id(), stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && runtime_wf(after) && result.consumed <= target_len
            && progress::residual_after_prefix(after.pair, history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)),
                bindings@, result.consumed as nat, result.residual)
            && batch_matches_snapshot(after.pair, result, stored.id(), stored.revision(), bindings, after.snapshots@)
    }

    pub open(crate) spec fn advance_requires(
        runtime: RuleRuntime, cursor: BatchCursor, bindings: Bindings, stored: StoredHistory,
    ) -> bool {
        runtime_wf(runtime)
            && snapshot_compatible(runtime.snapshots@, stored.id(), stored.revision(), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && batch_matches_snapshot(runtime.pair, cursor, stored.id(), stored.revision(), bindings, runtime.snapshots@)
    }

    pub open(crate) spec fn advance_ensures(
        before: RuleRuntime, after: RuleRuntime, start: BatchCursor, cursor: BatchCursor,
        bindings: Bindings, stored: StoredHistory,
        target_len: usize, batch_size: usize, result: Result<Option<bool>, HistoryError>,
    ) -> bool {
        result != Err(HistoryError::WrongHistoryOwner)
            && (batch_size > 0 && start.consumed <= target_len
                && target_len <= stored@.events.len() ==> language::no_invariant_failure(result))
            && (batch_size > 0 && start.consumed <= target_len
                && target_len <= stored@.events.len()
                ==> (result matches Err(error) ==> resource_error(error)))
            && runtime_wf(after) && after.store == before.store && progress::pair_frame(before.pair, after.pair)
            && after.snapshots@ == before.snapshots@.insert((stored.id(), stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && batch_matches_snapshot(after.pair, cursor, stored.id(), stored.revision(), bindings, after.snapshots@)
            && progress::residual_after_prefix(after.pair, history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)),
                bindings@, cursor.consumed as nat, cursor.residual)
            && (result is Err ==> cursor.consumed == start.consumed
                && cursor.residual == start.residual && after.cursors@ == before.cursors@)
            && (result is Ok ==> start.consumed <= cursor.consumed <= target_len
                && cursor.consumed == language::selected_end(start.consumed as nat, target_len as nat, batch_size as nat))
            && (result matches Ok(None) ==> cursor.consumed < target_len)
            && (result matches Ok(Some(answer)) ==> cursor.consumed == target_len
                && answer == model::regex_lang(before.pair.store.graph(), bindings@, before.pair.root@,
                    history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)).take(target_len as int)))
    }

    /// Logical graph IDs and the retained numeric store survive every transaction.
    pub open(crate) spec fn runtime_frame(before: RuleRuntime, after: RuleRuntime) -> bool {
        after.store == before.store && progress::pair_frame(before.pair, after.pair)
    }

    /// Retained graph growth does not change the root language of an earlier runtime.
    pub proof fn lemma_runtime_frame_accepts(
        before: RuleRuntime, after: RuleRuntime,
        bindings: language::EventView, events: Seq<language::EventView>,
    )
        requires runtime_wf(before), runtime_frame(before, after),
        ensures runtime_accepts(before, bindings, events) == runtime_accepts(after, bindings, events),
    {
        hide(language::numeric_lang);
        hide(model::lift_regex);
        reveal(runtime_wf);
        reveal(runtime_frame);
        reveal(runtime_accepts);
        model::lemma_graph_wf_elim(before.pair.store.graph());
        model::lemma_lift_regex_stable(before.pair.store.graph(), after.pair.store.graph(), before.pair.root@);
    }

    /// A failed transaction preserves every previously retained cursor.
    pub open(crate) spec fn cursor_cache_unchanged(before: RuleRuntime, after: RuleRuntime) -> bool {
        after.cursors@ == before.cursors@
    }

    pub proof fn lemma_constructor_runtime_wf(runtime: RuleRuntime, store: Arc<HistoryStore>,
        template: junco_core::flat::FlatPair<u64>)
        requires constructor_result(Ok(runtime), store, template),
        ensures runtime_wf(runtime), runtime.spec_store() == store,
            runtime.spec_snapshots() == HistorySnapshots::empty(),
    {
        reveal(constructor_result);
    }

    /// A newly constructed runtime has not observed any history revision yet.
    pub proof fn lemma_constructor_snapshot_compatible(
        runtime: RuleRuntime, store: Arc<HistoryStore>, template: FlatPair<u64>, stored: StoredHistory,
    )
        requires constructor_result(Ok(runtime), store, template),
        ensures snapshot_compatible(runtime.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
    {
        lemma_constructor_runtime_wf(runtime, store, template);
        lemma_snapshot_compatible_intro(runtime.spec_snapshots(), stored.id(), stored.revision(), stored@.events);
    }

    /// Introduce readiness from public observations, not from readiness itself.
    pub proof fn lemma_resume_requires(
        runtime: RuleRuntime, bindings: Bindings, stored: StoredHistory, target_len: usize,
    )
        requires runtime_wf(runtime),
            snapshot_compatible(runtime.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
            language::event_wf(bindings@, bindings@.len()), target_len <= stored@.events.len(),
        ensures resume_requires(runtime, bindings, stored, target_len),
    {
        history_store::history::lemma_stored_history_view(stored);
        reveal(resume_requires);
    }

    pub proof fn lemma_resume_can_advance(
        before: RuleRuntime, after: RuleRuntime, cursor: BatchCursor,
        bindings: Bindings, stored: StoredHistory, target_len: usize,
    )
        requires resume_ensures(before, after, cursor, bindings, stored, target_len),
        ensures advance_requires(after, cursor, bindings, stored), runtime_wf(after),
            runtime_frame(before, after), cursor_cache_unchanged(before, after),
            after.spec_store() == before.spec_store(), cursor_consumed(cursor) <= target_len,
            after.spec_snapshots() == before.spec_snapshots().insert(
                (stored.id(), stored.revision()), stored@.events),
            snapshot_compatible(after.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
    {
        history_store::history::lemma_stored_history_view(stored);
        reveal(resume_ensures);
        reveal(advance_requires);
        reveal(snapshot_compatible);
        reveal(runtime_frame);
        reveal(cursor_cache_unchanged);
        reveal(cursor_consumed);
    }

    pub proof fn lemma_advance_result_facts(
        before: RuleRuntime, after: RuleRuntime, start: BatchCursor, cursor: BatchCursor,
        bindings: Bindings, stored: StoredHistory,
        target_len: usize, batch_size: usize, result: Result<Option<bool>, HistoryError>,
    )
        requires advance_ensures(before, after, start, cursor, bindings, stored,
            target_len, batch_size, result),
        ensures runtime_wf(after), runtime_frame(before, after),
            result != Err(HistoryError::WrongHistoryOwner),
            batch_size > 0 && cursor_consumed(start) <= target_len && target_len <= stored@.events.len()
                ==> language::no_invariant_failure(result),
            batch_size > 0 && cursor_consumed(start) <= target_len && target_len <= stored@.events.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            after.spec_store() == before.spec_store(),
            after.spec_snapshots() == before.spec_snapshots().insert(
                (stored.id(), stored.revision()), stored@.events),
            snapshot_compatible(after.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
            advance_requires(after, cursor, bindings, stored),
            result is Err ==> cursor_consumed(cursor) == cursor_consumed(start)
                && cursor_cache_unchanged(before, after),
            result matches Ok(None) ==> cursor_consumed(cursor) < target_len,
            result matches Ok(Some(answer)) ==> cursor_consumed(cursor) == target_len
                && answer == runtime_accepts(before, bindings@, stored@.events.take(target_len as int)),
    {
        history_store::history::lemma_stored_history_view(stored);
        reveal(advance_ensures);
        reveal(runtime_frame);
        reveal(cursor_cache_unchanged);
        reveal(cursor_consumed);
        reveal(advance_requires);
        reveal(snapshot_compatible);
        reveal(runtime_accepts);
    }

    pub open(crate) spec fn root_cursor_matches(runtime: RuleRuntime, cursor: BatchCursor) -> bool {
        cursor.consumed == 0 && cursor.residual == runtime.pair.root
    }

    pub open(crate) spec fn cursor_consumed(cursor: BatchCursor) -> nat {
        cursor.consumed as nat
    }

    /// Numeric event snapshots keyed by immutable history identity and revision.
    pub type HistorySnapshots = Map<(usize, u64), Seq<language::EventView>>;

    /// Reobserving a revision may extend, but cannot replace, its retained prefix.
    pub closed spec fn snapshot_compatible(
        snapshots: HistorySnapshots, history: usize, revision: u64, events: Seq<language::EventView>,
    ) -> bool {
        !snapshots.contains_key((history, revision))
            || snapshots[(history, revision)].is_prefix_of(events)
    }

    pub proof fn lemma_snapshot_compatible_intro(
        snapshots: HistorySnapshots, history: usize, revision: u64, events: Seq<language::EventView>,
    )
        requires !snapshots.contains_key((history, revision))
            || snapshots[(history, revision)].is_prefix_of(events),
        ensures snapshot_compatible(snapshots, history, revision, events),
    {
        reveal(snapshot_compatible);
    }

    pub proof fn lemma_snapshot_compatible_elim(
        snapshots: HistorySnapshots, history: usize, revision: u64, events: Seq<language::EventView>,
    )
        requires snapshot_compatible(snapshots, history, revision, events),
        ensures !snapshots.contains_key((history, revision))
            || snapshots[(history, revision)].is_prefix_of(events),
    {
        reveal(snapshot_compatible);
    }

    /// Actual lifecycle receipts justify reuse even when other writers intervene.
    pub proof fn lemma_snapshot_compatible_lifecycle(
        snapshots: HistorySnapshots, stored: StoredHistory,
        tracked snapshot: &raw::Snapshot, tracked lifecycle: &raw::Lifecycle,
    )
        requires lifecycle.wf(), lifecycle.state() == stored@, snapshot.id() == lifecycle.id(),
            snapshots.contains_key((stored.id(), stored.revision())) ==>
                snapshot.value().revision == stored@.revision
                    && snapshot.value().events == snapshots[(stored.id(), stored.revision())],
        ensures snapshot_compatible(snapshots, stored.id(), stored.revision(), stored@.events),
    {
        history_store::history::lemma_stored_history_view(stored);
        if snapshots.contains_key((stored.id(), stored.revision())) {
            lifecycle.validate(snapshot);
        }
        lemma_snapshot_compatible_intro(snapshots, stored.id(), stored.revision(), stored@.events);
    }

    pub(crate) open spec fn cursor_matches_snapshot(
        pair: CompiledPair, cursor: HistoryCursor, snapshots: HistorySnapshots,
    ) -> bool {
        language::event_wf(cursor.bindings@, cursor.bindings@.len())
            && snapshots.contains_key((cursor.history, cursor.revision))
            && progress::residual_after_prefix(pair, snapshots[(cursor.history, cursor.revision)],
                cursor.bindings@, cursor.consumed as nat, cursor.residual)
    }

    pub(crate) open spec fn batch_matches_snapshot(
        pair: CompiledPair, cursor: BatchCursor, history: usize, revision: u64,
        bindings: Bindings, snapshots: HistorySnapshots,
    ) -> bool {
        language::event_wf(bindings@, bindings@.len())
            && ((cursor.consumed == 0 && cursor.residual == pair.root)
                || (snapshots.contains_key((history, revision))
                    && progress::residual_after_prefix(pair, snapshots[(history, revision)],
                        bindings@, cursor.consumed as nat, cursor.residual)))
    }

    pub(crate) open spec fn cursor_cache_wf(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
    ) -> bool {
        crate::progress::verify::pair_wf(pair)
            && cursors.len() <= HISTORY_CACHE_CAPACITY
            && (forall|i: int| 0 <= i < cursors.len() ==> cursor_matches_snapshot(pair, cursors[i], snapshots))
            && (forall|i: int, j: int| 0 <= i < j < cursors.len()
                ==> !cursor_key_eq(cursors[i], cursors[j]))
    }


    pub(super) proof fn lemma_cursor_remove(
        pair: crate::progress::CompiledPair,
        cursors: Seq<HistoryCursor>, index: int, cursor: HistoryCursor, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(pair, cursors, snapshots), 0 <= index < cursors.len(),
            cursor_key_eq(cursors[index], cursor),
        ensures cursor_cache_wf(pair, cursors.remove(index), snapshots),
            cursors.remove(index).len() < HISTORY_CACHE_CAPACITY,
            forall|i: int| 0 <= i < cursors.remove(index).len()
                ==> !cursor_key_eq(cursors.remove(index)[i], cursor)
                    && cursors.contains(cursors.remove(index)[i]),
    {
        cursors.remove_ensures(index);
        let kept = cursors.remove(index);
        assert forall|i: int| 0 <= i < kept.len() implies cursor_matches_snapshot(pair, kept[i], snapshots)
            && !cursor_key_eq(kept[i], cursor) && cursors.contains(kept[i]) by {
            let original = if i < index { i } else { i + 1 };
            assert(0 <= original < cursors.len());
            assert(kept[i] == cursors[original]);
            assert(original != index);
            assert(cursor_matches_snapshot(pair, cursors[original], snapshots));
            if original < index {
                assert(!cursor_key_eq(cursors[original], cursors[index]));
            } else {
                assert(!cursor_key_eq(cursors[index], cursors[original]));
            }
            assert(!cursor_key_eq(cursors[original], cursor));
            assert(cursors.contains(cursors[original]));
        }
        assert forall|i: int, j: int| 0 <= i < j < kept.len()
            implies !cursor_key_eq(kept[i], kept[j]) by {
            let left = if i < index { i } else { i + 1 };
            let right = if j < index { j } else { j + 1 };
            assert(0 <= left < right < cursors.len());
            assert(left < right);
            assert(kept[i] == cursors[left]);
            assert(kept[j] == cursors[right]);
        }
    }

    pub(super) proof fn lemma_cursor_drop_last(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(pair, cursors, snapshots), cursors.len() > 0,
        ensures cursor_cache_wf(pair, cursors.drop_last(), snapshots),
            forall|i: int| 0 <= i < cursors.drop_last().len()
                ==> cursors.drop_last()[i] == cursors[i] && cursors.contains(cursors.drop_last()[i]),
    {
        assert forall|i: int| 0 <= i < cursors.drop_last().len()
            implies cursors.drop_last()[i] == cursors[i] && cursors.contains(cursors.drop_last()[i]) by {}
        assert forall|i: int, j: int| 0 <= i < j < cursors.drop_last().len()
            implies !cursor_key_eq(cursors.drop_last()[i], cursors.drop_last()[j]) by {
            assert(cursors.drop_last()[i] == cursors[i]);
            assert(cursors.drop_last()[j] == cursors[j]);
        }
    }

    pub(super) proof fn lemma_cursor_prepend(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, cursor: HistoryCursor, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(pair, cursors, snapshots), cursors.len() < HISTORY_CACHE_CAPACITY,
            cursor_matches_snapshot(pair, cursor, snapshots),
            forall|i: int| 0 <= i < cursors.len() ==> !cursor_key_eq(cursors[i], cursor),
        ensures cursor_cache_wf(pair, seq![cursor] + cursors, snapshots),
    {
        let after = seq![cursor] + cursors;
        assert forall|i: int| 0 <= i < after.len() implies cursor_matches_snapshot(pair, after[i], snapshots) by {
            if i == 0 { assert(after[i] == cursor); }
            else { assert(after[i] == cursors[i - 1]); }
        }
        assert forall|i: int, j: int| 0 <= i < j < after.len()
            implies !cursor_key_eq(after[i], after[j]) by {
            assert(after[j] == cursors[j - 1]);
            if i == 0 { assert(after[i] == cursor); }
            else { assert(after[i] == cursors[i - 1]); }
        }
    }

    pub(crate) proof fn lemma_cursor_cache_frame(
        before: CompiledPair, after: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(before, cursors, snapshots), progress::pair_wf(after),
            progress::pair_frame(before, after),
        ensures cursor_cache_wf(after, cursors, snapshots),
    {
        assert forall|i: int| 0 <= i < cursors.len()
            implies cursor_matches_snapshot(after, cursors[i], snapshots) by {
            let cursor = cursors[i];
            progress::lemma_residual_after_prefix_frame(before, after,
                snapshots[(cursor.history, cursor.revision)], cursor.bindings@,
                cursor.consumed as nat, cursor.residual);
        }
    }

    pub(crate) proof fn lemma_cursor_cache_observe(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
        history: usize, revision: u64, events: Seq<language::EventView>,
    )
        requires cursor_cache_wf(pair, cursors, snapshots),
            snapshot_compatible(snapshots, history, revision, events),
        ensures cursor_cache_wf(pair, cursors, snapshots.insert((history, revision), events)),
    {
        let updated = snapshots.insert((history, revision), events);
        assert forall|i: int| 0 <= i < cursors.len()
            implies cursor_matches_snapshot(pair, cursors[i], updated) by {
            let cursor = cursors[i];
            if (cursor.history, cursor.revision) == (history, revision) {
                progress::lemma_residual_after_prefix_history_extends(pair,
                    snapshots[(history, revision)], events, cursor.bindings@,
                    cursor.consumed as nat, cursor.residual);
            }
        }
    }
}
}

#[verus_verify]
pub struct RuleRuntime {
    pub(crate) pair: crate::progress::CompiledPair,
    pub(crate) cursors: CursorCache,
    pub(crate) store: Arc<HistoryStore>,
    #[cfg(verus_keep_ghost)]
    pub(crate) snapshots: Ghost<verify::HistorySnapshots>,
}

impl core::fmt::Debug for RuleRuntime {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RuleRuntime")
            .field("pair", &self.pair)
            .field("cursors", &self.cursors)
            .finish()
    }
}

#[verus_verify]
impl RuleRuntime {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub open(crate) spec fn spec_store(&self) -> Arc<HistoryStore> { self.store }

        /// Read-only observations used to establish compatibility before evaluation.
        pub open(crate) spec fn spec_snapshots(&self) -> verify::HistorySnapshots { self.snapshots@ }
    }

    /// The numeric store whose records name this runtime's cursor keys.
    #[verus_spec(result => ensures *result == self.spec_store())]
    pub fn store(&self) -> &Arc<HistoryStore> {
        &self.store
    }

    /// Start a replacement graph generation without exposing or fabricating graph IDs.
    #[verus_spec(result => ensures root_cursor_matches(*self, result))]
    pub fn root_cursor(&self) -> BatchCursor {
        proof! { reveal(root_cursor_matches); }
        BatchCursor {
            consumed: 0,
            residual: self.pair.root,
        }
    }

    #[verus_spec(result => ensures constructor_result(result, *store, *template),
        result != Err(HistoryError::WrongHistoryOwner),
        junco_core::flat::verify::structural_wf(*template) ==> language::no_invariant_failure(result)
            && !(result matches Err(HistoryError::InvalidPolicy { .. }))
            && (result matches Err(error) ==> resource_error(error))) ]
    pub fn new<L: Limits>(
        store: &Arc<HistoryStore>,
        template: &junco_core::flat::FlatPair<u64>,
        precompile: bool,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, HistoryError> {
        proof! { reveal(constructor_result); reveal(runtime_wf); }
        #[cfg_attr(not(feature = "cache"), allow(unused_mut))]
        let mut pair =
            CompiledPair::compile(template, junco_core::limits::MAX_GRAPH_BYTES, limits, world)?;
        #[cfg(feature = "cache")]
        if precompile {
            proof_decl! { let ghost compiled = pair; }
            if let Err(error) = pair.precompile(limits, world) {
                if !matches!(
                    error,
                    HistoryError::GraphBudget { .. } | HistoryError::GraphIndex
                ) {
                    return Err(error);
                }
                drop(pair);
                pair = CompiledPair::compile(
                    template,
                    junco_core::limits::MAX_GRAPH_BYTES,
                    limits,
                    world,
                )?;
            }
            proof! {
                if progress::pair_frame(compiled, pair) {
                    model::lemma_graph_wf_elim(compiled.store.graph());
                    model::lemma_lift_regex_stable(compiled.store.graph(), pair.store.graph(), compiled.root@);
                }
            }
        }
        #[cfg(not(feature = "cache"))]
        let _ = precompile;
        let cursors = CursorCache::new(limits, world)?;
        // The expression macro also supplies the ghost field during Verus's erased Rust check.
        let runtime = Self {
            pair,
            cursors,
            store: Arc::clone(store),
            #[cfg(verus_keep_ghost)]
            snapshots: verus_exec_expr! { Ghost(Map::empty()) },
        };
        Ok(runtime)
    }

    /// Bind the candidate and commit one complete-prefix answer/publication transaction.
    #[verus_verify]
    #[verus_spec(result =>
        requires decision::runtime_represents(*template, *old(self)),
            junco_core::flat::verify::structural_wf(*template),
            snapshot_compatible(old(self).snapshots@, stored.id(), stored.revision(),
                history_store::store::verify::events_view(raw::stored_events(&stored))),
        ensures decision::runtime_represents(*template, *final(self)),
            runtime_wf(*final(self)),
            progress::pair_frame(old(self).pair, final(self).pair),
            final(self).spec_store() == old(self).spec_store(),
            result != Err(HistoryError::WrongHistoryOwner),
            language::no_invariant_failure(result),
            result matches Err(error) ==> resource_error(error),
            result is Err ==> final(self).cursors@ == old(self).cursors@,
            final(self).snapshots@ == old(self).snapshots@
                || final(self).snapshots@ == old(self).snapshots@.insert((stored.id(), stored.revision()),
                    history_store::store::verify::events_view(raw::stored_events(&stored))),
            result != Ok(None) ==> final(self).snapshots@ == old(self).snapshots@.insert(
                (stored.id(), stored.revision()),
                history_store::store::verify::events_view(raw::stored_events(&stored))),
            numeric_result(*template, *request, *stored, result),
            result matches Ok(Some(answer)) ==> exists|bindings: Bindings|
                crate::compile::verify::bindings_match(*template, *request, bindings)
                    && language::event_wf(bindings@, bindings@.len())
                    && answer == model::regex_lang(old(self).pair.store.graph(), bindings@,
                        old(self).pair.root@,
                        history_store::store::verify::events_view(raw::stored_events(&stored))),
    )]
    pub(crate) fn accepts<L: Limits>(
        &mut self,
        template: &FlatPair<u64>,
        request: &Event,
        stored: &StoredHistory,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<bool>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        let bindings = match Self::bindings(template, request) {
            Some(bindings) => bindings,
            None => return Ok(None),
        };
        proof! {
            crate::compile::verify::lemma_bindings_match(*template, *request, bindings);
            history_store::history::lemma_stored_history_view(*stored);
            reveal(runtime_wf);
            reveal(resume_requires);
            reveal(resume_ensures);
            reveal(advance_requires);
            reveal(advance_ensures);
        }
        proof_decl! { let ghost initial_snapshots = self.snapshots@; }
        let target = stored.len();
        let mut cursor = self.resume_cursor(&bindings, stored, target);
        proof! {
            lemma_resume_can_advance(entry, *self, cursor, bindings, *stored, target);
            assert(self.snapshots@ == initial_snapshots.insert((stored.id(), stored.revision()),
                history_store::store::verify::events_view(raw::stored_events(&stored))));
        }
        proof_decl! { let ghost start = cursor; }
        let result = self.advance_cursor(
            &mut cursor,
            &bindings,
            stored,
            target,
            usize::MAX,
            limits,
            world,
        );
        proof! {
            let key = (stored.id(), stored.revision());
            let events = history_store::store::verify::events_view(raw::stored_events(&stored));
            assert(self.snapshots@ == initial_snapshots.insert(key, events).insert(key, events));
            assert(initial_snapshots.insert(key, events).insert(key, events) =~= initial_snapshots.insert(key, events));
            language::lemma_selected_end(start.consumed as nat, target as nat, usize::MAX as nat);
            assert(history_store::store::verify::events_view(raw::stored_events(&stored)).take(target as int)
                =~= history_store::store::verify::events_view(raw::stored_events(&stored)));
            decision::lemma_runtime_frame(*template, entry, *self);
        }
        match result {
            Err(error) => Err(error),
            Ok(Some(answer)) => {
                proof! {
                    assert(exists|witness: Bindings|
                        crate::compile::verify::bindings_match(*template, *request, witness)
                            && language::event_wf(witness@, witness@.len())
                            && answer == crate::compile::verify::source_regex(*template,
                                template.root as nat, witness@,
                                history_store::store::verify::events_view(raw::stored_events(&stored)))) by {
                        assert(crate::compile::verify::bindings_match(*template, *request, bindings));
                    }
                    assert(exists|witness: Bindings|
                        crate::compile::verify::bindings_match(*template, *request, witness)
                            && language::event_wf(witness@, witness@.len())
                            && answer == model::regex_lang(entry.pair.store.graph(), witness@,
                                entry.pair.root@,
                                history_store::store::verify::events_view(raw::stored_events(&stored)))) by {
                        assert(crate::compile::verify::bindings_match(*template, *request, bindings));
                    }
                }
                Ok(Some(answer))
            }
            Ok(None) => {
                proof! { assert(false); }
                Err(HistoryError::invariant(
                    "complete history batch returned no answer",
                ))
            }
        }
    }

    /// Public so hosts can drive bounded batches (Regorus HistoryStep).
    #[expect(
        clippy::collapsible_if,
        reason = "Pinned Verus does not support let-chain expressions"
    )]
    #[verus_spec(result =>
        requires resume_requires(*old(self), *bindings, *stored, target_len),
        ensures resume_ensures(*old(self), *final(self), result, *bindings, *stored, target_len),
    )]
    pub fn resume_cursor(
        &mut self,
        bindings: &Bindings,
        stored: &StoredHistory,
        target_len: usize,
    ) -> BatchCursor {
        proof! { reveal(resume_requires); reveal(resume_ensures); reveal(runtime_wf); }
        let history = stored.id();
        proof_decl! { let ghost entry = *self; }
        proof! {
            lemma_cursor_cache_observe(self.pair, self.cursors@, self.snapshots@,
                history, stored.revision(), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)));
            *self.snapshots = self.snapshots@.insert((history, stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)));
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.cursors@.len(),
                entry == *old(self), history == stored.id(),
                self.pair == entry.pair, self.cursors@ == entry.cursors@, self.store == entry.store,
                self.snapshots@ == entry.snapshots@.insert((history, stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored))),
                cursor_cache_wf(self.pair, self.cursors@, self.snapshots@),
                self.snapshots@.contains_key((history, stored.revision())),
                self.snapshots@[(history, stored.revision())] == history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)),
            decreases self.cursors@.len() - index,
        ))]
        while index < self.cursors.entries().len() {
            if let Some(cursor) = self.cursors.entries().get(index) {
                if cursor.history == history
                    && cursor.bindings == *bindings
                    && cursor.revision == stored.revision()
                    && cursor.consumed <= target_len
                {
                    proof! {
                        assert(cursor_matches_snapshot(self.pair, *cursor, self.snapshots@));
                        assert(cursor.bindings@ == bindings@);
                        assert(progress::residual_after_prefix(self.pair, history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)),
                            bindings@, cursor.consumed as nat, cursor.residual));
                    }
                    return BatchCursor {
                        consumed: cursor.consumed,
                        residual: cursor.residual,
                    };
                }
            }
            index = index.saturating_add(1);
        }
        proof! {
            assert(history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)).take(0) =~= Seq::<language::EventView>::empty());
            assert forall|word: Seq<language::EventView>| model::regex_lang(self.pair.store.graph(), bindings@, self.pair.root@, word)
                == model::regex_lang(self.pair.store.graph(), bindings@, self.pair.root@,
                    history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)).take(0) + word) by {
                assert(Seq::<language::EventView>::empty() + word =~= word);
            }
        }
        BatchCursor {
            consumed: 0,
            residual: self.pair.root,
        }
    }

    /// Public so hosts can drive bounded batches (Regorus HistoryStep).
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep the locked history transaction inputs explicit."
    )]
    #[verus_spec(result =>
        requires advance_requires(*old(self), *old(cursor), *bindings, *stored),
        ensures advance_ensures(*old(self), *final(self), *old(cursor), *final(cursor),
            *bindings, *stored, target_len, batch_size, result),
            result != Err(HistoryError::WrongHistoryOwner),
    )]
    pub fn advance_cursor<L: Limits>(
        &mut self,
        cursor: &mut BatchCursor,
        bindings: &Bindings,
        stored: &StoredHistory,
        target_len: usize,
        batch_size: usize,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<bool>, HistoryError> {
        proof! { reveal(advance_requires); reveal(advance_ensures); reveal(runtime_wf); }
        let history = stored.id();
        proof_decl! { let ghost entry = self.pair; let ghost entry_cursors = self.cursors@; let ghost start = *cursor; }
        proof! {
            let events = history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored));
            lemma_snapshot_compatible_elim(self.snapshots@, history, stored.revision(), events);
            if cursor.consumed == 0 && cursor.residual == self.pair.root {
                assert(events.take(0) =~= Seq::<language::EventView>::empty());
                assert forall|word: Seq<language::EventView>| model::regex_lang(self.pair.store.graph(), bindings@, cursor.residual@, word)
                    == model::regex_lang(self.pair.store.graph(), bindings@, self.pair.root@, events.take(0) + word) by {
                    assert(events.take(0) + word =~= word);
                }
            } else {
                progress::lemma_residual_after_prefix_history_extends(self.pair,
                    self.snapshots@[(history, stored.revision())], events, bindings@, cursor.consumed as nat, cursor.residual);
            }
            lemma_cursor_cache_observe(self.pair, self.cursors@, self.snapshots@, history, stored.revision(), events);
            *self.snapshots = self.snapshots@.insert((history, stored.revision()), events);
        }
        let result = cursor.advance(
            &mut self.pair,
            stored.as_slice(),
            bindings,
            target_len,
            batch_size,
            limits,
            world,
        );
        proof! {
            lemma_cursor_cache_frame(entry, self.pair, entry_cursors, self.snapshots@);
            if result is Err {
                progress::lemma_residual_after_prefix_frame(entry, self.pair, history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)),
                    bindings@, start.consumed as nat, start.residual);
            }
        }
        match result {
            Err(error) => Err(error),
            Ok(answer) => {
                let published = HistoryCursor {
                    history,
                    bindings: *bindings,
                    revision: stored.revision(),
                    consumed: cursor.consumed,
                    residual: cursor.residual,
                };
                proof! { assert(cursor_matches_snapshot(self.pair, published, self.snapshots@)); }
                self.publish(published);
                Ok(answer)
            }
        }
    }

    /// Called only after all fallible batch work, while its history is read-locked.
    #[verus_verify]
    #[verus_spec(
        requires cursor_cache_wf(old(self).pair, old(self).cursors@, old(self).snapshots@),
            cursor_matches_snapshot(old(self).pair, cursor, old(self).snapshots@),
        ensures
        final(self).pair == old(self).pair, final(self).store == old(self).store,
        final(self).snapshots@ == old(self).snapshots@,
        cursor_cache_wf(final(self).pair, final(self).cursors@, final(self).snapshots@),
        longer_cached_prefix(old(self).cursors@, cursor) ==> final(self).cursors@ == old(self).cursors@,
        !longer_cached_prefix(old(self).cursors@, cursor) ==> final(self).cursors@.len() > 0
            && final(self).cursors@[0] == cursor,
        forall|i: int| 0 <= i < final(self).cursors@.len()
            ==> final(self).cursors@[i] == cursor || old(self).cursors@.contains(final(self).cursors@[i]),
    )]
    pub(crate) fn publish(&mut self, cursor: HistoryCursor) {
        proof_decl! { let ghost entry = self.cursors@; }
        self.cursors.publish(cursor);
        proof! {
            assert forall|i: int| 0 <= i < self.cursors@.len()
                implies cursor_matches_snapshot(self.pair, self.cursors@[i], self.snapshots@) by {
                if self.cursors@[i] != cursor {
                    assert(entry.contains(self.cursors@[i]));
                    let original = choose|j: int| 0 <= j < entry.len() && entry[j] == self.cursors@[i];
                    assert(cursor_matches_snapshot(self.pair, entry[original], self.snapshots@));
                }
            }
        }
    }
}

#[cfg(any(test, feature = "test-util"))]
impl RuleRuntime {
    /// Read the existing engine counters without exposing mutable graph state.
    pub fn work_counters(&self) -> &WorkCounters {
        &self.pair.work
    }

    pub fn reset_work_events(&mut self) {
        self.pair.reset_work_events();
    }

    pub fn work_events(&self) -> usize {
        self.pair.work_events()
    }

    /// Return keys and committed positions, never graph-local residual IDs.
    pub fn cursor_positions(&self) -> Vec<(usize, Bindings, u64, usize)> {
        self.cursors
            .entries()
            .iter()
            .map(|cursor| {
                (
                    cursor.history,
                    cursor.bindings,
                    cursor.revision,
                    cursor.consumed,
                )
            })
            .collect()
    }

    /// Exchange only byte pressure so replacement tests can restore an old generation.
    pub fn replace_graph_byte_pressure(&mut self, bytes: usize) -> usize {
        self.pair.store.replace_graph_byte_pressure(bytes)
    }

    pub fn set_answer_checkpoint_failure(&mut self, fail: bool) {
        self.pair.set_answer_checkpoint_failure(fail);
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub struct BatchCursor {
    pub(crate) consumed: usize,
    pub(crate) residual: RegexId,
}

impl BatchCursor {
    /// Return the committed prefix length.
    #[verus_verify]
    #[verus_spec(result => ensures result == cursor_consumed(*self))]
    pub const fn consumed(&self) -> usize {
        proof! { reveal(cursor_consumed); }
        self.consumed
    }

    /// The same executable transaction is used under the runtime/history locks.
    /// No cursor changes until fold, final answer, and publication checks all succeed.
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep explicit transaction inputs aligned with its verified contract."
    )]
    #[verus_verify]
    #[verus_spec(result =>
        requires
            crate::progress::verify::pair_wf(*old(pair)),
            crate::progress::verify::residual_after_prefix(
                *old(pair), history_store::store::verify::events_view(events@), bindings@,
                old(self).consumed as nat, old(self).residual),
        ensures
            crate::progress::verify::pair_wf(*final(pair)),
            crate::progress::verify::pair_frame(*old(pair), *final(pair)),
            result != Err(HistoryError::WrongHistoryOwner),
            batch_size > 0 && old(self).consumed <= target_len && target_len <= events@.len()
                ==> language::no_invariant_failure(result),
            batch_size > 0 && old(self).consumed <= target_len && target_len <= events@.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result is Err ==> final(self).consumed == old(self).consumed
                && final(self).residual == old(self).residual,
            result is Ok ==> old(self).consumed <= final(self).consumed
                && final(self).consumed <= target_len
                && final(self).consumed == junco_core::verify::history_specs::selected_end(old(self).consumed as nat, target_len as nat, batch_size as nat),
            result matches Ok(Some(_)) ==> final(self).consumed == target_len,
            result matches Ok(None) ==> final(self).consumed < target_len,
            result is Ok ==> crate::progress::verify::residual_folds(
                *final(pair), bindings@, old(self).residual,
                history_store::store::verify::events_view(events@).subrange(old(self).consumed as int, final(self).consumed as int),
                final(self).residual),
            result matches Ok(Some(answer)) ==> answer == junco_core::kernel::verify::regex_lang(
                (*final(pair)).store.graph(), bindings@,
                old(self).residual@, history_store::store::verify::events_view(events@).subrange(old(self).consumed as int, target_len as int)),
            result is Ok ==> crate::progress::verify::residual_after_prefix(
                *final(pair), history_store::store::verify::events_view(events@), bindings@,
                final(self).consumed as nat, final(self).residual),
            result matches Ok(Some(answer)) ==> answer == junco_core::kernel::verify::regex_lang(
                (*old(pair)).store.graph(), bindings@,
                old(pair).root@, history_store::store::verify::events_view(events@).take(target_len as int)),
    )]
    pub(crate) fn advance<L: Limits>(
        &mut self,
        pair: &mut CompiledPair,
        events: &[Event],
        bindings: &Bindings,
        target_len: usize,
        batch_size: usize,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> KernelResult<Option<bool>> {
        proof_decl! { let ghost entry = *pair; let ghost entry_cursor = *self; }
        if batch_size == 0 || self.consumed > target_len || target_len > events.len() {
            return Err(HistoryError::invariant("invalid history batch bounds"));
        }
        let remaining = target_len
            .checked_sub(self.consumed)
            .ok_or(HistoryError::invariant("invalid history remaining length"))?;
        let count = if batch_size < remaining {
            batch_size
        } else {
            remaining
        };
        let end = self
            .consumed
            .checked_add(count)
            .ok_or(HistoryError::invariant("invalid history batch end"))?;
        proof! {
            language::lemma_selected_end(self.consumed as nat, target_len as nat, batch_size as nat);
            assert(end == language::selected_end(self.consumed as nat, target_len as nat, batch_size as nat));
        }
        let suffix = events
            .get(self.consumed..end)
            .ok_or(HistoryError::invariant("invalid history batch slice"))?;
        proof! {
            assert(history_store::store::verify::events_view(suffix@) =~= history_store::store::verify::events_view(events@).subrange(self.consumed as int, end as int));
        }
        let residual = pair.fold(self.residual, suffix, bindings, limits, world)?;
        let answer = if end == target_len {
            let answer = pair.answer(residual, limits, world)?;
            proof! {
                language::lemma_nullable_iff_nil(model::gsem(bindings@), model::lift_regex((*pair).store.graph(), residual@));
                assert(history_store::store::verify::events_view(suffix@) + Seq::<language::EventView>::empty() =~= history_store::store::verify::events_view(suffix@));
                assert(model::regex_lang((*pair).store.graph(), bindings@, residual@, Seq::empty())
                    == model::regex_lang((*pair).store.graph(), bindings@, entry_cursor.residual@, history_store::store::verify::events_view(suffix@)));
            }
            Some(answer)
        } else {
            None
        };
        limits.publication_checkpoint()?;
        proof! {
            model::lemma_graph_wf_elim(entry.store.graph());
            model::lemma_lift_regex_stable(entry.store.graph(), (*pair).store.graph(), entry.root@);
            history_algebra::lemma_batch_extends_pinned_prefix(
                entry.store.graph(), (*pair).store.graph(), bindings@,
                entry.root@, entry_cursor.residual@, residual@, history_store::store::verify::events_view(events@),
                entry_cursor.consumed as nat, end as nat,
            );
        }
        // Commit the cursor last so every fallible operation leaves it unchanged.
        self.consumed = end;
        self.residual = residual;
        Ok(answer)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::indexing_slicing)]

    use super::*;
    use alloc::vec;
    use history_syntax::syntax::Component;
    use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
    use junco_core::limits::Unmetered;

    fn runtime(regex: FlatRegex) -> RuleRuntime {
        let store = HistoryStore::new(3);
        let runtime = RuleRuntime::new(
            &store,
            &FlatPair {
                head: vec![FlatHead::Any, FlatHead::Any, FlatHead::Any],
                tests: Vec::new(),
                regexes: vec![regex],
                root: 0,
            },
            false,
            &mut Unmetered,
            &mut ObservationWorld,
        )
        .unwrap();
        assert!(Arc::ptr_eq(runtime.store(), &store));
        runtime
    }

    fn event(store: &HistoryStore) -> Event {
        let principal = store
            .intern(
                Component(0),
                b"alice",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let action = store
            .intern(Component(1), b"edit", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let resource = store
            .intern(Component(2), b"doc", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store.event(&[principal, action, resource]).unwrap()
    }

    #[test]
    fn compiled_pair_uses_send_dependencies() {
        fn assert_send<T: Send>() {}
        assert_send::<CompiledPair>();
        assert_send::<RuleRuntime>();
    }

    #[test]
    fn batch_cursor_ends_and_retained_prefix_are_exact() {
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(
                &history,
                &[event(&store); 7],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let mut runtime = runtime(FlatRegex::All);
        let bindings = Bindings::new(&[0; 3]);
        let mut cursor = runtime.root_cursor();
        for expected in [3, 6, 7] {
            let answer = runtime
                .advance_cursor(
                    &mut cursor,
                    &bindings,
                    &stored,
                    7,
                    3,
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
            assert_eq!(answer, if expected == 7 { Some(true) } else { None });
            assert_eq!(cursor.consumed(), expected);
            assert_eq!(runtime.cursors.entries()[0].consumed, expected);
        }
        let latest = runtime.cursors.entries()[0];
        runtime.publish(HistoryCursor {
            consumed: 1,
            residual: runtime.pair.root,
            ..latest
        });
        assert_eq!(runtime.cursors.entries()[0].consumed, 7);
        assert_eq!(runtime.cursors.entries()[0].residual, latest.residual);
        let warm = runtime.resume_cursor(&bindings, &stored, 7);
        assert_eq!(warm.consumed(), 7);
    }

    #[test]
    fn failed_batch_and_final_answer_never_publish() {
        let mut empty = runtime(FlatRegex::Epsilon);
        let mut cursor = empty.root_cursor();
        let before = cursor;
        let error = cursor
            .advance(
                &mut empty.pair,
                &[],
                &Bindings::new(&[0; 3]),
                1,
                3,
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap_err();
        assert!(matches!(error, HistoryError::Invariant { .. }));
        assert_eq!(cursor.consumed, before.consumed);
        assert_eq!(cursor.residual, before.residual);
        assert!(empty.cursors.entries().is_empty());

        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(
                &history,
                &[event(&store); 2],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let bindings = Bindings::new(&[0; 3]);
        let mut runtime = runtime(FlatRegex::All);
        let mut cursor = runtime.root_cursor();
        assert_eq!(
            runtime
                .advance_cursor(
                    &mut cursor,
                    &bindings,
                    &stored,
                    2,
                    1,
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap(),
            None
        );
        let entry = cursor;
        let retained = runtime.cursors.entries()[0];
        runtime.set_answer_checkpoint_failure(true);
        assert!(matches!(
            runtime.advance_cursor(
                &mut cursor,
                &bindings,
                &stored,
                2,
                1,
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(cursor.consumed, entry.consumed);
        assert_eq!(cursor.residual, entry.residual);
        assert_eq!(runtime.cursors.entries()[0].consumed, retained.consumed);
        assert_eq!(runtime.cursors.entries()[0].residual, retained.residual);
        runtime.set_answer_checkpoint_failure(false);
        assert_eq!(
            runtime
                .advance_cursor(
                    &mut cursor,
                    &bindings,
                    &stored,
                    2,
                    1,
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap(),
            Some(true)
        );
        assert_eq!(runtime.cursors.entries()[0].consumed, 2);
    }

    #[test]
    fn publication_failure_preserves_cursor_and_retained_prefix() {
        struct FailPublication;
        impl Limits for FailPublication {
            fn checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn enforce_memory(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn publication_checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Err(junco_core::limits::LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
            }
        }
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let mut runtime = runtime(FlatRegex::All);
        let mut cursor = runtime.root_cursor();
        let entry = cursor;
        assert!(matches!(
            runtime.advance_cursor(
                &mut cursor,
                &Bindings::new(&[0; 3]),
                &stored,
                0,
                1,
                &mut FailPublication,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(cursor.consumed, entry.consumed);
        assert_eq!(cursor.residual, entry.residual);
        assert!(runtime.cursors.entries().is_empty());
    }

    #[test]
    fn retained_cursor_lru_is_bounded_and_keeps_recent_histories() {
        let store = HistoryStore::new(3);
        let mut runtime = runtime(FlatRegex::All);
        let mut keys = Vec::new();
        for _ in 0..17 {
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            let record = store.history_record(&history).unwrap();
            let stored = record.read();
            assert_eq!(stored.id(), history.index());
            keys.push(history.index());
            let mut cursor = runtime.root_cursor();
            assert_eq!(
                runtime
                    .advance_cursor(
                        &mut cursor,
                        &Bindings::new(&[0; 3]),
                        &stored,
                        0,
                        3,
                        &mut Unmetered,
                        &mut ObservationWorld
                    )
                    .unwrap(),
                Some(true)
            );
        }
        assert_eq!(runtime.cursors.entries().len(), 16);
        assert_eq!(runtime.cursors.entries()[0].history, keys[16]);
        assert_eq!(runtime.cursors.entries()[15].history, keys[1]);
        assert!(
            runtime
                .cursors
                .entries()
                .iter()
                .all(|cursor| cursor.bindings == Bindings::new(&[0; 3]))
        );
    }

    #[test]
    fn equal_shape_records_never_share_residuals() {
        let store = HistoryStore::new(3);
        let event = |action: &str| {
            let principal = store
                .intern(
                    Component(0),
                    b"alice",
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
            let action = store
                .intern(
                    Component(1),
                    action.as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
            let resource = store
                .intern(Component(2), b"doc", &mut Unmetered, &mut ObservationWorld)
                .unwrap();
            store.event(&[principal, action, resource]).unwrap()
        };
        let read = event("read");
        let mut runtime = RuleRuntime::new(
            &store,
            &FlatPair {
                head: vec![FlatHead::Any, FlatHead::Any, FlatHead::Any],
                tests: vec![FlatTest::Atom {
                    field: Component(1),
                    term: FlatTerm::Constant(read.component(1)),
                    positive: true,
                }],
                regexes: vec![FlatRegex::Test(0), FlatRegex::Star(0)],
                root: 1,
            },
            false,
            &mut Unmetered,
            &mut ObservationWorld,
        )
        .unwrap();
        let mut histories = Vec::new();
        for (event, expected) in [(read, true), (event("edit"), false)] {
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            store
                .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
                .unwrap();
            histories.push((history, expected));
        }
        assert_ne!(histories[0].0.index(), histories[1].0.index());
        let bindings = Bindings::new(&[0; 3]);
        // Cold then warm, in both orders: same length, revision and bindings, distinct keys.
        for order in [[0, 1], [1, 0], [0, 1], [1, 0]] {
            for index in order {
                let (history, expected) = &histories[index];
                let record = store.history_record(history).unwrap();
                let stored = record.read();
                let mut cursor = runtime.resume_cursor(&bindings, &stored, 1);
                let answer = runtime
                    .advance_cursor(
                        &mut cursor,
                        &bindings,
                        &stored,
                        1,
                        1,
                        &mut Unmetered,
                        &mut ObservationWorld,
                    )
                    .unwrap();
                assert_eq!(answer, Some(*expected));
            }
        }
        assert_eq!(runtime.cursors.entries().len(), 2);
    }
}

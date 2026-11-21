// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Numeric and typed committed histories with failure-atomic mutation.
//! Typed owners retain erased process-key receipts alongside their local lifecycle registration;
//! mutation preserves identity evidence, while a fork retains its newly issued key receipt.
//! Arc sharing retains native referent identity separately from registry and encoding receipts.
//! Actual source checkpoints and retained owner receipts prove foreign rollback rejection.
//! Exact iterator conversion facts retain the original event sequence when the input supplies
//! the shared conversion law. Truncation is a no-op at or beyond length, otherwise consumes
//! one revision or fails unchanged at exhaustion; rollback checks owner, then length first.

#[cfg(verus_keep_ghost)]
use self::verify::*;
use crate::graph::allocation;
use crate::store::Event;
#[cfg(verus_keep_ghost)]
use crate::typed::verify as books;
use crate::typed::{Store, share_store};
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use history_syntax::Event as TypedEvent;
use junco_core::errors::HistoryError;
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

#[cfg(verus_keep_ghost)]
verus! {
impl View for StoredHistory {
    type V = junco_core::verify::history_specs::HistoryStateView;
    closed spec fn view(&self) -> junco_core::verify::history_specs::HistoryStateView {
        junco_core::verify::history_specs::HistoryStateView {
            events: crate::store::verify::events_view(self.events@),
            revision: self.revision as nat,
        }
    }
}

pub proof fn lemma_stored_history_view(stored: StoredHistory)
    ensures stored@ == (junco_core::verify::history_specs::HistoryStateView {
        events: crate::store::verify::events_view(verify::stored_events(&stored)),
        revision: stored.spec_revision() as nat,
    }),
{
    reveal(<StoredHistory as View>::view);
}
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub struct StoredHistory {
    pub(crate) events: Vec<Event>,
    pub(crate) revision: u64,
    pub(crate) id: usize,
}

#[verus_verify]
impl StoredHistory {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn spec_revision(&self) -> u64 { self.revision }
        pub closed spec fn spec_id(&self) -> usize { self.id }
    }

    #[verus_spec(result => ensures result@ == verify::stored_events(self),
        crate::store::verify::events_view(result@) == self@.events)]
    pub fn as_slice(&self) -> &[Event] {
        proof! { reveal(<StoredHistory as View>::view); }
        &self.events
    }

    /// Return the number of encoded events without exposing mutable storage.
    #[verus_spec(result => ensures result == self@.events.len())]
    pub fn len(&self) -> usize {
        proof! { reveal(<StoredHistory as View>::view); }
        self.events.len()
    }

    /// Return whether the encoded history is empty without exposing storage.
    #[verus_spec(result => ensures result == (self@.events.len() == 0))]
    pub fn is_empty(&self) -> bool {
        proof! { reveal(<StoredHistory as View>::view); }
        self.events.is_empty()
    }

    /// Return the revision invalidating decisions after a shortening transaction.
    #[cfg_attr(verus_keep_ghost, verifier::when_used_as_spec(spec_revision))]
    #[verus_spec(result => ensures result == self@.revision, result == self.spec_revision())]
    pub const fn revision(&self) -> u64 {
        proof! { reveal(<StoredHistory as View>::view); }
        self.revision
    }

    /// Return the immutable process-wide key that names this record in cursor caches.
    #[cfg_attr(verus_keep_ghost, verifier::when_used_as_spec(spec_id))]
    #[verus_spec(result => ensures result == self.spec_id())]
    pub const fn id(&self) -> usize {
        self.id
    }

    #[verus_spec(result => ensures result.events@ == Seq::<Event>::empty(), result.revision == 0,
        verify::stored_events(&result) == Seq::<Event>::empty(), result.spec_revision() == 0,
        result.id == id, result.spec_id() == id)]
    pub(crate) const fn new(id: usize) -> Self {
        Self {
            events: Vec::new(),
            revision: 0,
            id,
        }
    }

    #[verus_spec(result =>
        ensures verify::stored_append_result(*old(self), *final(self), events@, result),
            result != Err(HistoryError::WrongHistoryOwner),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
    )]
    pub(crate) fn append_events<L: Limits>(
        &mut self,
        events: &[Event],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        proof! {
            reveal(<StoredHistory as View>::view);
            reveal(StoredHistory::spec_id);
            reveal(StoredHistory::spec_revision);
        }
        proof_decl! { let ghost entry_events = self.events@; }
        proof_decl! { let ghost entry = *self; }
        let previous = self.events.len();
        allocation(world.try_reserve_vec(&mut self.events, events.len()))?;
        limits.enforce_memory()?;
        self.events.extend_from_slice(events);
        if let Err(error) = limits.enforce_memory() {
            self.events.truncate(previous);
            proof! {
                assert(self.events@ =~= entry_events);
                assert(self.id == entry.id && self.revision == entry.revision);
                assert(junco_core::verify::history_specs::history_mutation(entry@, self@));
                assert(verify::stored_events(&*self) == entry_events);
            }
            return Err(error.into());
        }
        proof! {
            assert(crate::store::verify::events_view(self.events@)
                =~= crate::store::verify::events_view(entry_events)
                    + crate::store::verify::events_view(events@));
            assert(self.id == entry.id && self.revision == entry.revision);
            assert(self.events@ == entry_events + events@);
            assert(junco_core::verify::history_specs::history_mutation(entry@, self@));
            assert(verify::stored_events(&*self) == entry_events + events@);
        }
        Ok(())
    }

    #[verus_spec(result =>
        ensures verify::stored_truncate_result(*old(self), *final(self), len, result),
    )]
    pub(crate) fn truncate_events(&mut self, len: usize) -> Result<(), HistoryError> {
        proof! { reveal(<StoredHistory as View>::view); }
        proof_decl! { let ghost entry_events = self.events@; }
        if len < self.events.len() {
            let revision = self
                .revision
                .checked_add(1)
                .ok_or(HistoryError::RevisionExhausted)?;
            self.events.truncate(len);
            self.revision = revision;
            proof! {
                assert(self.events@ == entry_events.take(len as int));
                assert(crate::store::verify::events_view(self.events@)
                    =~= crate::store::verify::events_view(entry_events).take(len as int));
            }
        }
        Ok(())
    }
}

/// Opaque length marker accepted only by the history that produced it.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Checkpoint {
    pub(crate) store_id: u64,
    pub(crate) history: usize,
    pub(crate) len: usize,
}

/// Raw committed events and their store-bound numeric encoding.
///
/// Equality and diagnostics observe the original events, not their projections or owner.
/// No mutable slice or numeric record escapes this owner.
#[verus_verify]
pub struct History<E: TypedEvent> {
    pub(crate) events: Vec<E>,
    pub(crate) numeric: StoredHistory,
    pub(crate) store: Arc<Store<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) maps: Ghost<books::ComponentMaps<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) lifecycle: Tracked<Lifecycle>,
    #[cfg(verus_keep_ghost)]
    pub(crate) registration: Tracked<books::HistoryRegistration>,
    #[cfg(verus_keep_ghost)]
    pub(crate) global_registration: Tracked<crate::store::HistoryKeyReceipt>,
}

#[verus_verify]
impl<E: TypedEvent> History<E> {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn spec_id(&self) -> usize { self.numeric.id }
        pub closed spec fn spec_numeric(&self) -> &StoredHistory { &self.numeric }
    }

    /// Returns the numeric record's process-wide key.
    #[cfg_attr(verus_keep_ghost, verifier::when_used_as_spec(spec_id))]
    #[verus_spec(result => ensures result == self.spec_id())]
    pub const fn id(&self) -> usize {
        self.numeric.id
    }

    #[cfg_attr(verus_keep_ghost, verifier::when_used_as_spec(spec_numeric))]
    #[verus_spec(result => ensures *result == *self.spec_numeric())]
    pub fn numeric(&self) -> &StoredHistory {
        &self.numeric
    }

    /// Creates an empty history in `store`, with a fresh process-wide key.
    #[verus_spec(result =>
        requires books::store_wf(*store),
        ensures result matches Ok(history) ==> history_wf(history) && empty_history(history, store),
            junco_core::verify::history_specs::no_invariant_failure(result),
    )]
    pub fn new(store: Arc<Store<E>>) -> Result<Self, HistoryError> {
        proof! { books::lemma_empty_snapshot(&*store); }
        proof_decl! {
            let ghost empty = junco_core::verify::history_specs::HistoryStateView {
                events: Seq::empty(), revision: 0,
            };
            let tracked lifecycle = Lifecycle::new(empty);
        }
        #[cfg(verus_keep_ghost)]
        let (id, registration, global_registration) = store.allocate_history_id_for_resource(
            verus_exec_expr! { Ghost(lifecycle.id()) },
            verus_exec_expr! { Tracked(None) },
        )?;
        #[cfg(not(verus_keep_ghost))]
        let (id, _, _) =
            store.allocate_history_id_for_resource(Ghost::assume_new(), Tracked::assume_new())?;
        let numeric = StoredHistory::new(id);
        proof! {
            reveal(<StoredHistory as View>::view);
            assert(crate::store::verify::events_view(numeric.events@) =~= Seq::empty());
            assert(numeric@ == empty);
            if junco_core::spec::hypotheses::event_obligations::<E>() { books::lemma_empty_maps_wf::<E>(); }
        }
        Ok(Self {
            events: Vec::new(),
            numeric,
            store,
            #[cfg(verus_keep_ghost)]
            maps: verus_exec_expr! { Ghost(books::empty_maps::<E>()) },
            #[cfg(verus_keep_ghost)]
            lifecycle: verus_exec_expr! { Tracked(lifecycle) },
            #[cfg(verus_keep_ghost)]
            registration,
            #[cfg(verus_keep_ghost)]
            global_registration,
        })
    }

    /// Creates a history by committing the supplied events in iteration order.
    #[verus_spec(result =>
        requires books::store_wf(*store),
        ensures result matches Ok(history) ==> history_wf(history) && initialized_history(history, store)
            && forall|items: Seq<E>| junco_core::verify::history_specs::into_iter_yields(events, items)
                ==> raw_events(history) == items,
    )]
    pub fn from_events<I: IntoIterator<Item = E>>(
        store: Arc<Store<E>>,
        events: I,
    ) -> Result<Self, HistoryError> {
        proof_decl! { let ghost input = events; }
        let convert = I::into_iter;
        let iterator = convert(events);
        proof_decl! { let ghost converted = iterator; }
        proof! { assert(call_ensures(convert, (input,), converted)); }
        let result = Self::from_iterator(store, iterator);
        proof! {
            if let Ok(ref history) = result {
                assert forall|items: Seq<E>|
                    junco_core::verify::history_specs::into_iter_yields(input, items)
                    implies raw_events(*history) == items by {
                    assert(converted.obeys_prophetic_iter_laws());
                    assert(converted.remaining() == items);
                }
            }
        }
        result
    }

    // Caller-supplied iterators may be infinite; each yielded event still commits atomically.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    #[verus_spec(result =>
        requires books::store_wf(*store),
        ensures result matches Ok(history) ==> history_wf(history)
            && history.numeric.revision == 0 && history.store == store
            && (iterator.obeys_prophetic_iter_laws() ==> history.events@ == iterator.remaining()),
    )]
    fn from_iterator<I: Iterator<Item = E>>(
        store: Arc<Store<E>>,
        iterator: I,
    ) -> Result<Self, HistoryError> {
        proof_decl! { let ghost original_iterator = iterator; }
        let mut remaining = iterator;
        let mut history = Self::new(store)?;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant history_wf(history),
            history.numeric.revision == 0, history.store == store,
            original_iterator == iterator,
            remaining.obeys_prophetic_iter_laws() == original_iterator.obeys_prophetic_iter_laws(),
            remaining.obeys_prophetic_iter_laws() ==>
                history.events@ + remaining.remaining() == original_iterator.remaining()))]
        loop {
            match remaining.next() {
                Some(event) => history.push(event)?,
                None => {
                    proof! {
                        assert(history_wf(history));
                        assert(history.numeric.revision == 0);
                        assert(history.store == store);
                        if original_iterator.obeys_prophetic_iter_laws() {
                            assert(remaining.remaining().len() == 0);
                            assert(history.events@ =~= original_iterator.remaining());
                            assert(history.events@ == iterator.remaining());
                        }
                    }
                    return Ok(history);
                }
            }
        }
    }

    /// Appends one original event and its numeric encoding atomically.
    #[verus_spec(result =>
        requires history_wf(*old(self)),
        ensures history_wf(*final(self)), push_result(*old(self), *final(self), event, result),
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
    )]
    pub fn push(&mut self, event: E) -> Result<(), HistoryError> {
        self.push_with(event, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result =>
        requires history_wf(*old(self)),
        ensures history_wf(*final(self)), push_result(*old(self), *final(self), event, result),
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
    )]
    pub fn push_with<L: Limits>(
        &mut self,
        event: E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        proof_decl! { let ghost before = *self; }
        proof! {
            reveal(<StoredHistory as View>::view);
            reveal(StoredHistory::spec_id);
            reveal(StoredHistory::spec_revision);
        }
        allocation(world.try_reserve_vec(&mut self.events, 1))?;
        limits.checkpoint()?;
        #[cfg(verus_keep_ghost)]
        let (encoded, maps) = self.store.encode_event_with_snapshot(
            &event,
            verus_exec_expr! { Ghost(self.maps@) },
            verus_exec_expr! { Ghost(self.maps@) },
        );
        #[cfg(not(verus_keep_ghost))]
        let encoded = self.store.encode_event(&event);
        proof! {
            *self.maps = maps@;
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                lemma_correspondence_extends(before.events@, before.numeric.events@,
                    before.maps@, self.maps@);
            }
        }
        let encoded = encoded?;
        self.numeric.append_events(&[encoded], limits, world)?;
        self.events.push(event);
        proof! {
            assert(self.events@ == before.events@.push(event));
            assert(self.numeric.events@ == before.numeric.events@.push(encoded));
            assert(self.numeric.events@.last() == encoded);
            assert(stored_events(&self.numeric) == stored_events(&before.numeric) + seq![encoded]);
            assert(stored_append_result(before.numeric, self.numeric, seq![encoded], Ok(())));
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                assert forall|i: int| 0 <= i < self.events@.len() implies
                    books::event_encoded::<E>(self.maps@, self.events@[i], self.numeric.events@[i]) by {
                    if i < before.events@.len() {
                        assert(self.events@[i] == before.events@[i]);
                        assert(self.numeric.events@[i] == before.numeric.events@[i]);
                    } else {
                        assert(i == before.events@.len());
                        assert(self.events@[i] == event && self.numeric.events@[i] == encoded);
                    }
                }
            }
            self.lifecycle.borrow_mut().advance(self.numeric@);
            assert(owner_frame(before, *self));
            assert(self.numeric.events@.drop_last() == before.numeric.events@);
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                assert(books::maps_extend::<E>(before.maps@, self.maps@));
            }
            assert(push_result(before, *self, event, Ok(())));
        }
        Ok(())
    }

    /// Shortens the history; equal or larger lengths are no-ops.
    #[verus_spec(result =>
        requires history_wf(*old(self)),
        ensures history_wf(*final(self)), truncate_result(*old(self), *final(self), len, result),
    )]
    pub fn truncate(&mut self, len: usize) -> Result<(), HistoryError> {
        proof_decl! { let ghost before = *self; }
        proof! { reveal(<StoredHistory as View>::view); }
        self.numeric.truncate_events(len)?;
        self.events.truncate(len);
        proof! {
            if len < before.events@.len() {
                assert(self.events@ == before.events@.take(len as int));
            }
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                assert forall|i: int| 0 <= i < self.events@.len() implies
                    books::event_encoded::<E>(self.maps@, self.events@[i], self.numeric.events@[i]) by {
                    assert(self.events@[i] == before.events@[i]);
                    assert(self.numeric.events@[i] == before.numeric.events@[i]);
                }
            }
            self.lifecycle.borrow_mut().advance(self.numeric@);
            assert(owner_frame(before, *self));
            assert(self.maps@ == before.maps@);
            assert(junco_core::verify::history_specs::history_mutation(before.numeric@, self.numeric@));
            if len < before.events@.len() {
                assert(self.numeric.events@ == before.numeric.events@.take(len as int));
                assert(self.numeric.revision == before.numeric.revision + 1);
            } else {
                assert(self.events@ =~= before.events@);
                assert(self.numeric.events@ == before.numeric.events@);
                assert(self.numeric.revision == before.numeric.revision);
                assert(state_frame(before, *self));
            }
            assert(truncate_result(before, *self, len, Ok(())));
        }
        Ok(())
    }

    /// Restores a marker's length after checking store, owner, then length.
    #[verus_spec(result =>
        requires history_wf(*old(self)),
        ensures history_wf(*final(self)), rollback_result(*old(self), *final(self), checkpoint, result),
    )]
    pub fn rollback(&mut self, checkpoint: Checkpoint) -> Result<(), HistoryError> {
        if checkpoint.store_id != self.store.id() || checkpoint.history != self.numeric.id {
            return Err(HistoryError::WrongCheckpointOwner);
        }
        if checkpoint.len > self.events.len() {
            return Err(HistoryError::CheckpointBeyondHistory);
        }
        self.truncate(checkpoint.len)
    }

    /// Copies raw and numeric events without invoking user projections or `Clone`.
    /// The fork shares codebooks, but has a fresh key and revision zero.
    #[verus_spec(result =>
        requires history_wf(*self),
        ensures result matches Ok(history) ==> history_wf(history) && clone_result(*self, history),
    )]
    pub fn try_clone(&self) -> Result<Self, HistoryError> {
        self.try_clone_with(&mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result =>
        requires history_wf(*self),
        ensures result matches Ok(history) ==> history_wf(history) && clone_result(*self, history),
    )]
    pub(crate) fn try_clone_with<L: Limits>(
        &self,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, HistoryError> {
        let mut events = Vec::new();
        allocation(world.try_reserve_vec_exact(&mut events, self.events.len()))?;
        let mut numeric_events = Vec::new();
        allocation(world.try_reserve_vec_exact(&mut numeric_events, self.numeric.events.len()))?;
        limits.enforce_memory()?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant index <= self.events@.len(),
            events@ == self.events@.take(index as int),
            numeric_events@ == self.numeric.events@.take(index as int),
            history_wf(*self),
            decreases self.events@.len() - index))]
        while index < self.events.len() {
            limits.checkpoint()?;
            events.push(self.events[index]);
            numeric_events.push(self.numeric.events[index]);
            index += 1;
        }
        limits.enforce_memory()?;
        proof_decl! {
            let ghost copied = junco_core::verify::history_specs::HistoryStateView {
                events: crate::store::verify::events_view(numeric_events@), revision: 0,
            };
            let tracked lifecycle = Lifecycle::new(copied);
        }
        #[cfg(verus_keep_ghost)]
        let (id, registration, global_registration) = self.store.allocate_history_id_for_resource(
            verus_exec_expr! { Ghost(lifecycle.id()) },
            verus_exec_expr! { Tracked(Some(self.registration.borrow())) },
        )?;
        #[cfg(not(verus_keep_ghost))]
        let (id, _, _) = self
            .store
            .allocate_history_id_for_resource(Ghost::assume_new(), Tracked::assume_new())?;
        // Move the copied buffer into the fresh record; no event is copied twice.
        let numeric = StoredHistory {
            events: numeric_events,
            revision: 0,
            id,
        };
        proof! { reveal(<StoredHistory as View>::view); }
        let clone = Self {
            events,
            numeric,
            store: share_store(&self.store),
            #[cfg(verus_keep_ghost)]
            maps: self.maps,
            #[cfg(verus_keep_ghost)]
            lifecycle: verus_exec_expr! { Tracked(lifecycle) },
            #[cfg(verus_keep_ghost)]
            registration,
            #[cfg(verus_keep_ghost)]
            global_registration,
        };
        proof! {
            assert(clone.events@ == self.events@);
            assert(clone.numeric.events@ == self.numeric.events@);
            assert(clone.numeric.revision == 0);
            assert(clone.store == self.store);
            assert(clone.numeric.id > self.numeric.id);
            assert(history_wf(clone));
            assert(clone_result(*self, clone));
        }
        Ok(clone)
    }

    /// Returns the original committed events, including all payload fields and variants.
    #[verus_spec(result => ensures result@ == raw_events(*self))]
    pub fn as_slice(&self) -> &[E] {
        &self.events
    }

    /// Iterates the original committed events in order.
    pub fn iter(&self) -> core::slice::Iter<'_, E> {
        self.events.iter()
    }

    /// Returns the number of committed events.
    #[verus_spec(result => ensures result == raw_events(*self).len())]
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Returns whether the history is empty.
    #[verus_spec(result => ensures result == (raw_events(*self).len() == 0))]
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Captures a reusable owner-specific length marker.
    #[verus_spec(result => ensures checkpoint_matches(*self, result))]
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            store_id: self.store.id(),
            history: self.numeric.id,
            len: self.events.len(),
        }
    }

    /// Returns the shared store binding this history's numeric events.
    #[verus_spec(result => ensures *result == store_of(*self),
        junco_core::verify::history_assumptions::arc_identity(*result)
            == junco_core::verify::history_assumptions::arc_identity(store_of(*self)))]
    pub fn store(&self) -> &Arc<Store<E>> {
        &self.store
    }
}

impl<E: TypedEvent> fmt::Debug for History<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("History")
            .field(&self.events)
            .finish()
    }
}

impl<E: TypedEvent> PartialEq for History<E> {
    fn eq(&self, other: &Self) -> bool {
        self.events == other.events
    }
}

impl<E: TypedEvent> Eq for History<E> {}

/// Finite observed codebook snapshots supporting the typed/numeric correspondence.
#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    use history_syntax::{Arity, spec::events::event_view};
    use junco_core::verify::history_specs::{
        HistoryStateView, history_mutation, lemma_revision_chain_preserves_prefix,
    };
    use vstd::prelude::*;
    use vstd::resource::Loc;
    use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};

    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

    pub open(super) spec fn stored_events(stored: &StoredHistory) -> Seq<Event> { stored.events@ }

    /// Failure-atomic numeric append, retaining record identity and lifecycle compatibility.
    pub open spec fn stored_append_result(before: StoredHistory, after: StoredHistory,
        events: Seq<Event>, result: Result<(), HistoryError>) -> bool {
        after.spec_id() == before.spec_id() && after.spec_revision() == before.spec_revision()
        && history_mutation(before@, after@)
        && match result {
            Ok(()) => stored_events(&after) == stored_events(&before) + events,
            Err(_) => stored_events(&after) == stored_events(&before),
        }
    }

    /// Exact numeric truncation table; only a proper shrink consumes a revision.
    pub open spec fn stored_truncate_result(before: StoredHistory, after: StoredHistory,
        len: usize, result: Result<(), HistoryError>) -> bool {
        after.spec_id() == before.spec_id() && history_mutation(before@, after@)
        && if len >= stored_events(&before).len() {
            result == Ok(()) && after@ == before@
            && stored_events(&after) == stored_events(&before) && after.spec_revision() == before.spec_revision()
        } else if before.spec_revision() == u64::MAX {
            result == Err(HistoryError::RevisionExhausted) && after@ == before@
            && stored_events(&after) == stored_events(&before) && after.spec_revision() == before.spec_revision()
        } else {
            result == Ok(()) && stored_events(&after) == stored_events(&before).take(len as int)
            && after.spec_revision() == before.spec_revision() + 1
        }
    }

    /// Expose every numeric truncate case and its public record observations.
    pub proof fn lemma_stored_truncate_result_facts(
        before: StoredHistory, after: StoredHistory, len: usize, result: Result<(), HistoryError>,
    )
        requires stored_truncate_result(before, after, len, result),
        ensures
            after.spec_id() == before.spec_id(), history_mutation(before@, after@),
            before@.events.len() == stored_events(&before).len(),
            after@.events.len() == stored_events(&after).len(),
            before@.revision == before.spec_revision() as nat,
            after@.revision == after.spec_revision() as nat,
            if len >= before@.events.len() {
                result == Ok(()) && after@ == before@
                && stored_events(&after) == stored_events(&before)
                && after.spec_revision() == before.spec_revision()
            } else if before.spec_revision() == u64::MAX {
                result == Err(HistoryError::RevisionExhausted) && after@ == before@
                && stored_events(&after) == stored_events(&before)
                && after.spec_revision() == before.spec_revision()
            } else {
                result == Ok(())
                && stored_events(&after) == stored_events(&before).take(len as int)
                && after@.events == before@.events.take(len as int)
                && after.spec_revision() == before.spec_revision() + 1
                && after@.revision == before@.revision + 1
            },
    {
        super::lemma_stored_history_view(before);
        super::lemma_stored_history_view(after);
        if len < stored_events(&before).len() && before.spec_revision() < u64::MAX {
            assert(after@.events =~= before@.events.take(len as int));
        }
    }


    impl<E: TypedEvent> History<E> {
        pub open(super) spec fn lifecycle_model(&self) -> Lifecycle { self.lifecycle@ }
        pub open(super) spec fn registration_model(&self) -> books::HistoryRegistration { self.registration@ }
        pub open(super) spec fn global_registration_model(&self) -> crate::store::HistoryKeyReceipt {
            self.global_registration@
        }

        pub proof fn lifecycle_ref(tracked &self) -> (tracked reference: &Lifecycle)
            requires history_wf(*self),
            ensures *reference == self.lifecycle_model(),
                reference.wf(), reference.state() == (*self.spec_numeric())@,
                reference.id() == self.registration_model().value(),
        { self.lifecycle.borrow() }

        pub proof fn registration_ref(tracked &self) -> (tracked reference: &books::HistoryRegistration)
            requires history_wf(*self),
            ensures *reference == self.registration_model(),
                reference.id() == books::registry_id::<E>(&*store_of(*self)),
                reference.key() == self.spec_id(), reference.value() == self.lifecycle_model().id(),
        { self.registration.borrow() }

        pub(crate) proof fn history_key_receipt_ref(tracked &self)
            -> (tracked reference: &crate::store::HistoryKeyReceipt)
            requires history_wf(*self),
            ensures *reference == self.global_registration_model(),
                reference.id() == crate::store::verify::history_authority(),
                reference.key() == self.spec_id(),
                reference.value() == (crate::store::HistoryIssuer::Typed {
                    store: books::registry_id::<E>(&*store_of(*self)),
                    lifecycle: self.lifecycle_model().id(),
                }),
        { self.global_registration.borrow() }
    }

    pub proof fn lemma_history_wf<E: TypedEvent>(history: History<E>)
        requires history_wf(history),
        ensures books::store_wf(*store_of(history)),
            history.registration_model().id() == books::registry_id::<E>(&*store_of(history)),
            history.registration_model().key() == history.spec_id(),
            history.spec_id() == history.spec_numeric().spec_id(),
            raw_events(history).len() == stored_events(history.spec_numeric()).len(),
            history.lifecycle_model().wf(), history.lifecycle_model().state() == (*history.spec_numeric())@,
            history.lifecycle_model().id() == history.registration_model().value(),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> books::maps_wf::<E>(history_maps(history))
                && books::snapshot_published::<E>(books::registry_id::<E>(&*store_of(history)), history_maps(history))
                && correspondence(raw_events(history), stored_events(history.spec_numeric()), history_maps(history)),
    { reveal(history_wf); }

    pub type Snapshot = GhostPersistentPointsTo<nat, HistoryStateView>;

    /// Only actual numeric transactions append to this ghost-only lifecycle ledger.
    pub tracked struct Lifecycle {
        pub(crate) authority: GhostMapAuth<nat, HistoryStateView>,
        pub(crate) current: Snapshot,
        pub(crate) ghost states: Seq<HistoryStateView>,
    }

    impl Lifecycle {
        pub closed spec fn id(self) -> Loc { self.authority.id() }

        pub closed spec fn state(self) -> HistoryStateView { self.states.last() }

        pub closed spec fn wf(self) -> bool {
            self.states.len() > 0 && self.states[0].revision <= u64::MAX
            && (forall|i: nat| #[trigger] self.authority@.contains_key(i) == (i < self.states.len())
                && (i < self.states.len() ==> self.authority@[i] == self.states[i as int]))
            && (forall|i: int| 0 < i < self.states.len()
                ==> #[trigger] history_mutation(self.states[i - 1], self.states[i]))
            && self.current.id() == self.id() && self.current.key() == self.states.len() - 1
            && self.current.value() == self.state()
        }

        pub proof fn new(state: HistoryStateView) -> (tracked result: Self)
            requires state.revision <= u64::MAX,
            ensures result.wf(), result.state() == state,
        {
            let tracked (mut authority, empty) = GhostMapAuth::new(Map::<nat, HistoryStateView>::empty());
            let tracked current = authority.insert(0, state).persist();
            Self { authority, current, states: seq![state] }
        }

        pub proof fn advance(tracked &mut self, next: HistoryStateView)
            requires old(self).wf(), history_mutation(old(self).state(), next),
            ensures final(self).wf(), final(self).id() == old(self).id(), final(self).state() == next,
        {
            let ghost previous = self.states;
            let tracked current = self.authority.insert(previous.len(), next).persist();
            self.current = current;
            self.states = previous.push(next);
            assert forall|i: nat| self.authority@.contains_key(i) == (i < self.states.len())
                && (i < self.states.len() ==> self.authority@[i] == self.states[i as int]) by {
                if i < previous.len() { assert(self.states[i as int] == previous[i as int]); }
            }
            assert forall|i: int| 0 < i < self.states.len() implies
                #[trigger] history_mutation(self.states[i - 1], self.states[i]) by {
                if i < previous.len() {
                    assert(history_mutation(previous[i - 1], previous[i]));
                } else {
                    assert(self.states[i - 1] == previous.last());
                    assert(self.states[i] == next);
                }
            }
        }

        pub proof fn observe(tracked &self) -> (tracked result: Snapshot)
            requires self.wf(),
            ensures result.id() == self.id(), result.value() == self.state(),
        {
            self.current.duplicate()
        }

        pub proof fn validate(tracked &self, tracked snapshot: &Snapshot)
            requires self.wf(), snapshot.id() == self.id(),
            ensures snapshot.value().revision <= self.state().revision,
                snapshot.value().revision == self.state().revision
                    ==> snapshot.value().events.is_prefix_of(self.state().events),
        {
            snapshot.agree(&self.authority);
            let index = snapshot.key();
            assert(index < self.states.len());
            assert(self.states[index as int] == snapshot.value());
            let suffix = self.states.subrange(index as int, self.states.len() as int);
            assert(suffix.len() > 0);
            assert(suffix.first() == snapshot.value());
            assert(suffix.last() == self.state());
            assert forall|i: int| 0 < i < suffix.len() implies
                #[trigger] history_mutation(suffix[i - 1], suffix[i]) by {
                assert(suffix[i - 1] == self.states[index + i - 1]);
                assert(suffix[i] == self.states[index + i]);
                assert(history_mutation(self.states[index + i - 1], self.states[index + i]));
            }
            lemma_revision_chain_preserves_prefix(suffix);
        }
    }

    pub open(super) spec fn raw_events<E: TypedEvent>(history: History<E>) -> Seq<E> {
        history.events@
    }

    pub open(super) spec fn store_of<E: TypedEvent>(history: History<E>) -> Arc<Store<E>> {
        history.store
    }

    pub open(super) spec fn initialized_history<E: TypedEvent>(history: History<E>, store: Arc<Store<E>>) -> bool {
        history.numeric.revision == 0 && history.store == store
    }

    pub open(super) spec fn empty_history<E: TypedEvent>(history: History<E>, store: Arc<Store<E>>) -> bool {
        initialized_history(history, store) && history.events@ == Seq::<E>::empty()
            && history.numeric.events@ == Seq::<Event>::empty()
    }

    pub open(super) spec fn checkpoint_matches<E: TypedEvent>(history: History<E>, checkpoint: Checkpoint) -> bool {
        checkpoint.store_id == books::store_id(*history.store)
            && checkpoint.history == history.numeric.id && checkpoint.len == history.events@.len()
    }

    pub open(super) spec fn rollback_result<E: TypedEvent>(before: History<E>, after: History<E>,
        checkpoint: Checkpoint, result: Result<(), HistoryError>) -> bool {
        history_wf(after) && owner_frame(before, after) && after.maps@ == before.maps@
        && (result is Err ==> state_frame(before, after))
        && if checkpoint.store_id != books::store_id(*before.store) || checkpoint.history != before.numeric.id {
            result == Err(HistoryError::WrongCheckpointOwner) && state_frame(before, after)
        } else if checkpoint.len > before.events@.len() {
            result == Err(HistoryError::CheckpointBeyondHistory) && state_frame(before, after)
        } else {
            truncate_result(before, after, checkpoint.len, result)
        }
    }

    pub open spec fn correspondence<E: TypedEvent>(
        raw: Seq<E>, numeric: Seq<Event>, maps: books::ComponentMaps<E>,
    ) -> bool {
        raw.len() == numeric.len() && forall|i: int| 0 <= i < raw.len()
            ==> books::event_encoded::<E>(maps, raw[i], numeric[i])
    }

    pub open(super) spec fn history_maps<E: TypedEvent>(history: History<E>) -> books::ComponentMaps<E> {
        history.maps@
    }

    pub open(super) spec fn history_wf<E: TypedEvent>(history: History<E>) -> bool {
        books::store_wf(*history.store)
        && history.registration@.id() == books::registry_id::<E>(&*history.store)
        && history.registration@.key() == history.numeric.id
        && history.events@.len() == history.numeric.events@.len()
        && history.lifecycle@.wf() && history.lifecycle@.state() == history.numeric@
        && history.lifecycle@.id() == history.registration@.value()
        && history.global_registration@.id() == crate::store::verify::history_authority()
        && history.global_registration@.key() == history.numeric.id
        && history.global_registration@.value() == (crate::store::HistoryIssuer::Typed {
            store: books::registry_id::<E>(&*history.store),
            lifecycle: history.lifecycle@.id(),
        })
        && (junco_core::spec::hypotheses::event_obligations::<E>() ==> books::maps_wf::<E>(history.maps@)
            && books::snapshot_published::<E>(books::registry_id::<E>(&history.store), history.maps@)
            && correspondence(history.events@, history.numeric.events@, history.maps@))
    }

    pub open spec fn raw_event<E: TypedEvent>(event: E)
        -> Seq<E::Component>
    {
        event_view(event)
    }

    pub open spec fn raw_word<E: TypedEvent>(history: History<E>)
        -> Seq<Seq<E::Component>>
    {
        raw_events(history).map(|i: int, event: E| raw_event(event))
    }

    pub open(super) spec fn owner_frame<E: TypedEvent>(before: History<E>, after: History<E>) -> bool {
        after.store == before.store && after.numeric.id == before.numeric.id
            && after.lifecycle@.id() == before.lifecycle@.id()
            && after.global_registration@.id() == before.global_registration@.id()
            && after.global_registration@.key() == before.global_registration@.key()
            && after.global_registration@.value() == before.global_registration@.value()
    }

    pub open(super) spec fn state_frame<E: TypedEvent>(before: History<E>, after: History<E>) -> bool {
        owner_frame(before, after) && after.events@ == before.events@
            && after.numeric.events@ == before.numeric.events@
            && after.numeric.revision == before.numeric.revision
    }

    pub open(super) spec fn push_result<E: TypedEvent>(
        before: History<E>, after: History<E>, event: E, result: Result<(), HistoryError>,
    ) -> bool {
        history_wf(after) && owner_frame(before, after)
        && (junco_core::spec::hypotheses::event_obligations::<E>() ==> junco_core::verify::history_specs::no_invariant_failure(result))
        && after.numeric.revision == before.numeric.revision
        && junco_core::verify::history_specs::history_mutation(before.numeric@, after.numeric@)
        && (junco_core::spec::hypotheses::event_obligations::<E>() ==> books::maps_extend::<E>(before.maps@, after.maps@))
        && match result {
            Err(_) => state_frame(before, after),
            Ok(()) => after.events@ == before.events@.push(event)
                && after.numeric.events@.len() > 0
                && stored_append_result(before.numeric, after.numeric,
                    seq![after.numeric.events@.last()], result),
        }
    }

    pub proof fn lemma_state_frame_facts<E: TypedEvent>(before: History<E>, after: History<E>)
        requires state_frame(before, after),
        ensures raw_events(after) == raw_events(before), store_of(after) == store_of(before),
            stored_events(after.spec_numeric()) == stored_events(before.spec_numeric()),
            after.spec_numeric().spec_revision() == before.spec_numeric().spec_revision(),
    {}

    pub proof fn lemma_checkpoint_matches<E: TypedEvent>(history: History<E>, checkpoint: Checkpoint)
        requires checkpoint_matches(history, checkpoint),
        ensures checkpoint_owned(history, checkpoint), checkpoint_len(checkpoint) == raw_events(history).len(),
    {}

    pub proof fn lemma_checkpoint_owner_preserved<E: TypedEvent>(before: History<E>, after: History<E>, checkpoint: Checkpoint)
        requires owner_frame(before, after),
        ensures checkpoint_owned(before, checkpoint) == checkpoint_owned(after, checkpoint),
    {}

    pub proof fn lemma_distinct_checkpoint_owner<E: TypedEvent>(left: History<E>, right: History<E>, checkpoint: Checkpoint)
        requires checkpoint_matches(left, checkpoint), books::store_id(*store_of(left)) != books::store_id(*store_of(right)),
        ensures !checkpoint_owned(right, checkpoint),
    {}

    /// Boundary harness for the exact numeric table, not a forged reachable typed lifecycle.
    #[doc(hidden)]
    pub fn revision_boundary_record(id: usize, events: Vec<Event>) -> (stored: StoredHistory)
        ensures stored.spec_id() == id, stored.spec_revision() == u64::MAX,
            stored_events(&stored) == events@,
    { StoredHistory { id, revision: u64::MAX, events } }

    #[doc(hidden)]
    pub fn truncate_boundary_record(stored: &mut StoredHistory, len: usize) -> (result: Result<(), HistoryError>)
        ensures stored_truncate_result(*old(stored), *final(stored), len, result),
    { stored.truncate_events(len) }

    pub proof fn lemma_initialized_history_facts<E: TypedEvent>(history: History<E>, store: Arc<Store<E>>)
        requires initialized_history(history, store),
        ensures store_of(history) == store, history.spec_numeric().spec_revision() == 0,
    {}

    pub proof fn lemma_clone_facts<E: TypedEvent>(before: History<E>, after: History<E>, checkpoint: Checkpoint)
        requires clone_result(before, after), checkpoint_matches(before, checkpoint),
        ensures raw_events(after) == raw_events(before), store_of(after) == store_of(before),
            after.spec_numeric().spec_revision() == 0, after.spec_id() != before.spec_id(),
            !checkpoint_owned(after, checkpoint),
    {}

    pub proof fn lemma_empty_history<E: TypedEvent>(history: History<E>, store: Arc<Store<E>>)
        requires history_wf(history), empty_history(history, store),
        ensures raw_events(history) == Seq::<E>::empty(), store_of(history) == store,
            books::store_wf(*store), history.spec_numeric().spec_revision() == 0,
    {}

    pub proof fn lemma_push_result<E: TypedEvent>(before: History<E>, after: History<E>, event: E,
        result: Result<(), HistoryError>)
        requires push_result(before, after, event, result),
        ensures history_wf(after), owner_frame(before, after), store_of(after) == store_of(before),
            after.spec_numeric().spec_revision() == before.spec_numeric().spec_revision(),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> junco_core::verify::history_specs::no_invariant_failure(result),
            result is Err ==> state_frame(before, after),
            result is Ok ==> raw_events(after) == raw_events(before).push(event),
    {}

    pub proof fn lemma_state_frame_transitive<E: TypedEvent>(before: History<E>, middle: History<E>, after: History<E>)
        requires state_frame(before, middle), state_frame(middle, after),
        ensures state_frame(before, after),
    {}

    pub proof fn lemma_history_frame_facts<E: TypedEvent>(before: History<E>, after: History<E>)
        ensures state_frame(before, before), owner_frame(before, before),
            owner_frame(before, after) ==> store_of(before) == store_of(after),
            state_frame(before, after) ==> raw_events(before) == raw_events(after),
            history_wf(before) ==> books::store_wf(*store_of(before)),
    {}

    pub closed spec fn checkpoint_owned<E: TypedEvent>(history: History<E>, checkpoint: Checkpoint) -> bool {
        checkpoint.store_id == books::store_id(*history.store) && checkpoint.history == history.numeric.id
    }
    pub closed spec fn checkpoint_len(checkpoint: Checkpoint) -> usize { checkpoint.len }

    pub proof fn lemma_rollback_result<E: TypedEvent>(before: History<E>, after: History<E>, checkpoint: Checkpoint,
        result: Result<(), HistoryError>)
        requires history_wf(after), rollback_result(before, after, checkpoint, result),
        ensures owner_frame(before, after), store_of(before) == store_of(after),
            history_maps(after) == history_maps(before),
            result is Err ==> state_frame(before, after),
            !checkpoint_owned(before, checkpoint) ==> result == Err(HistoryError::WrongCheckpointOwner),
            checkpoint_owned(before, checkpoint) && checkpoint_len(checkpoint) > raw_events(before).len()
                ==> result == Err(HistoryError::CheckpointBeyondHistory),
            checkpoint_owned(before, checkpoint) && checkpoint_len(checkpoint) <= raw_events(before).len()
                ==> truncate_result(before, after, checkpoint_len(checkpoint), result),
            checkpoint_owned(before, checkpoint) && checkpoint_len(checkpoint) == raw_events(before).len()
                ==> result == Ok(()) && state_frame(before, after),
            checkpoint_owned(before, checkpoint) && checkpoint_len(checkpoint) < raw_events(before).len()
                && before.spec_numeric().spec_revision() == u64::MAX
                ==> result == Err(HistoryError::RevisionExhausted) && state_frame(before, after),
            checkpoint_owned(before, checkpoint) && checkpoint_len(checkpoint) < raw_events(before).len()
                && before.spec_numeric().spec_revision() < u64::MAX
                ==> result == Ok(()) && raw_events(after) == raw_events(before).take(checkpoint_len(checkpoint) as int)
                    && stored_events(after.spec_numeric()) == stored_events(before.spec_numeric()).take(checkpoint_len(checkpoint) as int)
                    && after.spec_numeric().spec_revision() == before.spec_numeric().spec_revision() + 1,
    {
        if checkpoint_owned(before, checkpoint) && checkpoint_len(checkpoint) <= raw_events(before).len() {
            lemma_truncate_result(before, after, checkpoint_len(checkpoint), result);
        }
    }

    pub open(super) spec fn truncate_result<E: TypedEvent>(
        before: History<E>, after: History<E>, len: usize, result: Result<(), HistoryError>,
    ) -> bool {
        history_wf(before) && history_wf(after) && owner_frame(before, after) && after.maps@ == before.maps@
        && stored_truncate_result(before.numeric, after.numeric, len, result)
        && if result is Err || len >= before.events@.len() {
            state_frame(before, after)
        } else {
            after.events@ == before.events@.take(len as int)
        }
    }

    pub proof fn lemma_truncate_result<E: TypedEvent>(before: History<E>, after: History<E>, len: usize,
        result: Result<(), HistoryError>)
        requires truncate_result(before, after, len, result),
        ensures history_wf(after), owner_frame(before, after), store_of(before) == store_of(after),
            history_maps(after) == history_maps(before),
            stored_truncate_result(*before.spec_numeric(), *after.spec_numeric(), len, result),
            result is Err ==> state_frame(before, after),
            len >= raw_events(before).len() ==> result == Ok(()) && state_frame(before, after),
            len < raw_events(before).len() && before.spec_numeric().spec_revision() == u64::MAX
                ==> result == Err(HistoryError::RevisionExhausted) && state_frame(before, after),
            len < raw_events(before).len() && before.spec_numeric().spec_revision() < u64::MAX
                ==> result == Ok(()) && raw_events(after) == raw_events(before).take(len as int)
                    && stored_events(after.spec_numeric()) == stored_events(before.spec_numeric()).take(len as int)
                    && after.spec_numeric().spec_revision() == before.spec_numeric().spec_revision() + 1,
    {
        reveal(History::spec_numeric);
        reveal(StoredHistory::spec_revision);
        reveal(history_wf);
        lemma_stored_truncate_result_facts(before.numeric, after.numeric, len, result);
    }

    pub open(super) spec fn clone_result<E: TypedEvent>(before: History<E>, after: History<E>) -> bool {
        history_wf(after) && after.store == before.store && after.numeric.id > before.numeric.id
        && after.events@ == before.events@ && after.numeric.events@ == before.numeric.events@
        && after.numeric.revision == 0 && after.maps@ == before.maps@
    }

    pub proof fn lemma_clone_raw_word<E: TypedEvent>(before: History<E>, after: History<E>)
        requires clone_result(before, after),
        ensures raw_word(after) == raw_word(before), after.spec_id() != before.spec_id(),
    {}

    pub(crate) proof fn lemma_foreign_store_checkpoint<E: TypedEvent, F: TypedEvent>(
        source: History<E>, target: History<F>, checkpoint: Checkpoint,
        tracked source_receipt: &crate::typed::StoreIdReceipt,
        tracked target_receipt: &crate::typed::StoreIdReceipt,
    )
        requires history_wf(source), history_wf(target), checkpoint_matches(source, checkpoint),
            source_receipt.id() == target_receipt.id(),
            source_receipt.id() == source.store.store_id_receipt@.id(),
            source_receipt.key() == books::store_id(*source.store),
            target_receipt.key() == books::store_id(*target.store),
            source_receipt.value() == books::registry_id::<E>(&*source.store),
            target_receipt.value() == books::registry_id::<F>(&*target.store),
            books::registry_id::<E>(&*source.store) != books::registry_id::<F>(&*target.store),
        ensures checkpoint.store_id != books::store_id(*target.store),
    {
        books::lemma_store_receipts_distinct(
            books::registry_id::<E>(&*source.store), books::registry_id::<F>(&*target.store),
            source_receipt, target_receipt,
        );
    }

    pub(crate) fn independently_constructed_foreign_rollback_client<E: TypedEvent, F: TypedEvent>()
        -> (result: Result<(History<F>, Ghost<History<F>>, Result<(), HistoryError>), HistoryError>)
        ensures result matches Ok((target, before, rollback)) ==> history_wf(target)
            && state_frame(before@, target)
            && rollback == Err(HistoryError::WrongCheckpointOwner),
    {
        let mut source_store = Store::<E>::new()?;
        let target_store = Store::<F>::new()?;
        proof {
            books::lemma_registry_births_distinct(
                source_store.registry_birth.borrow_mut(), target_store.registry_birth.borrow(),
            );
            books::lemma_store_receipts_distinct(
                source_store.history_registry@, target_store.history_registry@,
                source_store.store_id_receipt.borrow(), target_store.store_id_receipt.borrow(),
            );
            assert(books::store_wf(source_store));
            assert(books::store_wf(target_store));
            assert(source_store.history_registry@ != target_store.history_registry@);
            assert(books::store_id(source_store) != books::store_id(target_store));
        }
        let source_store = Arc::new(source_store);
        let target_store = Arc::new(target_store);
        let source = History::new(source_store)?;
        let mut target = History::new(target_store)?;
        let checkpoint = source.checkpoint();
        proof {
            lemma_foreign_store_checkpoint(
                source, target, checkpoint,
                source.store.store_id_receipt_ref(), target.store.store_id_receipt_ref(),
            );
        }
        let ghost before = target;
        let rollback = target.rollback(checkpoint);
        proof {
            assert(rollback == Err(HistoryError::WrongCheckpointOwner));
            assert(state_frame(before, target));
        }
        Ok((target, Ghost(before), rollback))
    }

    pub(crate) fn byte_typed_history_key_client<E: TypedEvent, L: Limits>(
        store: Arc<Store<E>>, limits: &mut L, world: &mut ObservationWorld,
    ) -> (result: Result<(crate::store::HistoryHandle, History<E>), HistoryError>)
        requires books::store_wf(*store),
        ensures result matches Ok((byte, typed)) ==> crate::store::verify::handle_wf(byte)
            && history_wf(typed)
            && crate::store::verify::handle_index(byte) != typed.spec_id(),
    {
        let owner = crate::store::HistoryStore::new(E::Arity::value());
        let byte = owner.new_history(limits, world)?;
        let typed = History::new(store)?;
        proof {
            let tracked byte_receipt = byte.history_key_receipt_ref();
            let tracked typed_receipt = typed.history_key_receipt_ref();
            let tracked mut duplicate = byte_receipt.duplicate();
            duplicate.intersection_agrees(typed_receipt);
            assert(byte_receipt.value() != typed_receipt.value());
            assert(crate::store::verify::handle_index(byte) != typed.spec_id());
        }
        Ok((byte, typed))
    }

    pub(crate) fn same_store_fork_receipt_client<E: TypedEvent>(source: &History<E>)
        -> (result: Result<History<E>, HistoryError>)
        requires history_wf(*source),
        ensures result matches Ok(fork) ==> clone_result(*source, fork)
            && fork.global_registration@.id() == source.global_registration@.id()
            && fork.global_registration@.key() != source.global_registration@.key(),
    {
        let fork = source.try_clone()?;
        proof {
            let tracked source_receipt = source.history_key_receipt_ref();
            let tracked fork_receipt = fork.history_key_receipt_ref();
            assert(source_receipt.id() == fork_receipt.id());
            assert(source_receipt.key() < fork_receipt.key());
        }
        Ok(fork)
    }

    pub proof fn lemma_correspondence_extends<E: TypedEvent>(
        raw: Seq<E>, numeric: Seq<Event>, before: books::ComponentMaps<E>, after: books::ComponentMaps<E>,
    )
        requires correspondence(raw, numeric, before), books::maps_extend::<E>(before, after),
        ensures correspondence(raw, numeric, after),
    {
        assert forall|i: int| 0 <= i < raw.len() implies
            books::event_encoded::<E>(after, raw[i], numeric[i]) by {
            books::lemma_event_extension::<E>(before, after, raw[i], numeric[i]);
        }
    }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;
    use crate::store::HistoryStore;
    use junco_core::limits::{LimitError, Unmetered};

    struct FailMemory {
        observations: usize,
        fail_at: usize,
    }

    impl Limits for FailMemory {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            self.observations = self.observations.saturating_add(1);
            if self.observations == self.fail_at {
                Err(LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
            } else {
                Ok(())
            }
        }
    }

    fn fresh_key() -> usize {
        HistoryStore::new(3)
            .allocate_history_after(0, Ghost::assume_new(), Tracked::assume_new())
            .unwrap()
            .0
    }

    fn event() -> Event {
        let store = HistoryStore::new(3);
        let mut slots = [0; 3];
        for (index, bytes) in [b"alice".as_slice(), b"edit".as_slice(), b"doc".as_slice()]
            .into_iter()
            .enumerate()
        {
            slots[index] = store
                .intern(
                    history_syntax::Component::new(index),
                    bytes,
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
        }
        Event::from_encoded(&slots)
    }

    #[test]
    fn append_memory_failures_preserve_sequence_and_revision() {
        let event = event();
        let mut stored = StoredHistory::new(fresh_key());
        stored
            .append_events(&[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        for fail_at in [1, 2] {
            let mut limits = FailMemory {
                observations: 0,
                fail_at,
            };
            assert!(matches!(
                stored.append_events(&[event, event], &mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            assert_eq!(stored.events, [event]);
            assert_eq!(stored.len(), 1);
            assert_eq!(stored.revision(), 0);
        }
        stored
            .append_events(&[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(stored.events, [event, event]);
        assert_eq!(stored.revision(), 0);
    }

    #[test]
    fn truncate_revision_exhaustion_fails_before_mutation() {
        let event = event();
        let mut stored = StoredHistory::new(fresh_key());
        stored
            .append_events(&[event, event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        stored.revision = u64::MAX;
        assert!(matches!(
            stored.truncate_events(1),
            Err(HistoryError::RevisionExhausted)
        ));
        assert_eq!(stored.events, [event, event]);
        assert_eq!(stored.revision(), u64::MAX);
        stored.truncate_events(2).unwrap();
        stored.truncate_events(3).unwrap();
        assert_eq!(stored.events, [event, event]);
        assert_eq!(stored.revision(), u64::MAX);
    }
}

#[cfg(test)]
mod typed_tests {
    use super::*;
    use core::time::Duration;
    use junco_core::limits::LimitError;
    use junco_core::observation::fail_reservations_after;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Actor(u32);

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Path(u32);

    impl history_syntax::KeyHash for Actor {
        fn key_hash(&self) -> u64 {
            history_syntax::key_hash::hash_via_std(self)
        }
    }

    impl history_syntax::KeyHash for Path {
        fn key_hash(&self) -> u64 {
            history_syntax::key_hash::hash_via_std(self)
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct TestEvent {
        actor: Actor,
        path: Path,
    }

    impl TypedEvent for TestEvent {
        type Component = history_syntax::Component3<Actor, (), Path>;
        type Arity = history_syntax::N3;

        fn component(self, index: usize) -> Self::Component {
            (self.actor, (), self.path).component(index)
        }

        fn coordinate(component: Self::Component) -> usize {
            <(Actor, (), Path) as TypedEvent>::coordinate(component)
        }
    }

    fn read(actor: Actor) -> TestEvent {
        TestEvent {
            actor,
            path: Path(0),
        }
    }

    fn store() -> Arc<Store<TestEvent>> {
        Arc::new(Store::new().unwrap())
    }

    fn assert_unchanged(
        history: &History<TestEvent>,
        raw: &[TestEvent],
        numeric: &[Event],
        revision: u64,
    ) {
        assert_eq!(history.as_slice(), raw);
        assert_eq!(history.numeric.events, numeric);
        assert_eq!(history.numeric.revision, revision);
    }

    #[test]
    fn clone_is_an_equal_new_owner_at_revision_zero() {
        let store = store();
        let mut original = History::from_events(
            store.clone(),
            [read(Actor(1)), read(Actor(2)), read(Actor(3))],
        )
        .unwrap();
        original.truncate(2).unwrap();
        assert_eq!(original.numeric.revision, 1);

        let clone = original.try_clone().unwrap();
        assert_eq!(clone, original);
        assert_ne!(clone.id(), original.id());
        assert_eq!(clone.numeric.revision, 0);
        assert_eq!(clone.numeric.events, original.numeric.events);
        assert!(Arc::ptr_eq(clone.store(), original.store()));

        let other_owner = History::from_events(self::store(), original.iter().copied()).unwrap();
        assert_eq!(other_owner, original);
        assert_eq!(
            alloc::format!("{:?}", clone),
            alloc::format!("{:?}", original)
        );
    }

    #[test]
    fn only_real_shortening_advances_the_revision() {
        let mut history = History::new(store()).unwrap();
        let empty = history.checkpoint();
        history.push(read(Actor(1))).unwrap();
        history.push(read(Actor(2))).unwrap();
        assert_eq!(history.numeric.revision, 0);

        history.truncate(2).unwrap();
        history.truncate(5).unwrap();
        history.rollback(history.checkpoint()).unwrap();
        assert_eq!(history.numeric.revision, 0);

        history.truncate(1).unwrap();
        assert_eq!(history.numeric.revision, 1);
        assert_eq!(history.as_slice(), [read(Actor(1))]);

        history.push(read(Actor(3))).unwrap();
        assert_eq!(history.numeric.revision, 1);
        history.rollback(empty).unwrap();
        assert_eq!(history.numeric.revision, 2);
        assert!(history.is_empty());
        assert!(history.numeric.events.is_empty());
    }

    #[test]
    fn byte_and_typed_records_share_one_key_space() {
        use crate::store::HistoryStore;
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        struct Other(u8);
        impl TypedEvent for Other {
            type Component = history_syntax::Component3<u8, u8, u8>;
            type Arity = history_syntax::N3;

            fn component(self, index: usize) -> Self::Component {
                (self.0, self.0, self.0).component(index)
            }

            fn coordinate(component: Self::Component) -> usize {
                <(u8, u8, u8) as TypedEvent>::coordinate(component)
            }
        }
        let bytes = HistoryStore::new(3);
        let byte_first = bytes
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let byte_second = bytes
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let view = store();
        let first = History::new(view.clone()).unwrap();
        let second = History::new(view.clone()).unwrap();
        let from_events = History::from_events(view.clone(), [read(Actor(1))]).unwrap();
        let fork = from_events.try_clone().unwrap();
        let other_view = History::new(store()).unwrap();
        let other_event =
            History::from_events(Arc::new(Store::new().unwrap()), [Other(1)]).unwrap();
        assert!(Arc::ptr_eq(view.numeric_store(), &bytes));
        assert!(Arc::ptr_eq(other_event.store().numeric_store(), &bytes));
        assert_eq!(
            bytes.history_record(&byte_first).unwrap().read().id(),
            byte_first.index()
        );
        assert_eq!(fork.numeric().id(), fork.id());
        let keys = [
            byte_first.index(),
            byte_second.index(),
            first.id(),
            second.id(),
            from_events.id(),
            fork.id(),
            other_view.id(),
            other_event.id(),
        ];
        let distinct: alloc::collections::BTreeSet<_> = keys.iter().copied().collect();
        assert_eq!(distinct.len(), keys.len());
        assert!(keys.iter().all(|key| *key > 0));
    }

    struct FailLimits {
        checkpoint: bool,
        memory_calls: usize,
        fail_memory_at: usize,
    }

    impl Limits for FailLimits {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            if self.checkpoint {
                Err(LimitError::TimeLimitExceeded {
                    elapsed: Duration::from_secs(1),
                    limit: Duration::ZERO,
                })
            } else {
                Ok(())
            }
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            self.memory_calls = self.memory_calls.saturating_add(1);
            if self.memory_calls == self.fail_memory_at {
                Err(LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn append_reservation_failures_preserve_both_sequences_and_revision() {
        // Raw reservation, a new principal, then numeric reservation are separate failure leaves.
        for successful_reservations in 0..3 {
            let mut history = History::from_events(store(), [read(Actor(1))]).unwrap();
            let numeric = history.numeric.events.clone();
            {
                let _failure = fail_reservations_after(successful_reservations);
                assert!(matches!(
                    history.push(read(Actor(2))),
                    Err(HistoryError::AllocationFailed)
                ));
            }
            assert_unchanged(&history, &[read(Actor(1))], &numeric, 0);
            history.push(read(Actor(2))).unwrap();
            assert_eq!(history.as_slice(), [read(Actor(1)), read(Actor(2))]);
            assert_eq!(history.numeric.events.len(), 2);
            assert_eq!(history.numeric.revision, 0);
        }
    }

    #[test]
    fn append_checkpoint_and_memory_failures_preserve_both_sequences() {
        let mut history = History::from_events(store(), [read(Actor(1))]).unwrap();
        let numeric = history.numeric.events.clone();
        for (checkpoint, fail_memory_at) in [(true, 0), (false, 1), (false, 2)] {
            let mut limits = FailLimits {
                checkpoint,
                memory_calls: 0,
                fail_memory_at,
            };
            assert!(matches!(
                history.push_with(read(Actor(2)), &mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            assert_unchanged(&history, &[read(Actor(1))], &numeric, 0);
        }
        history.push(read(Actor(2))).unwrap();
        assert_eq!(history.len(), 2);
    }

    #[test]
    fn clone_failures_never_modify_the_original() {
        let history = History::from_events(store(), [read(Actor(1)), read(Actor(2))]).unwrap();
        let numeric = history.numeric.events.clone();
        for successful_reservations in [0, 1] {
            let _failure = fail_reservations_after(successful_reservations);
            assert!(matches!(
                history.try_clone(),
                Err(HistoryError::AllocationFailed)
            ));
            assert_unchanged(&history, &[read(Actor(1)), read(Actor(2))], &numeric, 0);
        }
        for (checkpoint, fail_memory_at) in [(true, 0), (false, 1), (false, 2)] {
            let mut limits = FailLimits {
                checkpoint,
                memory_calls: 0,
                fail_memory_at,
            };
            assert!(matches!(
                history.try_clone_with(&mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            assert_unchanged(&history, &[read(Actor(1)), read(Actor(2))], &numeric, 0);
        }
    }

    #[test]
    fn invalid_checkpoints_and_revision_exhaustion_fail_before_mutation() {
        let store = store();
        let mut history =
            History::from_events(store.clone(), [read(Actor(1)), read(Actor(2))]).unwrap();
        let future = history.checkpoint();
        history.truncate(1).unwrap();
        let numeric = history.numeric.events.clone();
        let foreign = History::from_events(store, [read(Actor(1)), read(Actor(2))])
            .unwrap()
            .checkpoint();
        let foreign_store = History::from_events(self::store(), [read(Actor(1)), read(Actor(2))])
            .unwrap()
            .checkpoint();
        for checkpoint in [foreign, foreign_store] {
            assert_eq!(
                history.rollback(checkpoint),
                Err(HistoryError::WrongCheckpointOwner)
            );
            assert_unchanged(&history, &[read(Actor(1))], &numeric, 1);
        }
        assert_eq!(
            history.rollback(future),
            Err(HistoryError::CheckpointBeyondHistory)
        );
        assert_unchanged(&history, &[read(Actor(1))], &numeric, 1);

        history.numeric.revision = u64::MAX;
        assert_eq!(history.truncate(0), Err(HistoryError::RevisionExhausted));
        assert_unchanged(&history, &[read(Actor(1))], &numeric, u64::MAX);
        history.truncate(1).unwrap();
        history.truncate(usize::MAX).unwrap();
        history.rollback(history.checkpoint()).unwrap();
        assert_unchanged(&history, &[read(Actor(1))], &numeric, u64::MAX);
        let clone = history.try_clone().unwrap();
        assert_eq!(clone.numeric.revision, 0);
        assert_eq!(clone.numeric.events, numeric);
        assert_ne!(clone.id(), history.id());
    }
}

#[cfg(test)]
mod typed_copy_tests {
    use super::*;
    use core::sync::atomic::{AtomicUsize, Ordering};

    static PROJECTIONS: AtomicUsize = AtomicUsize::new(0);

    #[derive(Copy, Debug, PartialEq, Eq, Hash)]
    struct CopyOnly(u8);

    #[allow(
        clippy::non_canonical_clone_impl,
        reason = "Regression fixture rejects user Clone calls; production forks copy Copy events"
    )]
    impl Clone for CopyOnly {
        fn clone(&self) -> Self {
            panic!("a history fork must copy events, not invoke user Clone")
        }
    }

    impl TypedEvent for CopyOnly {
        type Component = history_syntax::Component3<u8, u8, u8>;
        type Arity = history_syntax::N3;

        fn component(self, index: usize) -> Self::Component {
            PROJECTIONS.fetch_add(1, Ordering::Relaxed);
            (self.0, self.0, self.0).component(index)
        }

        fn coordinate(component: Self::Component) -> usize {
            <(u8, u8, u8) as TypedEvent>::coordinate(component)
        }
    }

    #[test]
    fn fork_copies_both_sequences_without_projection_or_user_clone() {
        let store = Arc::new(Store::new().unwrap());
        let mut history = History::from_events(store, [CopyOnly(1), CopyOnly(2)]).unwrap();
        PROJECTIONS.store(0, Ordering::Relaxed);
        let clone = history.try_clone().unwrap();
        assert_eq!(PROJECTIONS.load(Ordering::Relaxed), 0);
        assert_eq!(clone.as_slice(), history.as_slice());
        assert_eq!(clone.numeric.events, history.numeric.events);
        assert_eq!(
            history.rollback(clone.checkpoint()),
            Err(HistoryError::WrongCheckpointOwner)
        );
        assert_eq!(history.len(), 2);
        assert_eq!(history.numeric.revision, 0);
    }
}

#[cfg(test)]
mod arity_tests {
    use super::*;
    use crate::store::HistoryStore;
    use alloc::collections::BTreeSet;

    #[test]
    fn history_keys_do_not_alias_across_event_arities() {
        let mut keys = BTreeSet::new();
        for arity in 1..=history_syntax::MAX_ARITY {
            let store = HistoryStore::new(arity);
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            assert!(keys.insert(history.index()));
        }
        let pair = History::from_events(Arc::new(Store::new().unwrap()), [(1_u8, 2_u8)]).unwrap();
        let quartet =
            History::from_events(Arc::new(Store::new().unwrap()), [(1_u8, 2_u8, 3_u8, 4_u8)])
                .unwrap();
        assert!(keys.insert(pair.id()));
        assert!(keys.insert(quartet.id()));
        assert_eq!(pair.numeric.events[0].arity(), 2);
        assert_eq!(quartet.numeric.events[0].arity(), 4);
    }
}

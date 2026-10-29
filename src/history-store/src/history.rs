// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Numeric and typed committed histories with failure-atomic mutation.

#[cfg(verus_keep_ghost)]
use self::verify::*;
use crate::graph::allocation;
use crate::store::Event;
use crate::typed::Store;
#[cfg(verus_keep_ghost)]
use crate::typed::verify as books;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use history_syntax::Event as TypedEvent;
use junco_core::error::HistoryError;
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
}

#[verus_verify]
impl StoredHistory {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn spec_revision(&self) -> u64 { self.revision }
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

    #[verus_spec(result => ensures result.events@ == Seq::<Event>::empty(), result.revision == 0)]
    pub(crate) const fn new() -> Self {
        Self {
            events: Vec::new(),
            revision: 0,
        }
    }

    #[verus_spec(result =>
        ensures final(self).revision == old(self).revision,
            result is Err ==> final(self).events@ == old(self).events@,
            result is Ok ==> final(self).events@ == old(self).events@ + events@,
            junco_core::verify::history_specs::history_mutation(old(self)@, final(self)@),
    )]
    pub(crate) fn append_events<L: Limits>(
        &mut self,
        events: &[Event],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        proof! { reveal(<StoredHistory as View>::view); }
        proof_decl! { let ghost entry_events = self.events@; }
        let previous = self.events.len();
        allocation(world.try_reserve_vec(&mut self.events, events.len()))?;
        limits.enforce_memory()?;
        self.events.extend_from_slice(events);
        if let Err(error) = limits.enforce_memory() {
            self.events.truncate(previous);
            return Err(error.into());
        }
        proof! {
            assert(crate::store::verify::events_view(self.events@)
                =~= crate::store::verify::events_view(entry_events)
                    + crate::store::verify::events_view(events@));
        }
        Ok(())
    }

    #[verus_spec(result =>
        ensures result is Err ==> final(self)@ == old(self)@
                && final(self).events@ == old(self).events@ && final(self).revision == old(self).revision,
            junco_core::verify::history_specs::history_mutation(old(self)@, final(self)@),
            result is Ok && len < old(self).events@.len() ==> final(self).revision == old(self).revision + 1
                && final(self).events@ == old(self).events@.take(len as int),
            result is Ok && len >= old(self).events@.len() ==> final(self)@ == old(self)@
                && final(self).events@ == old(self).events@ && final(self).revision == old(self).revision,
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
    pub(crate) id: usize,
    #[cfg(verus_keep_ghost)]
    pub(crate) maps: Ghost<books::ComponentMaps<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) lifecycle: Tracked<Lifecycle>,
    #[cfg(verus_keep_ghost)]
    pub(crate) registration: Tracked<books::HistoryRegistration>,
}

// Sharing an Arc changes only its native reference count, not the owned store.
#[verus_verify(external_body)]
#[verus_spec(result => ensures result == *store, *result == **store)]
fn share_store<E: TypedEvent>(store: &Arc<Store<E>>) -> Arc<Store<E>> {
    Arc::clone(store)
}

#[verus_verify]
impl<E: TypedEvent> History<E> {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn spec_id(&self) -> usize { self.id }
        pub closed spec fn spec_numeric(&self) -> &StoredHistory { &self.numeric }
    }

    #[cfg_attr(verus_keep_ghost, verifier::when_used_as_spec(spec_id))]
    #[verus_spec(result => ensures result == self.spec_id())]
    pub const fn id(&self) -> usize {
        self.id
    }

    #[cfg_attr(verus_keep_ghost, verifier::when_used_as_spec(spec_numeric))]
    #[verus_spec(result => ensures *result == *self.spec_numeric())]
    pub fn numeric(&self) -> &StoredHistory {
        &self.numeric
    }

    /// Creates an empty history in `store`, with a fresh local identity.
    #[verus_spec(result =>
        requires books::store_wf(*store),
        ensures result matches Ok(history) ==> history_wf(history) && empty_history(history, store),
    )]
    pub fn new(store: Arc<Store<E>>) -> Result<Self, HistoryError> {
        proof! { books::lemma_empty_snapshot(&*store); }
        let numeric = StoredHistory::new();
        proof! { reveal(<StoredHistory as View>::view); }
        proof_decl! { let tracked lifecycle = Lifecycle::new(numeric@); }
        #[cfg(verus_keep_ghost)]
        let (id, registration) = store.allocate_history_id_for_resource(
            verus_exec_expr! { Ghost(lifecycle.id()) },
            verus_exec_expr! { Tracked(None) },
        )?;
        #[cfg(not(verus_keep_ghost))]
        let id = store.allocate_history_id()?;
        proof! {
            if books::native_obligations::<E>() { books::lemma_empty_maps_wf::<E>(); }
        }
        Ok(Self {
            events: Vec::new(),
            numeric,
            store,
            id,
            #[cfg(verus_keep_ghost)]
            maps: verus_exec_expr! { Ghost(books::empty_maps::<E>()) },
            #[cfg(verus_keep_ghost)]
            lifecycle: verus_exec_expr! { Tracked(lifecycle) },
            #[cfg(verus_keep_ghost)]
            registration,
        })
    }

    /// Creates a history by committing the supplied events in iteration order.
    #[verus_spec(result =>
        requires books::store_wf(*store),
        ensures result matches Ok(history) ==> history_wf(history) && initialized_history(history, store),
    )]
    pub fn from_events<I: IntoIterator<Item = E>>(
        store: Arc<Store<E>>,
        events: I,
    ) -> Result<Self, HistoryError> {
        Self::from_iterator(store, events.into_iter())
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
    )]
    pub fn push(&mut self, event: E) -> Result<(), HistoryError> {
        self.push_with(event, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result =>
        requires history_wf(*old(self)),
        ensures history_wf(*final(self)), push_result(*old(self), *final(self), event, result),
    )]
    pub fn push_with<L: Limits>(
        &mut self,
        event: E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        proof_decl! { let ghost before = *self; }
        proof! { reveal(<StoredHistory as View>::view); }
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
            if books::native_obligations::<E>() {
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
            if books::native_obligations::<E>() {
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
            assert(self.numeric.revision == before.numeric.revision);
            assert(junco_core::verify::history_specs::history_mutation(before.numeric@, self.numeric@));
            assert(self.numeric.events@.drop_last() == before.numeric.events@);
            if books::native_obligations::<E>() {
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
            if books::native_obligations::<E>() {
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
        if checkpoint.store_id != self.store.id() || checkpoint.history != self.id {
            return Err(HistoryError::WrongCheckpointOwner);
        }
        if checkpoint.len > self.events.len() {
            return Err(HistoryError::CheckpointBeyondHistory);
        }
        self.truncate(checkpoint.len)
    }

    /// Copies raw and numeric events without invoking user projections or `Clone`.
    /// The fork shares codebooks, but has a fresh identity and revision zero.
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
        let mut numeric = StoredHistory::new();
        allocation(world.try_reserve_vec_exact(&mut numeric.events, self.numeric.events.len()))?;
        limits.enforce_memory()?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant index <= self.events@.len(),
            events@ == self.events@.take(index as int),
            numeric.events@ == self.numeric.events@.take(index as int), numeric.revision == 0,
            history_wf(*self),
            decreases self.events@.len() - index))]
        while index < self.events.len() {
            limits.checkpoint()?;
            events.push(self.events[index]);
            numeric.events.push(self.numeric.events[index]);
            index += 1;
        }
        limits.enforce_memory()?;
        proof! { reveal(<StoredHistory as View>::view); }
        proof_decl! { let tracked lifecycle = Lifecycle::new(numeric@); }
        #[cfg(verus_keep_ghost)]
        let (id, registration) = self.store.allocate_history_id_for_resource(
            verus_exec_expr! { Ghost(lifecycle.id()) },
            verus_exec_expr! { Tracked(Some(self.registration.borrow())) },
        )?;
        #[cfg(not(verus_keep_ghost))]
        let id = self.store.allocate_history_id()?;
        let clone = Self {
            events,
            numeric,
            store: share_store(&self.store),
            id,
            #[cfg(verus_keep_ghost)]
            maps: self.maps,
            #[cfg(verus_keep_ghost)]
            lifecycle: verus_exec_expr! { Tracked(lifecycle) },
            #[cfg(verus_keep_ghost)]
            registration,
        };
        proof! {
            assert(clone.events@ == self.events@);
            assert(clone.numeric.events@ == self.numeric.events@);
            assert(clone.numeric.revision == 0);
            assert(clone.store == self.store);
            assert(clone.id > self.id);
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
            history: self.id,
            len: self.events.len(),
        }
    }

    /// Returns the shared store binding this history's numeric events.
    #[verus_spec(result => ensures *result == store_of(*self))]
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
    use junco_core::verify::dsl::EventView;
    use junco_core::verify::history_specs::{
        HistoryStateView, history_mutation, lemma_revision_chain_preserves_prefix,
    };
    use vstd::prelude::*;
    use vstd::resource::Loc;
    use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};

    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

    pub open(super) spec fn stored_events(stored: &StoredHistory) -> Seq<Event> { stored.events@ }


    impl<E: TypedEvent> History<E> {
        pub open(super) spec fn lifecycle_model(&self) -> Lifecycle { self.lifecycle@ }
        pub open(super) spec fn registration_model(&self) -> books::HistoryRegistration { self.registration@ }

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
    }

    pub proof fn lemma_history_wf<E: TypedEvent>(history: History<E>)
        requires history_wf(history),
        ensures books::store_wf(*store_of(history)),
            history.registration_model().id() == books::registry_id::<E>(&*store_of(history)),
            history.registration_model().key() == history.spec_id(),
            raw_events(history).len() == stored_events(history.spec_numeric()).len(),
            history.lifecycle_model().wf(), history.lifecycle_model().state() == (*history.spec_numeric())@,
            history.lifecycle_model().id() == history.registration_model().value(),
            books::native_obligations::<E>() ==> books::maps_wf::<E>(history_maps(history))
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
            && checkpoint.history == history.id && checkpoint.len == history.events@.len()
    }

    pub open(super) spec fn rollback_result<E: TypedEvent>(before: History<E>, after: History<E>,
        checkpoint: Checkpoint, result: Result<(), HistoryError>) -> bool {
        owner_frame(before, after)
        && (result is Err ==> state_frame(before, after))
        && (result is Ok ==> truncate_result(before, after, checkpoint.len, result))
        && (checkpoint.store_id != books::store_id(*before.store) || checkpoint.history != before.id
            ==> result == Err(HistoryError::WrongCheckpointOwner))
        && (checkpoint.store_id == books::store_id(*before.store) && checkpoint.history == before.id
            && checkpoint.len > before.events@.len() ==> result == Err(HistoryError::CheckpointBeyondHistory))
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
        && history.registration@.key() == history.id
        && history.events@.len() == history.numeric.events@.len()
        && history.lifecycle@.wf() && history.lifecycle@.state() == history.numeric@
        && history.lifecycle@.id() == history.registration@.value()
        && (books::native_obligations::<E>() ==> books::maps_wf::<E>(history.maps@)
            && books::snapshot_published::<E>(books::registry_id::<E>(&history.store), history.maps@)
            && correspondence(history.events@, history.numeric.events@, history.maps@))
    }

    pub open spec fn raw_event<E: TypedEvent>(event: E)
        -> EventView<E::Principal, E::Action, E::Resource>
    {
        books::projection::<E>(event)
    }

    pub open spec fn raw_word<E: TypedEvent>(history: History<E>)
        -> Seq<EventView<E::Principal, E::Action, E::Resource>>
    {
        raw_events(history).map(|i: int, event: E| raw_event(event))
    }

    pub open(super) spec fn owner_frame<E: TypedEvent>(before: History<E>, after: History<E>) -> bool {
        after.store == before.store && after.id == before.id
            && after.lifecycle@.id() == before.lifecycle@.id()
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
        && after.numeric.revision == before.numeric.revision
        && junco_core::verify::history_specs::history_mutation(before.numeric@, after.numeric@)
        && (books::native_obligations::<E>() ==> books::maps_extend::<E>(before.maps@, after.maps@))
        && match result {
            Err(_) => state_frame(before, after),
            Ok(()) => after.events@ == before.events@.push(event)
                && after.numeric.events@.drop_last() == before.numeric.events@,
        }
    }

    pub open(super) spec fn truncate_result<E: TypedEvent>(
        before: History<E>, after: History<E>, len: usize, result: Result<(), HistoryError>,
    ) -> bool {
        history_wf(after) && owner_frame(before, after) && after.maps@ == before.maps@
        && junco_core::verify::history_specs::history_mutation(before.numeric@, after.numeric@)
        && match result {
            Err(_) => state_frame(before, after),
            Ok(()) => if len < before.events@.len() {
                after.events@ == before.events@.take(len as int)
                && after.numeric.events@ == before.numeric.events@.take(len as int)
                && after.numeric.revision == before.numeric.revision + 1
            } else { state_frame(before, after) },
        }
    }

    pub open(super) spec fn clone_result<E: TypedEvent>(before: History<E>, after: History<E>) -> bool {
        history_wf(after) && after.store == before.store && after.id > before.id
        && after.events@ == before.events@ && after.numeric.events@ == before.numeric.events@
        && after.numeric.revision == 0 && after.maps@ == before.maps@
    }

    pub proof fn lemma_clone_raw_word<E: TypedEvent>(before: History<E>, after: History<E>)
        requires clone_result(before, after),
        ensures raw_word(after) == raw_word(before),
    {}

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

    fn event() -> Event {
        let store = HistoryStore::new();
        Event {
            principal: store
                .intern_principal("alice", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
            action: store
                .intern_action("edit", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
            resource: store
                .intern_resource("doc", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
        }
    }

    #[test]
    fn append_memory_failures_preserve_sequence_and_revision() {
        let event = event();
        let mut stored = StoredHistory::new();
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
        let mut stored = StoredHistory::new();
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

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct TestEvent {
        actor: Actor,
        path: Path,
    }

    impl TypedEvent for TestEvent {
        type Principal = Actor;
        type Action = ();
        type Resource = Path;

        fn principal(self) -> Actor {
            self.actor
        }
        fn action(self) {}
        fn resource(self) -> Path {
            self.path
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
        assert_ne!(clone.id, original.id);
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
    fn every_constructor_allocates_a_distinct_identity() {
        let store = store();
        let first = History::new(store.clone()).unwrap();
        let second = History::new(store.clone()).unwrap();
        let from_events = History::from_events(store.clone(), [read(Actor(1))]).unwrap();
        let clone = from_events.try_clone().unwrap();
        let ids = [first.id, second.id, from_events.id, clone.id];
        for (index, id) in ids.iter().enumerate() {
            assert!(!ids[index + 1..].contains(id));
        }
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
        assert_ne!(clone.id, history.id);
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
        type Principal = u8;
        type Action = u8;
        type Resource = u8;

        fn principal(self) -> u8 {
            PROJECTIONS.fetch_add(1, Ordering::Relaxed);
            self.0
        }
        fn action(self) -> u8 {
            PROJECTIONS.fetch_add(1, Ordering::Relaxed);
            self.0
        }
        fn resource(self) -> u8 {
            PROJECTIONS.fetch_add(1, Ordering::Relaxed);
            self.0
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

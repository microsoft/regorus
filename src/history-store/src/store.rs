// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Exact-byte identities and application-owned synchronized numeric histories.

use crate::graph::allocation;
use crate::history::StoredHistory;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use junco_core::error::HistoryError;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(feature = "std")]
use parking_lot::{Mutex, RwLock, RwLockReadGuard};
#[cfg(not(feature = "std"))]
use spin::{Mutex, RwLock, RwLockReadGuard};
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

// Only allocation is global; paths, membership and histories belong to each store.
static NEXT_IDS: spin::Mutex<[u64; 3]> = spin::Mutex::new([1; 3]);

/// An interned principal identity, local to its owning store.
#[verus_verify]
#[verus_verify(external_derive)]
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Principal(u64);
#[verus_verify]
impl Principal {
    /// Return the full-width identity.
    #[verus_spec(result => ensures result == self@)]
    pub const fn get(self) -> u64 {
        proof! { reveal(<Principal as View>::view); }
        self.0
    }
}

/// An interned action identity, local to its owning store.
#[verus_verify]
#[verus_verify(external_derive)]
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Action(u64);
#[verus_verify]
impl Action {
    /// Return the full-width identity.
    #[verus_spec(result => ensures result == self@)]
    pub const fn get(self) -> u64 {
        proof! { reveal(<Action as View>::view); }
        self.0
    }
}

/// An interned resource identity, local to its owning store.
#[verus_verify]
#[verus_verify(external_derive)]
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Resource(u64);
#[verus_verify]
impl Resource {
    /// Return the full-width identity.
    #[verus_spec(result => ensures result == self@)]
    pub const fn get(self) -> u64 {
        proof! { reveal(<Resource as View>::view); }
        self.0
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl View for Principal {
    type V = nat;
    closed spec fn view(&self) -> nat { self.0 as nat }
}
impl View for Action {
    type V = nat;
    closed spec fn view(&self) -> nat { self.0 as nat }
}
impl View for Resource {
    type V = nat;
    closed spec fn view(&self) -> nat { self.0 as nat }
}

impl View for Domain {
    type V = DomainView;
    closed spec fn view(&self) -> DomainView {
        DomainView { paths: path_map(self.paths), ids: self.ids@ }
    }
}
}

/// The three mandatory coordinates of a history event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Copy, Debug, Eq, PartialEq, Hash)]
pub struct Event {
    pub principal: Principal,
    pub action: Action,
    pub resource: Resource,
}

#[verus_verify]
impl Event {
    #[verus_spec(result => ensures result@ == (junco_core::verify::history_specs::EventView {
        principal: principal as nat, action: action as nat, resource: resource as nat,
    }))]
    pub(crate) const fn from_encoded(principal: u64, action: u64, resource: u64) -> Self {
        proof! {
            reveal(<Principal as View>::view);
            reveal(<Action as View>::view);
            reveal(<Resource as View>::view);
        }
        Self {
            principal: Principal(principal),
            action: Action(action),
            resource: Resource(resource),
        }
    }
}

#[verus_verify]
impl Clone for Event {
    #[verus_spec(result => ensures result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
struct Domain {
    paths: BTreeMap<String, u64>,
    ids: BTreeSet<u64>,
}

#[expect(
    clippy::derivable_impls,
    reason = "Default carries the verified interner and allocator invariants."
)]
#[verus_verify]
impl Default for Domain {
    #[verus_spec(result => ensures domain_wf(result@),
        forall|index: nat| ids_from_allocator(result@.ids, index))]
    fn default() -> Self {
        proof! { reveal(path_map); reveal(<Domain as View>::view); }
        Self {
            paths: BTreeMap::new(),
            ids: BTreeSet::new(),
        }
    }
}

#[verus_verify]
impl Domain {
    // Allocation fails without changing the counter; zero is never issued.
    #[verus_verify]
    #[verus_spec(result => ensures
        match result {
            Ok(id) => id == *old(next) && id > 0 && *final(next) == id + 1,
            Err(_) => *final(next) == *old(next),
        }
    )]
    const fn allocate_id(next: &mut u64, domain: &'static str) -> Result<u64, HistoryError> {
        let id = *next;
        if id == 0 {
            return Err(HistoryError::IdExhausted { domain });
        }
        let following = match id.checked_add(1) {
            Some(following) => following,
            None => return Err(HistoryError::IdExhausted { domain }),
        };
        *next = following;
        Ok(id)
    }

    // Borrowed String keys and native BTree ordering are outside the pinned vstd model.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures match result {
        Some(id) => path_map(*paths).contains_key(vstd::utf8::encode_utf8(path@))
            && path_map(*paths)[vstd::utf8::encode_utf8(path@)] == id as nat,
        None => !path_map(*paths).contains_key(vstd::utf8::encode_utf8(path@)),
    })]
    #[inline]
    fn path_lookup(paths: &BTreeMap<String, u64>, path: &str) -> Option<u64> {
        paths.get(path).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(ensures path_map(*final(paths)) == path_map(*old(paths)).insert(
        vstd::utf8::encode_utf8(path@), id as nat))]
    #[inline]
    fn path_insert(paths: &mut BTreeMap<String, u64>, path: String, id: u64) {
        paths.insert(path, id);
    }

    #[verus_verify(external_body)]
    #[verus_spec(ensures path_map(*final(paths)) == path_map(*old(paths)).remove(
        vstd::utf8::encode_utf8(path@)))]
    #[inline]
    fn path_remove(paths: &mut BTreeMap<String, u64>, path: &str) {
        paths.remove(path);
    }

    // Native mutex invariant: each domain's counter exceeds every ID previously issued there.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        requires domain_wf(self@), ids_from_allocator(self.ids@, index as nat), index < 3,
        ensures result matches Ok(id) ==> 0 < id < u64::MAX
            && allocator_issued(index as nat, id as nat)
            && (forall|old_id: u64| self.ids@.contains(old_id) ==> old_id < id),
    )]
    #[inline]
    // The receiver binds the allocator's freshness guarantee to the owned-ID set.
    #[allow(clippy::unused_self)]
    fn allocate_global(&self, index: usize, domain: &'static str) -> Result<u64, HistoryError> {
        allocate_after(index, domain, 0)
    }

    #[verus_spec(result =>
        requires domain_wf(old(self)@), ids_from_allocator(old(self).ids@, index as nat), index < 3,
        ensures domain_wf(final(self)@), ids_from_allocator(final(self).ids@, index as nat),
            result is Err ==> final(self)@ == old(self)@,
            result matches Ok(id) ==> final(self)@.paths.contains_key(vstd::utf8::encode_utf8(path@))
                && final(self)@.paths[vstd::utf8::encode_utf8(path@)] == id as nat,
            forall|old_path: Seq<u8>| old(self)@.paths.contains_key(old_path)
                ==> final(self)@.paths.contains_key(old_path)
                    && final(self)@.paths[old_path] == old(self)@.paths[old_path],
    )]
    fn intern<L: Limits>(
        &mut self,
        path: &str,
        index: usize,
        domain: &'static str,
        limits: &mut L,
    ) -> Result<u64, HistoryError> {
        proof! { reveal(<Domain as View>::view); reveal(domain_wf); }
        proof_decl! { let ghost entry = self@; }
        if let Some(id) = Self::path_lookup(&self.paths, path) {
            return Ok(id);
        }
        let mut owned = String::new();
        allocation(owned.try_reserve(path.len()))?;
        owned.push_str(path);
        limits.enforce_memory()?;
        let id = self.allocate_global(index, domain)?;
        proof! {
            assert(vstd::utf8::encode_utf8(owned@) == vstd::utf8::encode_utf8(path@));
            assert(entry.ids == self.ids@);
            assert forall|old_path: Seq<u8>| entry.paths.contains_key(old_path)
                implies 0 < entry.paths[old_path] < id as nat by {
                let old_id = entry.paths[old_path] as u64;
                assert(old_id as nat == entry.paths[old_path]);
                assert(entry.paths.values().contains(old_id as nat));
                assert(entry.ids.contains(old_id) <==> entry.paths.values().contains(old_id as nat));
                assert(self.ids@.contains(old_id));
                assert(old_id < id);
            }
            assert(!entry.ids.contains(id));
            assert(junco_core::verify::history_specs::interner_wf(entry.paths, id as nat));
            junco_core::verify::history_specs::lemma_interner_fresh_nonreuse(entry.paths, id as nat,
                vstd::utf8::encode_utf8(path@), id as nat);
        }
        Self::path_insert(&mut self.paths, owned, id);
        self.ids.insert(id);
        if let Err(error) = limits.enforce_memory() {
            // Roll back the mapping, never the allocator: an issued ID must never be reused.
            Self::path_remove(&mut self.paths, path);
            self.ids.remove(&id);
            proof! {
                assert(self@.paths =~= entry.paths);
                assert(self@.ids =~= entry.ids);
            }
            return Err(error.into());
        }
        proof! {
            junco_core::verify::history_specs::lemma_interner_raise_frontier(self@.paths,
                id as nat + 1, u64::MAX as nat);
            assert forall|known_id: u64| self.ids@.contains(known_id)
                <==> self@.paths.values().contains(known_id as nat) by {
                let key = vstd::utf8::encode_utf8(path@);
                let updated = entry.paths.insert(key, id as nat);
                if updated.values().contains(known_id as nat) {
                    let witness = choose|p: Seq<u8>| updated.contains_key(p)
                        && updated[p] == known_id as nat;
                    if witness != key {
                        assert(entry.paths.contains_key(witness));
                        assert(entry.paths[witness] == known_id as nat);
                        assert(entry.paths.values().contains(known_id as nat));
                    }
                }
                if entry.paths.values().contains(known_id as nat) {
                    let witness = choose|p: Seq<u8>| entry.paths.contains_key(p)
                        && entry.paths[p] == known_id as nat;
                    assert(witness != key);
                    assert(updated.contains_key(witness));
                    assert(updated[witness] == known_id as nat);
                    assert(updated.values().contains(known_id as nat));
                }
                if known_id == id {
                    assert(updated.contains_key(key));
                    assert(updated[key] == known_id as nat);
                    assert(updated.values().contains(known_id as nat));
                }
            }
            assert forall|known_id: u64| self.ids@.contains(known_id)
                implies allocator_issued(index as nat, known_id as nat) by {
                if known_id != id { assert(entry.ids.contains(known_id)); }
            }
        }
        Ok(id)
    }

    #[verus_spec(result => requires domain_wf(self@),
        ensures (result is Ok) == self.ids@.contains(id),
            result is Ok ==> self@.paths.values().contains(id as nat))]
    fn validate(&self, id: u64, domain: &'static str) -> Result<(), HistoryError> {
        proof! {
            reveal(<Domain as View>::view);
            reveal(domain_wf);
            assert(self@.ids.contains(id) <==> self@.paths.values().contains(id as nat));
        }
        if self.ids.contains(&id) {
            Ok(())
        } else {
            Err(HistoryError::UnknownId { domain, id })
        }
    }
}

/// Issue a component ID above `last` from the counters shared by byte and typed stores, so a
/// numeric event from one store can never name another store's identity.
#[verus_verify(external_body)]
#[verus_spec(result => ensures result matches Ok(id) ==> last < id < u64::MAX)]
pub(crate) fn allocate_after(
    index: usize,
    domain: &'static str,
    last: u64,
) -> Result<u64, HistoryError> {
    let mut counters = NEXT_IDS.lock();
    let next = counters
        .get_mut(index)
        .ok_or(HistoryError::invariant("invalid identity domain"))?;
    let id = Domain::allocate_id(next, domain)?;
    // Counters only grow; checking keeps the caller's freshness fact out of the trusted contract.
    if id <= last {
        return Err(HistoryError::invariant(
            "identity allocator moved backwards",
        ));
    }
    Ok(id)
}

#[cfg(verus_keep_ghost)]
verus! {
pub mod verify {
    use super::*;
    use junco_core::verify::history_specs as language;
    impl View for Event {
        type V = language::EventView;
        open spec fn view(&self) -> language::EventView {
            language::EventView { principal: self.principal@, action: self.action@, resource: self.resource@ }
        }
    }
    pub open spec fn events_view(events: Seq<Event>) -> Seq<language::EventView> {
        Seq::new(events.len(), |i: int| events[i]@)
    }

    // Default's trait contract is public; its model is visible but predicate bodies stay local.
    pub struct DomainView {
        pub paths: Map<Seq<u8>, nat>,
        pub ids: Set<u64>,
    }

    #[verifier::opaque]
    pub(super) open spec fn path_map(paths: BTreeMap<String, u64>) -> Map<Seq<u8>, nat> {
        Map::new(
            paths@.dom().map(|path: String| vstd::utf8::encode_utf8(path@)),
            |bytes: Seq<u8>| {
                let path = choose|path: String| paths@.contains_key(path)
                    && vstd::utf8::encode_utf8(path@) == bytes;
                paths@[path] as nat
            },
        )
    }


    pub open spec fn domain_wf(domain: DomainView) -> bool {
        language::interner_wf(domain.paths, u64::MAX as nat)
            && (forall|id: u64| domain.ids.contains(id)
                <==> domain.paths.values().contains(id as nat))
    }

    // Historical provenance is maintained by the lock-protected process allocator.
    pub(super) uninterp spec fn allocator_issued(domain: nat, id: nat) -> bool;

    pub open(super) spec fn ids_from_allocator(ids: Set<u64>, domain: nat) -> bool {
        forall|id: u64| ids.contains(id) ==> allocator_issued(domain, id as nat)
    }
}
}

/// Application-owned synchronized identities and histories; no global history state.
#[derive(Debug, Default)]
pub struct HistoryStore {
    principals: Mutex<Domain>,
    actions: Mutex<Domain>,
    resources: Mutex<Domain>,
    histories: Mutex<Vec<Arc<RwLock<StoredHistory>>>>,
}

/// A shared history reference. Cloning it never copies events.
#[derive(Clone, Debug)]
pub struct HistoryHandle {
    pub(crate) owner: Arc<HistoryStore>,
    pub(crate) index: usize,
}

impl HistoryHandle {
    /// Return the never-reused local history index.
    pub const fn index(&self) -> usize {
        self.index
    }

    /// Check the owner without exposing a mutable record or store reference.
    pub fn belongs_to(&self, store: &HistoryStore) -> bool {
        core::ptr::eq(store, self.owner.as_ref())
    }
}

/// A shared read-only history record. Mutations remain transactions on `HistoryStore`.
///
/// A record never grants the write capability needed to replace another history's word:
///
/// ```compile_fail
/// use history_store::store::HistoryRecord;
/// fn swap_histories(left: &HistoryRecord, right: &HistoryRecord) {
///     let mut left = left.read();
///     let mut right = right.read();
///     core::mem::swap(&mut *left, &mut *right);
/// }
/// ```
///
/// ```compile_fail
/// use history_store::store::HistoryRecord;
/// fn write_history(record: &HistoryRecord) {
///     let _guard = record.write();
/// }
/// ```
#[derive(Clone, Debug)]
pub struct HistoryRecord {
    inner: Arc<RwLock<StoredHistory>>,
}

impl HistoryRecord {
    /// Hold a read lock without exposing the underlying lock or its write capability.
    pub fn read(&self) -> HistoryRecordReadGuard<'_> {
        HistoryRecordReadGuard {
            guard: self.inner.read(),
        }
    }
}

/// A borrowed record view. The native guard stays private because it can reveal its lock.
///
/// ```compile_fail
/// use history_store::store::HistoryRecord;
/// fn recover_native_guard(record: &HistoryRecord) {
///     let _native_guard = record.read().guard;
/// }
/// ```
pub struct HistoryRecordReadGuard<'a> {
    guard: RwLockReadGuard<'a, StoredHistory>,
}

impl core::ops::Deref for HistoryRecordReadGuard<'_> {
    type Target = StoredHistory;

    fn deref(&self) -> &Self::Target {
        &self.guard
    }
}

impl HistoryStore {
    /// Create an empty owner. Share it through an `Arc` before creating histories.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern the complete UTF-8 bytes without normalization or prefix matching.
    pub fn intern_principal<L: Limits>(
        &self,
        path: &str,
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<Principal, HistoryError> {
        self.principals
            .lock()
            .intern(path, 0, "principal", limits)
            .map(Principal)
    }

    /// Intern the complete UTF-8 bytes in the action domain.
    pub fn intern_action<L: Limits>(
        &self,
        path: &str,
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<Action, HistoryError> {
        self.actions
            .lock()
            .intern(path, 1, "action", limits)
            .map(Action)
    }

    /// Intern the complete UTF-8 bytes in the resource domain.
    pub fn intern_resource<L: Limits>(
        &self,
        path: &str,
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<Resource, HistoryError> {
        self.resources
            .lock()
            .intern(path, 2, "resource", limits)
            .map(Resource)
    }

    /// Create a history whose lifetime is retained by this owner.
    pub fn new_history<L: Limits>(
        self: &Arc<Self>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<HistoryHandle, HistoryError> {
        let record = Arc::new(RwLock::new(StoredHistory::new()));
        let mut histories = self.histories.lock();
        allocation(world.try_reserve_vec(&mut histories, 1))?;
        limits.enforce_memory()?;
        let index = histories.len();
        histories.push(record);
        if let Err(error) = limits.enforce_memory() {
            histories.pop();
            return Err(error.into());
        }
        Ok(HistoryHandle {
            owner: Arc::clone(self),
            index,
        })
    }

    pub fn validate_event(&self, event: &Event) -> Result<(), HistoryError> {
        self.principals
            .lock()
            .validate(event.principal.get(), "principal")?;
        self.actions.lock().validate(event.action.get(), "action")?;
        self.resources
            .lock()
            .validate(event.resource.get(), "resource")
    }

    /// Borrow a read-only record after checking that the history belongs to this store.
    pub fn history_record(&self, history: &HistoryHandle) -> Result<HistoryRecord, HistoryError> {
        self.history_record_inner(history)
            .map(|inner| HistoryRecord { inner })
    }

    fn history_record_inner(
        &self,
        history: &HistoryHandle,
    ) -> Result<Arc<RwLock<StoredHistory>>, HistoryError> {
        if !core::ptr::eq(self, history.owner.as_ref()) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        self.histories
            .lock()
            .get(history.index)
            .cloned()
            .ok_or(HistoryError::invariant("invalid local history index"))
    }

    /// Atomically append validated events, preserving the history revision.
    pub fn append<L: Limits>(
        &self,
        history: &HistoryHandle,
        events: &[Event],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        let record = self.history_record_inner(history)?;
        if events.is_empty() {
            return Ok(());
        }
        for event in events {
            self.validate_event(event)?;
        }
        let mut stored = record.write();
        stored.append_events(events, limits, world)
    }

    /// Remove a suffix, invalidating prior snapshots only when events are removed.
    pub fn truncate(&self, history: &HistoryHandle, len: usize) -> Result<(), HistoryError> {
        let record = self.history_record_inner(history)?;
        let mut stored = record.write();
        stored.truncate_events(len)
    }

    /// Return the current event count after verifying ownership.
    pub fn len(&self, history: &HistoryHandle) -> Result<usize, HistoryError> {
        let record = self.history_record(history)?;
        let len = record.read().events.len();
        Ok(len)
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::unwrap_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects
    )]

    use super::*;
    use junco_core::limits::Unmetered;

    fn event(store: &HistoryStore) -> Event {
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
    fn read_only_record_clones_observe_store_transactions() {
        let store = Arc::new(HistoryStore::new());
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let retained = record.clone();
        {
            let first = record.read();
            let second = retained.read();
            assert!(core::ptr::eq(&*first, &*second));
            assert_eq!(first.len(), 0);
            assert_eq!(second.revision(), 0);
        }
        store
            .append(
                &history,
                &[event(&store)],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(retained.read().len(), 1);
        assert_eq!(record.read().revision(), 0);
        store.truncate(&history, 0).unwrap();
        assert_eq!(retained.read().len(), 0);
        assert_eq!(record.read().revision(), 1);
    }

    #[test]
    fn exact_identities_and_large_domain() {
        let store = HistoryStore::new();
        let paths = ["a", "A", "/a", "a/", "a\0", "é", "e\u{301}"];
        let mut ids = BTreeSet::new();
        for path in paths {
            let id = store
                .intern_principal(path, &mut Unmetered, &mut ObservationWorld)
                .unwrap();
            assert_eq!(
                id,
                store
                    .intern_principal(path, &mut Unmetered, &mut ObservationWorld)
                    .unwrap()
            );
            assert!(ids.insert(id));
        }
        let first = store
            .intern_resource("common/prefix/0", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        for index in 1..5000 {
            store
                .intern_resource(
                    &alloc::format!("common/prefix/{index}"),
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
        }
        assert_eq!(
            first,
            store
                .intern_resource("common/prefix/0", &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        );
        assert_eq!(store.resources.lock().ids.len(), 5000);
        let action = store
            .intern_action("a", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .intern_principal("new", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(
            action,
            store
                .intern_action("a", &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        );
        let long = "x".repeat(4096);
        assert_ne!(
            store
                .intern_resource(&long, &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
            store
                .intern_resource(&(long + "/"), &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        );
    }

    #[test]
    fn checked_full_width_allocator() {
        let mut next = u64::from(u32::MAX) + 1;
        assert_eq!(
            Domain::allocate_id(&mut next, "principal").unwrap(),
            u64::from(u32::MAX) + 1
        );
        next = u64::MAX - 1;
        assert_eq!(
            Domain::allocate_id(&mut next, "principal").unwrap(),
            u64::MAX - 1
        );
        assert!(matches!(
            Domain::allocate_id(&mut next, "principal"),
            Err(HistoryError::IdExhausted {
                domain: "principal"
            })
        ));
        assert_eq!(next, u64::MAX);
    }

    #[test]
    fn ownership_atomic_append_and_revisions() {
        let store = Arc::new(HistoryStore::new());
        let foreign = Arc::new(HistoryStore::new());
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let valid = event(&store);
        let foreign_event = event(&foreign);
        assert!(matches!(
            foreign.len(&history),
            Err(HistoryError::WrongHistoryOwner)
        ));
        assert!(matches!(
            foreign.append(&history, &[], &mut Unmetered, &mut ObservationWorld),
            Err(HistoryError::WrongHistoryOwner)
        ));
        assert!(matches!(
            store.append(
                &history,
                &[valid, foreign_event],
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::UnknownId {
                domain: "principal",
                ..
            })
        ));
        assert_eq!(store.len(&history).unwrap(), 0);
        assert!(matches!(
            store.validate_event(&Event {
                action: foreign_event.action,
                ..valid
            }),
            Err(HistoryError::UnknownId {
                domain: "action",
                ..
            })
        ));
        assert!(matches!(
            store.validate_event(&Event {
                resource: foreign_event.resource,
                ..valid
            }),
            Err(HistoryError::UnknownId {
                domain: "resource",
                ..
            })
        ));
        store
            .append(
                &history,
                &[valid, valid],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(store.len(&history.clone()).unwrap(), 2);
        let record = store.history_record(&history).unwrap();
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 3).unwrap();
        store.truncate(&history, 2).unwrap();
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 1).unwrap();
        assert_eq!(record.read().revision, 1);
        store
            .history_record_inner(&history)
            .unwrap()
            .write()
            .revision = u64::MAX;
        assert!(matches!(
            store.truncate(&history, 0),
            Err(HistoryError::RevisionExhausted)
        ));
        assert_eq!(store.len(&history).unwrap(), 1);
    }

    #[cfg(feature = "std")]
    #[test]
    fn synchronized_interning_shares_one_identity() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<HistoryStore>();
        let store = Arc::new(HistoryStore::new());
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let store = Arc::clone(&store);
                let barrier = Arc::clone(&barrier);
                std::thread::spawn(move || {
                    barrier.wait();
                    event(&store)
                })
            })
            .collect();
        let events: Vec<_> = threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect();
        assert!(events.iter().all(|event| *event == events[0]));
        assert_eq!(store.principals.lock().paths.len(), 1);
        assert_eq!(store.actions.lock().paths.len(), 1);
        assert_eq!(store.resources.lock().paths.len(), 1);
    }

    #[test]
    fn interning_and_history_creation_roll_back_memory_failures() {
        struct FailMemory {
            calls: usize,
            fail_at: usize,
        }
        impl Limits for FailMemory {
            fn checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn publication_checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn enforce_memory(&mut self) -> Result<(), junco_core::limits::LimitError> {
                self.calls = self.calls.saturating_add(1);
                if self.calls == self.fail_at {
                    Err(junco_core::limits::LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
                } else {
                    Ok(())
                }
            }
        }
        let store = Arc::new(HistoryStore::new());
        let known = store
            .intern_principal("known", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        for fail_at in [1, 2] {
            let mut limits = FailMemory { calls: 0, fail_at };
            assert!(matches!(
                store.intern_principal("new", &mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            let domain = store.principals.lock();
            assert_eq!(domain.paths.len(), 1);
            assert_eq!(domain.ids.len(), 1);
            assert_eq!(domain.paths.get("known"), Some(&known.get()));
            assert!(!domain.paths.contains_key("new"));
            drop(domain);

            let mut limits = FailMemory { calls: 0, fail_at };
            assert!(matches!(
                store.new_history(&mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            assert!(store.histories.lock().is_empty());
        }
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(history.index(), 0);
        assert!(history.belongs_to(&store));
        assert!(!history.belongs_to(&HistoryStore::new()));
        assert_eq!(store.len(&history).unwrap(), 0);
    }
}

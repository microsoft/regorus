// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Process-wide exact-byte identities and synchronized numeric histories.

use crate::history::StoredHistory;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_syntax::{Component, MAX_ARITY};
use junco_core::errors::HistoryError;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(feature = "std")]
use parking_lot::{Mutex, RwLock, RwLockReadGuard};
#[cfg(not(feature = "std"))]
use spin::{Mutex, RwLock, RwLockReadGuard};

// Per-arity byte domains share one process-wide numeric issuance authority.
static STORES: spin::Mutex<Option<StoreRegistry>> = spin::Mutex::new(None);

struct StoreRegistry {
    authorities: Arc<NumericAuthorities>,
    stores: [Option<Arc<HistoryStore>>; MAX_ARITY],
}

/// Map a failed native reservation to `AllocationFailed`.
pub(crate) fn allocation<T>(result: Result<T, impl core::fmt::Debug>) -> Result<T, HistoryError> {
    match result {
        Ok(value) => Ok(value),
        Err(_) => Err(HistoryError::AllocationFailed),
    }
}

/// An inline numeric event; identity and hashing use only its active coordinates.
#[derive(Copy, Debug)]
pub struct Event {
    pub(crate) arity: u8,
    pub(crate) slots: [u64; MAX_ARITY],
}

impl Event {
    pub(crate) fn from_encoded(values: &[u64]) -> Self {
        assert!(values.len() <= MAX_ARITY);
        let mut slots = [0; MAX_ARITY];
        slots[..values.len()].copy_from_slice(values);
        Self {
            arity: values.len() as u8,
            slots,
        }
    }

    /// Return a coordinate, or zero when the index is outside the active tuple.
    pub fn component(&self, index: usize) -> u64 {
        if index < self.arity as usize {
            self.slots[index]
        } else {
            0
        }
    }

    pub const fn arity(&self) -> usize {
        self.arity as usize
    }

    /// The active coordinates, in component order.
    pub fn active(&self) -> &[u64] {
        &self.slots[..self.arity as usize]
    }
}

impl Clone for Event {
    fn clone(&self) -> Self {
        *self
    }
}

impl PartialEq for Event {
    fn eq(&self, other: &Self) -> bool {
        self.active() == other.active()
    }
}
impl Eq for Event {}

impl core::hash::Hash for Event {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        core::hash::Hash::hash(self.active(), state);
    }
}

#[derive(Debug, Default)]
pub(crate) struct Domain {
    paths: BTreeMap<Vec<u8>, u64>,
    ids: BTreeSet<u64>,
}

impl Domain {
    // Allocation fails without changing the counter; zero is never issued.
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

    fn intern<L: Limits>(
        &mut self,
        path: &[u8],
        index: usize,
        domain: &'static str,
        limits: &mut L,
        numeric_store: &HistoryStore,
    ) -> Result<u64, HistoryError> {
        if let Some(id) = self.paths.get(path).copied() {
            return Ok(id);
        }
        let mut owned = Vec::new();
        allocation(owned.try_reserve(path.len()))?;
        owned.extend_from_slice(path);
        limits.enforce_memory()?;
        let id = numeric_store.allocate_after(index, domain, 0)?;
        self.paths.insert(owned, id);
        self.ids.insert(id);
        if let Err(error) = limits.enforce_memory() {
            // Roll back the mapping, never the allocator: an issued ID must never be reused.
            self.paths.remove(path);
            self.ids.remove(&id);
            return Err(error.into());
        }
        Ok(id)
    }

    fn validate(&self, id: u64, domain: &'static str) -> Result<(), HistoryError> {
        if self.ids.contains(&id) {
            Ok(())
        } else {
            Err(HistoryError::UnknownId { domain, id })
        }
    }
}

/// Advance the process history-key counter, failing at `usize::MAX` without changing it.
fn next_history_id(next: &mut usize) -> Result<usize, HistoryError> {
    let id = *next;
    let following = match id.checked_add(1) {
        Some(following) => following,
        None => return Err(HistoryError::IdExhausted { domain: "history" }),
    };
    *next = following;
    Ok(id)
}

#[derive(Debug)]
pub(crate) struct CoordinateState {
    pub(crate) next: [u64; MAX_ARITY],
}

#[derive(Debug)]
pub(crate) struct HistoryKeyState {
    pub(crate) next: usize,
}

impl CoordinateState {
    pub(crate) const fn new() -> Self {
        Self {
            next: [1; MAX_ARITY],
        }
    }
}

impl HistoryKeyState {
    pub(crate) const fn new() -> Self {
        Self { next: 1 }
    }
}

pub(crate) fn allocate_coordinate_state(
    state: &mut CoordinateState,
    index: usize,
    domain: &'static str,
    last: u64,
) -> Result<u64, HistoryError> {
    let Some(next) = state.next.get_mut(index) else {
        return Err(HistoryError::invariant("invalid identity domain"));
    };
    let id = Domain::allocate_id(next, domain)?;
    if id <= last {
        return Err(HistoryError::invariant(
            "identity allocator moved backwards",
        ));
    }
    Ok(id)
}

pub(crate) fn allocate_history_state(
    state: &mut HistoryKeyState,
    last: usize,
) -> Result<usize, HistoryError> {
    if last == usize::MAX {
        return Err(HistoryError::IdExhausted { domain: "history" });
    }
    let id = next_history_id(&mut state.next)?;
    if id <= last {
        return Err(HistoryError::invariant(
            "history identity allocator moved backwards",
        ));
    }
    Ok(id)
}

/// The process-wide synchronized byte identities and numeric ID allocators.
///
/// Every handle owns its record; this owner never retains histories, runtimes or caches.
#[derive(Debug)]
pub struct HistoryStore {
    pub(crate) domains: Vec<Mutex<Domain>>,
    pub(crate) authorities: Arc<NumericAuthorities>,
}

#[derive(Debug)]
pub(crate) struct NumericAuthorities {
    pub(crate) coordinates: spin::Mutex<CoordinateState>,
    pub(crate) history_keys: spin::Mutex<HistoryKeyState>,
}

/// A shared history reference. Cloning it never copies events.
#[derive(Clone, Debug)]
pub struct HistoryHandle {
    pub(crate) owner: Arc<HistoryStore>,
    pub(crate) index: usize,
    pub(crate) record: Arc<RwLock<StoredHistory>>,
}

impl HistoryHandle {
    /// Return the opaque, never-reused process-wide history ID.
    pub const fn index(&self) -> usize {
        self.index
    }

    /// Check exact native owner identity without exposing the store or a mutable record.
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
    native: Arc<RwLock<StoredHistory>>,
}

impl HistoryRecord {
    /// Hold a read lock without exposing the underlying lock or its write capability.
    pub fn read(&self) -> HistoryRecordReadGuard<'_> {
        HistoryRecordReadGuard {
            guard: self.native.read(),
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
    /// Return the process-wide store for `arity`, sharing numeric issuance across all arities.
    /// Panics unless `1 <= arity <= MAX_ARITY`.
    // No user code runs under the registry lock.
    pub fn new(arity: usize) -> Arc<Self> {
        assert!(
            (1..=MAX_ARITY).contains(&arity),
            "event arity must be between 1 and MAX_ARITY"
        );
        let mut registry = STORES.lock();
        let registry = registry.get_or_insert_with(|| StoreRegistry {
            authorities: Arc::new(NumericAuthorities {
                coordinates: spin::Mutex::new(CoordinateState::new()),
                history_keys: spin::Mutex::new(HistoryKeyState::new()),
            }),
            stores: core::array::from_fn(|_| None),
        });
        if let Some(store) = &registry.stores[arity - 1] {
            return Arc::clone(store);
        }
        let mut domains = Vec::with_capacity(arity);
        for _ in 0..arity {
            domains.push(Mutex::new(Domain::default()));
        }
        let store = Arc::new(Self {
            domains,
            authorities: Arc::clone(&registry.authorities),
        });
        registry.stores[arity - 1] = Some(Arc::clone(&store));
        store
    }

    pub fn arity(&self) -> usize {
        self.domains.len()
    }

    /// Issue a component ID above `last` from the counters shared by every arity,
    /// so a numeric event from one store can never name another store's identity.
    pub(crate) fn allocate_after(
        &self,
        index: usize,
        domain: &'static str,
        last: u64,
    ) -> Result<u64, HistoryError> {
        let mut state = self.authorities.coordinates.lock();
        allocate_coordinate_state(&mut state, index, domain, last)
    }

    /// Issue a never-recycled history ID above `last`.
    pub(crate) fn allocate_history_after(&self, last: usize) -> Result<usize, HistoryError> {
        if last == usize::MAX {
            return Err(HistoryError::IdExhausted { domain: "history" });
        }
        let mut state = self.authorities.history_keys.lock();
        allocate_history_state(&mut state, last)
    }

    /// Intern arbitrary exact bytes in one coordinate; prior bindings survive every outcome.
    /// A coordinate outside this store's arity returns `InvalidPolicy` without touching a domain.
    pub fn intern<L: Limits>(
        &self,
        component: Component,
        bytes: &[u8],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<u64, HistoryError> {
        self.intern_observed(component, bytes, limits, world)
    }

    /// Same as [`Self::intern`]; kept for callers that observe the binding directly.
    #[doc(hidden)]
    pub fn intern_observed<L: Limits>(
        &self,
        component: Component,
        bytes: &[u8],
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<u64, HistoryError> {
        let index = component.index();
        let Some(native) = self.domains.get(index) else {
            return Err(HistoryError::invalid_policy(
                "component",
                "component index is outside event arity",
            ));
        };
        native
            .lock()
            .intern(bytes, index, "component", limits, self)
    }

    /// Create an empty history owned by its handles and read-only records.
    pub fn new_history<L: Limits>(
        self: &Arc<Self>,
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<HistoryHandle, HistoryError> {
        let index = self.allocate_history_after(0)?;
        limits.enforce_memory()?;
        let record = Arc::new(RwLock::new(StoredHistory::new(index)));
        limits.enforce_memory()?;
        Ok(HistoryHandle {
            owner: Arc::clone(self),
            index,
            record,
        })
    }

    /// Build an inline event from IDs belonging to this store's byte domains.
    /// Wrong arity and unknown IDs are rejected before the event is returned.
    pub fn event(&self, slots: &[u64]) -> Result<Event, HistoryError> {
        if slots.len() != self.arity() {
            return Err(HistoryError::invalid_policy(
                "event",
                "event arity does not match store",
            ));
        }
        let event = Event::from_encoded(slots);
        self.validate_event(&event)?;
        Ok(event)
    }

    /// Validate arity, then coordinates in index order at separate read linearizations.
    pub fn validate_event(&self, event: &Event) -> Result<(), HistoryError> {
        if event.arity() != self.arity() {
            return Err(HistoryError::invalid_policy(
                "event",
                "event arity does not match store",
            ));
        }
        for (domain, &id) in self.domains.iter().zip(event.active()) {
            domain.lock().validate(id, "component")?;
        }
        Ok(())
    }

    /// Borrow a read-only record after checking that the history belongs to this store.
    pub fn history_record(&self, history: &HistoryHandle) -> Result<HistoryRecord, HistoryError> {
        Ok(HistoryRecord {
            native: self.history_record_inner(history)?,
        })
    }

    fn history_record_inner(
        &self,
        history: &HistoryHandle,
    ) -> Result<Arc<RwLock<StoredHistory>>, HistoryError> {
        if !history.belongs_to(self) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        Ok(Arc::clone(&history.record))
    }

    /// Atomically append validated events, preserving the history revision.
    /// Ownership and validation errors, and empty input, need no record lock.
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
        record.write().append_events(events, limits, world)
    }

    /// Remove a suffix, invalidating prior snapshots only when events are removed.
    pub fn truncate(&self, history: &HistoryHandle, len: usize) -> Result<(), HistoryError> {
        self.history_record_inner(history)?
            .write()
            .truncate_events(len)
    }

    /// Return the event count observed by a read guard after verifying ownership.
    /// Concurrent callers may change the record after this observation is released.
    pub fn len(&self, history: &HistoryHandle) -> Result<usize, HistoryError> {
        Ok(self.history_record(history)?.read().len())
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
        Event::from_encoded(&[
            store
                .intern(
                    Component(0),
                    b"alice",
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap(),
            store
                .intern(Component(1), b"edit", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
            store
                .intern(Component(2), b"doc", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
        ])
    }

    fn foreign_event() -> Event {
        // Another arity's domains share the numeric counters, so its IDs are never members here.
        let store = HistoryStore::new(4);
        let slots: Vec<u64> = (0..3)
            .map(|index| {
                store
                    .intern(
                        Component(index),
                        b"foreign",
                        &mut Unmetered,
                        &mut ObservationWorld,
                    )
                    .unwrap()
            })
            .collect();
        Event::from_encoded(&slots)
    }

    #[test]
    fn global_owners_share_identities_and_handles() {
        let first = HistoryStore::new(3);
        let second = HistoryStore::new(3);
        assert!(Arc::ptr_eq(&first, &second));
        let principal = first
            .intern(
                Component(0),
                b"global-test/alice",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(
            principal,
            second
                .intern(
                    Component(0),
                    b"global-test/alice",
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap()
        );
        let history = first
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(history.belongs_to(&second));
        second
            .append(
                &history,
                &[event(&first)],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(first.len(&history).unwrap(), 1);
        assert!(matches!(
            first.allocate_history_after(usize::MAX),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
    }

    #[test]
    fn all_arities_share_numeric_authorities_not_byte_domains() {
        let first = HistoryStore::new(1);
        let mut history_ids = BTreeSet::new();
        let mut coordinate_ids: Vec<BTreeSet<u64>> =
            (0..MAX_ARITY).map(|_| BTreeSet::new()).collect();
        for arity in 1..=MAX_ARITY {
            let store = HistoryStore::new(arity);
            assert_eq!(store.arity(), arity);
            assert_eq!(store.domains.len(), arity);
            assert!(Arc::ptr_eq(&store, &HistoryStore::new(arity)));
            assert!(Arc::ptr_eq(&first.authorities, &store.authorities));
            let mut slots = [0; MAX_ARITY];
            for index in 0..arity {
                let bytes = b"all-arities/\xff\x80\0";
                let component = Component(index as u8);
                let id = store
                    .intern(component, bytes, &mut Unmetered, &mut ObservationWorld)
                    .unwrap();
                assert_eq!(
                    id,
                    store
                        .intern(component, bytes, &mut Unmetered, &mut ObservationWorld)
                        .unwrap()
                );
                assert!(coordinate_ids[index].insert(id));
                slots[index] = id;
            }
            let event = store.event(&slots[..arity]).unwrap();
            assert_eq!(event.arity(), arity);
            store.validate_event(&event).unwrap();
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            assert!(history_ids.insert(history.index()));
            store
                .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
                .unwrap();
            if arity != 1 {
                assert!(!history.belongs_to(&first));
                assert!(matches!(
                    first.len(&history),
                    Err(HistoryError::WrongHistoryOwner)
                ));
                assert!(matches!(
                    first.validate_event(&event),
                    Err(HistoryError::InvalidPolicy { .. })
                ));
            }
            for index in [arity as u8, u8::MAX] {
                assert!(matches!(
                    store.intern(
                        Component(index),
                        b"invalid",
                        &mut Unmetered,
                        &mut ObservationWorld
                    ),
                    Err(HistoryError::InvalidPolicy { .. })
                ));
            }
            let malformed = Event::from_encoded(&slots[..arity - 1]);
            assert!(matches!(
                store.event(&slots[..arity - 1]),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert!(matches!(
                store.event(&[1; MAX_ARITY + 1]),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert!(matches!(
                store.event(&[0; MAX_ARITY][..arity]),
                Err(HistoryError::UnknownId {
                    domain: "component",
                    id: 0
                })
            ));
            assert!(matches!(
                store.validate_event(&malformed),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert!(matches!(
                store.append(
                    &history,
                    &[event, malformed],
                    &mut Unmetered,
                    &mut ObservationWorld
                ),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert_eq!(store.len(&history).unwrap(), 1);
            assert_eq!(event.component(arity), 0);
            assert_eq!(event.component(usize::MAX), 0);
        }
    }

    #[test]
    fn numeric_event_equality_and_hash_ignore_inactive_slots() {
        use core::hash::{Hash, Hasher};
        #[derive(Default)]
        struct TestHasher(u64);
        impl Hasher for TestHasher {
            fn finish(&self) -> u64 {
                self.0
            }
            fn write(&mut self, bytes: &[u8]) {
                for byte in bytes {
                    self.0 = self.0.wrapping_mul(31).wrapping_add(u64::from(*byte));
                }
            }
        }
        for arity in 1..=MAX_ARITY {
            let left = Event::from_encoded(&[17; MAX_ARITY][..arity]);
            let mut right = left;
            right.slots[arity..].fill(u64::MAX);
            assert_eq!(left, right);
            let mut left_hash = TestHasher::default();
            let mut right_hash = TestHasher::default();
            left.hash(&mut left_hash);
            right.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
            if arity < MAX_ARITY {
                assert_ne!(left, Event::from_encoded(&[17; MAX_ARITY][..arity + 1]));
            }
        }
    }

    #[test]
    #[should_panic(expected = "event arity must be between 1 and MAX_ARITY")]
    fn zero_store_arity_is_rejected() {
        HistoryStore::new(0);
    }

    #[test]
    #[should_panic(expected = "event arity must be between 1 and MAX_ARITY")]
    fn oversized_store_arity_is_rejected() {
        HistoryStore::new(MAX_ARITY + 1);
    }

    #[test]
    fn read_only_record_clones_observe_store_transactions() {
        let store = HistoryStore::new(3);
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
            assert_eq!(first.id(), history.index());
        }
        let event = event(&store);
        store
            .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(retained.read().len(), 1);
        assert_eq!(record.read().revision(), 0);
        store.truncate(&history, 0).unwrap();
        assert_eq!(retained.read().len(), 0);
        assert_eq!(record.read().revision(), 1);
        store
            .append(
                &history,
                &[event, event],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        // Records keep the buffer alive after the handle; the singleton never retains it.
        let weak = Arc::downgrade(&history.record);
        drop(history);
        assert_eq!(retained.read().as_slice(), [event, event]);
        assert_eq!(retained.read().revision(), 1);
        drop(record);
        drop(retained);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn exact_identities_and_large_domain() {
        let store = HistoryStore::new(3);
        let paths = ["a", "A", "/a", "a/", "a\0", "é", "e\u{301}"];
        let mut ids = BTreeSet::new();
        for path in paths {
            let id = store
                .intern(
                    Component(0),
                    path.as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
            assert_eq!(
                id,
                store
                    .intern(
                        Component(0),
                        path.as_bytes(),
                        &mut Unmetered,
                        &mut ObservationWorld
                    )
                    .unwrap()
            );
            assert!(ids.insert(id));
        }
        let first = store
            .intern(
                Component(2),
                b"common/prefix/0",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let mut resources = BTreeSet::from([first]);
        for index in 1..5000 {
            assert!(
                resources.insert(
                    store
                        .intern(
                            Component(2),
                            alloc::format!("common/prefix/{index}").as_bytes(),
                            &mut Unmetered,
                            &mut ObservationWorld,
                        )
                        .unwrap()
                )
            );
        }
        assert_eq!(
            first,
            store
                .intern(
                    Component(2),
                    b"common/prefix/0",
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap()
        );
        assert_eq!(resources.len(), 5000);
        let action = store
            .intern(Component(1), b"a", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .intern(Component(0), b"new", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(
            action,
            store
                .intern(Component(1), b"a", &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        );
        let long = "x".repeat(4096);
        assert_ne!(
            store
                .intern(
                    Component(2),
                    long.as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap(),
            store
                .intern(
                    Component(2),
                    (long + "/").as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap()
        );
    }

    #[test]
    fn checked_full_width_allocator() {
        let mut next = u64::from(u32::MAX) + 1;
        assert_eq!(
            Domain::allocate_id(&mut next, "component").unwrap(),
            u64::from(u32::MAX) + 1
        );
        next = u64::MAX - 1;
        assert_eq!(
            Domain::allocate_id(&mut next, "component").unwrap(),
            u64::MAX - 1
        );
        assert!(matches!(
            Domain::allocate_id(&mut next, "component"),
            Err(HistoryError::IdExhausted {
                domain: "component"
            })
        ));
        assert_eq!(next, u64::MAX);
    }

    #[test]
    fn checked_history_key_counter() {
        let mut next = 1;
        assert_eq!(next_history_id(&mut next).unwrap(), 1);
        assert_eq!(next, 2);
        next = usize::MAX - 1;
        assert_eq!(next_history_id(&mut next).unwrap(), usize::MAX - 1);
        assert_eq!(next, usize::MAX);
        assert!(matches!(
            next_history_id(&mut next),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(next, usize::MAX);
    }

    #[test]
    fn allocator_failures_preserve_consumed_ids() {
        let mut coordinates = CoordinateState::new();
        assert!(matches!(
            allocate_coordinate_state(&mut coordinates, 0, "component", 1),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(coordinates.next[0], 2);
        assert_eq!(&coordinates.next[1..], &[1; MAX_ARITY - 1]);
        let second = allocate_coordinate_state(&mut coordinates, 0, "component", 0).unwrap();
        assert_eq!(second, 2);
        assert_eq!(coordinates.next[0], 3);
        assert_eq!(&coordinates.next[1..], &[1; MAX_ARITY - 1]);
        assert!(matches!(
            allocate_coordinate_state(&mut coordinates, MAX_ARITY, "invalid", 0),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(coordinates.next[0], 3);
        assert_eq!(&coordinates.next[1..], &[1; MAX_ARITY - 1]);

        let mut histories = HistoryKeyState::new();
        assert!(matches!(
            allocate_history_state(&mut histories, 1),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(histories.next, 2);
        let second = allocate_history_state(&mut histories, 0).unwrap();
        assert_eq!(second, 2);
        assert_eq!(histories.next, 3);
        assert!(matches!(
            allocate_history_state(&mut histories, usize::MAX),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(histories.next, 3);
    }

    #[test]
    fn atomic_append_and_revisions() {
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let valid = event(&store);
        let foreign = foreign_event();
        store
            .append(&history, &[valid], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(matches!(
            store.append(
                &history,
                &[valid, foreign],
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
        let record = store.history_record(&history).unwrap();
        assert_eq!(record.read().as_slice(), [valid]);
        assert_eq!(record.read().revision, 0);
        assert!(matches!(
            store.validate_event(&Event::from_encoded(&[
                valid.component(0),
                foreign.component(1),
                valid.component(2),
            ])),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
        assert!(matches!(
            store.validate_event(&Event::from_encoded(&[
                valid.component(0),
                valid.component(1),
                foreign.component(2),
            ])),
            Err(HistoryError::UnknownId {
                domain: "component",
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
        assert_eq!(store.len(&history.clone()).unwrap(), 3);
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 4).unwrap();
        store.truncate(&history, 3).unwrap();
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 2).unwrap();
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
        assert_eq!(store.len(&history).unwrap(), 2);
    }

    #[cfg(feature = "std")]
    #[test]
    fn synchronized_interning_shares_one_identity() {
        fn assert_send_sync<T: Send + Sync>() {}
        use alloc::vec::Vec;
        assert_send_sync::<HistoryStore>();
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let barrier = Arc::clone(&barrier);
                std::thread::spawn(move || {
                    barrier.wait();
                    let store = HistoryStore::new(3);
                    let history = store
                        .new_history(&mut Unmetered, &mut ObservationWorld)
                        .unwrap();
                    (event(&store), history)
                })
            })
            .collect();
        let results: Vec<_> = threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect();
        let store = HistoryStore::new(3);
        let mut keys = BTreeSet::new();
        for (event, history) in &results {
            assert_eq!(*event, results[0].0);
            assert!(Arc::ptr_eq(&history.owner, &store));
            assert!(history.index() > 0);
            assert!(keys.insert(history.index()));
        }
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
        let store = HistoryStore::new(3);
        let known = store
            .intern(
                Component(0),
                b"rollback-test/known",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        for fail_at in [1, 2] {
            let mut limits = FailMemory { calls: 0, fail_at };
            assert!(matches!(
                store.intern(
                    Component(0),
                    b"rollback-test/new",
                    &mut limits,
                    &mut ObservationWorld
                ),
                Err(HistoryError::Limit(_))
            ));
            let domain = store.domains[0].lock();
            assert_eq!(
                domain.paths.get(b"rollback-test/known".as_slice()),
                Some(&known)
            );
            assert!(!domain.paths.contains_key(b"rollback-test/new".as_slice()));
            drop(domain);

            let mut limits = FailMemory { calls: 0, fail_at };
            assert!(matches!(
                store.new_history(&mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
        }
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(history.index() > 0);
        assert!(history.belongs_to(&store));
        assert_eq!(store.len(&history).unwrap(), 0);
    }
}

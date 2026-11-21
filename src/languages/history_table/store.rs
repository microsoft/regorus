// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Core-owned byte identities and histories, plus the numeric rule tables of loaded programs.

#![allow(clippy::redundant_pub_crate)]

use super::limits::RegorusLimits;
use super::HistoryError;
use crate::rvm::program::Program;
use crate::utils::limits::ExecutionTimer;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
pub use history_store::store::{Event, HistoryHandle};
use history_store::store::{HistoryRecord, HistoryStore as CoreHistoryStore};
use history_syntax::{Component, RuleMode};
use junco_core::compile::{lower_flat, FlatEncoder};
use junco_core::flat::FlatPair;
use junco_core::limits::Limits as _;
use junco_core::observation::ObservationWorld;

/// Coordinates per event: principal, action, resource.
const ARITY: usize = 3;

/// A handle on the process-wide arity-3 history store. Identities and histories are shared by
/// every wrapper; wrapper construction is not an isolation boundary.
#[derive(Debug)]
pub struct HistoryStore {
    core: Arc<CoreHistoryStore>,
}

impl Default for HistoryStore {
    fn default() -> Self {
        Self {
            core: CoreHistoryStore::new(ARITY),
        }
    }
}

/// One program table's rules with constants encoded as store identities.
#[derive(Debug)]
pub(crate) struct HistoryTableRuntime {
    pub(crate) rules: Vec<HistoryRuleSlot>,
}

#[derive(Debug)]
pub(crate) struct HistoryRuleSlot {
    pub(crate) mode: RuleMode,
    pub(crate) template: FlatPair<u64>,
}

struct ByteEncoder<'a> {
    store: &'a HistoryStore,
}

impl FlatEncoder<String> for ByteEncoder<'_> {
    // The byte interner stays in core; this adapter routes each coordinate to its domain.
    fn encode(&mut self, field: Component, value: &String) -> Result<u64, HistoryError> {
        self.store.intern(field, value)
    }
}

impl HistoryStore {
    /// Create a handle on the process-wide identities and histories.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern the complete UTF-8 bytes of one coordinate without normalization or prefix matching.
    pub fn intern(&self, component: Component, path: &str) -> Result<u64, HistoryError> {
        self.core.intern(
            component,
            path.as_bytes(),
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
    }

    /// Build a validated event from one interned ID per coordinate (`[principal, action, resource]`).
    pub fn event(&self, slots: &[u64]) -> Result<Event, HistoryError> {
        self.core.event(slots)
    }

    /// Lower one program table's portable sources onto this store's identities.
    pub(crate) fn table_runtime(
        &self,
        program: &Program,
        table: usize,
    ) -> Result<HistoryTableRuntime, HistoryError> {
        let source = program
            .history_tables
            .get(table)
            .ok_or(HistoryError::Invariant {
                message: "invalid history table index",
            })?;
        let mut rules = Vec::new();
        rules
            .try_reserve_exact(source.rules.len())
            .map_err(|_| HistoryError::AllocationFailed)?;
        let mut timer = ExecutionTimer::new(None);
        let mut limits = RegorusLimits { timer: &mut timer };
        let mut world = ObservationWorld;
        for rule in &source.rules {
            // Deserialized programs may carry any validated arity; bindings would silently skip it.
            if rule.source.head.len() != self.core.arity() {
                return Err(HistoryError::invalid_policy(
                    "head",
                    "history head arity does not match the store",
                ));
            }
            let template = lower_flat(
                &rule.source,
                &mut ByteEncoder { store: self },
                &mut limits,
                &mut world,
            )?;
            rules.push(HistoryRuleSlot {
                mode: rule.mode,
                template,
            });
        }
        limits.enforce_memory()?;
        Ok(HistoryTableRuntime { rules })
    }

    /// Create a history kept alive by its handles and read-only records.
    pub fn new_history(self: &Arc<Self>) -> Result<HistoryHandle, HistoryError> {
        self.core.new_history(
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
    }

    pub(crate) fn validate_event(&self, event: &Event) -> Result<(), HistoryError> {
        self.core.validate_event(event)
    }

    pub(crate) fn history_record(
        &self,
        history: &HistoryHandle,
    ) -> Result<HistoryRecord, HistoryError> {
        self.core.history_record(history)
    }

    /// Atomically append validated events, preserving the history revision.
    pub fn append(&self, history: &HistoryHandle, events: &[Event]) -> Result<(), HistoryError> {
        self.core.append(
            history,
            events,
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
    }

    /// Remove a suffix, invalidating prior snapshots only when events are removed.
    pub fn truncate(&self, history: &HistoryHandle, len: usize) -> Result<(), HistoryError> {
        self.core.truncate(history, len)
    }

    /// Return the current event count after verifying ownership.
    pub fn len(&self, history: &HistoryHandle) -> Result<usize, HistoryError> {
        self.core.len(history)
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::unwrap_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects
    )]

    use super::super::{ACTION, PRINCIPAL, RESOURCE};
    use super::*;
    use alloc::collections::BTreeSet;

    fn event(store: &HistoryStore) -> Event {
        store
            .event(&[
                store.intern(PRINCIPAL, "alice").unwrap(),
                store.intern(ACTION, "edit").unwrap(),
                store.intern(RESOURCE, "doc").unwrap(),
            ])
            .unwrap()
    }

    #[test]
    fn exact_identities_and_large_domain() {
        let store = HistoryStore::new();
        let paths = ["a", "A", "/a", "a/", "a\0", "é", "e\u{301}"];
        let mut ids = BTreeSet::new();
        for path in paths {
            let id = store.intern(PRINCIPAL, path).unwrap();
            assert_eq!(id, store.intern(PRINCIPAL, path).unwrap());
            assert!(ids.insert(id));
        }
        let first = store.intern(RESOURCE, "common/prefix/0").unwrap();
        let mut resources = BTreeSet::from([first]);
        for index in 1..5000 {
            assert!(resources.insert(
                store
                    .intern(RESOURCE, &alloc::format!("common/prefix/{index}"))
                    .unwrap()
            ));
        }
        assert_eq!(first, store.intern(RESOURCE, "common/prefix/0").unwrap());
        assert_eq!(resources.len(), 5000);
        let action = store.intern(ACTION, "a").unwrap();
        store.intern(PRINCIPAL, "new").unwrap();
        assert_eq!(action, store.intern(ACTION, "a").unwrap());
        let long = "x".repeat(4096);
        assert_ne!(
            store.intern(RESOURCE, &long).unwrap(),
            store.intern(RESOURCE, &(long + "/")).unwrap()
        );
    }

    /// An arity-4 event; its IDs come from shared counters, so none is a member here.
    fn foreign_event() -> Event {
        let store = CoreHistoryStore::new(4);
        let mut slots = [0; 4];
        for (index, slot) in slots.iter_mut().enumerate() {
            *slot = store
                .intern(
                    Component::new(index),
                    b"foreign",
                    &mut RegorusLimits {
                        timer: &mut ExecutionTimer::new(None),
                    },
                    &mut ObservationWorld,
                )
                .unwrap();
        }
        store.event(&slots).unwrap()
    }

    #[test]
    fn ownership_atomic_append_and_revisions() {
        let store = Arc::new(HistoryStore::new());
        let peer = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let valid = event(&store);
        // Wrappers share one process-wide identity and history store.
        assert_eq!(event(&peer), valid);
        peer.append(&history, &[]).unwrap();
        assert_eq!(peer.len(&history).unwrap(), 0);
        let foreign = foreign_event();
        // Event fields are private: each foreign coordinate is rejected while building.
        for index in 0..3 {
            let mut slots = [valid.component(0), valid.component(1), valid.component(2)];
            slots[index] = foreign.component(index);
            assert!(matches!(
                store.event(&slots),
                Err(HistoryError::UnknownId { domain: "component", id }) if id == foreign.component(index)
            ));
        }
        assert!(matches!(
            store.append(&history, &[valid, foreign]),
            Err(HistoryError::InvalidPolicy { .. })
        ));
        assert!(matches!(
            peer.validate_event(&foreign),
            Err(HistoryError::InvalidPolicy { .. })
        ));
        assert_eq!(store.len(&history).unwrap(), 0);
        // Generic interning stays within the arity-3 store.
        assert!(matches!(
            store.intern(Component(3), "x"),
            Err(HistoryError::InvalidPolicy { .. })
        ));
        assert!(matches!(
            store.event(&[valid.component(0), valid.component(1)]),
            Err(HistoryError::InvalidPolicy { .. })
        ));
        store.append(&history, &[valid, valid]).unwrap();
        assert_eq!(store.len(&history.clone()).unwrap(), 2);
        let record = store.history_record(&history).unwrap();
        assert_eq!(record.read().revision(), 0);
        store.truncate(&history, 3).unwrap();
        store.truncate(&history, 2).unwrap();
        assert_eq!(record.read().revision(), 0);
        store.truncate(&history, 1).unwrap();
        assert_eq!(record.read().revision(), 1);
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
    }
}

// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Core-owned byte identities and histories with the shared Program-keyed graph cache.

#![allow(clippy::redundant_pub_crate)]

use super::limits::RegorusLimits;
use super::HistoryError;
use crate::rvm::program::Program;
use crate::utils::limits::ExecutionTimer;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_semantics::runtime::RuleRuntime;
pub use history_store::store::{Event, HistoryHandle};
use history_store::store::{HistoryRecord, HistoryStore as CoreHistoryStore};
use history_syntax::{Component, RuleMode};
use junco_core::compile::{lower_flat, FlatEncoder};
use junco_core::flat::FlatPair;
use junco_core::limits::Limits as _;
use junco_core::observation::ObservationWorld;
#[cfg(feature = "std")]
use parking_lot::Mutex;
#[cfg(not(feature = "std"))]
use spin::Mutex;
use vstd::prelude::*;

const HISTORY_CACHE_CAPACITY: usize = 16;
/// Coordinates per event: principal, action, resource.
const ARITY: usize = 3;

/// A Program-keyed table cache over the process-wide arity-3 history store. Identities and
/// histories are shared by every wrapper; wrapper construction is not an isolation boundary.
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct HistoryStore {
    core: Arc<CoreHistoryStore>,
    tables: Mutex<Vec<TableCacheEntry>>,
}

impl Default for HistoryStore {
    fn default() -> Self {
        Self {
            core: CoreHistoryStore::new(ARITY),
            tables: Mutex::new(Vec::new()),
        }
    }
}

/// A retained program Arc prevents pointer identity from being reused while cached.
#[derive(Debug)]
struct TableCacheEntry {
    program: Arc<Program>,
    table: usize,
    runtime: Arc<HistoryTableRuntime>,
}

#[derive(Debug)]
pub(crate) struct HistoryTableRuntime {
    pub(crate) rules: Vec<HistoryRuleSlot>,
}

#[derive(Debug)]
pub(crate) struct HistoryRuleSlot {
    pub(crate) mode: RuleMode,
    pub(crate) template: FlatPair<u64>,
    pub(crate) current: Mutex<Arc<Mutex<RuleRuntime>>>,
}

impl HistoryRuleSlot {
    /// Replace only the exhausted generation; other callers may already have won.
    pub(crate) fn replace(
        &self,
        exhausted: &Arc<Mutex<RuleRuntime>>,
        replacement: Arc<Mutex<RuleRuntime>>,
    ) -> Arc<Mutex<RuleRuntime>> {
        let mut current = self.current.lock();
        if Arc::ptr_eq(&current, exhausted) {
            // Residual IDs belong to one graph; a replacement replays from its new root.
            *current = replacement;
        }
        Arc::clone(&current)
    }
}

// Only external encoding accesses the native store; its internals carry no ghost model.
#[verus_verify(external_body)]
struct ByteEncoder<'a> {
    store: &'a HistoryStore,
}

verus! {
impl FlatEncoder<String> for ByteEncoder<'_> {
    open spec fn equality() -> junco_core::verify::encoding::Equality<String> {
        |_, left: String, right: String| left@ == right@
    }
    open spec fn domain() -> junco_core::verify::encoding::Domain<String> {
        |_, _| true
    }
    open spec fn maps(&self) -> junco_core::verify::encoding::Codebook<String> {
        Seq::empty()
    }
    // Native byte-store locking/encoding is not a blanket proof opt-in.
    open spec fn obeys_encoding_spec(&self) -> bool { false }
    open spec fn encoding_calls(&self) -> nat { 0 }
    #[verifier::prophetic]
    open spec fn restoration(&self) -> (junco_core::verify::encoding::Codebook<String>, bool) {
        (Seq::empty(), false)
    }

    // The byte interner stays in core; this native adapter routes each coordinate to its domain.
    #[verifier::external_body]
    fn encode(&mut self, field: Component, value: &String) -> Result<u64, HistoryError> {
        self.store.intern(field, value)
    }
}
}

impl HistoryStore {
    /// Create an empty table cache over the process-wide identities and histories.
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

    pub(crate) fn table_runtime(
        &self,
        program: &Arc<Program>,
        table: usize,
    ) -> Result<Arc<HistoryTableRuntime>, HistoryError> {
        {
            let mut tables = self.tables.lock();
            if let Some(position) = tables
                .iter()
                .position(|entry| Arc::ptr_eq(&entry.program, program) && entry.table == table)
            {
                let entry = tables.remove(position);
                let runtime = Arc::clone(&entry.runtime);
                tables.insert(0, entry);
                return Ok(runtime);
            }
        }
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
            let runtime = RuleRuntime::new(&self.core, &template, true, &mut limits, &mut world)?;
            rules.push(HistoryRuleSlot {
                mode: rule.mode,
                template,
                current: Mutex::new(Arc::new(Mutex::new(runtime))),
            });
        }
        let runtime = Arc::new(HistoryTableRuntime { rules });
        limits.enforce_memory()?;
        let mut tables = self.tables.lock();
        // Compilation ran unlocked; another caller may already have populated this entry.
        if let Some(position) = tables
            .iter()
            .position(|entry| Arc::ptr_eq(&entry.program, program) && entry.table == table)
        {
            let entry = tables.remove(position);
            let cached = Arc::clone(&entry.runtime);
            tables.insert(0, entry);
            return Ok(cached);
        }
        if tables.len() < HISTORY_CACHE_CAPACITY {
            tables
                .try_reserve(1)
                .map_err(|_| HistoryError::AllocationFailed)?;
        }
        limits.enforce_memory()?;
        if tables.len() >= HISTORY_CACHE_CAPACITY {
            tables.pop();
        }
        tables.insert(
            0,
            TableCacheEntry {
                program: Arc::clone(program),
                table,
                runtime: Arc::clone(&runtime),
            },
        );
        Ok(runtime)
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

    fn typed_only_event() -> Event {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        struct Typed;
        impl history_syntax::Event for Typed {
            type Component = history_syntax::Component3<(), (), ()>;
            type Arity = history_syntax::N3;
            fn component(self, index: usize) -> Self::Component {
                match index {
                    0 => history_syntax::Component3::C0(()),
                    1 => history_syntax::Component3::C1(()),
                    _ => history_syntax::Component3::C2(()),
                }
            }
            fn coordinate(component: Self::Component) -> usize {
                match component {
                    history_syntax::Component3::C0(()) => 0,
                    history_syntax::Component3::C1(()) => 1,
                    history_syntax::Component3::C2(()) => 2,
                }
            }
        }
        let store = Arc::new(history_store::Store::<Typed>::new().unwrap());
        let history = history_store::History::from_events(store, [Typed]).unwrap();
        history.numeric().as_slice()[0]
    }

    #[test]
    fn ownership_atomic_append_and_revisions() {
        let store = Arc::new(HistoryStore::new());
        let peer = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let valid = event(&store);
        // Wrappers are caches over one process-wide identity and history store.
        assert_eq!(event(&peer), valid);
        peer.append(&history, &[]).unwrap();
        assert_eq!(peer.len(&history).unwrap(), 0);
        let typed = typed_only_event();
        // Event fields are private: each typed-only coordinate is rejected while building.
        for index in 0..3 {
            let mut slots = [valid.component(0), valid.component(1), valid.component(2)];
            slots[index] = typed.component(index);
            assert!(matches!(
                store.event(&slots),
                Err(HistoryError::UnknownId { domain: "component", id }) if id == typed.component(index)
            ));
        }
        assert!(matches!(
            store.append(&history, &[valid, typed]),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
        assert!(matches!(
            peer.validate_event(&typed),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
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

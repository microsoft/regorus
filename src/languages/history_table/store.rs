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
pub use history_store::store::{Action, Event, HistoryHandle, Principal, Resource};
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

/// A Program-keyed table cache over the process-wide history store. Identities and
/// histories are shared by every wrapper; wrapper construction is not an isolation boundary.
#[derive(Debug)]
pub struct HistoryStore {
    core: Arc<CoreHistoryStore>,
    tables: Mutex<Vec<TableCacheEntry>>,
}

impl Default for HistoryStore {
    fn default() -> Self {
        Self {
            core: CoreHistoryStore::global(),
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
    #[verifier::prophetic]
    open spec fn restoration(&self) -> (junco_core::verify::encoding::Codebook<String>, bool) {
        (Seq::empty(), false)
    }

    // The UTF-8/BTreeMap interner stays in core; this native adapter chooses its domain.
    #[verifier::external_body]
    fn encode(&mut self, field: Component, value: &String) -> Result<u64, HistoryError> {
        match field {
            Component::Principal => self.store.intern_principal(value).map(Principal::get),
            Component::Action => self.store.intern_action(value).map(Action::get),
            Component::Resource => self.store.intern_resource(value).map(Resource::get),
        }
    }
}
}

impl HistoryStore {
    /// Create an empty table cache over the process-wide identities and histories.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern the complete UTF-8 bytes without normalization or prefix matching.
    pub fn intern_principal(&self, path: &str) -> Result<Principal, HistoryError> {
        self.core.intern_principal(
            path,
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
    }

    /// Intern the complete UTF-8 bytes in the action domain.
    pub fn intern_action(&self, path: &str) -> Result<Action, HistoryError> {
        self.core.intern_action(
            path,
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
    }

    /// Intern the complete UTF-8 bytes in the resource domain.
    pub fn intern_resource(&self, path: &str) -> Result<Resource, HistoryError> {
        self.core.intern_resource(
            path,
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
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

    use super::*;
    use alloc::collections::BTreeSet;

    fn event(store: &HistoryStore) -> Event {
        Event {
            principal: store.intern_principal("alice").unwrap(),
            action: store.intern_action("edit").unwrap(),
            resource: store.intern_resource("doc").unwrap(),
        }
    }

    #[test]
    fn exact_identities_and_large_domain() {
        let store = HistoryStore::new();
        let paths = ["a", "A", "/a", "a/", "a\0", "é", "e\u{301}"];
        let mut ids = BTreeSet::new();
        for path in paths {
            let id = store.intern_principal(path).unwrap();
            assert_eq!(id, store.intern_principal(path).unwrap());
            assert!(ids.insert(id));
        }
        let first = store.intern_resource("common/prefix/0").unwrap();
        let mut resources = BTreeSet::from([first]);
        for index in 1..5000 {
            assert!(resources.insert(
                store
                    .intern_resource(&alloc::format!("common/prefix/{index}"))
                    .unwrap()
            ));
        }
        assert_eq!(first, store.intern_resource("common/prefix/0").unwrap());
        assert_eq!(resources.len(), 5000);
        let action = store.intern_action("a").unwrap();
        store.intern_principal("new").unwrap();
        assert_eq!(action, store.intern_action("a").unwrap());
        let long = "x".repeat(4096);
        assert_ne!(
            store.intern_resource(&long).unwrap(),
            store.intern_resource(&(long + "/")).unwrap()
        );
    }

    fn typed_only_event() -> Event {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        struct Typed;
        impl history_syntax::Event for Typed {
            type Principal = ();
            type Action = ();
            type Resource = ();
            fn principal(self) {}
            fn action(self) {}
            fn resource(self) {}
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
        for (invalid, domain) in [
            (
                Event {
                    principal: typed.principal,
                    ..valid
                },
                "principal",
            ),
            (
                Event {
                    action: typed.action,
                    ..valid
                },
                "action",
            ),
            (
                Event {
                    resource: typed.resource,
                    ..valid
                },
                "resource",
            ),
        ] {
            assert!(matches!(
                store.append(&history, &[valid, invalid]),
                Err(HistoryError::UnknownId { domain: actual, .. }) if actual == domain
            ));
            assert!(matches!(
                peer.validate_event(&invalid),
                Err(HistoryError::UnknownId { domain: actual, .. }) if actual == domain
            ));
            assert_eq!(store.len(&history).unwrap(), 0);
        }
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

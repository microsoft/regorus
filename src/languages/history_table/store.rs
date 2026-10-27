// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Shared exact-byte identities and revisioned histories. Append preserves revisions;
//! truncating an existing prefix invalidates every decision using that revision.

#![allow(clippy::redundant_pub_crate)]

use super::HistoryError;
use crate::rvm::vm::history_tables::graph::allocation;
use crate::utils::limits::enforce_memory_limit;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
#[cfg(feature = "std")]
use parking_lot::{Mutex, RwLock};
#[cfg(not(feature = "std"))]
use spin::{Mutex, RwLock};
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
impl View for StoredHistory {
    type V = crate::verify::history_specs::HistoryStateView;
    closed spec fn view(&self) -> crate::verify::history_specs::HistoryStateView {
        crate::verify::history_specs::HistoryStateView {
            events: crate::rvm::vm::history_tables::kernel::verify::events_view(self.events@),
            revision: self.revision as nat,
        }
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
        let mut counters = NEXT_IDS.lock();
        let next = counters
            .get_mut(index)
            .ok_or(HistoryError::invariant("invalid identity domain"))?;
        Self::allocate_id(next, domain)
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
    fn intern(
        &mut self,
        path: &str,
        index: usize,
        domain: &'static str,
    ) -> Result<u64, HistoryError> {
        proof! { reveal(<Domain as View>::view); reveal(domain_wf); }
        proof_decl! { let ghost entry = self@; }
        if let Some(id) = Self::path_lookup(&self.paths, path) {
            return Ok(id);
        }
        let mut owned = String::new();
        allocation(owned.try_reserve(path.len()))?;
        owned.push_str(path);
        enforce_memory_limit()?;
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
            assert(crate::verify::history_specs::interner_wf(entry.paths, id as nat));
            crate::verify::history_specs::lemma_interner_fresh_nonreuse(entry.paths, id as nat,
                vstd::utf8::encode_utf8(path@), id as nat);
        }
        Self::path_insert(&mut self.paths, owned, id);
        self.ids.insert(id);
        if let Err(error) = enforce_memory_limit() {
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
            crate::verify::history_specs::lemma_interner_raise_frontier(self@.paths,
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

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) mod verify {
    use super::*;
    use crate::verify::history_specs as language;

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


    pub(crate) open spec fn cursor_key_eq(left: HistoryCursor, right: HistoryCursor) -> bool {
        left.history == right.history && left.bindings@ == right.bindings@
    }

    pub(crate) open spec fn cursor_in_graph(
        pair: crate::rvm::vm::history_tables::progress::CompiledPair, cursor: HistoryCursor,
    ) -> bool {
        cursor.residual@ < pair.store.graph().regexes.len()
            && language::event_wf(cursor.bindings@)
    }

    pub(crate) open spec fn cursor_cache_wf(
        pair: crate::rvm::vm::history_tables::progress::CompiledPair, cursors: Seq<HistoryCursor>,
    ) -> bool {
        crate::rvm::vm::history_tables::progress::verify::pair_wf(pair)
            && cursors.len() <= HISTORY_CACHE_CAPACITY
            && (forall|i: int| 0 <= i < cursors.len() ==> cursor_in_graph(pair, cursors[i]))
            && (forall|i: int, j: int| 0 <= i < j < cursors.len()
                ==> !cursor_key_eq(cursors[i], cursors[j]))
    }

    pub(crate) open spec fn longer_cached_prefix(cursors: Seq<HistoryCursor>, cursor: HistoryCursor) -> bool {
        exists|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], cursor)
            && cursors[i].revision == cursor.revision && cursors[i].consumed > cursor.consumed
    }

    pub(super) proof fn lemma_cursor_remove(
        pair: crate::rvm::vm::history_tables::progress::CompiledPair,
        cursors: Seq<HistoryCursor>, index: int, cursor: HistoryCursor,
    )
        requires cursor_cache_wf(pair, cursors), 0 <= index < cursors.len(),
            cursor_key_eq(cursors[index], cursor),
        ensures cursor_cache_wf(pair, cursors.remove(index)),
            cursors.remove(index).len() < HISTORY_CACHE_CAPACITY,
            forall|i: int| 0 <= i < cursors.remove(index).len()
                ==> !cursor_key_eq(cursors.remove(index)[i], cursor)
                    && cursors.contains(cursors.remove(index)[i]),
    {
        cursors.remove_ensures(index);
        let kept = cursors.remove(index);
        assert forall|i: int| 0 <= i < kept.len() implies cursor_in_graph(pair, kept[i])
            && !cursor_key_eq(kept[i], cursor) && cursors.contains(kept[i]) by {
            let original = if i < index { i } else { i + 1 };
            assert(0 <= original < cursors.len());
            assert(kept[i] == cursors[original]);
            assert(original != index);
            assert(cursor_in_graph(pair, cursors[original]));
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
        pair: crate::rvm::vm::history_tables::progress::CompiledPair, cursors: Seq<HistoryCursor>,
    )
        requires cursor_cache_wf(pair, cursors), cursors.len() > 0,
        ensures cursor_cache_wf(pair, cursors.drop_last()),
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
        pair: crate::rvm::vm::history_tables::progress::CompiledPair, cursors: Seq<HistoryCursor>, cursor: HistoryCursor,
    )
        requires cursor_cache_wf(pair, cursors), cursors.len() < HISTORY_CACHE_CAPACITY,
            cursor_in_graph(pair, cursor),
            forall|i: int| 0 <= i < cursors.len() ==> !cursor_key_eq(cursors[i], cursor),
        ensures cursor_cache_wf(pair, seq![cursor] + cursors),
    {
        let after = seq![cursor] + cursors;
        assert forall|i: int| 0 <= i < after.len() implies cursor_in_graph(pair, after[i]) by {
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
}
}

/// Application-owned synchronized identities and histories; no global history state.
#[derive(Debug, Default)]
pub struct HistoryStore {
    principals: Mutex<Domain>,
    actions: Mutex<Domain>,
    resources: Mutex<Domain>,
    histories: Mutex<Vec<Arc<RwLock<StoredHistory>>>>,
    tables: Mutex<Vec<TableCacheEntry>>,
}

/// A shared history reference. Cloning it never copies events.
#[derive(Clone, Debug)]
pub struct HistoryHandle {
    pub(crate) owner: Arc<HistoryStore>,
    pub(crate) index: usize,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct StoredHistory {
    pub(crate) events: Vec<Event>,
    pub(crate) revision: u64,
}

#[verus_verify]
impl StoredHistory {
    #[verus_spec(result => ensures result.events@ == Seq::<Event>::empty(), result.revision == 0)]
    const fn new() -> Self {
        Self {
            events: Vec::new(),
            revision: 0,
        }
    }

    #[verus_spec(result =>
        ensures final(self).revision == old(self).revision,
            result is Err ==> final(self).events@ == old(self).events@,
            result is Ok ==> final(self).events@ == old(self).events@ + events@,
            crate::verify::history_specs::history_mutation(old(self)@, final(self)@),
    )]
    fn append_events(&mut self, events: &[Event]) -> Result<(), HistoryError> {
        proof! { reveal(<StoredHistory as View>::view); }
        proof_decl! { let ghost entry_events = self.events@; }
        let previous = self.events.len();
        allocation(self.events.try_reserve(events.len()))?;
        enforce_memory_limit()?;
        self.events.extend_from_slice(events);
        if let Err(error) = enforce_memory_limit() {
            self.events.truncate(previous);
            return Err(error.into());
        }
        proof! {
            assert(crate::rvm::vm::history_tables::kernel::verify::events_view(self.events@)
                =~= crate::rvm::vm::history_tables::kernel::verify::events_view(entry_events)
                    + crate::rvm::vm::history_tables::kernel::verify::events_view(events@));
        }
        Ok(())
    }

    #[verus_spec(result =>
        ensures result is Err ==> final(self)@ == old(self)@,
            crate::verify::history_specs::history_mutation(old(self)@, final(self)@),
            result is Ok && len < old(self).events@.len() ==> final(self).revision == old(self).revision + 1
                && final(self).events@ == old(self).events@.take(len as int),
            result is Ok && len >= old(self).events@.len() ==> final(self)@ == old(self)@,
    )]
    fn truncate_events(&mut self, len: usize) -> Result<(), HistoryError> {
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
                assert(crate::rvm::vm::history_tables::kernel::verify::events_view(self.events@)
                    =~= crate::rvm::vm::history_tables::kernel::verify::events_view(entry_events).take(len as int));
            }
        }
        Ok(())
    }
}

/// A retained program Arc prevents pointer identity from being reused while cached.
#[derive(Debug)]
struct TableCacheEntry {
    program: Arc<crate::rvm::program::Program>,
    table: usize,
    runtime: Arc<HistoryTableRuntime>,
}

#[derive(Debug)]
pub(crate) struct HistoryTableRuntime {
    pub(crate) rules: Vec<HistoryRuleSlot>,
}

#[derive(Debug)]
pub(crate) struct HistoryRuleSlot {
    pub(crate) mode: crate::rvm::program::HistoryRuleMode,
    pub(crate) template: crate::rvm::vm::history_tables::source::NumericPair,
    pub(crate) current: Mutex<Arc<Mutex<RuleRuntime>>>,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct RuleRuntime {
    pub(crate) pair: crate::rvm::vm::history_tables::progress::CompiledPair,
    pub(crate) cursors: Vec<HistoryCursor>,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct HistoryCursor {
    pub(crate) history: usize,
    pub(crate) bindings: crate::rvm::vm::history_tables::kernel::Bindings,
    pub(crate) revision: u64,
    pub(crate) consumed: usize,
    pub(crate) residual: crate::rvm::vm::history_tables::kernel::RegexId,
}

#[verus_verify]
pub(crate) const HISTORY_CACHE_CAPACITY: usize = 16;

impl HistoryCursor {
    // The pinned vstd lacks Iterator::position; this leaf selects an existing exact key only.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures match result {
        Some(index) => index < cursors@.len() && cursor_key_eq(cursors@[index as int], *self)
            && (forall|i: int| 0 <= i < index ==> !cursor_key_eq(cursors@[i], *self)),
        None => forall|i: int| 0 <= i < cursors@.len() ==> !cursor_key_eq(cursors@[i], *self),
    })]
    #[inline]
    fn position(&self, cursors: &[Self]) -> Option<usize> {
        cursors
            .iter()
            .position(|old| old.history == self.history && old.bindings == self.bindings)
    }
}

impl RuleRuntime {
    pub(crate) fn new(
        template: &crate::rvm::vm::history_tables::source::NumericPair,
        precompile: bool,
        timer: &mut crate::utils::limits::ExecutionTimer,
        world: &mut crate::rvm::vm::history_tables::ObservationWorld,
    ) -> Result<Self, HistoryError> {
        #[cfg_attr(not(feature = "cache"), allow(unused_mut))]
        let mut pair = template.compile(timer, world)?;
        #[cfg(feature = "cache")]
        if precompile {
            if let Err(error) = pair.precompile(timer, world) {
                if !matches!(error, HistoryError::GraphLimit { .. }) {
                    return Err(error);
                }
                drop(pair);
                pair = template.compile(timer, world)?;
            }
        }
        #[cfg(not(feature = "cache"))]
        let _ = precompile;
        let mut cursors = Vec::new();
        allocation(cursors.try_reserve_exact(HISTORY_CACHE_CAPACITY))?;
        enforce_memory_limit()?;
        Ok(Self { pair, cursors })
    }

    /// Called only after all fallible batch work, while its history is read-locked.
    #[verus_verify]
    #[verus_spec(
        requires cursor_cache_wf(old(self).pair, old(self).cursors@), cursor_in_graph(old(self).pair, cursor),
        ensures
        final(self).pair == old(self).pair,
        cursor_cache_wf(final(self).pair, final(self).cursors@),
        longer_cached_prefix(old(self).cursors@, cursor) ==> final(self).cursors@ == old(self).cursors@,
        !longer_cached_prefix(old(self).cursors@, cursor) ==> final(self).cursors@.len() > 0
            && final(self).cursors@[0] == cursor,
        forall|i: int| 0 <= i < final(self).cursors@.len()
            ==> final(self).cursors@[i] == cursor || old(self).cursors@.contains(final(self).cursors@[i]),
    )]
    pub(crate) fn publish(&mut self, cursor: HistoryCursor) {
        proof_decl! { let ghost entry = self.cursors@; }
        if let Some(position) = cursor.position(&self.cursors) {
            proof! {
                assert forall|i: int| 0 <= i < entry.len() && cursor_key_eq(entry[i], cursor)
                    implies i == position by {
                    if i < position { assert(!cursor_key_eq(entry[i], entry[position as int])); }
                    if i > position { assert(!cursor_key_eq(entry[position as int], entry[i])); }
                }
            }
            if let Some(old) = self.cursors.get(position) {
                if old.revision == cursor.revision && old.consumed > cursor.consumed {
                    proof! { assert(longer_cached_prefix(entry, cursor)); }
                    return;
                }
            }
            proof! { assert(!longer_cached_prefix(entry, cursor)); }
            self.cursors.remove(position);
            proof! { lemma_cursor_remove(self.pair, entry, position as int, cursor); }
        } else {
            proof! { assert(!longer_cached_prefix(entry, cursor)); }
            if self.cursors.len() >= HISTORY_CACHE_CAPACITY {
                self.cursors.pop();
                proof! { lemma_cursor_drop_last(self.pair, entry); }
            }
        }
        proof_decl! { let ghost kept = self.cursors@; }
        proof! {
            assert(kept.len() < HISTORY_CACHE_CAPACITY);
            assert forall|i: int| 0 <= i < kept.len()
                implies !cursor_key_eq(kept[i], cursor) && entry.contains(kept[i]) by {}
            lemma_cursor_prepend(self.pair, kept, cursor);
        }
        // Capacity was reserved at construction; publication cannot allocate or fail.
        self.cursors.insert(0, cursor);
        proof! {
            assert(self.cursors@ =~= seq![cursor] + kept);
            assert forall|i: int| 0 <= i < self.cursors@.len()
                implies self.cursors@[i] == cursor || entry.contains(self.cursors@[i]) by {
                if i == 0 { assert(self.cursors@[i] == cursor); }
                else { assert(self.cursors@[i] == kept[i - 1]); }
            }
        }
    }
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
            // Residual IDs belong to one graph; a replacement must replay from its new root.
            *current = replacement;
        }
        Arc::clone(&current)
    }
}

impl HistoryStore {
    /// Create an empty owner. Share it through an `Arc` before creating histories.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern the complete UTF-8 bytes without normalization or prefix matching.
    pub fn intern_principal(&self, path: &str) -> Result<Principal, HistoryError> {
        self.principals
            .lock()
            .intern(path, 0, "principal")
            .map(Principal)
    }

    /// Intern the complete UTF-8 bytes in the action domain.
    pub fn intern_action(&self, path: &str) -> Result<Action, HistoryError> {
        self.actions.lock().intern(path, 1, "action").map(Action)
    }

    /// Intern the complete UTF-8 bytes in the resource domain.
    pub fn intern_resource(&self, path: &str) -> Result<Resource, HistoryError> {
        self.resources
            .lock()
            .intern(path, 2, "resource")
            .map(Resource)
    }

    pub(crate) fn table_runtime(
        &self,
        program: &Arc<crate::rvm::program::Program>,
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
            .ok_or(HistoryError::invariant("invalid history table index"))?;
        let mut rules = Vec::new();
        allocation(rules.try_reserve_exact(source.rules.len()))?;
        let mut timer = crate::utils::limits::ExecutionTimer::new(None);
        let mut world = crate::rvm::vm::history_tables::ObservationWorld;
        for rule in &source.rules {
            let template =
                crate::rvm::vm::history_tables::source::NumericPair::lower(&rule.source, self)?;
            let runtime = RuleRuntime::new(&template, true, &mut timer, &mut world)?;
            rules.push(HistoryRuleSlot {
                mode: rule.mode,
                template,
                current: Mutex::new(Arc::new(Mutex::new(runtime))),
            });
        }
        let runtime = Arc::new(HistoryTableRuntime { rules });
        enforce_memory_limit()?;
        let mut tables = self.tables.lock();
        // Compilation ran unlocked; another caller may already have populated this cache entry.
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
            allocation(tables.try_reserve(1))?;
        }
        enforce_memory_limit()?;
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

    /// Create a history whose lifetime is retained by this owner.
    pub fn new_history(self: &Arc<Self>) -> Result<HistoryHandle, HistoryError> {
        let record = Arc::new(RwLock::new(StoredHistory::new()));
        let mut histories = self.histories.lock();
        allocation(histories.try_reserve(1))?;
        enforce_memory_limit()?;
        let index = histories.len();
        histories.push(record);
        if let Err(error) = enforce_memory_limit() {
            histories.pop();
            return Err(error.into());
        }
        Ok(HistoryHandle {
            owner: Arc::clone(self),
            index,
        })
    }

    pub(crate) fn validate_event(&self, event: &Event) -> Result<(), HistoryError> {
        self.principals
            .lock()
            .validate(event.principal.get(), "principal")?;
        self.actions.lock().validate(event.action.get(), "action")?;
        self.resources
            .lock()
            .validate(event.resource.get(), "resource")
    }

    pub(crate) fn history_record(
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
    pub fn append(&self, history: &HistoryHandle, events: &[Event]) -> Result<(), HistoryError> {
        let record = self.history_record(history)?;
        if events.is_empty() {
            return Ok(());
        }
        for event in events {
            self.validate_event(event)?;
        }
        let mut stored = record.write();
        stored.append_events(events)
    }

    /// Remove a suffix, invalidating prior snapshots only when events are removed.
    pub fn truncate(&self, history: &HistoryHandle, len: usize) -> Result<(), HistoryError> {
        let record = self.history_record(history)?;
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
        for index in 1..5000 {
            store
                .intern_resource(&alloc::format!("common/prefix/{index}"))
                .unwrap();
        }
        assert_eq!(first, store.intern_resource("common/prefix/0").unwrap());
        assert_eq!(store.resources.lock().ids.len(), 5000);
        let action = store.intern_action("a").unwrap();
        store.intern_principal("new").unwrap();
        assert_eq!(action, store.intern_action("a").unwrap());
        let long = "x".repeat(4096);
        assert_ne!(
            store.intern_resource(&long).unwrap(),
            store.intern_resource(&(long + "/")).unwrap()
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
        let history = store.new_history().unwrap();
        let valid = event(&store);
        let foreign_event = event(&foreign);
        assert!(matches!(
            foreign.len(&history),
            Err(HistoryError::WrongHistoryOwner)
        ));
        assert!(matches!(
            foreign.append(&history, &[]),
            Err(HistoryError::WrongHistoryOwner)
        ));
        assert!(matches!(
            store.append(&history, &[valid, foreign_event]),
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
        store.append(&history, &[valid, valid]).unwrap();
        assert_eq!(store.len(&history.clone()).unwrap(), 2);
        let record = store.history_record(&history).unwrap();
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 3).unwrap();
        store.truncate(&history, 2).unwrap();
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 1).unwrap();
        assert_eq!(record.read().revision, 1);
        record.write().revision = u64::MAX;
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
}

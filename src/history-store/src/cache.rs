// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
//! Storage for graph-local memoization and bounded history cursors.
use crate::graph::allocation;
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use junco_core::error::HistoryError;
use junco_core::kernel::{AtomSet, RegexId, TransitionId};
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::*;
use lru::LruCache;
use smallvec::SmallVec;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EventClass {
    pub transition: TransitionId,
    pub words: SmallVec<[u64; 2]>,
}

/// Self-loop certificate for one residual: when any atom of `transition` whose bit is set in
/// `mask` is false on an event, the event's successor is the residual itself. `mask == 0`
/// means "computed, nothing usable" (constant, wide, or budget-limited transition).
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Guard {
    pub transition: TransitionId,
    pub mask: u64,
}

#[verus_verify]
pub const SUCCESSOR_CAPACITY: u64 = 256;

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub struct GraphCaches {
    pub derivatives: Vec<Option<TransitionId>>,
    pub atoms: Vec<Option<AtomSet>>,
    pub guards: Vec<Option<Guard>>,
    pub successors: Option<LruCache<EventClass, RegexId>>,
}
#[verus_verify]
impl GraphCaches {
    #[expect(
        clippy::new_without_default,
        reason = "Construction stays on this verified constructor; Default would add an unverified path."
    )]
    #[verus_spec(result => ensures result.derivatives@ == Seq::<Option<TransitionId>>::empty(),
        result.atoms@ == Seq::<Option<AtomSet>>::empty(), result.guards@ == Seq::<Option<Guard>>::empty(),
        result.successors is None)]
    pub const fn new() -> Self {
        Self {
            derivatives: Vec::new(),
            atoms: Vec::new(),
            guards: Vec::new(),
            successors: None,
        }
    }
    // Concrete LRU leaves expose semantic keys and membership, not policy semantics.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures result matches Some(cache) ==> successor_cache_view(cache) == Map::<ClassKey, RegexId>::empty())]
    pub fn successor_cache() -> Option<LruCache<EventClass, RegexId>> {
        usize::try_from(SUCCESSOR_CAPACITY)
            .ok()
            .and_then(NonZeroUsize::new)
            .map(LruCache::new)
    }

    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures successor_entries(*final(cache)) == successor_entries(*old(cache)),
            result == if successor_entries(*old(cache)).contains_key(class_key(*key)) {
                Some(successor_entries(*old(cache))[class_key(*key)])
            } else { None },
    )]
    pub fn successor_get(
        cache: &mut Option<LruCache<EventClass, RegexId>>,
        key: &EventClass,
    ) -> Option<RegexId> {
        cache.as_mut().and_then(|cache| cache.get(key)).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(
        ensures *old(cache) is Some ==> *final(cache) is Some
            && successor_entries(*final(cache)).contains_key(class_key(key))
            && successor_entries(*final(cache))[class_key(key)] == value,
            *old(cache) is None ==> *final(cache) is None,
            forall|other: ClassKey| #[trigger] successor_entries(*final(cache)).contains_key(other) ==> other == class_key(key)
                || (successor_entries(*old(cache)).contains_key(other)
                    && successor_entries(*final(cache))[other] == successor_entries(*old(cache))[other]),
    )]
    pub fn successor_put(
        cache: &mut Option<LruCache<EventClass, RegexId>>,
        key: EventClass,
        value: RegexId,
    ) {
        if let Some(cache) = cache.as_mut() {
            cache.put(key, value);
        }
    }
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub struct HistoryCursor {
    pub history: usize,
    pub bindings: junco_core::kernel::Bindings,
    pub revision: u64,
    pub consumed: usize,
    pub residual: junco_core::kernel::RegexId,
}

#[verus_verify]
pub const HISTORY_CACHE_CAPACITY: usize = 16;

impl HistoryCursor {
    // The pinned vstd lacks Iterator::position; this leaf selects an existing exact key only.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures match result {
        Some(index) => index < cursors@.len() && cursor_key_eq(cursors@[index as int], *self)
            && (forall|i: int| 0 <= i < index ==> !cursor_key_eq(cursors@[i], *self)),
        None => forall|i: int| 0 <= i < cursors@.len() ==> !cursor_key_eq(cursors@[i], *self),
    })]
    #[inline]
    pub fn position(&self, cursors: &[Self]) -> Option<usize> {
        cursors
            .iter()
            .position(|old| old.history == self.history && old.bindings == self.bindings)
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub struct CursorCache {
    entries: Vec<HistoryCursor>,
}
#[verus_verify]
impl CursorCache {
    #[verus_spec(result => ensures result matches Ok(cache) ==> cache@ == Seq::<HistoryCursor>::empty()
        && cursor_cache_wf(cache@))]
    pub fn new<L: Limits>(
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, HistoryError> {
        let mut entries = Vec::new();
        allocation(world.try_reserve_vec_exact(&mut entries, HISTORY_CACHE_CAPACITY))?;
        limits.enforce_memory()?;
        proof! { reveal(<CursorCache as View>::view); }
        Ok(Self { entries })
    }

    #[verus_spec(result => ensures result@ == self@)]
    pub fn entries(&self) -> &[HistoryCursor] {
        proof! { reveal(<CursorCache as View>::view); }
        &self.entries
    }

    #[cfg(any(test, feature = "test-util"))]
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    #[expect(
        clippy::collapsible_if,
        reason = "Pinned Verus does not support let-chain expressions"
    )]
    #[verus_spec(
        requires cursor_cache_wf(old(self)@),
        ensures final(self)@ == published_cursors(old(self)@, cursor),
            cursor_cache_wf(final(self)@),
            longer_cached_prefix(old(self)@, cursor) ==> final(self)@ == old(self)@,
            !longer_cached_prefix(old(self)@, cursor) ==> final(self)@.len() > 0 && final(self)@[0] == cursor,
            forall|i: int| 0 <= i < final(self)@.len() ==> final(self)@[i] == cursor || old(self)@.contains(final(self)@[i]),
    )]
    pub fn publish(&mut self, cursor: HistoryCursor) {
        proof! { reveal(<CursorCache as View>::view); }
        proof_decl! { let ghost entry = self.entries@; }
        if let Some(position) = cursor.position(&self.entries) {
            proof! {
                assert forall|i: int| 0 <= i < entry.len() && cursor_key_eq(entry[i], cursor) implies i == position by {
                    if i < position { assert(!cursor_key_eq(entry[i], entry[position as int])); }
                    if i > position { assert(!cursor_key_eq(entry[position as int], entry[i])); }
                }
            }
            if let Some(old) = self.entries.get(position) {
                if old.revision == cursor.revision && old.consumed > cursor.consumed {
                    proof! { assert(longer_cached_prefix(entry, cursor)); }
                    return;
                }
            }
            proof! { assert(!longer_cached_prefix(entry, cursor)); }
            self.entries.remove(position);
            proof! {
                entry.remove_ensures(position as int);
                assert(self.entries@ == kept_cursors(entry, cursor));
                lemma_kept_cursors(entry, cursor);
            }
        } else {
            proof! { assert(!longer_cached_prefix(entry, cursor)); }
            if self.entries.len() >= HISTORY_CACHE_CAPACITY {
                self.entries.pop();
            }
            proof! {
                assert(self.entries@ == kept_cursors(entry, cursor));
                lemma_kept_cursors(entry, cursor);
            }
        }
        proof_decl! { let ghost kept = self.entries@; }
        // Capacity was reserved at construction; publication cannot allocate or fail.
        self.entries.insert(0, cursor);
        proof! {
            assert(self.entries@ =~= seq![cursor] + kept);
            assert forall|i: int, j: int| 0 <= i < j < self.entries@.len()
                implies !cursor_key_eq(self.entries@[i], self.entries@[j]) by {
                if i == 0 { assert(self.entries@[j] == kept[j - 1]); }
                else { assert(self.entries@[i] == kept[i - 1]); assert(self.entries@[j] == kept[j - 1]); }
            }
            assert forall|i: int| 0 <= i < self.entries@.len()
                implies self.entries@[i] == cursor || entry.contains(self.entries@[i]) by {
                if i > 0 { assert(self.entries@[i] == kept[i - 1]); }
            }
        }
    }
}
#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    verus! {
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExSuccessorHasher(lru::DefaultHasher);
    #[verifier::external_type_specification]
    #[verifier::external_body]
    #[verifier::accept_recursive_types(K)]
    #[verifier::accept_recursive_types(V)]
    #[verifier::reject_recursive_types(S)]
    pub struct ExLruCache<K, V, S>(LruCache<K, V, S>);



        pub struct ClassKey { pub transition: TransitionId, pub words: Seq<u64> }
        pub open spec fn class_key(key: EventClass) -> ClassKey {
            ClassKey { transition: key.transition, words: key.words.view() }
        }
        pub uninterp spec fn successor_cache_view(cache: LruCache<EventClass, RegexId>) -> Map<ClassKey, RegexId>;
        pub open spec fn successor_entries(cache: Option<LruCache<EventClass, RegexId>>) -> Map<ClassKey, RegexId> {
            match cache { Some(cache) => successor_cache_view(cache), None => Map::empty() }
        }

        impl View for CursorCache {
            type V = Seq<HistoryCursor>;
            open(super) spec fn view(&self) -> Seq<HistoryCursor> { self.entries@ }
        }
        pub open spec fn cursor_key_eq(left: HistoryCursor, right: HistoryCursor) -> bool {
            left.history == right.history && left.bindings@ == right.bindings@
        }
        pub open spec fn cursor_cache_wf(cursors: Seq<HistoryCursor>) -> bool {
            cursors.len() <= HISTORY_CACHE_CAPACITY
                && (forall|i: int, j: int| 0 <= i < j < cursors.len() ==> !cursor_key_eq(cursors[i], cursors[j]))
        }
        pub open spec fn longer_cached_prefix(cursors: Seq<HistoryCursor>, cursor: HistoryCursor) -> bool {
            exists|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], cursor)
                && cursors[i].revision == cursor.revision && cursors[i].consumed > cursor.consumed
        }
        pub open spec fn kept_cursors(cursors: Seq<HistoryCursor>, cursor: HistoryCursor) -> Seq<HistoryCursor> {
            if exists|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], cursor) {
                let index = choose|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], cursor);
                cursors.remove(index)
            } else if cursors.len() >= HISTORY_CACHE_CAPACITY { cursors.drop_last() }
            else { cursors }
        }
        pub open spec fn published_cursors(cursors: Seq<HistoryCursor>, cursor: HistoryCursor) -> Seq<HistoryCursor> {
            if longer_cached_prefix(cursors, cursor) { cursors }
            else { seq![cursor] + kept_cursors(cursors, cursor) }
        }
        pub proof fn lemma_kept_cursors(cursors: Seq<HistoryCursor>, cursor: HistoryCursor)
            requires cursor_cache_wf(cursors),
            ensures kept_cursors(cursors, cursor).len() < HISTORY_CACHE_CAPACITY,
                cursor_cache_wf(kept_cursors(cursors, cursor)),
                forall|i: int| 0 <= i < kept_cursors(cursors, cursor).len()
                    ==> !cursor_key_eq(kept_cursors(cursors, cursor)[i], cursor)
                        && cursors.contains(kept_cursors(cursors, cursor)[i]),
        {
            let kept = kept_cursors(cursors, cursor);
            if exists|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], cursor) {
                let index = choose|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], cursor);
                cursors.remove_ensures(index);
                assert forall|i: int| 0 <= i < kept.len() implies !cursor_key_eq(kept[i], cursor) && cursors.contains(kept[i]) by {
                    let original = if i < index { i } else { i + 1 };
                    assert(kept[i] == cursors[original]);
                    if original < index { assert(!cursor_key_eq(cursors[original], cursors[index])); }
                    else { assert(!cursor_key_eq(cursors[index], cursors[original])); }
                }
                assert forall|i: int, j: int| 0 <= i < j < kept.len() implies !cursor_key_eq(kept[i], kept[j]) by {
                    let left = if i < index { i } else { i + 1 };
                    let right = if j < index { j } else { j + 1 };
                    assert(kept[i] == cursors[left]); assert(kept[j] == cursors[right]);
                }
            } else {
                assert forall|i: int| 0 <= i < kept.len() implies !cursor_key_eq(kept[i], cursor) && cursors.contains(kept[i]) by {
                    assert(kept[i] == cursors[i]);
                }
                assert forall|i: int, j: int| 0 <= i < j < kept.len() implies !cursor_key_eq(kept[i], kept[j]) by {
                    assert(kept[i] == cursors[i]); assert(kept[j] == cursors[j]);
                }
            }
        }
        }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{ArenaStorage, CanonicalStore};
    use crate::store::HistoryStore;
    use junco_core::kernel::Bindings;
    use junco_core::limits::Unmetered;

    #[test]
    fn publication_evicts_replaces_and_retains_longer_prefix() -> Result<(), HistoryError> {
        let store = HistoryStore::global();
        let graph = CanonicalStore::new(ArenaStorage::new()?, &mut ObservationWorld)?;
        let mut cache = CursorCache::new(&mut Unmetered, &mut ObservationWorld)?;
        let mut handles = Vec::new();
        for _ in 0..=HISTORY_CACHE_CAPACITY {
            let history = store.new_history(&mut Unmetered, &mut ObservationWorld)?;
            cache.publish(HistoryCursor {
                history: history.index(),
                bindings: Bindings::new([0; 3]),
                revision: 0,
                consumed: 3,
                residual: graph.constants().all,
            });
            handles.push(history);
        }
        assert_eq!(cache.entries().len(), HISTORY_CACHE_CAPACITY);
        assert!(
            !cache
                .entries()
                .iter()
                .any(|entry| entry.history == handles[0].index())
        );
        let replacement = HistoryCursor {
            history: handles[8].index(),
            bindings: Bindings::new([0; 3]),
            revision: 0,
            consumed: 5,
            residual: graph.constants().epsilon,
        };
        cache.publish(replacement);
        assert_eq!(cache.entries()[0].history, replacement.history);
        assert_eq!(
            cache
                .entries()
                .iter()
                .filter(|entry| entry.history == replacement.history)
                .count(),
            1
        );
        let before = cache.entries().to_vec();
        cache.publish(HistoryCursor {
            consumed: 4,
            residual: graph.constants().empty,
            ..replacement
        });
        assert_eq!(cache.entries().len(), before.len());
        for (old, new) in before.iter().zip(cache.entries()) {
            assert_eq!(old.history, new.history);
            assert_eq!(old.bindings, new.bindings);
            assert_eq!(old.revision, new.revision);
            assert_eq!(old.consumed, new.consumed);
            assert_eq!(old.residual, new.residual);
        }
        Ok(())
    }
}

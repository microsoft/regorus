// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Interned string operands for `EqCore` atoms: equal ids iff equal UTF-8 bytes.

use super::graph::{allocation, ObservationWorld};
use super::kernel::KernelResult;
use crate::Value;
use alloc::vec::Vec;
pub(crate) use namespacius::PathId as StringId;
use namespacius::{AllocErr, PathCache};
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

/// Per-pair budget: 4096 trie nodes (16 KiB), 64 KiB of component bytes, 1024 memoized
/// full paths. bumpus chunks are allocated eagerly, so this is the fixed cost per pair.
#[verus_verify]
const MAX_NODES: usize = 4096;
#[verus_verify]
const MAX_BYTES: usize = 64 * 1024;
#[verus_verify]
const MEMO_ENTRIES: usize = 1024;

// ponytail: after arena exhaustion every compare falls back to `Value::eq` for the
// pair's lifetime; memo misses allocate a boxed key. Raise the budget if profiles of
// high-cardinality histories show either.
#[verus_verify]
pub(crate) struct Interner {
    cache: PathCache,
    exhausted: bool,
}

#[verus_verify(external)]
impl core::fmt::Debug for Interner {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Interner")
            .field("len", &self.cache.len())
            .field("exhausted", &self.exhausted)
            .finish()
    }
}

#[verus_verify]
impl Interner {
    #[verus_spec(result => ensures result matches Ok(i) ==> i.inv() && i@.len() == 1)]
    pub(crate) fn new() -> Result<Self, AllocErr> {
        Ok(Self {
            cache: PathCache::with_capacity("/", MAX_NODES, MAX_BYTES, MEMO_ENTRIES)?,
            exhausted: false,
        })
    }

    #[verus_spec(result =>
        requires old(self).inv(),
        ensures final(self).inv(), interner_frame(*old(self), *final(self)),
            result matches Some(id) ==> final(self).interned(id, text@),
    )]
    pub(crate) fn intern(&mut self, text: &str) -> Option<StringId> {
        if self.exhausted {
            return None;
        }
        match self.cache.intern(text) {
            Ok(id) => Some(id),
            Err(_) => {
                self.exhausted = true;
                None
            }
        }
    }

    #[verus_spec(result =>
        requires old(self).inv(),
        ensures final(self).inv(), interner_frame(*old(self), *final(self)),
            result matches Ok(ids) ==> ids_wf(*final(self), values@, ids@),
    )]
    pub(crate) fn intern_values(
        &mut self,
        values: &[Value],
        world: &mut ObservationWorld,
    ) -> KernelResult<Vec<Option<StringId>>> {
        proof_decl! { let ghost entry = *self; }
        let mut ids = Vec::new();
        allocation(world.try_reserve_exact_vec(&mut ids, values.len()))?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant self.inv(), interner_frame(entry, *self),
                index <= values@.len(), ids@.len() == index,
                ids_wf(*self, values@.take(index as int), ids@),
            decreases values@.len() - index,
        ))]
        while index < values.len() {
            proof_decl! { let ghost before = *self; }
            let id = match values.get(index) {
                Some(Value::String(text)) => self.intern(text),
                _ => None,
            };
            proof! {
                lemma_ids_wf_frame(before, *self, values@.take(index as int), ids@);
                lemma_interner_frame_trans(entry, before, *self);
                assert(values@.take(index as int + 1) =~= values@.take(index as int).push(values@[index as int]));
            }
            ids.push(id);
            index = index.saturating_add(1);
        }
        Ok(ids)
    }

    pub(crate) fn free(self) {
        self.cache.free();
    }

    #[cfg(test)]
    pub(crate) const fn is_exhausted(&self) -> bool {
        self.exhausted
    }
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    use vstd::utf8::{encode_utf8, encode_utf8_decode_utf8};
    verus! {
    impl View for Interner {
        type V = Seq<Seq<Seq<u8>>>;
        open(super) spec fn view(&self) -> Seq<Seq<Seq<u8>>> { self.cache@ }
    }
    impl Interner {
        pub open(super) spec fn inv(&self) -> bool { self.cache.inv() }
        pub open(super) spec fn delim(&self) -> Seq<u8> { self.cache.delim() }
        /// `id` was returned by this cache for the UTF-8 bytes of `chars`.
        pub open(crate) spec fn interned(&self, id: StringId, chars: Seq<char>) -> bool {
            1 <= id.0 < self@.len()
                && self@[id.0 as int] == namespacius::split(encode_utf8(chars), self.delim())
        }
    }
    /// Ids never invalidate: the view only grows and the delimiter is fixed.
    pub open(crate) spec fn interner_frame(before: Interner, after: Interner) -> bool {
        after.delim() == before.delim() && before@.len() <= after@.len()
        && forall|i: int| 0 <= i < before@.len() ==> #[trigger] after@[i] == before@[i]
    }
    /// `ids[i]` is `Some` only for string `values[i]`, and then names exactly its bytes.
    pub open(crate) spec fn ids_wf(interner: Interner, values: Seq<Value>, ids: Seq<Option<StringId>>) -> bool {
        ids.len() == values.len()
        && forall|i: int| 0 <= i < ids.len() && #[trigger] ids[i] is Some
            ==> match values[i] {
                Value::String(text) => interner.interned(ids[i]->Some_0, text@),
                _ => false,
            }
    }
    pub proof fn lemma_interned_frame(before: Interner, after: Interner, id: StringId, chars: Seq<char>)
        requires before.interned(id, chars), interner_frame(before, after),
        ensures after.interned(id, chars),
    {}
    pub proof fn lemma_interner_frame_trans(a: Interner, b: Interner, c: Interner)
        requires interner_frame(a, b), interner_frame(b, c),
        ensures interner_frame(a, c),
    {}
    pub proof fn lemma_ids_wf_frame(before: Interner, after: Interner, values: Seq<Value>, ids: Seq<Option<StringId>>)
        requires ids_wf(before, values, ids), interner_frame(before, after),
        ensures ids_wf(after, values, ids),
    {
        assert forall|i: int| 0 <= i < ids.len() && #[trigger] ids[i] is Some
            implies match values[i] {
                Value::String(text) => after.interned(ids[i]->Some_0, text@),
                _ => false,
            } by {
            if let Value::String(text) = values[i] {
                lemma_interned_frame(before, after, ids[i]->Some_0, text@);
            }
        }
    }
    /// The compare theorem: equal ids iff equal char sequences.
    pub proof fn lemma_interned_eq(interner: Interner, a: Seq<char>, ia: StringId, b: Seq<char>, ib: StringId)
        requires interner.inv(), interner.interned(ia, a), interner.interned(ib, b),
        ensures (ia.0 == ib.0) <==> (a == b),
    {
        interner.cache.lemma_id_eq_bytes(encode_utf8(a), ia, encode_utf8(b), ib);
        if ia == ib { encode_utf8_decode_utf8(a); encode_utf8_decode_utf8(b); }
    }
    }
}

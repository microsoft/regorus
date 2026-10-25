// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Hash-consing mixes `u32` ids, counts, and flags into `u64` digests; every cast widens.
#![allow(clippy::as_conversions)]

#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
use super::{error::HistoryError, kernel::*};
use crate::utils::limits::{check_memory_limit_if_needed, monotonic_now, ExecutionTimer};
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::{KernelStoreSpec, SmallVecSpecFns, StorageSpec};
use alloc::vec::Vec;
use core::mem::{align_of, size_of};
use hashconsius::BHConsign;
use smallvec::SmallVec;
use verus_bumpalo::{AllocErr, SliceArena, CHUNK_ALIGN};
use vstd::prelude::*;

/// Capability for native observations made during one matcher call.
#[expect(
    clippy::redundant_pub_crate,
    reason = "Capability is re-exported at the builtin boundary."
)]
#[verus_verify]
pub(crate) struct ObservationWorld;

#[expect(
    clippy::unused_self,
    reason = "The native ZST carries mutable observation state in extraction."
)]
impl ObservationWorld {
    #[verus_verify(external_body)]
    #[inline]
    pub(crate) fn now(&mut self) -> Option<core::time::Duration> {
        monotonic_now()
    }

    #[verus_verify(external_body)]
    #[verus_spec(result => ensures final(values)@ == old(values)@)]
    #[inline]
    pub(crate) fn try_reserve_vec<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        values.try_reserve(additional)
    }

    #[verus_verify(external_body)]
    #[verus_spec(result => ensures final(values)@ == old(values)@)]
    #[inline]
    pub(crate) fn try_reserve_exact_vec<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        values.try_reserve_exact(additional)
    }

    #[verus_verify(external_body)]
    #[verus_spec(result => ensures final(values).view() == old(values).view())]
    #[inline]
    pub(crate) fn try_reserve_words(
        &mut self,
        values: &mut SmallVec<[u64; 2]>,
        additional: usize,
    ) -> Result<(), smallvec::CollectionAllocErr> {
        values.try_reserve_exact(additional)
    }
}

#[verus_verify]
#[inline(always)]
pub(crate) fn checkpoint(
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<()> {
    if timer.accumulate(1) {
        deadline_check(timer, world)?;
    }
    check_memory_limit_if_needed()?;
    Ok(())
}

/// Clock read and deadline comparison, out of line so the inlined `checkpoint`
/// body stays a counter bump when no check is due.
#[verus_verify]
#[cold]
#[inline(never)]
fn deadline_check(timer: &mut ExecutionTimer, world: &mut ObservationWorld) -> KernelResult<()> {
    if let Some(now) = world.now() {
        timer.check_now(now)?;
    }
    Ok(())
}

#[verus_verify]
#[verus_spec(result => ensures result == (HistoryError::Invariant { message }))]
pub(crate) const fn invariant(message: &'static str) -> HistoryError {
    HistoryError::Invariant { message }
}
#[verus_verify]
#[verus_spec(result => ensures result == match value {
    Some(value) => Ok(value),
    None => Err((HistoryError::Invariant { message })),
})]
fn present<T>(value: Option<T>, message: &'static str) -> KernelResult<T> {
    match value {
        Some(value) => Ok(value),
        None => Err(HistoryError::Invariant { message }),
    }
}
#[verus_verify]
#[verus_spec(outcome => ensures outcome == match result {
    Ok(value) => Ok(value),
    Err(_) => Err(HistoryError::AllocationFailed),
})]
pub(crate) fn allocation<T>(result: Result<T, impl core::fmt::Debug>) -> KernelResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(_) => Err(HistoryError::AllocationFailed),
    }
}
/// Arena pushes: `Exhausted` is the only error the capacity theorem reasons about.
#[verus_verify]
#[verus_spec(outcome => ensures outcome == match result {
    Ok(value) => Ok(value),
    Err(AllocErr::Exhausted) => Err(HistoryError::ArenaExhausted),
    Err(_) => Err(HistoryError::AllocationFailed),
})]
fn arena<T>(result: Result<T, AllocErr>) -> KernelResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(AllocErr::Exhausted) => Err(HistoryError::ArenaExhausted),
        Err(AllocErr::Global | AllocErr::Capacity) => Err(HistoryError::AllocationFailed),
    }
}

/// Chunk size per arena. Sufficiency: every pushed byte is charged via `projected` first;
/// `size_of::<ArenaX>() > 0`, `align_of::<ArenaX>() <= CHUNK_ALIGN` and
/// `ARENA_CAPACITY % align == 0` are asserted below for every compile target and re-checked at
/// runtime in `ArenaTables::with_capacity` so Verus can use them; same-type allocations from an
/// aligned cursor never pad. Theorem (`CanonicalStore::intern_*`): `ArenaExhausted` is returned
/// only if `storage.slack() < MAX_GRAPH_BYTES - storage.capacity()`, which a production store
/// (`capacity == MAX_GRAPH_BYTES`, `slack == 0`) never satisfies.
// ponytail: six fixed 100 KiB chunks per retained pair; share a chunk if allocation cost matters.
#[verus_verify]
pub(crate) const ARENA_CAPACITY: usize = MAX_GRAPH_BYTES;
// Premises of the capacity argument, checked on every compile target. `%` rather than
// `is_multiple_of` so Verus can reason about the same expression at runtime below.
#[allow(clippy::manual_is_multiple_of)]
const _: () = assert!(
    size_of::<ArenaTest>() > 0
        && size_of::<ArenaRegex>() > 0
        && size_of::<ArenaTransition>() > 0
        && align_of::<ArenaTest>() <= CHUNK_ALIGN
        && align_of::<ArenaRegex>() <= CHUNK_ALIGN
        && align_of::<ArenaTransition>() <= CHUNK_ALIGN
        && ARENA_CAPACITY % align_of::<ArenaTest>() == 0
        && ARENA_CAPACITY % align_of::<ArenaRegex>() == 0
        && ARENA_CAPACITY % align_of::<ArenaTransition>() == 0
        && ARENA_CAPACITY % align_of::<TestId>() == 0
        && ARENA_CAPACITY % align_of::<RegexId>() == 0
        && ARENA_CAPACITY % align_of::<TransitionId>() == 0
);
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(bytes) => bytes as int == len * vstd::layout::size_of::<T>(),
    Err(error) => error is GraphLimit,
})]
pub(crate) fn sequence_bytes<T>(len: usize) -> KernelResult<usize> {
    vstd::layout::layout_for_type_is_valid::<T>();
    len.checked_mul(size_of::<T>())
        .ok_or(HistoryError::GraphLimit {
            limit: MAX_GRAPH_BYTES,
        })
}

pub(crate) trait Storage {
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>>;
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>>;
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>>;
    fn find_test(&self, view: TestView<'_>) -> KernelResult<Option<TestId>>;
    fn find_regex(&self, view: RegexView<'_>) -> KernelResult<Option<RegexId>>;
    fn find_transition(&self, view: TransitionView<'_>) -> KernelResult<Option<TransitionId>>;
    fn push_test(
        &mut self,
        view: TestView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<TestId>;
    fn push_regex(
        &mut self,
        view: RegexView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId>;
    fn push_transition(
        &mut self,
        view: TransitionView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<TransitionId>;
    fn release(self);
}
// Crate visibility lets Verus retain these payload types in the open weight specs.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) enum ArenaTest {
    True,
    False,
    Atom {
        primitive: Primitive,
        positive: bool,
    },
    And(usize),
    Or(usize),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
enum ArenaRegexKind {
    Empty,
    All,
    Epsilon,
    Test(TestId),
    Union(usize),
    Concat(usize),
    Star(RegexId),
    Intersect(usize),
    Not(RegexId),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) struct ArenaRegex {
    kind: ArenaRegexKind,
    nullable: bool,
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) enum ArenaTransition {
    Const(RegexId),
    If {
        test: TestId,
        then_transition: TransitionId,
        else_transition: TransitionId,
    },
    Union(usize),
    Intersect(usize),
    Not(TransitionId),
    Append {
        transition: TransitionId,
        suffix: usize,
    },
}

// Identity keys keep hash-consing over arena records, not lifted graph nodes.
vstd::prelude::verus! {
    impl View for ArenaTest {
        type V = Self;
        open(in crate::builtins::history::graph) spec fn view(&self) -> Self { *self }
    }
    impl View for ArenaRegex {
        type V = Self;
        open(in crate::builtins::history::graph) spec fn view(&self) -> Self { *self }
    }
    impl View for ArenaTransition {
        type V = Self;
        open(in crate::builtins::history::graph) spec fn view(&self) -> Self { *self }
    }

    pub(crate) open spec fn primitive_key_hash(p: Primitive) -> u64 {
        match p {
            Primitive::HasValue(p) => hashconsius::spec_mix(0, p.0 as u64),
            Primitive::EqCore(p, Term::Constant(c)) => hashconsius::spec_mix(hashconsius::spec_mix(hashconsius::spec_mix(1, p.0 as u64), 0), c.0 as u64),
            Primitive::EqCore(p, Term::Variable(v)) => hashconsius::spec_mix(hashconsius::spec_mix(hashconsius::spec_mix(1, p.0 as u64), 1), v.0 as u64),
        }
    }
    fn hash_primitive_key(p: Primitive) -> (h: u64)
        ensures h == primitive_key_hash(p),
    {
        match p {
            Primitive::HasValue(p) => hashconsius::mix(0, p.0 as u64),
            Primitive::EqCore(p, Term::Constant(c)) => hashconsius::mix(hashconsius::mix(hashconsius::mix(1, p.0 as u64), 0), c.0 as u64),
            Primitive::EqCore(p, Term::Variable(v)) => hashconsius::mix(hashconsius::mix(hashconsius::mix(1, p.0 as u64), 1), v.0 as u64),
        }
    }
    impl hashconsius::HashKey for ArenaTest {
        open(in crate::builtins::history::graph) spec fn spec_hash(v: Self::V) -> u64 { match v {
                ArenaTest::True => 0,
                ArenaTest::False => 1,
                ArenaTest::Atom { primitive, positive } => hashconsius::spec_mix(hashconsius::spec_mix(2, primitive_key_hash(primitive)), positive as u64),
                ArenaTest::And(s) => hashconsius::spec_mix(3, s as u64),
                ArenaTest::Or(s) => hashconsius::spec_mix(4, s as u64),
            } }
        fn hash(&self) -> (h: u64)
            ensures h == Self::spec_hash(self@),
        {
            let v = *self;
            match v {
                ArenaTest::True => 0,
                ArenaTest::False => 1,
                ArenaTest::Atom { primitive, positive } => hashconsius::mix(hashconsius::mix(2, hash_primitive_key(primitive)), positive as u64),
                ArenaTest::And(s) => hashconsius::mix(3, s as u64),
                ArenaTest::Or(s) => hashconsius::mix(4, s as u64),
            }
        }
        fn key_eq(&self, other: &Self) -> (b: bool)
            ensures b == (self@ == other@),
        { match (*self, *other) {
                (ArenaTest::True, ArenaTest::True) | (ArenaTest::False, ArenaTest::False) => true,
                (ArenaTest::Atom { primitive: a, positive: p }, ArenaTest::Atom { primitive: b, positive: q }) => a == b && p == q,
                (ArenaTest::And(a), ArenaTest::And(b)) | (ArenaTest::Or(a), ArenaTest::Or(b)) => a == b,
                _ => false,
            } }
    }
    impl hashconsius::HashKey for ArenaRegex {
        open(in crate::builtins::history::graph) spec fn spec_hash(v: Self::V) -> u64 { hashconsius::spec_mix(match v.kind {
                ArenaRegexKind::Empty => 0,
                ArenaRegexKind::All => 1,
                ArenaRegexKind::Epsilon => 2,
                ArenaRegexKind::Test(id) => hashconsius::spec_mix(3, id.0 as u64),
                ArenaRegexKind::Union(s) => hashconsius::spec_mix(4, s as u64),
                ArenaRegexKind::Concat(s) => hashconsius::spec_mix(5, s as u64),
                ArenaRegexKind::Star(id) => hashconsius::spec_mix(6, id.0 as u64),
                ArenaRegexKind::Intersect(s) => hashconsius::spec_mix(7, s as u64),
                ArenaRegexKind::Not(id) => hashconsius::spec_mix(8, id.0 as u64),
            }, v.nullable as u64) }
        fn hash(&self) -> (h: u64)
            ensures h == Self::spec_hash(self@),
        {
            let v = *self;
            hashconsius::mix(match v.kind {
                ArenaRegexKind::Empty => 0,
                ArenaRegexKind::All => 1,
                ArenaRegexKind::Epsilon => 2,
                ArenaRegexKind::Test(id) => hashconsius::mix(3, id.0 as u64),
                ArenaRegexKind::Union(s) => hashconsius::mix(4, s as u64),
                ArenaRegexKind::Concat(s) => hashconsius::mix(5, s as u64),
                ArenaRegexKind::Star(id) => hashconsius::mix(6, id.0 as u64),
                ArenaRegexKind::Intersect(s) => hashconsius::mix(7, s as u64),
                ArenaRegexKind::Not(id) => hashconsius::mix(8, id.0 as u64),
            }, v.nullable as u64)
        }
        fn key_eq(&self, other: &Self) -> (b: bool)
            ensures b == (self@ == other@),
        { self.nullable == other.nullable && match (self.kind, other.kind) {
                (ArenaRegexKind::Empty, ArenaRegexKind::Empty) | (ArenaRegexKind::All, ArenaRegexKind::All) | (ArenaRegexKind::Epsilon, ArenaRegexKind::Epsilon) => true,
                (ArenaRegexKind::Test(a), ArenaRegexKind::Test(b)) => a == b,
                (ArenaRegexKind::Union(a), ArenaRegexKind::Union(b)) | (ArenaRegexKind::Concat(a), ArenaRegexKind::Concat(b)) | (ArenaRegexKind::Intersect(a), ArenaRegexKind::Intersect(b)) => a == b,
                (ArenaRegexKind::Star(a), ArenaRegexKind::Star(b)) | (ArenaRegexKind::Not(a), ArenaRegexKind::Not(b)) => a == b,
                _ => false,
            } }
    }
    impl hashconsius::HashKey for ArenaTransition {
        open(in crate::builtins::history::graph) spec fn spec_hash(v: Self::V) -> u64 { match v {
                ArenaTransition::Const(id) => hashconsius::spec_mix(0, id.0 as u64),
                ArenaTransition::If { test, then_transition, else_transition } => hashconsius::spec_mix(hashconsius::spec_mix(hashconsius::spec_mix(1, test.0 as u64), then_transition.0 as u64), else_transition.0 as u64),
                ArenaTransition::Union(s) => hashconsius::spec_mix(2, s as u64),
                ArenaTransition::Intersect(s) => hashconsius::spec_mix(3, s as u64),
                ArenaTransition::Not(id) => hashconsius::spec_mix(4, id.0 as u64),
                ArenaTransition::Append { transition, suffix } => hashconsius::spec_mix(hashconsius::spec_mix(5, transition.0 as u64), suffix as u64),
            } }
        fn hash(&self) -> (h: u64)
            ensures h == Self::spec_hash(self@),
        {
            let v = *self;
            match v {
                ArenaTransition::Const(id) => hashconsius::mix(0, id.0 as u64),
                ArenaTransition::If { test, then_transition, else_transition } => hashconsius::mix(hashconsius::mix(hashconsius::mix(1, test.0 as u64), then_transition.0 as u64), else_transition.0 as u64),
                ArenaTransition::Union(s) => hashconsius::mix(2, s as u64),
                ArenaTransition::Intersect(s) => hashconsius::mix(3, s as u64),
                ArenaTransition::Not(id) => hashconsius::mix(4, id.0 as u64),
                ArenaTransition::Append { transition, suffix } => hashconsius::mix(hashconsius::mix(5, transition.0 as u64), suffix as u64),
            }
        }
        fn key_eq(&self, other: &Self) -> (b: bool)
            ensures b == (self@ == other@),
        { match (*self, *other) {
                (ArenaTransition::Const(a), ArenaTransition::Const(b)) => a == b,
                (ArenaTransition::If { test: a, then_transition: b, else_transition: c }, ArenaTransition::If { test: d, then_transition: e, else_transition: f }) => a == d && b == e && c == f,
                (ArenaTransition::Union(a), ArenaTransition::Union(b)) | (ArenaTransition::Intersect(a), ArenaTransition::Intersect(b)) => a == b,
                (ArenaTransition::Not(a), ArenaTransition::Not(b)) => a == b,
                (ArenaTransition::Append { transition: a, suffix: b }, ArenaTransition::Append { transition: c, suffix: d }) => a == c && b == d,
                _ => false,
            } }
    }
}

macro_rules! id_lists {
    ($name:ident, $id:ident) => {
        #[verus_verify]
        struct $name {
            slices: SliceArena<$id>,
            index: hashconsius::index::Buckets,
        }
        vstd::prelude::verus! {
            impl View for $name {
                type V = Seq<Seq<$id>>;
                open(in crate::builtins::history::graph) spec fn view(&self) -> Self::V { self.slices@ }
            }
            impl $name {
                pub(super) open(in crate::builtins::history::graph) spec fn ids_hash_prefix(ids: Seq<$id>, n: nat) -> u64
                    recommends n <= ids.len(),
                    decreases n,
                {
                    if n == 0 { ids.len() as u64 }
                    else { hashconsius::spec_mix(Self::ids_hash_prefix(ids, (n - 1) as nat), ids[n - 1].0 as u64) }
                }
                pub(super) open(in crate::builtins::history::graph) spec fn ids_spec_hash(ids: Seq<$id>) -> u64 {
                    Self::ids_hash_prefix(ids, ids.len())
                }
                pub(super) open(in crate::builtins::history::graph) spec fn hashes(self) -> Seq<u64> {
                    self@.map_values(|ids: Seq<$id>| Self::ids_spec_hash(ids))
                }
                pub(super) open(in crate::builtins::history::graph) spec fn inv(self) -> bool {
                    self.index.inv(self.hashes()) && self@.no_duplicates()
                        && self@.len() <= usize::MAX
                }
                pub(super) open(in crate::builtins::history::graph) spec fn capacity(self) -> int { self.slices.capacity() }
                pub(super) open(in crate::builtins::history::graph) spec fn remaining(self) -> int { self.slices.remaining() }
                pub(super) open(in crate::builtins::history::graph) spec fn aligned(self) -> bool { self.slices.aligned() }

                fn ids_hash(ids: &[$id]) -> (h: u64)
                    ensures h == Self::ids_spec_hash(ids@),
                {
                    let mut h = ids.len() as u64;
                    let mut i = 0;
                    while i < ids.len()
                        invariant i <= ids.len(), h == Self::ids_hash_prefix(ids@, i as nat),
                        decreases ids.len() - i,
                    {
                        let id = match ids.get(i) { Some(id) => id, None => return h };
                        h = hashconsius::mix(h, id.0 as u64);
                        i = i.saturating_add(1);
                    }
                    h
                }

                fn with_capacity(bytes: usize) -> (r: Result<Self, AllocErr>)
                    ensures r matches Ok(a) ==> a.inv() && a@ == Seq::<Seq<$id>>::empty()
                        && a.capacity() == bytes && a.remaining() == bytes
                        && (vstd::layout::align_of::<$id>() <= CHUNK_ALIGN
                            && bytes as int % vstd::layout::align_of::<$id>() as int == 0 ==> a.aligned()),
                {
                    vstd::layout::layout_for_type_is_valid::<$id>();
                    let slices = SliceArena::with_capacity(bytes)?;
                    let index = hashconsius::index::Buckets::new(64);
                    let result = Self { slices, index };
                    proof { assert(result.hashes() =~= Seq::<u64>::empty()); }
                    Ok(result)
                }

                fn len(&self) -> (n: usize)
                    ensures n == self@.len(),
                { self.slices.len() }

                fn get(&self, slot: usize) -> (r: Option<&[$id]>)
                    ensures
                        r matches Some(ids) ==> slot < self@.len() && ids@ == self@[slot as int],
                        r is None ==> slot >= self@.len(),
                { self.slices.get(slot) }

                fn find(&self, ids: &[$id]) -> (r: Option<usize>)
                    requires self.inv(),
                    ensures
                        r matches Some(slot) ==> slot < self@.len() && self@[slot as int] == ids@,
                        r is None ==> !self@.contains(ids@),
                {
                    let h = Self::ids_hash(ids);
                    proof { self.index.lemma_nonempty(self.hashes()); }
                    let bucket = self.index.bucket(h);
                    let mut j = 0;
                    while j < bucket.len()
                        invariant
                            self.inv(), h == Self::ids_spec_hash(ids@),
                            self.index.nb() > 0,
                            bucket@ == self.index.bucket_of(h), j <= bucket@.len(),
                            forall|k: int| 0 <= k < j ==> bucket@[k].1 < self@.len()
                                && !(bucket@[k].0 == h && self@[bucket@[k].1 as int] == ids@),
                        decreases bucket@.len() - j,
                    {
                        let (bh, slot) = match bucket.get(j) {
                            Some(entry) => *entry,
                            None => return None,
                        };
                        proof { self.index.lemma_sound(self.hashes(), h, j as int); }
                        if bh == h {
                            let candidate = match self.slices.get(slot) {
                                Some(candidate) => candidate,
                                None => return None,
                            };
                            if super::kernel::id_slice_eq(candidate, ids) { return Some(slot); }
                        }
                        j = j.saturating_add(1);
                    }
                    proof {
                        assert forall|slot: int| 0 <= slot < self@.len()
                            implies self@[slot] != ids@ by {
                            if self@[slot] == ids@ {
                                self.index.lemma_complete(self.hashes(), slot);
                                assert(self.hashes()[slot] == h);
                                let k = bucket@.lemma_contains_to_index((h, slot as usize));
                                assert(bucket@[k] == (h, slot as usize));
                            }
                        }
                    }
                    None
                }

                fn intern(&mut self, ids: &[$id]) -> (r: Result<usize, AllocErr>)
                    requires old(self).inv(),
                    ensures
                        final(self).inv(),
                        old(self)@.is_prefix_of(final(self)@),
                        final(self).capacity() == old(self).capacity(),
                        old(self).aligned() ==> final(self).aligned(),
                        r is Err ==> final(self)@ == old(self)@
                            && final(self).remaining() == old(self).remaining()
                            && final(self).aligned() == old(self).aligned(),
                        r matches Ok(slot) ==> slot < final(self)@.len()
                            && final(self)@[slot as int] == ids@
                            && (old(self)@.contains(ids@) ==>
                                final(self)@ == old(self)@
                                && final(self).remaining() == old(self).remaining())
                            && (!old(self)@.contains(ids@) ==>
                                slot == old(self)@.len() && final(self)@ == old(self)@.push(ids@)
                                && (old(self).aligned() ==> final(self).remaining()
                                    == old(self).remaining() - ids@.len() * vstd::layout::size_of::<$id>())),
                        old(self).aligned() && r == Err(AllocErr::Exhausted) ==>
                            ids@.len() * vstd::layout::size_of::<$id>() > old(self).remaining(),
                {
                    vstd::layout::layout_for_type_is_valid::<$id>();
                    let ghost before = *self;
                    match self.find(ids) {
                        Some(slot) => return Ok(slot),
                        None => {},
                    }
                    let h = Self::ids_hash(ids);
                    let ghost hashes = self.hashes();
                    let slot = self.len();
                    self.slices.try_push(ids)?;
                    let _count = self.slices.len();
                    proof {
                        assert(self@ == before@.push(ids@));
                        assert(self@.no_duplicates());
                        assert(self.hashes() =~= hashes.push(h));
                        assert(hashes.len() < usize::MAX) by {
                            assert(_count == hashes.len() + 1);
                        }
                    }
                    self.index.insert(h, slot, Ghost(hashes));
                    Ok(slot)
                }

                fn free(self)
                    requires self.inv(),
                { self.slices.free(); }
            }
        }
    };
}

id_lists!(TestIdLists, TestId);
id_lists!(RegexIdLists, RegexId);
id_lists!(TransitionIdLists, TransitionId);

#[verus_verify]
struct ArenaTables {
    tests: BHConsign<ArenaTest>,
    test_ids: TestIdLists,
    regexes: BHConsign<ArenaRegex>,
    regex_ids: RegexIdLists,
    transitions: BHConsign<ArenaTransition>,
    transition_ids: TransitionIdLists,
}
#[verus_verify]
pub(crate) struct ArenaStorage {
    tables: Option<ArenaTables>,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl ArenaStorage {
        #[verifier::type_invariant]
        closed spec fn inv(&self) -> bool {
            self.tables is Some ==> verify::tables_wf(&self.tables->0)
        }
    }
}

#[verus_verify]
impl ArenaTables {
    #[verus_spec(result => ensures result matches Ok(t) ==> verify::tables_wf(&t)
        && verify::empty_tables(verify::tables_graph(&t))
        && verify::tables_capacity(&t) == capacity && verify::tables_slack(&t) == 0)]
    #[allow(clippy::manual_is_multiple_of)]
    fn with_capacity(capacity: usize) -> KernelResult<Self> {
        vstd::layout::layout_for_type_is_valid::<ArenaTest>();
        vstd::layout::layout_for_type_is_valid::<ArenaRegex>();
        vstd::layout::layout_for_type_is_valid::<ArenaTransition>();
        vstd::layout::layout_for_type_is_valid::<TestId>();
        vstd::layout::layout_for_type_is_valid::<RegexId>();
        vstd::layout::layout_for_type_is_valid::<TransitionId>();
        // Statically true (see the `const _` assert above); repeated here so Verus can use it.
        if size_of::<ArenaTest>() == 0
            || size_of::<ArenaRegex>() == 0
            || size_of::<ArenaTransition>() == 0
            || align_of::<ArenaTest>() > CHUNK_ALIGN
            || align_of::<ArenaRegex>() > CHUNK_ALIGN
            || align_of::<ArenaTransition>() > CHUNK_ALIGN
            || align_of::<TestId>() > CHUNK_ALIGN
            || align_of::<RegexId>() > CHUNK_ALIGN
            || align_of::<TransitionId>() > CHUNK_ALIGN
            || capacity % align_of::<ArenaTest>() != 0
            || capacity % align_of::<ArenaRegex>() != 0
            || capacity % align_of::<ArenaTransition>() != 0
            || capacity % align_of::<TestId>() != 0
            || capacity % align_of::<RegexId>() != 0
            || capacity % align_of::<TransitionId>() != 0
        {
            return Err(invariant("arena layout premises violated"));
        }
        let tests = allocation(BHConsign::new(capacity))?;
        let test_ids = match TestIdLists::with_capacity(capacity) {
            Ok(arena) => arena,
            Err(_) => {
                tests.free();
                return Err(HistoryError::AllocationFailed);
            }
        };
        let regexes = match BHConsign::new(capacity) {
            Ok(arena) => arena,
            Err(_) => {
                tests.free();
                test_ids.free();
                return Err(HistoryError::AllocationFailed);
            }
        };
        let regex_ids = match RegexIdLists::with_capacity(capacity) {
            Ok(arena) => arena,
            Err(_) => {
                tests.free();
                test_ids.free();
                regexes.free();
                return Err(HistoryError::AllocationFailed);
            }
        };
        let transitions = match BHConsign::new(capacity) {
            Ok(arena) => arena,
            Err(_) => {
                tests.free();
                test_ids.free();
                regexes.free();
                regex_ids.free();
                return Err(HistoryError::AllocationFailed);
            }
        };
        let transition_ids = match TransitionIdLists::with_capacity(capacity) {
            Ok(arena) => arena,
            Err(_) => {
                tests.free();
                test_ids.free();
                regexes.free();
                regex_ids.free();
                transitions.free();
                return Err(HistoryError::AllocationFailed);
            }
        };
        let tables = Self {
            tests,
            test_ids,
            regexes,
            regex_ids,
            transitions,
            transition_ids,
        };
        proof! { verify::lemma_fresh_tables(&tables, capacity); }
        Ok(tables)
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result.0 == verify::tables_graph(self).tests.len(),
        result.1 == verify::tables_graph(self).regexes.len(),
        result.2 == verify::tables_graph(self).transitions.len())]
    fn lengths(&self) -> (usize, usize, usize) {
        (self.tests.len(), self.regexes.len(), self.transitions.len())
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(v) ==> index < verify::tables_graph(self).tests.len()
            && v@ == verify::tables_graph(self).tests[index as int],
        result matches Err(error) ==> error is Invariant)]
    fn test(&self, index: usize) -> KernelResult<TestView<'_>> {
        if index >= self.tests.len() {
            return Err(invariant("invalid test ID"));
        }
        let node = self.tests.elem(index);
        Ok(match *node {
            ArenaTest::True => TestView::True,
            ArenaTest::False => TestView::False,
            ArenaTest::Atom {
                primitive,
                positive,
            } => TestView::Atom {
                primitive,
                positive,
            },
            ArenaTest::And(slot) => {
                TestView::And(present(self.test_ids.get(slot), "invalid test children")?)
            }
            ArenaTest::Or(slot) => {
                TestView::Or(present(self.test_ids.get(slot), "invalid test children")?)
            }
        })
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(v) ==> index < verify::tables_graph(self).regexes.len()
            && v@ == verify::tables_graph(self).regexes[index as int],
        result matches Err(error) ==> error is Invariant)]
    fn regex(&self, index: usize) -> KernelResult<RegexView<'_>> {
        if index >= self.regexes.len() {
            return Err(invariant("invalid regex ID"));
        }
        let node = self.regexes.elem(index);
        let kind = match node.kind {
            ArenaRegexKind::Empty => RegexKindView::Empty,
            ArenaRegexKind::All => RegexKindView::All,
            ArenaRegexKind::Epsilon => RegexKindView::Epsilon,
            ArenaRegexKind::Test(id) => RegexKindView::Test(id),
            ArenaRegexKind::Union(slot) => {
                RegexKindView::Union(present(self.regex_ids.get(slot), "invalid regex children")?)
            }
            ArenaRegexKind::Concat(slot) => {
                RegexKindView::Concat(present(self.regex_ids.get(slot), "invalid regex children")?)
            }
            ArenaRegexKind::Star(id) => RegexKindView::Star(id),
            ArenaRegexKind::Intersect(slot) => RegexKindView::Intersect(present(
                self.regex_ids.get(slot),
                "invalid regex children",
            )?),
            ArenaRegexKind::Not(id) => RegexKindView::Not(id),
        };
        Ok(RegexView {
            kind,
            nullable: node.nullable,
        })
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(v) ==> index < verify::tables_graph(self).transitions.len()
            && v@ == verify::tables_graph(self).transitions[index as int],
        result matches Err(error) ==> error is Invariant)]
    fn transition(&self, index: usize) -> KernelResult<TransitionView<'_>> {
        if index >= self.transitions.len() {
            return Err(invariant("invalid transition ID"));
        }
        let node = self.transitions.elem(index);
        Ok(match *node {
            ArenaTransition::Const(id) => TransitionView::Const(id),
            ArenaTransition::If {
                test,
                then_transition,
                else_transition,
            } => TransitionView::If {
                test,
                then_transition,
                else_transition,
            },
            ArenaTransition::Union(slot) => TransitionView::Union(present(
                self.transition_ids.get(slot),
                "invalid transition children",
            )?),
            ArenaTransition::Intersect(slot) => TransitionView::Intersect(present(
                self.transition_ids.get(slot),
                "invalid transition children",
            )?),
            ArenaTransition::Not(id) => TransitionView::Not(id),
            ArenaTransition::Append { transition, suffix } => TransitionView::Append {
                transition,
                suffix: present(self.regex_ids.get(suffix), "invalid append suffix")?,
            },
        })
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(Some(id)) ==> id.0 < verify::tables_graph(self).tests.len()
            && verify::tables_graph(self).tests[id.0 as int] == view@,
        result matches Ok(None) ==> !verify::tables_graph(self).tests.contains(view@),
        result matches Err(error) ==> !(error is ArenaExhausted))]
    fn find_test(&self, view: TestView<'_>) -> KernelResult<Option<TestId>> {
        let node = match view {
            TestView::True => ArenaTest::True,
            TestView::False => ArenaTest::False,
            TestView::Atom {
                primitive,
                positive,
            } => ArenaTest::Atom {
                primitive,
                positive,
            },
            TestView::And(ids) | TestView::Or(ids) => {
                let Some(slot) = self.test_ids.find(ids) else {
                    proof! { verify::lemma_missing_test_children(self, view@, ids@); }
                    return Ok(None);
                };
                match view {
                    TestView::And(_) => ArenaTest::And(slot),
                    _ => ArenaTest::Or(slot),
                }
            }
        };
        proof! { verify::lemma_test_contains(self, node); }
        match self.tests.find(&node) {
            Some(slot) => Ok(Some(TestId::from_index(slot)?)),
            None => Ok(None),
        }
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(Some(id)) ==> id.0 < verify::tables_graph(self).regexes.len()
            && verify::tables_graph(self).regexes[id.0 as int] == view@,
        result matches Ok(None) ==> !verify::tables_graph(self).regexes.contains(view@),
        result matches Err(error) ==> !(error is ArenaExhausted))]
    fn find_regex(&self, view: RegexView<'_>) -> KernelResult<Option<RegexId>> {
        let kind = match view.kind {
            RegexKindView::Empty => ArenaRegexKind::Empty,
            RegexKindView::All => ArenaRegexKind::All,
            RegexKindView::Epsilon => ArenaRegexKind::Epsilon,
            RegexKindView::Test(id) => ArenaRegexKind::Test(id),
            RegexKindView::Star(id) => ArenaRegexKind::Star(id),
            RegexKindView::Not(id) => ArenaRegexKind::Not(id),
            RegexKindView::Union(ids)
            | RegexKindView::Concat(ids)
            | RegexKindView::Intersect(ids) => {
                let Some(slot) = self.regex_ids.find(ids) else {
                    proof! { verify::lemma_missing_regex_children(self, view@, ids@); }
                    return Ok(None);
                };
                match view.kind {
                    RegexKindView::Union(_) => ArenaRegexKind::Union(slot),
                    RegexKindView::Concat(_) => ArenaRegexKind::Concat(slot),
                    _ => ArenaRegexKind::Intersect(slot),
                }
            }
        };
        let node = ArenaRegex {
            kind,
            nullable: view.nullable,
        };
        proof! { verify::lemma_regex_contains(self, node); }
        match self.regexes.find(&node) {
            Some(slot) => Ok(Some(RegexId::from_index(slot)?)),
            None => Ok(None),
        }
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(Some(id)) ==> id.0 < verify::tables_graph(self).transitions.len()
            && verify::tables_graph(self).transitions[id.0 as int] == view@,
        result matches Ok(None) ==> !verify::tables_graph(self).transitions.contains(view@),
        result matches Err(error) ==> !(error is ArenaExhausted))]
    fn find_transition(&self, view: TransitionView<'_>) -> KernelResult<Option<TransitionId>> {
        let node = match view {
            TransitionView::Const(id) => ArenaTransition::Const(id),
            TransitionView::If {
                test,
                then_transition,
                else_transition,
            } => ArenaTransition::If {
                test,
                then_transition,
                else_transition,
            },
            TransitionView::Not(id) => ArenaTransition::Not(id),
            TransitionView::Union(ids) | TransitionView::Intersect(ids) => {
                let Some(slot) = self.transition_ids.find(ids) else {
                    proof! { verify::lemma_missing_transition_children(self, view@, ids@); }
                    return Ok(None);
                };
                match view {
                    TransitionView::Union(_) => ArenaTransition::Union(slot),
                    _ => ArenaTransition::Intersect(slot),
                }
            }
            TransitionView::Append { transition, suffix } => {
                let Some(slot) = self.regex_ids.find(suffix) else {
                    proof! { verify::lemma_missing_append_suffix(self, transition@, suffix@); }
                    return Ok(None);
                };
                ArenaTransition::Append {
                    transition,
                    suffix: slot,
                }
            }
        };
        proof! { verify::lemma_transition_contains(self, node); }
        match self.transitions.find(&node) {
            Some(slot) => Ok(Some(TransitionId::from_index(slot)?)),
            None => Ok(None),
        }
    }
    #[verus_spec(result => requires verify::tables_wf(old(self)),
        !verify::tables_graph(old(self)).tests.contains(view@), ensures
        verify::tables_wf(final(self)),
        verify::tables_graph(final(self)).constants == verify::tables_graph(old(self)).constants,
        verify::tables_graph(final(self)).regexes == verify::tables_graph(old(self)).regexes,
        verify::tables_graph(final(self)).transitions == verify::tables_graph(old(self)).transitions,
        result is Err ==> verify::tables_graph(final(self)) == verify::tables_graph(old(self)),
        result matches Ok(id) ==> id.0 == verify::tables_graph(old(self)).tests.len()
            && verify::tables_graph(final(self)).tests == verify::tables_graph(old(self)).tests.push(view@),
        verify::tables_capacity(final(self)) == verify::tables_capacity(old(self)),
        result is Ok ==> verify::tables_slack(final(self)) >= verify::tables_slack(old(self)),
        result matches Err(error) ==> error is ArenaExhausted ==>
            verify::graph_weight(verify::tables_graph(old(self))) + verify::test_weight(view@)
                - verify::tables_slack(old(self)) > verify::tables_capacity(old(self)))]
    fn push_test(
        &mut self,
        view: TestView<'_>,
        _world: &mut ObservationWorld,
    ) -> KernelResult<TestId> {
        vstd::layout::layout_for_type_is_valid::<ArenaTest>();
        proof_decl! { let ghost before = *self; }
        let id = TestId::from_index(self.tests.len())?;
        let node = match view {
            TestView::True => ArenaTest::True,
            TestView::False => ArenaTest::False,
            TestView::Atom {
                primitive,
                positive,
            } => ArenaTest::Atom {
                primitive,
                positive,
            },
            TestView::And(ids) => {
                let slot = arena(self.test_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.test_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.test_ids@) <= verify::pool_bytes(before.test_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<TestId>()));
                }
                ArenaTest::And(slot)
            }
            TestView::Or(ids) => {
                let slot = arena(self.test_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.test_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.test_ids@) <= verify::pool_bytes(before.test_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<TestId>()));
                }
                ArenaTest::Or(slot)
            }
        };
        proof! {
            assert(self.test_ids@.take(before.test_ids@.len() as int) =~= before.test_ids@);
            assert(self.regex_ids@.take(before.regex_ids@.len() as int) =~= before.regex_ids@);
            assert(self.transition_ids@.take(before.transition_ids@.len() as int) =~= before.transition_ids@);
            verify::pool_extension(&before, &*self);
            assert(verify::tables_space_wf(self));
            assert(verify::arena_test_node(node, self.test_ids@) == view@);
            verify::lemma_test_contains(self, node);
            assert(!self.tests@.contains(node));
        }
        let _handle = match self.tests.try_mk(node) {
            Ok(handle) => handle,
            Err(_) => return Err(HistoryError::ArenaExhausted),
        };
        proof! {
            assert(verify::tables_graph(self).tests =~= verify::tables_graph(&before).tests.push(view@));
            assert(_handle.spec_uid() == id.0 as nat);
            assert forall|i: int| 0 <= i < self.tests@.len() implies
                verify::arena_test_wf(self, self.tests@[i]) by {
                if i < before.tests@.len() { assert(self.tests@[i] == before.tests@[i]); }
            }
            verify::lemma_tests_weight_push(verify::tables_graph(&before).tests, view@);
            verify::lemma_mul_bytes_succ(before.tests@.len(), vstd::layout::size_of::<ArenaTest>());
            assert(verify::tables_wf(self));
            assert(verify::arena_live(self) <= verify::arena_live(&before) + verify::test_weight(view@));
        }
        Ok(id)
    }
    #[verus_spec(result => requires verify::tables_wf(old(self)),
        !verify::tables_graph(old(self)).regexes.contains(view@), ensures
        verify::tables_wf(final(self)),
        verify::tables_graph(final(self)).constants == verify::tables_graph(old(self)).constants,
        verify::tables_graph(final(self)).tests == verify::tables_graph(old(self)).tests,
        verify::tables_graph(final(self)).transitions == verify::tables_graph(old(self)).transitions,
        result is Err ==> verify::tables_graph(final(self)) == verify::tables_graph(old(self)),
        result matches Ok(id) ==> id.0 == verify::tables_graph(old(self)).regexes.len()
            && verify::tables_graph(final(self)).regexes == verify::tables_graph(old(self)).regexes.push(view@),
        verify::tables_capacity(final(self)) == verify::tables_capacity(old(self)),
        result is Ok ==> verify::tables_slack(final(self)) >= verify::tables_slack(old(self)),
        result matches Err(error) ==> error is ArenaExhausted ==>
            verify::graph_weight(verify::tables_graph(old(self))) + verify::regex_weight(view@)
                - verify::tables_slack(old(self)) > verify::tables_capacity(old(self)))]
    fn push_regex(
        &mut self,
        view: RegexView<'_>,
        _world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        vstd::layout::layout_for_type_is_valid::<ArenaRegex>();
        proof_decl! { let ghost before = *self; }
        let id = RegexId::from_index(self.regexes.len())?;
        let kind = match view.kind {
            RegexKindView::Empty => ArenaRegexKind::Empty,
            RegexKindView::All => ArenaRegexKind::All,
            RegexKindView::Epsilon => ArenaRegexKind::Epsilon,
            RegexKindView::Test(id) => ArenaRegexKind::Test(id),
            RegexKindView::Union(ids) => {
                let slot = arena(self.regex_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<RegexId>()));
                }
                ArenaRegexKind::Union(slot)
            }
            RegexKindView::Concat(ids) => {
                let slot = arena(self.regex_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<RegexId>()));
                }
                ArenaRegexKind::Concat(slot)
            }
            RegexKindView::Star(id) => ArenaRegexKind::Star(id),
            RegexKindView::Intersect(ids) => {
                let slot = arena(self.regex_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<RegexId>()));
                }
                ArenaRegexKind::Intersect(slot)
            }
            RegexKindView::Not(id) => ArenaRegexKind::Not(id),
        };
        let node = ArenaRegex {
            kind,
            nullable: view.nullable,
        };
        proof! {
            assert(self.test_ids@.take(before.test_ids@.len() as int) =~= before.test_ids@);
            assert(self.regex_ids@.take(before.regex_ids@.len() as int) =~= before.regex_ids@);
            assert(self.transition_ids@.take(before.transition_ids@.len() as int) =~= before.transition_ids@);
            verify::pool_extension(&before, &*self);
            assert(verify::tables_space_wf(self));
            assert(verify::arena_regex_node(node, self.regex_ids@) == view@);
            verify::lemma_regex_contains(self, node);
            assert(!self.regexes@.contains(node));
        }
        let _handle = match self.regexes.try_mk(node) {
            Ok(handle) => handle,
            Err(_) => return Err(HistoryError::ArenaExhausted),
        };
        proof! {
            assert(verify::tables_graph(self).regexes =~= verify::tables_graph(&before).regexes.push(view@));
            assert(_handle.spec_uid() == id.0 as nat);
            assert forall|i: int| 0 <= i < self.regexes@.len() implies
                verify::arena_regex_wf(self, self.regexes@[i]) by {
                if i < before.regexes@.len() { assert(self.regexes@[i] == before.regexes@[i]); }
            }
            verify::lemma_regexes_weight_push(verify::tables_graph(&before).regexes, view@);
            verify::lemma_mul_bytes_succ(before.regexes@.len(), vstd::layout::size_of::<ArenaRegex>());
            assert(verify::tables_wf(self));
            assert(verify::arena_live(self) <= verify::arena_live(&before) + verify::regex_weight(view@));
        }
        Ok(id)
    }
    #[verus_spec(result => requires verify::tables_wf(old(self)),
        !verify::tables_graph(old(self)).transitions.contains(view@), ensures
        verify::tables_wf(final(self)),
        verify::tables_graph(final(self)).constants == verify::tables_graph(old(self)).constants,
        verify::tables_graph(final(self)).tests == verify::tables_graph(old(self)).tests,
        verify::tables_graph(final(self)).regexes == verify::tables_graph(old(self)).regexes,
        result is Err ==> verify::tables_graph(final(self)) == verify::tables_graph(old(self)),
        result matches Ok(id) ==> id.0 == verify::tables_graph(old(self)).transitions.len()
            && verify::tables_graph(final(self)).transitions == verify::tables_graph(old(self)).transitions.push(view@),
        verify::tables_capacity(final(self)) == verify::tables_capacity(old(self)),
        result is Ok ==> verify::tables_slack(final(self)) >= verify::tables_slack(old(self)),
        result matches Err(error) ==> error is ArenaExhausted ==>
            verify::graph_weight(verify::tables_graph(old(self))) + verify::transition_weight(view@)
                - verify::tables_slack(old(self)) > verify::tables_capacity(old(self)))]
    fn push_transition(
        &mut self,
        view: TransitionView<'_>,
        _world: &mut ObservationWorld,
    ) -> KernelResult<TransitionId> {
        vstd::layout::layout_for_type_is_valid::<ArenaTransition>();
        proof_decl! { let ghost before = *self; }
        let id = TransitionId::from_index(self.transitions.len())?;
        let node = match view {
            TransitionView::Const(id) => ArenaTransition::Const(id),
            TransitionView::If {
                test,
                then_transition,
                else_transition,
            } => ArenaTransition::If {
                test,
                then_transition,
                else_transition,
            },
            TransitionView::Union(ids) => {
                let slot = arena(self.transition_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.transition_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.transition_ids@) <= verify::pool_bytes(before.transition_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<TransitionId>()));
                }
                ArenaTransition::Union(slot)
            }
            TransitionView::Intersect(ids) => {
                let slot = arena(self.transition_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.transition_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.transition_ids@) <= verify::pool_bytes(before.transition_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<TransitionId>()));
                }
                ArenaTransition::Intersect(slot)
            }
            TransitionView::Not(id) => ArenaTransition::Not(id),
            TransitionView::Append { transition, suffix } => {
                let slot = arena(self.regex_ids.intern(suffix))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, suffix@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(suffix@.len(), vstd::layout::size_of::<RegexId>()));
                }
                ArenaTransition::Append {
                    transition,
                    suffix: slot,
                }
            }
        };
        proof! {
            assert(self.test_ids@.take(before.test_ids@.len() as int) =~= before.test_ids@);
            assert(self.regex_ids@.take(before.regex_ids@.len() as int) =~= before.regex_ids@);
            assert(self.transition_ids@.take(before.transition_ids@.len() as int) =~= before.transition_ids@);
            verify::pool_extension(&before, &*self);
            assert(verify::tables_space_wf(self));
            assert(verify::arena_transition_node(node, self.transition_ids@, self.regex_ids@) == view@);
            verify::lemma_transition_contains(self, node);
            assert(!self.transitions@.contains(node));
        }
        let _handle = match self.transitions.try_mk(node) {
            Ok(handle) => handle,
            Err(_) => return Err(HistoryError::ArenaExhausted),
        };
        proof! {
            assert(verify::tables_graph(self).transitions =~= verify::tables_graph(&before).transitions.push(view@));
            assert(_handle.spec_uid() == id.0 as nat);
            assert forall|i: int| 0 <= i < self.transitions@.len() implies
                verify::arena_transition_wf(self, self.transitions@[i]) by {
                if i < before.transitions@.len() { assert(self.transitions@[i] == before.transitions@[i]); }
            }
            verify::lemma_transitions_weight_push(verify::tables_graph(&before).transitions, view@);
            verify::lemma_mul_bytes_succ(before.transitions@.len(), vstd::layout::size_of::<ArenaTransition>());
            assert(verify::tables_wf(self));
            assert(verify::arena_live(self) <= verify::arena_live(&before) + verify::transition_weight(view@));
        }
        Ok(id)
    }
    #[verus_spec(requires verify::tables_wf(&self))]
    fn release(self) {
        self.tests.free();
        self.test_ids.free();
        self.regexes.free();
        self.regex_ids.free();
        self.transitions.free();
        self.transition_ids.free();
    }
}
#[verus_verify]
impl ArenaStorage {
    #[verus_spec(result => ensures result matches Ok(s) ==> verify::empty_tables(s.graph())
        && s.capacity() == ARENA_CAPACITY && s.slack() == 0)]
    pub(crate) fn new() -> KernelResult<Self> {
        Self::with_capacity(ARENA_CAPACITY)
    }
    #[verus_spec(result => ensures result matches Ok(s) ==> verify::empty_tables(s.graph())
        && s.capacity() == capacity && s.slack() == 0)]
    pub(crate) fn with_capacity(capacity: usize) -> KernelResult<Self> {
        Ok(Self {
            tables: Some(ArenaTables::with_capacity(capacity)?),
        })
    }
    #[verus_spec(result => ensures
        result.0 == self.graph().tests.len(),
        result.1 == self.graph().regexes.len(),
        result.2 == self.graph().transitions.len())]
    pub(crate) fn lengths(&self) -> (usize, usize, usize) {
        proof! { use_type_invariant(&*self); }
        match self.tables.as_ref() {
            Some(tables) => tables.lengths(),
            None => (0, 0, 0),
        }
    }
}
#[verus_verify]
impl Storage for ArenaStorage {
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>> {
        proof! { use_type_invariant(&*self); }
        let tables = present(self.tables.as_ref(), "arena released")?;
        tables.test(id.index()?)
    }
    fn find_test(&self, view: TestView<'_>) -> KernelResult<Option<TestId>> {
        proof! { use_type_invariant(&*self); }
        present(self.tables.as_ref(), "arena released")?.find_test(view)
    }
    fn find_regex(&self, view: RegexView<'_>) -> KernelResult<Option<RegexId>> {
        proof! { use_type_invariant(&*self); }
        present(self.tables.as_ref(), "arena released")?.find_regex(view)
    }
    fn find_transition(&self, view: TransitionView<'_>) -> KernelResult<Option<TransitionId>> {
        proof! { use_type_invariant(&*self); }
        present(self.tables.as_ref(), "arena released")?.find_transition(view)
    }
    fn push_test(
        &mut self,
        view: TestView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<TestId> {
        proof! { use_type_invariant(&*self); }
        let Some(mut tables) = self.tables.take() else {
            return Err(invariant("arena released"));
        };
        let result = tables.push_test(view, world);
        self.tables = Some(tables);
        result
    }
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>> {
        proof! { use_type_invariant(&*self); }
        let tables = present(self.tables.as_ref(), "arena released")?;
        tables.regex(id.index()?)
    }
    fn push_regex(
        &mut self,
        view: RegexView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        proof! { use_type_invariant(&*self); }
        let Some(mut tables) = self.tables.take() else {
            return Err(invariant("arena released"));
        };
        let result = tables.push_regex(view, world);
        self.tables = Some(tables);
        result
    }
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>> {
        proof! { use_type_invariant(&*self); }
        let tables = present(self.tables.as_ref(), "arena released")?;
        tables.transition(id.index()?)
    }
    fn push_transition(
        &mut self,
        view: TransitionView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<TransitionId> {
        proof! { use_type_invariant(&*self); }
        let Some(mut tables) = self.tables.take() else {
            return Err(invariant("arena released"));
        };
        let result = tables.push_transition(view, world);
        self.tables = Some(tables);
        result
    }
    fn release(self) {
        proof! { use_type_invariant(&self); }
        if let Some(tables) = self.tables {
            tables.release();
        }
    }
}

#[verus_verify(external)]
impl core::fmt::Debug for ArenaStorage {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (tests, regexes, transitions) = self.lengths();
        f.debug_struct("ArenaStorage")
            .field("tests", &tests)
            .field("regexes", &regexes)
            .field("transitions", &transitions)
            .finish()
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct CanonicalStore<S> {
    pub(crate) storage: S,
    constants: Constants,
    pub(crate) bytes: usize,
}
#[verus_verify]
impl<S: Storage> CanonicalStore<S> {
    #[verus_spec(result =>
        requires verify::empty_tables(storage.graph()),
        ensures match result { Ok(store) => model::graph_wf(store.graph()) && store.valid_store(), Err(_) => true },
    )]
    pub(crate) fn new(storage: S, world: &mut ObservationWorld) -> KernelResult<Self> {
        proof_decl! { let ghost initial_graph = storage.graph(); }
        let mut store = Self {
            storage,
            bytes: 0,
            constants: Constants {
                test_true: TestId(0),
                test_false: TestId(0),
                empty: RegexId(0),
                all: RegexId(0),
                epsilon: RegexId(0),
                transition_empty: TransitionId(0),
                transition_all: TransitionId(0),
                transition_epsilon: TransitionId(0),
            },
        };
        proof! { assert(store.valid_store()); }
        proof! { verify::lemma_tables_wf_same_tables(initial_graph, store.graph()); }
        if let Err(error) = store.intern_constants(world) {
            store.release();
            return Err(error);
        }
        Ok(store)
    }

    #[verus_spec(result =>
        requires old(self).valid_store(), verify::empty_tables(old(self).graph()),
            model::tables_wf(old(self).graph()),
        ensures match result {
            Ok(()) => model::graph_wf(final(self).graph()) && final(self).valid_store(),
            Err(_) => true,
        },
    )]
    fn intern_constants(&mut self, world: &mut ObservationWorld) -> KernelResult<()> {
        let test_true = self.intern_test(TestView::True, world)?;
        let test_false = self.intern_test(TestView::False, world)?;
        let empty = self.intern_regex(RegexKindView::Empty, false, world)?;
        let all = self.intern_regex(RegexKindView::All, true, world)?;
        let epsilon = self.intern_regex(RegexKindView::Epsilon, true, world)?;
        let transition_empty = self.intern_transition(TransitionView::Const(empty), world)?;
        let transition_all = self.intern_transition(TransitionView::Const(all), world)?;
        let transition_epsilon = self.intern_transition(TransitionView::Const(epsilon), world)?;
        proof_decl! { let ghost built_graph = self.graph(); }
        self.constants = Constants {
            test_true,
            test_false,
            empty,
            all,
            epsilon,
            transition_empty,
            transition_all,
            transition_epsilon,
        };
        proof! {
            verify::lemma_tables_wf_same_tables(built_graph, self.graph());
            assert(self.graph().tests == built_graph.tests);
            assert(self.graph().regexes == built_graph.regexes);
            assert(self.graph().transitions == built_graph.transitions);
            assert(verify::graph_weight(self.graph()) == verify::graph_weight(built_graph));
            assert(self.valid_store());
            assert(model::tables_wf(self.graph()));
            assert(model::constants_wf(self.graph()));
            model::lemma_graph_wf_intro(self.graph());
        }
        Ok(())
    }

    pub(crate) fn release(self) {
        self.storage.release();
    }
    #[verus_spec(result => ensures match result {
        Ok(total) => total as int == self.charged_bytes() as int + bytes as int && total <= MAX_GRAPH_BYTES,
        Err(error) => error is GraphLimit,
    })]
    pub(crate) fn projected(&self, bytes: usize) -> KernelResult<usize> {
        let total = self
            .bytes
            .checked_add(bytes)
            .ok_or(HistoryError::GraphLimit {
                limit: MAX_GRAPH_BYTES,
            })?;
        if total > MAX_GRAPH_BYTES {
            return Err(HistoryError::GraphLimit {
                limit: MAX_GRAPH_BYTES,
            });
        }
        Ok(total)
    }
    #[verus_spec(result => ensures final(self).graph() == old(self).graph(),
        final(self).charged_bytes() >= old(self).charged_bytes(),
        old(self).valid_store() ==> final(self).valid_store())]
    pub(crate) fn charge(&mut self, bytes: usize) -> KernelResult<()> {
        self.bytes = self.projected(bytes)?;
        Ok(())
    }
    /// Raises the byte charge to a value previously obtained from `projected` on this store.
    /// The charge never decreases, so `graph_weight(graph) <= charged_bytes()` is preserved
    /// even if an intervening checkpoint or intern already charged more.
    #[verus_spec(
        ensures final(self).graph() == old(self).graph(),
            old(self).valid_store() ==> final(self).valid_store(),
            final(self).charged_bytes() >= old(self).charged_bytes(),
            final(self).charged_bytes() >= bytes as nat,
    )]
    pub(crate) fn set_charged_bytes(&mut self, bytes: usize) {
        if bytes > self.bytes {
            self.bytes = bytes;
        }
    }

    #[verus_spec(result => ensures result@ == self.graph().constants)]
    pub(crate) const fn constants(&self) -> Constants {
        self.constants
    }
    #[verus_spec(result =>
        requires old(self).valid_store(), model::test_node_wf(old(self).graph(), node@),
        ensures
            final(self).valid_store(),
            model::graph_extends(old(self).graph(), final(self).graph()),
            model::tables_wf(old(self).graph()) ==> model::tables_wf(final(self).graph()),
            model::graph_wf(old(self).graph()) ==> model::graph_wf(final(self).graph()),
            match result {
                Ok(id) => id.0 < final(self).graph().tests.len()
                    && final(self).graph().tests[id.0 as int] == node@,
                Err(_) => final(self).graph() == old(self).graph()
                    && final(self).charged_bytes() == old(self).charged_bytes(),
            },
            final(self).capacity() == old(self).capacity(),
            result is Ok ==> final(self).slack() >= old(self).slack(),
            result matches Err(error) ==> error is ArenaExhausted ==>
                old(self).slack() < MAX_GRAPH_BYTES - old(self).capacity(),
    )]
    pub(crate) fn intern_test(
        &mut self,
        node: TestView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<TestId> {
        proof_decl! { let ghost original = self.graph(); }
        if let Some(id) = self.storage.find_test(node)? {
            return Ok(id);
        }
        let len = match node {
            TestView::And(ids) | TestView::Or(ids) => ids.len(),
            _ => 0,
        };
        let bytes = size_of::<ArenaTest>()
            .checked_add(sequence_bytes::<TestId>(len)?)
            .ok_or(HistoryError::GraphLimit {
                limit: MAX_GRAPH_BYTES,
            })?;
        let projected = self.projected(bytes)?;
        proof! {
            assert(model::unique_nodes(original));
            assert(verify::graph_weight(self.storage.graph()) == verify::graph_weight(original));
            assert(bytes as int == verify::test_weight(node@));
            assert(verify::graph_weight(original) + verify::test_weight(node@) <= MAX_GRAPH_BYTES);
        }
        let id = self.storage.push_test(node, world)?;
        self.bytes = projected;
        proof! {
            assert(self.graph() == model::append_test(original, node@));
            assert(model::unique_nodes(self.graph()));
            verify::lemma_tests_weight_push(original.tests, node@);
            assert(verify::graph_weight(self.graph()) == verify::graph_weight(original) + verify::test_weight(node@));
            assert(self.valid_store());
            if model::graph_wf(original) { model::lemma_graph_wf_elim(original); }
            if model::tables_wf(original) { model::lemma_tables_wf_append_test(original, node@); }
        }
        Ok(id)
    }
    #[verus_spec(result =>
        requires old(self).valid_store(), model::regex_node_wf(old(self).graph(), model::RegexNode { kind: kind@, nullable }),
        ensures
            final(self).valid_store(),
            model::graph_extends(old(self).graph(), final(self).graph()),
            model::tables_wf(old(self).graph()) ==> model::tables_wf(final(self).graph()),
            model::graph_wf(old(self).graph()) ==> model::graph_wf(final(self).graph()),
            match result {
                Ok(id) => id.0 < final(self).graph().regexes.len()
                    && final(self).graph().regexes[id.0 as int] == (model::RegexNode { kind: kind@, nullable }),
                Err(_) => final(self).graph() == old(self).graph()
                    && final(self).charged_bytes() == old(self).charged_bytes(),
            },
            final(self).capacity() == old(self).capacity(),
            result is Ok ==> final(self).slack() >= old(self).slack(),
            result matches Err(error) ==> error is ArenaExhausted ==>
                old(self).slack() < MAX_GRAPH_BYTES - old(self).capacity(),
    )]
    pub(crate) fn intern_regex(
        &mut self,
        kind: RegexKindView<'_>,
        nullable: bool,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        proof_decl! { let ghost original = self.graph(); }
        let node = RegexView { kind, nullable };
        if let Some(id) = self.storage.find_regex(node)? {
            return Ok(id);
        }
        let len = match kind {
            RegexKindView::Union(ids)
            | RegexKindView::Concat(ids)
            | RegexKindView::Intersect(ids) => ids.len(),
            _ => 0,
        };
        let bytes = size_of::<ArenaRegex>()
            .checked_add(sequence_bytes::<RegexId>(len)?)
            .ok_or(HistoryError::GraphLimit {
                limit: MAX_GRAPH_BYTES,
            })?;
        let projected = self.projected(bytes)?;
        proof! {
            assert(model::unique_nodes(original));
            assert(verify::graph_weight(self.storage.graph()) == verify::graph_weight(original));
            assert(bytes as int == verify::regex_weight(node@));
            assert(verify::graph_weight(original) + verify::regex_weight(node@) <= MAX_GRAPH_BYTES);
        }
        let id = self.storage.push_regex(node, world)?;
        self.bytes = projected;
        proof! {
            assert(self.graph() == model::append_regex(original, node@));
            assert(model::unique_nodes(self.graph()));
            verify::lemma_regexes_weight_push(original.regexes, node@);
            assert(verify::graph_weight(self.graph()) == verify::graph_weight(original) + verify::regex_weight(node@));
            assert(self.valid_store());
            if model::graph_wf(original) { model::lemma_graph_wf_elim(original); }
            if model::tables_wf(original) { model::lemma_tables_wf_append_regex(original, node@); }
        }
        Ok(id)
    }
    #[verus_spec(result =>
        requires old(self).valid_store(), model::transition_node_wf(old(self).graph(), node@),
        ensures
            final(self).valid_store(),
            model::graph_extends(old(self).graph(), final(self).graph()),
            model::tables_wf(old(self).graph()) ==> model::tables_wf(final(self).graph()),
            model::graph_wf(old(self).graph()) ==> model::graph_wf(final(self).graph()),
            match result {
                Ok(id) => id.0 < final(self).graph().transitions.len()
                    && final(self).graph().transitions[id.0 as int] == node@,
                Err(_) => final(self).graph() == old(self).graph()
                    && final(self).charged_bytes() == old(self).charged_bytes(),
            },
            final(self).capacity() == old(self).capacity(),
            result is Ok ==> final(self).slack() >= old(self).slack(),
            result matches Err(error) ==> error is ArenaExhausted ==>
                old(self).slack() < MAX_GRAPH_BYTES - old(self).capacity(),
    )]
    pub(crate) fn intern_transition(
        &mut self,
        node: TransitionView<'_>,
        world: &mut ObservationWorld,
    ) -> KernelResult<TransitionId> {
        proof_decl! { let ghost original = self.graph(); }
        if let Some(id) = self.storage.find_transition(node)? {
            return Ok(id);
        }
        let children = match node {
            TransitionView::Union(ids) | TransitionView::Intersect(ids) => {
                sequence_bytes::<TransitionId>(ids.len())?
            }
            TransitionView::Append { suffix, .. } => sequence_bytes::<RegexId>(suffix.len())?,
            _ => 0,
        };
        let bytes =
            size_of::<ArenaTransition>()
                .checked_add(children)
                .ok_or(HistoryError::GraphLimit {
                    limit: MAX_GRAPH_BYTES,
                })?;
        let projected = self.projected(bytes)?;
        proof! {
            assert(model::unique_nodes(original));
            assert(verify::graph_weight(self.storage.graph()) == verify::graph_weight(original));
            assert(bytes as int == verify::transition_weight(node@));
            assert(verify::graph_weight(original) + verify::transition_weight(node@) <= MAX_GRAPH_BYTES);
        }
        let id = self.storage.push_transition(node, world)?;
        self.bytes = projected;
        proof! {
            assert(self.graph() == model::append_transition(original, node@));
            assert(model::unique_nodes(self.graph()));
            verify::lemma_transitions_weight_push(original.transitions, node@);
            assert(verify::graph_weight(self.graph()) == verify::graph_weight(original) + verify::transition_weight(node@));
            assert(self.valid_store());
            if model::graph_wf(original) { model::lemma_graph_wf_elim(original); }
            if model::tables_wf(original) { model::lemma_tables_wf_append_transition(original, node@); }
        }
        Ok(id)
    }
}
#[verus_verify]
pub(crate) struct RuntimeKernel<'a, S> {
    pub(crate) store: &'a mut CanonicalStore<S>,
    pub(crate) timer: &'a mut ExecutionTimer,
    pub(crate) world: &'a mut ObservationWorld,
}
#[verus_verify]
impl<S: Storage> KernelStore for RuntimeKernel<'_, S> {
    fn checkpoint(&mut self) -> KernelResult<()> {
        checkpoint(self.timer, self.world)
    }
    fn charge_aux(&mut self, bytes: usize) -> KernelResult<()> {
        self.checkpoint()?;
        self.store.charge(bytes)
    }
    fn reserve_derivatives(
        &mut self,
        values: &mut Vec<Option<TransitionId>>,
        additional: usize,
    ) -> KernelResult<()> {
        allocation(self.world.try_reserve_vec(values, additional))
    }
    fn reserve_atoms(&mut self, values: &mut Vec<TestId>, additional: usize) -> KernelResult<()> {
        allocation(self.world.try_reserve_vec(values, additional))
    }
    fn constants(&self) -> Constants {
        self.store.constants()
    }
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>> {
        self.store.storage.test(id)
    }
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>> {
        self.store.storage.regex(id)
    }
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>> {
        self.store.storage.transition(id)
    }
    fn intern_test(&mut self, node: TestView<'_>) -> KernelResult<TestId> {
        self.checkpoint()?;
        let id = self.store.intern_test(node, self.world)?;
        self.checkpoint()?;
        Ok(id)
    }
    fn intern_regex(&mut self, kind: RegexKindView<'_>, nullable: bool) -> KernelResult<RegexId> {
        self.checkpoint()?;
        let id = self.store.intern_regex(kind, nullable, self.world)?;
        self.checkpoint()?;
        Ok(id)
    }
    fn intern_transition(&mut self, node: TransitionView<'_>) -> KernelResult<TransitionId> {
        self.checkpoint()?;
        let id = self.store.intern_transition(node, self.world)?;
        self.checkpoint()?;
        Ok(id)
    }
}

#[cfg(test)]
mod storage_tests {
    #![allow(clippy::panic_in_result_fn)]
    use super::*;

    #[test]
    fn interned_nodes_keep_ids_bytes_and_derivative_semantics() -> KernelResult<()> {
        let mut world = ObservationWorld;
        let mut timer = ExecutionTimer::new(None);
        let mut store = CanonicalStore::new(ArenaStorage::new()?, &mut world)?;
        let node = TestView::Atom {
            primitive: Primitive::HasValue(PathId(0)),
            positive: true,
        };
        let test = store.intern_test(node, &mut world)?;
        let regex = store.intern_regex(RegexKindView::Test(test), false, &mut world)?;
        let transition_node = TransitionView::If {
            test,
            then_transition: store.constants().transition_epsilon,
            else_transition: store.constants().transition_empty,
        };
        let transition = store.intern_transition(transition_node, &mut world)?;
        let and = store.intern_test(
            TestView::And(&[test, store.constants().test_true]),
            &mut world,
        )?;
        let lists = store
            .storage
            .tables
            .as_ref()
            .map(|tables| tables.test_ids.len());
        let or = store.intern_test(
            TestView::Or(&[test, store.constants().test_true]),
            &mut world,
        )?;
        assert_ne!(and, or);
        assert_eq!(
            store
                .storage
                .tables
                .as_ref()
                .map(|tables| tables.test_ids.len()),
            lists
        );
        assert_eq!(
            store.storage.test(or)?,
            TestView::Or(&[test, store.constants().test_true])
        );
        let bytes = store.bytes;
        let rows = store
            .storage
            .tables
            .as_ref()
            .map(|tables| tables.tests.len());
        assert_eq!(store.intern_test(node, &mut world)?, test);
        assert_eq!(
            store.intern_regex(RegexKindView::Test(test), false, &mut world)?,
            regex
        );
        assert_eq!(
            store.intern_transition(transition_node, &mut world)?,
            transition
        );
        assert_eq!(
            store.intern_test(
                TestView::And(&[test, store.constants().test_true]),
                &mut world
            )?,
            and
        );
        assert_eq!(store.bytes, bytes);
        assert_eq!(
            store
                .storage
                .tables
                .as_ref()
                .map(|tables| tables.tests.len()),
            rows
        );
        let mut kernel = RuntimeKernel {
            store: &mut store,
            timer: &mut timer,
            world: &mut world,
        };
        let mut derivatives = Vec::new();
        assert_eq!(
            super::super::symbolic::symbolic_derivative(&mut kernel, &mut derivatives, regex)?,
            transition
        );
        let atoms = super::super::progress::transition_atoms(&mut kernel, transition)?;
        let accepted =
            super::super::symbolic::interpret_transition(&mut kernel, transition, &atoms, &[1])?;
        assert!(super::super::normalize::nullable(&kernel, accepted)?);
        store.release();
        Ok(())
    }

    #[test]
    fn budget_equality_is_allowed_and_failed_growth_is_transactional() -> KernelResult<()> {
        let mut world = ObservationWorld;
        let mut store = CanonicalStore::new(ArenaStorage::new()?, &mut world)?;
        let payload = size_of::<ArenaTest>();
        store.bytes = MAX_GRAPH_BYTES
            .checked_sub(payload)
            .ok_or_else(|| invariant("invalid test budget"))?;
        let node = TestView::Atom {
            primitive: Primitive::HasValue(PathId(0)),
            positive: true,
        };
        let id = store.intern_test(node, &mut world)?;
        assert_eq!(store.bytes, MAX_GRAPH_BYTES);
        assert_eq!(store.intern_test(node, &mut world)?, id);
        let rows = store.storage.lengths();
        let failed = store.intern_test(
            TestView::Atom {
                primitive: Primitive::HasValue(PathId(1)),
                positive: true,
            },
            &mut world,
        );
        assert!(matches!(
            failed,
            Err(HistoryError::GraphLimit {
                limit: MAX_GRAPH_BYTES
            })
        ));
        assert_eq!(store.bytes, MAX_GRAPH_BYTES);
        assert_eq!(store.storage.lengths(), rows);
        store.release();
        Ok(())
    }

    #[test]
    fn arena_allocation_failure_does_not_publish_or_charge() -> KernelResult<()> {
        let mut world = ObservationWorld;
        let mut store = CanonicalStore::new(ArenaStorage::with_capacity(512)?, &mut world)?;
        for path in 0_u32..u32::MAX {
            let before = (store.bytes, store.storage.lengths());
            match store.intern_test(
                TestView::Atom {
                    primitive: Primitive::HasValue(PathId(path)),
                    positive: true,
                },
                &mut world,
            ) {
                Ok(_) => {}
                Err(HistoryError::ArenaExhausted) => {
                    assert_eq!((store.bytes, store.storage.lengths()), before);
                    let constant = store.intern_test(TestView::True, &mut world);
                    let expected = store.constants().test_true;
                    store.release();
                    assert_eq!(constant?, expected);
                    return Ok(());
                }
                Err(error) => {
                    store.release();
                    return Err(error);
                }
            }
        }
        store.release();
        Err(invariant("512-byte arena did not exhaust"))
    }

    #[test]
    fn arena_round_trips_child_slices() -> KernelResult<()> {
        let mut world = ObservationWorld;
        let mut store = CanonicalStore::new(ArenaStorage::new()?, &mut world)?;
        let outcome = (|| -> KernelResult<_> {
            let a = store.intern_test(
                TestView::Atom {
                    primitive: Primitive::HasValue(PathId(1)),
                    positive: true,
                },
                &mut world,
            )?;
            let b = store.intern_test(
                TestView::Atom {
                    primitive: Primitive::HasValue(PathId(2)),
                    positive: true,
                },
                &mut world,
            )?;
            let and = store.intern_test(TestView::And(&[a, b]), &mut world)?;
            let r = store.intern_regex(RegexKindView::Test(a), false, &mut world)?;
            let epsilon = store.constants().epsilon;
            let union =
                store.intern_regex(RegexKindView::Union(&[r, epsilon]), true, &mut world)?;
            let transition_epsilon = store.constants().transition_epsilon;
            let append = TransitionView::Append {
                transition: transition_epsilon,
                suffix: &[r],
            };
            let t = store.intern_transition(append, &mut world)?;
            assert_eq!(store.storage.test(and)?, TestView::And(&[a, b]));
            assert_eq!(
                store.storage.regex(union)?.kind,
                RegexKindView::Union(&[r, epsilon])
            );
            assert_eq!(store.storage.transition(t)?, append);
            assert_eq!(store.intern_test(TestView::And(&[a, b]), &mut world)?, and);
            assert_eq!(
                store.intern_regex(RegexKindView::Union(&[r, epsilon]), true, &mut world)?,
                union
            );
            assert_eq!(store.intern_transition(append, &mut world)?, t);
            Ok(())
        })();
        store.release();
        outcome?;
        Ok(())
    }
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::super::kernel::verify as model;
    use super::*;

    verus! {

                pub open spec fn storage_constants() -> model::ConstantsModel {
                    model::ConstantsModel {
                        test_true: 0, test_false: 0, empty: 0, all: 0, epsilon: 0,
                        transition_empty: 0, transition_all: 0, transition_epsilon: 0,
                    }
                }


    pub(super) open spec fn arena_test_node(node: ArenaTest, pools: Seq<Seq<TestId>>) -> model::TestNode {
        match node {
            ArenaTest::True => model::TestNode::True,
            ArenaTest::False => model::TestNode::False,
            ArenaTest::Atom { primitive, positive } => model::TestNode::Atom(primitive@, positive),
            ArenaTest::And(slot) => model::TestNode::And(model::test_ids(pools[slot as int])),
            ArenaTest::Or(slot) => model::TestNode::Or(model::test_ids(pools[slot as int])),
        }
    }
    pub(super) open spec fn arena_regex_node(node: ArenaRegex, pools: Seq<Seq<RegexId>>) -> model::RegexNode {
        model::RegexNode {
            nullable: node.nullable,
            kind: match node.kind {
                ArenaRegexKind::Empty => model::RegexKindNode::Empty,
                ArenaRegexKind::All => model::RegexKindNode::All,
                ArenaRegexKind::Epsilon => model::RegexKindNode::Epsilon,
                ArenaRegexKind::Test(id) => model::RegexKindNode::Test(id@),
                ArenaRegexKind::Union(slot) => model::RegexKindNode::Union(model::regex_ids(pools[slot as int])),
                ArenaRegexKind::Concat(slot) => model::RegexKindNode::Concat(model::regex_ids(pools[slot as int])),
                ArenaRegexKind::Star(id) => model::RegexKindNode::Star(id@),
                ArenaRegexKind::Intersect(slot) => model::RegexKindNode::Intersect(model::regex_ids(pools[slot as int])),
                ArenaRegexKind::Not(id) => model::RegexKindNode::Not(id@),
            },
        }
    }
    pub(super) open spec fn arena_transition_node(node: ArenaTransition, ids: Seq<Seq<TransitionId>>, regex_pools: Seq<Seq<RegexId>>) -> model::TransitionNode {
        match node {
            ArenaTransition::Const(id) => model::TransitionNode::Const(id@),
            ArenaTransition::If { test, then_transition, else_transition } => model::TransitionNode::If(test@, then_transition@, else_transition@),
            ArenaTransition::Union(slot) => model::TransitionNode::Union(model::transition_ids(ids[slot as int])),
            ArenaTransition::Intersect(slot) => model::TransitionNode::Intersect(model::transition_ids(ids[slot as int])),
            ArenaTransition::Not(id) => model::TransitionNode::Not(id@),
            ArenaTransition::Append { transition, suffix } => model::TransitionNode::Append(transition@, model::regex_ids(regex_pools[suffix as int])),
        }
    }
    pub(super) open spec fn arena_test_wf(t: &ArenaTables, node: ArenaTest) -> bool {
        match node {
            ArenaTest::And(slot) | ArenaTest::Or(slot) => slot < t.test_ids@.len(),
            _ => true,
        }
    }
    pub(super) open spec fn arena_regex_wf(t: &ArenaTables, node: ArenaRegex) -> bool {
        match node.kind {
            ArenaRegexKind::Union(slot) | ArenaRegexKind::Concat(slot) | ArenaRegexKind::Intersect(slot) =>
                slot < t.regex_ids@.len(),
            _ => true,
        }
    }
    pub(super) open spec fn arena_transition_wf(t: &ArenaTables, node: ArenaTransition) -> bool {
        match node {
            ArenaTransition::Union(slot) | ArenaTransition::Intersect(slot) => slot < t.transition_ids@.len(),
            ArenaTransition::Append { suffix, .. } => suffix < t.regex_ids@.len(),
            _ => true,
        }
    }
    proof fn lemma_pool_slot_eq<T>(pool: Seq<Seq<T>>, a: usize, b: usize)
        requires pool.no_duplicates(), a < pool.len(), b < pool.len(),
        ensures (a == b) == (pool[a as int] == pool[b as int]),
    {}
    proof fn lemma_primitive_eq(a: Primitive, b: Primitive)
        ensures (a == b) == (a@ == b@),
    {
        match (a, b) {
            (Primitive::EqCore(_, x), Primitive::EqCore(_, y)) => {
                match (x, y) {
                    (super::super::kernel::Term::Constant(_), super::super::kernel::Term::Constant(_)) => {},
                    (super::super::kernel::Term::Variable(_), super::super::kernel::Term::Variable(_)) => {},
                    _ => {},
                }
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_arena_test_eq_iff_node_eq(t: &ArenaTables, a: ArenaTest, b: ArenaTest)
        requires tables_index_wf(t), arena_test_wf(t, a), arena_test_wf(t, b),
        ensures (a == b) == (arena_test_node(a, t.test_ids@) == arena_test_node(b, t.test_ids@)),
    {
        match (a, b) {
            (ArenaTest::And(x), ArenaTest::And(y)) | (ArenaTest::Or(x), ArenaTest::Or(y)) => {
                model::lemma_test_ids_eq(t.test_ids@[x as int], t.test_ids@[y as int]);
                lemma_pool_slot_eq(t.test_ids@, x, y);
            },
            (ArenaTest::Atom { primitive: x, .. }, ArenaTest::Atom { primitive: y, .. }) => {
                lemma_primitive_eq(x, y);
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_arena_regex_eq_iff_node_eq(t: &ArenaTables, a: ArenaRegex, b: ArenaRegex)
        requires tables_index_wf(t), arena_regex_wf(t, a), arena_regex_wf(t, b),
        ensures (a == b) == (arena_regex_node(a, t.regex_ids@) == arena_regex_node(b, t.regex_ids@)),
    {
        match (a.kind, b.kind) {
            (ArenaRegexKind::Union(x), ArenaRegexKind::Union(y))
            | (ArenaRegexKind::Concat(x), ArenaRegexKind::Concat(y))
            | (ArenaRegexKind::Intersect(x), ArenaRegexKind::Intersect(y)) => {
                model::lemma_regex_ids_eq(t.regex_ids@[x as int], t.regex_ids@[y as int]);
                lemma_pool_slot_eq(t.regex_ids@, x, y);
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_arena_transition_eq_iff_node_eq(t: &ArenaTables, a: ArenaTransition, b: ArenaTransition)
        requires tables_index_wf(t), arena_transition_wf(t, a), arena_transition_wf(t, b),
        ensures (a == b) == (arena_transition_node(a, t.transition_ids@, t.regex_ids@)
            == arena_transition_node(b, t.transition_ids@, t.regex_ids@)),
    {
        match (a, b) {
            (ArenaTransition::Union(x), ArenaTransition::Union(y))
            | (ArenaTransition::Intersect(x), ArenaTransition::Intersect(y)) => {
                model::lemma_transition_ids_eq(t.transition_ids@[x as int], t.transition_ids@[y as int]);
                lemma_pool_slot_eq(t.transition_ids@, x, y);
            },
            (ArenaTransition::Append { suffix: x, .. }, ArenaTransition::Append { suffix: y, .. }) => {
                model::lemma_regex_ids_eq(t.regex_ids@[x as int], t.regex_ids@[y as int]);
                lemma_pool_slot_eq(t.regex_ids@, x, y);
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_test_contains(t: &ArenaTables, node: ArenaTest)
        requires tables_index_wf(t), arena_test_wf(t, node),
        ensures t.tests@.contains(node) == tables_graph(t).tests.contains(arena_test_node(node, t.test_ids@)),
    {
        let lifted = arena_test_node(node, t.test_ids@);
        if t.tests@.contains(node) {
            let i = t.tests@.lemma_contains_to_index(node);
            assert(tables_graph(t).tests[i] == lifted);
        }
        if tables_graph(t).tests.contains(lifted) {
            let i = tables_graph(t).tests.lemma_contains_to_index(lifted);
            lemma_arena_test_eq_iff_node_eq(t, t.tests@[i], node);
            assert(t.tests@.contains(node));
        }
    }
    pub(super) proof fn lemma_regex_contains(t: &ArenaTables, node: ArenaRegex)
        requires tables_index_wf(t), arena_regex_wf(t, node),
        ensures t.regexes@.contains(node) == tables_graph(t).regexes.contains(arena_regex_node(node, t.regex_ids@)),
    {
        let lifted = arena_regex_node(node, t.regex_ids@);
        if t.regexes@.contains(node) {
            let i = t.regexes@.lemma_contains_to_index(node);
            assert(tables_graph(t).regexes[i] == lifted);
        }
        if tables_graph(t).regexes.contains(lifted) {
            let i = tables_graph(t).regexes.lemma_contains_to_index(lifted);
            lemma_arena_regex_eq_iff_node_eq(t, t.regexes@[i], node);
            assert(t.regexes@.contains(node));
        }
    }
    pub(super) proof fn lemma_transition_contains(t: &ArenaTables, node: ArenaTransition)
        requires tables_index_wf(t), arena_transition_wf(t, node),
        ensures t.transitions@.contains(node) == tables_graph(t).transitions.contains(
            arena_transition_node(node, t.transition_ids@, t.regex_ids@)),
    {
        let lifted = arena_transition_node(node, t.transition_ids@, t.regex_ids@);
        if t.transitions@.contains(node) {
            let i = t.transitions@.lemma_contains_to_index(node);
            assert(tables_graph(t).transitions[i] == lifted);
        }
        if tables_graph(t).transitions.contains(lifted) {
            let i = tables_graph(t).transitions.lemma_contains_to_index(lifted);
            lemma_arena_transition_eq_iff_node_eq(t, t.transitions@[i], node);
            assert(t.transitions@.contains(node));
        }
    }
    pub(super) proof fn lemma_missing_test_children(t: &ArenaTables, view: model::TestNode, ids: Seq<TestId>)
        requires tables_index_wf(t), !t.test_ids@.contains(ids),
            view == model::TestNode::And(model::test_ids(ids)) || view == model::TestNode::Or(model::test_ids(ids)),
        ensures !tables_graph(t).tests.contains(view),
    {
        assert forall|i: int| 0 <= i < t.tests@.len() implies tables_graph(t).tests[i] != view by {
            match t.tests@[i] {
                ArenaTest::And(slot) | ArenaTest::Or(slot) => {
                    assert(t.test_ids@.contains(t.test_ids@[slot as int]));
                    model::lemma_test_ids_eq(t.test_ids@[slot as int], ids);
                },
                _ => {},
            }
        }
    }
    pub(super) proof fn lemma_missing_regex_children(t: &ArenaTables, view: model::RegexNode, ids: Seq<RegexId>)
        requires tables_index_wf(t), !t.regex_ids@.contains(ids),
            view.kind == model::RegexKindNode::Union(model::regex_ids(ids))
                || view.kind == model::RegexKindNode::Concat(model::regex_ids(ids))
                || view.kind == model::RegexKindNode::Intersect(model::regex_ids(ids)),
        ensures !tables_graph(t).regexes.contains(view),
    {
        assert forall|i: int| 0 <= i < t.regexes@.len() implies tables_graph(t).regexes[i] != view by {
            match t.regexes@[i].kind {
                ArenaRegexKind::Union(slot) | ArenaRegexKind::Concat(slot) | ArenaRegexKind::Intersect(slot) => {
                    assert(t.regex_ids@.contains(t.regex_ids@[slot as int]));
                    model::lemma_regex_ids_eq(t.regex_ids@[slot as int], ids);
                },
                _ => {},
            }
        }
    }
    pub(super) proof fn lemma_missing_transition_children(t: &ArenaTables, view: model::TransitionNode, ids: Seq<TransitionId>)
        requires tables_index_wf(t), !t.transition_ids@.contains(ids),
            view == model::TransitionNode::Union(model::transition_ids(ids))
                || view == model::TransitionNode::Intersect(model::transition_ids(ids)),
        ensures !tables_graph(t).transitions.contains(view),
    {
        assert forall|i: int| 0 <= i < t.transitions@.len() implies tables_graph(t).transitions[i] != view by {
            match t.transitions@[i] {
                ArenaTransition::Union(slot) | ArenaTransition::Intersect(slot) => {
                    assert(t.transition_ids@.contains(t.transition_ids@[slot as int]));
                    model::lemma_transition_ids_eq(t.transition_ids@[slot as int], ids);
                },
                _ => {},
            }
        }
    }
    pub(super) proof fn lemma_missing_append_suffix(t: &ArenaTables, transition: nat, ids: Seq<RegexId>)
        requires tables_index_wf(t), !t.regex_ids@.contains(ids),
        ensures !tables_graph(t).transitions.contains(model::TransitionNode::Append(transition, model::regex_ids(ids))),
    {
        assert forall|i: int| 0 <= i < t.transitions@.len() implies tables_graph(t).transitions[i]
            != model::TransitionNode::Append(transition, model::regex_ids(ids)) by {
            match t.transitions@[i] {
                ArenaTransition::Append { suffix, .. } => {
                    assert(t.regex_ids@.contains(t.regex_ids@[suffix as int]));
                    model::lemma_regex_ids_eq(t.regex_ids@[suffix as int], ids);
                },
                _ => {},
            }
        }
    }
    pub(super) open spec fn tables_wf(t: &ArenaTables) -> bool {
        tables_index_wf(t) && tables_space_wf(t)
    }
    // Every pool slot referenced by a node exists.
    pub(super) open spec fn tables_index_wf(t: &ArenaTables) -> bool {
        &&& t.tests.inv() && t.regexes.inv() && t.transitions.inv()
        &&& t.test_ids.inv() && t.regex_ids.inv() && t.transition_ids.inv()
        &&& forall|i: int| 0 <= i < t.tests@.len() ==> match #[trigger] t.tests@[i] {
            ArenaTest::And(slot) | ArenaTest::Or(slot) => slot < t.test_ids@.len(),
            _ => true,
        }
        &&& forall|i: int| 0 <= i < t.regexes@.len() ==> match (#[trigger] t.regexes@[i]).kind {
            ArenaRegexKind::Union(slot) | ArenaRegexKind::Concat(slot) | ArenaRegexKind::Intersect(slot) => slot < t.regex_ids@.len(),
            _ => true,
        }
        &&& forall|i: int| 0 <= i < t.transitions@.len() ==> match #[trigger] t.transitions@[i] {
            ArenaTransition::Union(slot) | ArenaTransition::Intersect(slot) => slot < t.transition_ids@.len(),
            ArenaTransition::Append { transition, suffix } => suffix < t.regex_ids@.len(),
            _ => true,
        }
    }
    pub(super) open spec fn tables_graph(t: &ArenaTables) -> model::Graph {
        model::Graph {
            tests: Seq::new(t.tests@.len(), |i: int| arena_test_node(t.tests@[i], t.test_ids@)),
            regexes: Seq::new(t.regexes@.len(), |i: int| arena_regex_node(t.regexes@[i], t.regex_ids@)),
            transitions: Seq::new(t.transitions@.len(), |i: int| arena_transition_node(t.transitions@[i], t.transition_ids@, t.regex_ids@)),
            constants: storage_constants(),
        }
    }

    // ---- Capacity accounting -------------------------------------------------------------
    //
    // `graph_weight` is the byte charge `CanonicalStore::intern_*` levies for a graph
    // (`size_of::<ArenaX>()` per node plus `size_of::<Id>()` per child). `arena_live` is what the
    // six arenas actually hold. Their difference, `tables_slack`, never decreases on a successful
    // push and is 0 for a fresh store, so exhaustion before `GraphLimit` is impossible.

    pub open spec fn mul_bytes(count: nat, size: nat) -> nat { count * size }
    pub proof fn lemma_mul_bytes_succ(count: nat, size: nat)
        ensures mul_bytes(count + 1, size) == mul_bytes(count, size) + size,
    {
        assert((count + 1) * size == count * size + size) by (nonlinear_arith);
    }

    pub open spec fn test_weight(n: model::TestNode) -> nat {
        vstd::layout::size_of::<ArenaTest>() + match n {
            model::TestNode::And(ids) | model::TestNode::Or(ids) => mul_bytes(ids.len(), vstd::layout::size_of::<TestId>()),
            _ => 0,
        }
    }
    pub open spec fn regex_weight(n: model::RegexNode) -> nat {
        vstd::layout::size_of::<ArenaRegex>() + match n.kind {
            model::RegexKindNode::Union(ids) | model::RegexKindNode::Concat(ids) | model::RegexKindNode::Intersect(ids) =>
                mul_bytes(ids.len(), vstd::layout::size_of::<RegexId>()),
            _ => 0,
        }
    }
    pub open spec fn transition_weight(n: model::TransitionNode) -> nat {
        vstd::layout::size_of::<ArenaTransition>() + match n {
            model::TransitionNode::Union(ids) | model::TransitionNode::Intersect(ids) =>
                mul_bytes(ids.len(), vstd::layout::size_of::<TransitionId>()),
            model::TransitionNode::Append(_, suffix) => mul_bytes(suffix.len(), vstd::layout::size_of::<RegexId>()),
            _ => 0,
        }
    }
    pub open spec fn tests_weight(s: Seq<model::TestNode>) -> nat
        decreases s.len(),
    {
        if s.len() == 0 { 0 } else { tests_weight(s.drop_last()) + test_weight(s.last()) }
    }
    pub open spec fn regexes_weight(s: Seq<model::RegexNode>) -> nat
        decreases s.len(),
    {
        if s.len() == 0 { 0 } else { regexes_weight(s.drop_last()) + regex_weight(s.last()) }
    }
    pub open spec fn transitions_weight(s: Seq<model::TransitionNode>) -> nat
        decreases s.len(),
    {
        if s.len() == 0 { 0 } else { transitions_weight(s.drop_last()) + transition_weight(s.last()) }
    }
    pub open spec fn graph_weight(g: model::Graph) -> nat {
        tests_weight(g.tests) + regexes_weight(g.regexes) + transitions_weight(g.transitions)
    }
    pub proof fn lemma_tests_weight_push(s: Seq<model::TestNode>, n: model::TestNode)
        ensures tests_weight(s.push(n)) == tests_weight(s) + test_weight(n),
    {
        assert(s.push(n).drop_last() =~= s);
    }
    pub proof fn lemma_regexes_weight_push(s: Seq<model::RegexNode>, n: model::RegexNode)
        ensures regexes_weight(s.push(n)) == regexes_weight(s) + regex_weight(n),
    {
        assert(s.push(n).drop_last() =~= s);
    }
    pub proof fn lemma_transitions_weight_push(s: Seq<model::TransitionNode>, n: model::TransitionNode)
        ensures transitions_weight(s.push(n)) == transitions_weight(s) + transition_weight(n),
    {
        assert(s.push(n).drop_last() =~= s);
    }

    pub open spec fn pool_bytes<T>(p: Seq<Seq<T>>) -> nat
        decreases p.len(),
    {
        if p.len() == 0 { 0 } else { pool_bytes(p.drop_last()) + mul_bytes(p.last().len(), vstd::layout::size_of::<T>()) }
    }
    pub proof fn lemma_pool_bytes_push<T>(p: Seq<Seq<T>>, s: Seq<T>)
        ensures pool_bytes(p.push(s)) == pool_bytes(p) + mul_bytes(s.len(), vstd::layout::size_of::<T>()),
    {
        assert(p.push(s).drop_last() =~= p);
    }

    pub(super) open spec fn layout_premises() -> bool {
        &&& vstd::layout::size_of::<ArenaTest>() > 0
        &&& vstd::layout::size_of::<ArenaRegex>() > 0
        &&& vstd::layout::size_of::<ArenaTransition>() > 0
    }
    pub(super) open spec fn arena_live(t: &ArenaTables) -> nat {
        mul_bytes(t.tests@.len(), vstd::layout::size_of::<ArenaTest>())
            + mul_bytes(t.regexes@.len(), vstd::layout::size_of::<ArenaRegex>())
            + mul_bytes(t.transitions@.len(), vstd::layout::size_of::<ArenaTransition>())
            + pool_bytes(t.test_ids@) + pool_bytes(t.regex_ids@) + pool_bytes(t.transition_ids@)
    }
    // All six arenas share one capacity, stay aligned, and hold exactly `arena_live` bytes.
    pub(super) open spec fn tables_space_wf(t: &ArenaTables) -> bool {
        let cap = t.tests.capacity();
        &&& layout_premises()
        &&& t.tests.aligned() && t.test_ids.aligned() && t.regexes.aligned()
            && t.regex_ids.aligned() && t.transitions.aligned() && t.transition_ids.aligned()
        &&& t.test_ids.capacity() == cap && t.regexes.capacity() == cap && t.regex_ids.capacity() == cap
            && t.transitions.capacity() == cap && t.transition_ids.capacity() == cap
        &&& t.tests.remaining() == cap - mul_bytes(t.tests@.len(), vstd::layout::size_of::<ArenaTest>())
        &&& t.regexes.remaining() == cap - mul_bytes(t.regexes@.len(), vstd::layout::size_of::<ArenaRegex>())
        &&& t.transitions.remaining() == cap - mul_bytes(t.transitions@.len(), vstd::layout::size_of::<ArenaTransition>())
        &&& t.test_ids.remaining() == cap - pool_bytes(t.test_ids@)
        &&& t.regex_ids.remaining() == cap - pool_bytes(t.regex_ids@)
        &&& t.transition_ids.remaining() == cap - pool_bytes(t.transition_ids@)
    }
    pub(super) open spec fn tables_capacity(t: &ArenaTables) -> int { t.tests.capacity() }
    pub(super) open spec fn tables_slack(t: &ArenaTables) -> int {
        graph_weight(tables_graph(t)) - arena_live(t)
    }
    // A freshly constructed table set: empty, aligned, full capacity, zero slack.
    pub(super) proof fn lemma_fresh_tables(t: &ArenaTables, capacity: usize)
        requires
            layout_premises(),
            t.tests.inv() && t.regexes.inv() && t.transitions.inv(),
            t.test_ids.inv() && t.regex_ids.inv() && t.transition_ids.inv(),
            t.tests@ == Seq::<ArenaTest>::empty(), t.regexes@ == Seq::<ArenaRegex>::empty(),
            t.transitions@ == Seq::<ArenaTransition>::empty(),
            t.test_ids@ == Seq::<Seq<TestId>>::empty(), t.regex_ids@ == Seq::<Seq<RegexId>>::empty(),
            t.transition_ids@ == Seq::<Seq<TransitionId>>::empty(),
            t.tests.aligned() && t.test_ids.aligned() && t.regexes.aligned()
                && t.regex_ids.aligned() && t.transitions.aligned() && t.transition_ids.aligned(),
            t.tests.capacity() == capacity && t.test_ids.capacity() == capacity
                && t.regexes.capacity() == capacity && t.regex_ids.capacity() == capacity
                && t.transitions.capacity() == capacity && t.transition_ids.capacity() == capacity,
            t.tests.remaining() == capacity && t.test_ids.remaining() == capacity
                && t.regexes.remaining() == capacity && t.regex_ids.remaining() == capacity
                && t.transitions.remaining() == capacity && t.transition_ids.remaining() == capacity,
        ensures
            tables_wf(t), empty_tables(tables_graph(t)),
            tables_capacity(t) == capacity, tables_slack(t) == 0,
    {
        assert(tables_graph(t).tests.len() == 0);
        assert(tables_graph(t).regexes.len() == 0);
        assert(tables_graph(t).transitions.len() == 0);
        assert(graph_weight(tables_graph(t)) == 0);
        assert(arena_live(t) == 0);
    }

    // Appending an unused pool slot cannot change any already-published node.
    pub(super) proof fn pool_extension(before: &ArenaTables, after: &ArenaTables)
        requires
            tables_index_wf(before),
            after.tests.inv() && after.regexes.inv() && after.transitions.inv(),
            after.test_ids.inv() && after.regex_ids.inv() && after.transition_ids.inv(),
            before.tests@ == after.tests@,
            before.regexes@ == after.regexes@,
            before.transitions@ == after.transitions@,
            before.test_ids@.len() <= after.test_ids@.len(),
            before.regex_ids@.len() <= after.regex_ids@.len(),
            before.transition_ids@.len() <= after.transition_ids@.len(),
            after.test_ids@.take(before.test_ids@.len() as int) == before.test_ids@,
            after.regex_ids@.take(before.regex_ids@.len() as int) == before.regex_ids@,
            after.transition_ids@.take(before.transition_ids@.len() as int) == before.transition_ids@,
        ensures tables_index_wf(after), tables_graph(after) == tables_graph(before),
    {
        assert forall|i: int| 0 <= i < before.tests@.len() implies
            arena_test_node(before.tests@[i], before.test_ids@) ==
            arena_test_node(after.tests@[i], after.test_ids@) by {
            match before.tests@[i] {
                ArenaTest::And(slot) | ArenaTest::Or(slot) => {
                    assert(before.test_ids@[slot as int] == after.test_ids@[slot as int]);
                },
                _ => {},
            }
        }
        assert forall|i: int| 0 <= i < before.regexes@.len() implies
            arena_regex_node(before.regexes@[i], before.regex_ids@) ==
            arena_regex_node(after.regexes@[i], after.regex_ids@) by {
            match before.regexes@[i].kind {
                ArenaRegexKind::Union(slot) | ArenaRegexKind::Concat(slot) | ArenaRegexKind::Intersect(slot) => {
                    assert(before.regex_ids@[slot as int] == after.regex_ids@[slot as int]);
                },
                _ => {},
            }
        }
        assert forall|i: int| 0 <= i < before.transitions@.len() implies
            arena_transition_node(before.transitions@[i], before.transition_ids@, before.regex_ids@) ==
            arena_transition_node(after.transitions@[i], after.transition_ids@, after.regex_ids@) by {
            match before.transitions@[i] {
                ArenaTransition::Union(slot) | ArenaTransition::Intersect(slot) => {
                    assert(before.transition_ids@[slot as int] == after.transition_ids@[slot as int]);
                },
                ArenaTransition::Append { transition, suffix } => {
                    assert(before.regex_ids@[suffix as int] == after.regex_ids@[suffix as int]);
                },
                _ => {},
            }
        }
        assert(tables_index_wf(after));
        assert(tables_graph(after).tests =~= tables_graph(before).tests);
        assert(tables_graph(after).regexes =~= tables_graph(before).regexes);
        assert(tables_graph(after).transitions =~= tables_graph(before).transitions);
    }
    impl crate::verify::history_assumptions::StorageSpecImpl for ArenaStorage {
        open(super) spec fn graph(&self) -> model::Graph {
            match self.tables {
                Some(t) => tables_graph(&t),
                None => model::Graph {
                    tests: Seq::empty(), regexes: Seq::empty(), transitions: Seq::empty(),
                    constants: storage_constants(),
                },
            }
        }
        open(super) spec fn capacity(&self) -> int {
            match self.tables { Some(t) => tables_capacity(&t), None => 0 }
        }
        open(super) spec fn slack(&self) -> int {
            match self.tables { Some(t) => tables_slack(&t), None => 0 }
        }
    }

                impl<S: Storage> CanonicalStore<S> {
                    pub(crate) open(super) spec fn graph(&self) -> model::Graph {
                        model::Graph { constants: self.constants@, ..self.storage.graph() }
                    }
                    pub(crate) open(super) spec fn charged_bytes(&self) -> nat { self.bytes as nat }

                    pub(crate) open(super) spec fn capacity(&self) -> int { self.storage.capacity() }
                    pub(crate) open(super) spec fn slack(&self) -> int { self.storage.slack() }
                    pub(crate) open(super) spec fn valid_store(&self) -> bool {
                        let g = self.graph();
                        model::unique_nodes(g) && graph_weight(g) <= self.charged_bytes()
                    }
                }

                impl<S: Storage> crate::verify::history_assumptions::KernelStoreSpecImpl for RuntimeKernel<'_, S> {
                    open(crate) spec fn graph(&self) -> model::Graph { self.store.graph() }
                    open(crate) spec fn valid_store(&self) -> bool { self.store.valid_store() }
                    #[verifier::prophetic]
                    open(crate) spec fn restoration(&self) -> (model::Graph, bool) {
                        let restored = mut_ref_future(self.store);
                        (restored.graph(), restored.valid_store())
                    }
                }


                pub(crate) proof fn lemma_id_clones()
                    ensures
                        forall|a: TestId, b: TestId| cloned(a, b) ==> a == b,
                        forall|a: RegexId, b: RegexId| cloned(a, b) ==> a == b,
                        forall|a: TransitionId, b: TransitionId| cloned(a, b) ==> a == b,
                {}

                pub(super) proof fn lemma_tables_wf_same_tables(before: model::Graph, after: model::Graph)
                    requires
                        model::tables_wf(before),
                        before.tests == after.tests,
                        before.regexes == after.regexes,
                        before.transitions == after.transitions,
                    ensures model::tables_wf(after),
                {
                    model::lemma_old_nodes_wf_under_extends(before, after);
                }


        pub open spec fn empty_tables(g: model::Graph) -> bool {
            g.tests.len() == 0 && g.regexes.len() == 0 && g.transitions.len() == 0
        }


            }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Hash-consing mixes `u32` ids, counts, and flags into `u64` digests; every cast widens.
#![allow(clippy::as_conversions)]

use alloc::vec::Vec;
use core::mem::{align_of, size_of};
use hashconsius::BHConsign;
#[cfg(verus_keep_ghost)]
use history_syntax::syntax::Component;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::KernelStoreSpec;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::no_invariant_failure;
use junco_core::{errors::HistoryError, kernel::*};
use verus_bumpalo::{AllocErr, CHUNK_ALIGN, SliceArena};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

#[allow(
    clippy::option_if_let_else,
    reason = "Explicit matches preserve the Verus proof structure"
)]
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
#[allow(
    clippy::option_if_let_else,
    reason = "Explicit matches preserve the Verus proof structure"
)]
#[verus_verify]
#[verus_spec(outcome => ensures outcome == match result {
    Ok(value) => Ok(value),
    Err(_) => Err(HistoryError::AllocationFailed),
}, outcome matches Err(error) ==> junco_core::spec::semantics::resource_error(error))]
pub fn allocation<T>(result: Result<T, impl core::fmt::Debug>) -> KernelResult<T> {
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
}, outcome matches Err(error) ==> junco_core::spec::semantics::resource_error(error))]
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
/// only if `storage.slack() < budget - storage.capacity()`, which a store whose arenas hold its
/// budget (`capacity == budget`, `slack == 0`) never satisfies.
// ponytail: six budget-sized chunks per retained pair (100 KiB for the runtime); share a chunk if
// allocation cost matters.
#[verus_verify]
pub(crate) const ARENA_CAPACITY: usize = MAX_GRAPH_BYTES;
// Premises of the capacity argument, checked on every compile target. `%` rather than
// `is_multiple_of` so Verus can reason about the same expression at runtime below.
#[allow(clippy::manual_is_multiple_of)]
const _: () = assert!(
    size_of::<TestNode>() > 0
        && size_of::<RegexNode>() > 0
        && size_of::<TransitionNode>() > 0
        && align_of::<TestNode>() <= CHUNK_ALIGN
        && align_of::<RegexNode>() <= CHUNK_ALIGN
        && align_of::<TransitionNode>() <= CHUNK_ALIGN
        && align_of::<TestId>() <= CHUNK_ALIGN
        && align_of::<RegexId>() <= CHUNK_ALIGN
        && align_of::<TransitionId>() <= CHUNK_ALIGN
        && ARENA_CAPACITY % align_of::<TestNode>() == 0
        && ARENA_CAPACITY % align_of::<RegexNode>() == 0
        && ARENA_CAPACITY % align_of::<TransitionNode>() == 0
        && ARENA_CAPACITY % align_of::<TestId>() == 0
        && ARENA_CAPACITY % align_of::<RegexId>() == 0
        && ARENA_CAPACITY % align_of::<TransitionId>() == 0
);
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(bytes) => bytes as int == len * vstd::layout::size_of::<T>(),
    Err(error) => error is GraphIndex,
}, result matches Err(error) ==> junco_core::spec::semantics::resource_error(error))]
pub fn sequence_bytes<T>(len: usize) -> KernelResult<usize> {
    vstd::layout::layout_for_type_is_valid::<T>();
    len.checked_mul(size_of::<T>())
        .ok_or(HistoryError::GraphIndex)
}

// Crate visibility lets Verus retain these payload types in the open weight specs.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) enum TestNode {
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
enum RegexKind {
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
pub(crate) struct RegexNode {
    kind: RegexKind,
    nullable: bool,
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) enum TransitionNode {
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
    // Pinned 64-bit native layouts, observed from the compiled Rust types.
    // Verus erasure emits exact Rust const assertions, so compiler layout drift fails to build.
    #[cfg(target_pointer_width = "64")]
    global layout TestNode is size == 32, align == 8;
    #[cfg(target_pointer_width = "64")]
    global layout RegexNode is size == 24, align == 8;
    #[cfg(target_pointer_width = "64")]
    global layout TransitionNode is size == 16, align == 8;
    #[cfg(target_pointer_width = "64")]
    global layout TestId is size == 4, align == 4;
    #[cfg(target_pointer_width = "64")]
    global layout RegexId is size == 4, align == 4;
    #[cfg(target_pointer_width = "64")]
    global layout TransitionId is size == 4, align == 4;

    impl View for TestNode {
        type V = Self;
        open(in crate::graph) spec fn view(&self) -> Self { *self }
    }
    impl View for RegexNode {
        type V = Self;
        open(in crate::graph) spec fn view(&self) -> Self { *self }
    }
    impl View for TransitionNode {
        type V = Self;
        open(in crate::graph) spec fn view(&self) -> Self { *self }
    }

    pub(crate) open spec fn field_key(field: Component) -> u64 {
        field.0 as u64
    }
    pub(crate) open spec fn primitive_key_hash(p: Primitive) -> u64 {
        match p {
            Primitive::Eq { field, term: Term::Constant(c) } => hashconsius::spec_mix(hashconsius::spec_mix(field_key(field), 0), c),
            Primitive::Eq { field, term: Term::Variable(v) } => hashconsius::spec_mix(hashconsius::spec_mix(field_key(field), 1), field_key(v)),
        }
    }
    impl hashconsius::HashKey for TestNode {
        open(in crate::graph) spec fn spec_hash(v: Self::V) -> u64 { match v {
                TestNode::True => 0,
                TestNode::False => 1,
                TestNode::Atom { primitive, positive } => hashconsius::spec_mix(hashconsius::spec_mix(2, primitive_key_hash(primitive)), positive as u64),
                TestNode::And(s) => hashconsius::spec_mix(3, s as u64),
                TestNode::Or(s) => hashconsius::spec_mix(4, s as u64),
            } }
        fn hash(&self) -> (h: u64)
            ensures h == Self::spec_hash(self@),
        {
            let v = *self;
            match v {
                TestNode::True => 0,
                TestNode::False => 1,
                TestNode::Atom { primitive, positive } => hashconsius::mix(hashconsius::mix(2, match primitive {
                    Primitive::Eq { field, term: Term::Constant(c) } => hashconsius::mix(hashconsius::mix(field.index() as u64, 0), c),
                    Primitive::Eq { field, term: Term::Variable(variable) } => hashconsius::mix(hashconsius::mix(field.index() as u64, 1), variable.index() as u64),
                }), positive as u64),
                TestNode::And(s) => hashconsius::mix(3, s as u64),
                TestNode::Or(s) => hashconsius::mix(4, s as u64),
            }
        }
        fn key_eq(&self, other: &Self) -> (b: bool)
            ensures b == (self@ == other@),
        { match (*self, *other) {
                (TestNode::True, TestNode::True) | (TestNode::False, TestNode::False) => true,
                // Full-field keys avoid the pinned verifier's early inherited-equality dependency; see verification/verus/inherited_ensures_order.rs.
                (
                    TestNode::Atom {
                        primitive: Primitive::Eq { field: a, term: x },
                        positive: p,
                    },
                    TestNode::Atom {
                        primitive: Primitive::Eq { field: b, term: y },
                        positive: q,
                    },
                ) => {
                    a == b
                        && p == q
                        && match (x, y) {
                            (Term::Constant(c), Term::Constant(d)) => c == d,
                            (Term::Variable(c), Term::Variable(d)) => c == d,
                            _ => false,
                        }
                },
                (TestNode::And(a), TestNode::And(b)) | (TestNode::Or(a), TestNode::Or(b)) => a == b,
                _ => false,
            } }
    }
    impl hashconsius::HashKey for RegexNode {
        open(in crate::graph) spec fn spec_hash(v: Self::V) -> u64 { hashconsius::spec_mix(match v.kind {
                RegexKind::Empty => 0,
                RegexKind::All => 1,
                RegexKind::Epsilon => 2,
                RegexKind::Test(id) => hashconsius::spec_mix(3, id@ as u64),
                RegexKind::Union(s) => hashconsius::spec_mix(4, s as u64),
                RegexKind::Concat(s) => hashconsius::spec_mix(5, s as u64),
                RegexKind::Star(id) => hashconsius::spec_mix(6, id@ as u64),
                RegexKind::Intersect(s) => hashconsius::spec_mix(7, s as u64),
                RegexKind::Not(id) => hashconsius::spec_mix(8, id@ as u64),
            }, v.nullable as u64) }
        fn hash(&self) -> (h: u64)
            ensures h == Self::spec_hash(self@),
        {
            let v = *self;
            hashconsius::mix(match v.kind {
                RegexKind::Empty => 0,
                RegexKind::All => 1,
                RegexKind::Epsilon => 2,
                RegexKind::Test(id) => hashconsius::mix(3, id.get() as u64),
                RegexKind::Union(s) => hashconsius::mix(4, s as u64),
                RegexKind::Concat(s) => hashconsius::mix(5, s as u64),
                RegexKind::Star(id) => hashconsius::mix(6, id.get() as u64),
                RegexKind::Intersect(s) => hashconsius::mix(7, s as u64),
                RegexKind::Not(id) => hashconsius::mix(8, id.get() as u64),
            }, v.nullable as u64)
        }
        fn key_eq(&self, other: &Self) -> (b: bool)
            ensures b == (self@ == other@),
        { self.nullable == other.nullable && match (self.kind, other.kind) {
                (RegexKind::Empty, RegexKind::Empty) | (RegexKind::All, RegexKind::All) | (RegexKind::Epsilon, RegexKind::Epsilon) => true,
                (RegexKind::Test(a), RegexKind::Test(b)) => a == b,
                (RegexKind::Union(a), RegexKind::Union(b)) | (RegexKind::Concat(a), RegexKind::Concat(b)) | (RegexKind::Intersect(a), RegexKind::Intersect(b)) => a == b,
                (RegexKind::Star(a), RegexKind::Star(b)) | (RegexKind::Not(a), RegexKind::Not(b)) => a == b,
                _ => false,
            } }
    }
    impl hashconsius::HashKey for TransitionNode {
        open(in crate::graph) spec fn spec_hash(v: Self::V) -> u64 { match v {
                TransitionNode::Const(id) => hashconsius::spec_mix(0, id@ as u64),
                TransitionNode::If { test, then_transition, else_transition } => hashconsius::spec_mix(hashconsius::spec_mix(hashconsius::spec_mix(1, test@ as u64), then_transition@ as u64), else_transition@ as u64),
                TransitionNode::Union(s) => hashconsius::spec_mix(2, s as u64),
                TransitionNode::Intersect(s) => hashconsius::spec_mix(3, s as u64),
                TransitionNode::Not(id) => hashconsius::spec_mix(4, id@ as u64),
                TransitionNode::Append { transition, suffix } => hashconsius::spec_mix(hashconsius::spec_mix(5, transition@ as u64), suffix as u64),
            } }
        fn hash(&self) -> (h: u64)
            ensures h == Self::spec_hash(self@),
        {
            let v = *self;
            match v {
                TransitionNode::Const(id) => hashconsius::mix(0, id.get() as u64),
                TransitionNode::If { test, then_transition, else_transition } => hashconsius::mix(hashconsius::mix(hashconsius::mix(1, test.get() as u64), then_transition.get() as u64), else_transition.get() as u64),
                TransitionNode::Union(s) => hashconsius::mix(2, s as u64),
                TransitionNode::Intersect(s) => hashconsius::mix(3, s as u64),
                TransitionNode::Not(id) => hashconsius::mix(4, id.get() as u64),
                TransitionNode::Append { transition, suffix } => hashconsius::mix(hashconsius::mix(5, transition.get() as u64), suffix as u64),
            }
        }
        fn key_eq(&self, other: &Self) -> (b: bool)
            ensures b == (self@ == other@),
        { match (*self, *other) {
                (TransitionNode::Const(a), TransitionNode::Const(b)) => a == b,
                (TransitionNode::If { test: a, then_transition: b, else_transition: c }, TransitionNode::If { test: d, then_transition: e, else_transition: f }) => a == d && b == e && c == f,
                (TransitionNode::Union(a), TransitionNode::Union(b)) | (TransitionNode::Intersect(a), TransitionNode::Intersect(b)) => a == b,
                (TransitionNode::Not(a), TransitionNode::Not(b)) => a == b,
                (TransitionNode::Append { transition: a, suffix: b }, TransitionNode::Append { transition: c, suffix: d }) => a == c && b == d,
                _ => false,
            } }
    }
}

macro_rules! id_lists {
    ($name:ident, $id:ident, $eq_lemma:ident) => {
        #[verus_verify]
        struct $name {
            slices: SliceArena<$id>,
            index: hashconsius::index::Buckets,
        }
        vstd::prelude::verus! {
            impl View for $name {
                type V = Seq<Seq<$id>>;
                open(in crate::graph) spec fn view(&self) -> Self::V { self.slices@ }
            }
            impl $name {
                pub(super) open(in crate::graph) spec fn ids_hash_prefix(ids: Seq<$id>, n: nat) -> u64
                    recommends n <= ids.len(),
                    decreases n,
                {
                    if n == 0 { ids.len() as u64 }
                    else { hashconsius::spec_mix(Self::ids_hash_prefix(ids, (n - 1) as nat), ids[n - 1]@ as u64) }
                }
                pub(super) open(in crate::graph) spec fn ids_spec_hash(ids: Seq<$id>) -> u64 {
                    Self::ids_hash_prefix(ids, ids.len())
                }
                pub(super) open(in crate::graph) spec fn hashes(self) -> Seq<u64> {
                    self@.map_values(|ids: Seq<$id>| Self::ids_spec_hash(ids))
                }
                pub(super) open(in crate::graph) spec fn inv(self) -> bool {
                    self.index.inv(self.hashes()) && self@.no_duplicates()
                        && self@.len() <= usize::MAX
                }
                pub(super) open(in crate::graph) spec fn capacity(self) -> int { self.slices.capacity() }
                pub(super) open(in crate::graph) spec fn remaining(self) -> int { self.slices.remaining() }
                pub(super) open(in crate::graph) spec fn aligned(self) -> bool { self.slices.aligned() }

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
                        h = hashconsius::mix(h, id.get() as u64);
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
                            proof {
                                assert forall|a: $id, b: $id| #[trigger] a.eq_spec(&b) == (a == b) by {
                                    verify::$eq_lemma(a, b);
                                }
                            }
                            if junco_core::kernel::id_slice_eq(candidate, ids) { return Some(slot); }
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
                    let slot = self.slices.len();
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

id_lists!(TestIdLists, TestId, lemma_test_id_eq);
id_lists!(RegexIdLists, RegexId, lemma_regex_id_eq);
id_lists!(TransitionIdLists, TransitionId, lemma_transition_id_eq);

#[verus_verify]
struct ArenaTables {
    tests: BHConsign<TestNode>,
    test_ids: TestIdLists,
    regexes: BHConsign<RegexNode>,
    regex_ids: RegexIdLists,
    transitions: BHConsign<TransitionNode>,
    transition_ids: TransitionIdLists,
    #[cfg(test)]
    lifetime_counts: Option<alloc::sync::Arc<ArenaLifetimeCounts>>,
}
#[verus_verify]
pub(crate) struct ArenaStorage {
    tables: Option<ArenaTables>,
}

// Verus does not model implicit destruction; ArenaTables::release checks the six frees.
#[verus_verify(external)]
impl Drop for ArenaStorage {
    fn drop(&mut self) {
        if let Some(tables) = self.tables.take() {
            tables.release();
        }
    }
}

#[cfg(test)]
#[derive(Default)]
pub struct ArenaLifetimeCounts {
    allocations: core::sync::atomic::AtomicUsize,
    frees: core::sync::atomic::AtomicUsize,
}

#[cfg(test)]
impl ArenaLifetimeCounts {
    pub fn snapshot(&self) -> (usize, usize) {
        use core::sync::atomic::Ordering;
        (
            self.allocations.load(Ordering::Relaxed),
            self.frees.load(Ordering::Relaxed),
        )
    }

    fn freed(counts: &Option<alloc::sync::Arc<Self>>) {
        if let Some(counts) = counts {
            counts
                .frees
                .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        }
    }
}

#[cfg(test)]
impl ArenaStorage {
    /// Observe this storage's six existing chunks and their individual frees.
    pub fn track_lifetime(
        &mut self,
        counts: alloc::sync::Arc<ArenaLifetimeCounts>,
    ) -> KernelResult<()> {
        let tables = present(self.tables.as_mut(), "arena released")?;
        if tables.lifetime_counts.is_some() {
            return Err(HistoryError::invariant("arena lifetime already observed"));
        }
        counts
            .allocations
            .fetch_add(6, core::sync::atomic::Ordering::Relaxed);
        tables.lifetime_counts = Some(counts);
        Ok(())
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl ArenaStorage {
        pub(crate) closed spec fn has_tables(&self) -> bool {
            self.tables is Some
        }

        #[verifier::type_invariant]
        closed spec fn inv(&self) -> bool {
            self.tables is Some ==> verify::tables_wf(&self.tables->0)
        }
    }
}

#[verus_verify]
impl ArenaTables {
    #[allow(
        clippy::arithmetic_side_effects,
        reason = "Type alignments are nonzero, so these remainder checks cannot panic"
    )]
    #[verus_spec(result => ensures result matches Ok(t) ==> verify::tables_wf(&t)
        && verify::empty_tables(verify::tables_graph(&t))
        && verify::tables_capacity(&t) == capacity && verify::tables_slack(&t) == 0,
        result matches Err(error) ==> error is Invariant || error is AllocationFailed,
        verify::construction_layout(capacity) ==> no_invariant_failure(result))]
    #[allow(clippy::manual_is_multiple_of)]
    fn with_capacity(capacity: usize) -> KernelResult<Self> {
        vstd::layout::layout_for_type_is_valid::<TestNode>();
        vstd::layout::layout_for_type_is_valid::<RegexNode>();
        vstd::layout::layout_for_type_is_valid::<TransitionNode>();
        vstd::layout::layout_for_type_is_valid::<TestId>();
        vstd::layout::layout_for_type_is_valid::<RegexId>();
        vstd::layout::layout_for_type_is_valid::<TransitionId>();
        // Statically true (see the `const _` assert above); repeated here so Verus can use it.
        if size_of::<TestNode>() == 0
            || size_of::<RegexNode>() == 0
            || size_of::<TransitionNode>() == 0
            || align_of::<TestNode>() > CHUNK_ALIGN
            || align_of::<RegexNode>() > CHUNK_ALIGN
            || align_of::<TransitionNode>() > CHUNK_ALIGN
            || align_of::<TestId>() > CHUNK_ALIGN
            || align_of::<RegexId>() > CHUNK_ALIGN
            || align_of::<TransitionId>() > CHUNK_ALIGN
            || capacity % align_of::<TestNode>() != 0
            || capacity % align_of::<RegexNode>() != 0
            || capacity % align_of::<TransitionNode>() != 0
            || capacity % align_of::<TestId>() != 0
            || capacity % align_of::<RegexId>() != 0
            || capacity % align_of::<TransitionId>() != 0
        {
            return Err(HistoryError::invariant("arena layout premises violated"));
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
            #[cfg(test)]
            lifetime_counts: None,
        };
        proof! { verify::lemma_fresh_tables(&tables, capacity); }
        Ok(tables)
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(v) ==> index < verify::tables_graph(self).tests.len()
            && v@ == verify::tables_graph(self).tests[index as int],
        result matches Err(error) ==> error is Invariant,
        index < verify::tables_graph(self).tests.len() ==> result is Ok)]
    fn test(&self, index: usize) -> KernelResult<TestView<'_>> {
        if index >= self.tests.len() {
            return Err(HistoryError::invariant("invalid test ID"));
        }
        let node = self.tests.elem(index);
        proof! { assert(verify::arena_test_wf(self, *node)); }
        Ok(match *node {
            TestNode::True => TestView::True,
            TestNode::False => TestView::False,
            TestNode::Atom {
                primitive,
                positive,
            } => TestView::Atom {
                primitive,
                positive,
            },
            TestNode::And(slot) => TestView::And(present(
                self.test_ids.slices.get(slot),
                "invalid test children",
            )?),
            TestNode::Or(slot) => TestView::Or(present(
                self.test_ids.slices.get(slot),
                "invalid test children",
            )?),
        })
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(v) ==> index < verify::tables_graph(self).regexes.len()
            && v@ == verify::tables_graph(self).regexes[index as int],
        result matches Err(error) ==> error is Invariant,
        index < verify::tables_graph(self).regexes.len() ==> result is Ok)]
    fn regex(&self, index: usize) -> KernelResult<RegexView<'_>> {
        if index >= self.regexes.len() {
            return Err(HistoryError::invariant("invalid regex ID"));
        }
        let node = self.regexes.elem(index);
        proof! { assert(verify::arena_regex_wf(self, *node)); }
        let kind = match node.kind {
            RegexKind::Empty => RegexKindView::Empty,
            RegexKind::All => RegexKindView::All,
            RegexKind::Epsilon => RegexKindView::Epsilon,
            RegexKind::Test(id) => RegexKindView::Test(id),
            RegexKind::Union(slot) => RegexKindView::Union(present(
                self.regex_ids.slices.get(slot),
                "invalid regex children",
            )?),
            RegexKind::Concat(slot) => RegexKindView::Concat(present(
                self.regex_ids.slices.get(slot),
                "invalid regex children",
            )?),
            RegexKind::Star(id) => RegexKindView::Star(id),
            RegexKind::Intersect(slot) => RegexKindView::Intersect(present(
                self.regex_ids.slices.get(slot),
                "invalid regex children",
            )?),
            RegexKind::Not(id) => RegexKindView::Not(id),
        };
        Ok(RegexView {
            kind,
            nullable: node.nullable,
        })
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(v) ==> index < verify::tables_graph(self).transitions.len()
            && v@ == verify::tables_graph(self).transitions[index as int],
        result matches Err(error) ==> error is Invariant,
        index < verify::tables_graph(self).transitions.len() ==> result is Ok)]
    fn transition(&self, index: usize) -> KernelResult<TransitionView<'_>> {
        if index >= self.transitions.len() {
            return Err(HistoryError::invariant("invalid transition ID"));
        }
        let node = self.transitions.elem(index);
        proof! { assert(verify::arena_transition_wf(self, *node)); }
        Ok(match *node {
            TransitionNode::Const(id) => TransitionView::Const(id),
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } => TransitionView::If {
                test,
                then_transition,
                else_transition,
            },
            TransitionNode::Union(slot) => TransitionView::Union(present(
                self.transition_ids.slices.get(slot),
                "invalid transition children",
            )?),
            TransitionNode::Intersect(slot) => TransitionView::Intersect(present(
                self.transition_ids.slices.get(slot),
                "invalid transition children",
            )?),
            TransitionNode::Not(id) => TransitionView::Not(id),
            TransitionNode::Append { transition, suffix } => TransitionView::Append {
                transition,
                suffix: present(self.regex_ids.slices.get(suffix), "invalid append suffix")?,
            },
        })
    }
    #[verus_spec(result => requires verify::tables_wf(self), ensures
        result matches Ok(Some(id)) ==> id@ < verify::tables_graph(self).tests.len()
            && verify::tables_graph(self).tests[id@ as int] == view@,
        result matches Ok(None) ==> !verify::tables_graph(self).tests.contains(view@),
        result matches Err(error) ==> error is GraphIndex)]
    fn find_test(&self, view: TestView<'_>) -> KernelResult<Option<TestId>> {
        let node = match view {
            TestView::True => TestNode::True,
            TestView::False => TestNode::False,
            TestView::Atom {
                primitive,
                positive,
            } => TestNode::Atom {
                primitive,
                positive,
            },
            TestView::And(ids) | TestView::Or(ids) => {
                let Some(slot) = self.test_ids.find(ids) else {
                    proof! { verify::lemma_missing_test_children(self, view@, ids@); }
                    return Ok(None);
                };
                match view {
                    TestView::And(_) => TestNode::And(slot),
                    _ => TestNode::Or(slot),
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
        result matches Ok(Some(id)) ==> id@ < verify::tables_graph(self).regexes.len()
            && verify::tables_graph(self).regexes[id@ as int] == view@,
        result matches Ok(None) ==> !verify::tables_graph(self).regexes.contains(view@),
        result matches Err(error) ==> error is GraphIndex)]
    fn find_regex(&self, view: RegexView<'_>) -> KernelResult<Option<RegexId>> {
        let kind = match view.kind {
            RegexKindView::Empty => RegexKind::Empty,
            RegexKindView::All => RegexKind::All,
            RegexKindView::Epsilon => RegexKind::Epsilon,
            RegexKindView::Test(id) => RegexKind::Test(id),
            RegexKindView::Star(id) => RegexKind::Star(id),
            RegexKindView::Not(id) => RegexKind::Not(id),
            RegexKindView::Union(ids)
            | RegexKindView::Concat(ids)
            | RegexKindView::Intersect(ids) => {
                let Some(slot) = self.regex_ids.find(ids) else {
                    proof! { verify::lemma_missing_regex_children(self, view@, ids@); }
                    return Ok(None);
                };
                match view.kind {
                    RegexKindView::Union(_) => RegexKind::Union(slot),
                    RegexKindView::Concat(_) => RegexKind::Concat(slot),
                    _ => RegexKind::Intersect(slot),
                }
            }
        };
        let node = RegexNode {
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
        result matches Ok(Some(id)) ==> id@ < verify::tables_graph(self).transitions.len()
            && verify::tables_graph(self).transitions[id@ as int] == view@,
        result matches Ok(None) ==> !verify::tables_graph(self).transitions.contains(view@),
        result matches Err(error) ==> error is GraphIndex)]
    fn find_transition(&self, view: TransitionView<'_>) -> KernelResult<Option<TransitionId>> {
        let node = match view {
            TransitionView::Const(id) => TransitionNode::Const(id),
            TransitionView::If {
                test,
                then_transition,
                else_transition,
            } => TransitionNode::If {
                test,
                then_transition,
                else_transition,
            },
            TransitionView::Not(id) => TransitionNode::Not(id),
            TransitionView::Union(ids) | TransitionView::Intersect(ids) => {
                let Some(slot) = self.transition_ids.find(ids) else {
                    proof! { verify::lemma_missing_transition_children(self, view@, ids@); }
                    return Ok(None);
                };
                match view {
                    TransitionView::Union(_) => TransitionNode::Union(slot),
                    _ => TransitionNode::Intersect(slot),
                }
            }
            TransitionView::Append { transition, suffix } => {
                let Some(slot) = self.regex_ids.find(suffix) else {
                    proof! { verify::lemma_missing_append_suffix(self, transition@, suffix@); }
                    return Ok(None);
                };
                TransitionNode::Append {
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
        result matches Ok(id) ==> id@ == verify::tables_graph(old(self)).tests.len()
            && verify::tables_graph(final(self)).tests == verify::tables_graph(old(self)).tests.push(view@),
        result matches Err(error) ==> error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed,
        verify::tables_capacity(final(self)) == verify::tables_capacity(old(self)),
        result is Ok ==> verify::tables_slack(final(self)) >= verify::tables_slack(old(self)),
        result matches Err(error) ==> error is ArenaExhausted ==>
            verify::graph_weight(verify::tables_graph(old(self))) + verify::test_weight(view@)
                - verify::tables_slack(old(self)) > verify::tables_capacity(old(self)))]
    fn push_test(&mut self, view: TestView<'_>) -> KernelResult<TestId> {
        vstd::layout::layout_for_type_is_valid::<TestNode>();
        proof_decl! { let ghost before = *self; }
        let id = TestId::from_index(self.tests.len())?;
        let node = match view {
            TestView::True => TestNode::True,
            TestView::False => TestNode::False,
            TestView::Atom {
                primitive,
                positive,
            } => TestNode::Atom {
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
                TestNode::And(slot)
            }
            TestView::Or(ids) => {
                let slot = arena(self.test_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.test_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.test_ids@) <= verify::pool_bytes(before.test_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<TestId>()));
                }
                TestNode::Or(slot)
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
            assert(_handle.spec_uid() == id@ as nat);
            assert forall|i: int| 0 <= i < self.tests@.len() implies
                verify::arena_test_wf(self, self.tests@[i]) by {
                if i < before.tests@.len() { assert(self.tests@[i] == before.tests@[i]); }
            }
            verify::lemma_tests_weight_push(verify::tables_graph(&before).tests, view@);
            verify::lemma_mul_bytes_succ(before.tests@.len(), vstd::layout::size_of::<TestNode>());
            assert(verify::tables_wf(self));
            assert(verify::arena_live(self) <= verify::arena_live(&before) + verify::test_weight(view@));
        }
        Ok(id)
    }
    #[allow(
        clippy::shadow_unrelated,
        reason = "Local node identifiers mirror the matched Verus model variants"
    )]
    #[verus_spec(result => requires verify::tables_wf(old(self)),
        !verify::tables_graph(old(self)).regexes.contains(view@), ensures
        verify::tables_wf(final(self)),
        verify::tables_graph(final(self)).constants == verify::tables_graph(old(self)).constants,
        verify::tables_graph(final(self)).tests == verify::tables_graph(old(self)).tests,
        verify::tables_graph(final(self)).transitions == verify::tables_graph(old(self)).transitions,
        result is Err ==> verify::tables_graph(final(self)) == verify::tables_graph(old(self)),
        result matches Ok(id) ==> id@ == verify::tables_graph(old(self)).regexes.len()
            && verify::tables_graph(final(self)).regexes == verify::tables_graph(old(self)).regexes.push(view@),
        result matches Err(error) ==> error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed,
        verify::tables_capacity(final(self)) == verify::tables_capacity(old(self)),
        result is Ok ==> verify::tables_slack(final(self)) >= verify::tables_slack(old(self)),
        result matches Err(error) ==> error is ArenaExhausted ==>
            verify::graph_weight(verify::tables_graph(old(self))) + verify::regex_weight(view@)
                - verify::tables_slack(old(self)) > verify::tables_capacity(old(self)))]
    fn push_regex(&mut self, view: RegexView<'_>) -> KernelResult<RegexId> {
        vstd::layout::layout_for_type_is_valid::<RegexNode>();
        proof_decl! { let ghost before = *self; }
        let id = RegexId::from_index(self.regexes.len())?;
        let kind = match view.kind {
            RegexKindView::Empty => RegexKind::Empty,
            RegexKindView::All => RegexKind::All,
            RegexKindView::Epsilon => RegexKind::Epsilon,
            RegexKindView::Test(id) => RegexKind::Test(id),
            RegexKindView::Union(ids) => {
                let slot = arena(self.regex_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<RegexId>()));
                }
                RegexKind::Union(slot)
            }
            RegexKindView::Concat(ids) => {
                let slot = arena(self.regex_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<RegexId>()));
                }
                RegexKind::Concat(slot)
            }
            RegexKindView::Star(id) => RegexKind::Star(id),
            RegexKindView::Intersect(ids) => {
                let slot = arena(self.regex_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<RegexId>()));
                }
                RegexKind::Intersect(slot)
            }
            RegexKindView::Not(id) => RegexKind::Not(id),
        };
        let node = RegexNode {
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
            assert(_handle.spec_uid() == id@ as nat);
            assert forall|i: int| 0 <= i < self.regexes@.len() implies
                verify::arena_regex_wf(self, self.regexes@[i]) by {
                if i < before.regexes@.len() { assert(self.regexes@[i] == before.regexes@[i]); }
            }
            verify::lemma_regexes_weight_push(verify::tables_graph(&before).regexes, view@);
            verify::lemma_mul_bytes_succ(before.regexes@.len(), vstd::layout::size_of::<RegexNode>());
            assert(verify::tables_wf(self));
            assert(verify::arena_live(self) <= verify::arena_live(&before) + verify::regex_weight(view@));
        }
        Ok(id)
    }
    #[allow(
        clippy::shadow_unrelated,
        reason = "Local node identifiers mirror the matched Verus model variants"
    )]
    #[verus_spec(result => requires verify::tables_wf(old(self)),
        !verify::tables_graph(old(self)).transitions.contains(view@), ensures
        verify::tables_wf(final(self)),
        verify::tables_graph(final(self)).constants == verify::tables_graph(old(self)).constants,
        verify::tables_graph(final(self)).tests == verify::tables_graph(old(self)).tests,
        verify::tables_graph(final(self)).regexes == verify::tables_graph(old(self)).regexes,
        result is Err ==> verify::tables_graph(final(self)) == verify::tables_graph(old(self)),
        result matches Ok(id) ==> id@ == verify::tables_graph(old(self)).transitions.len()
            && verify::tables_graph(final(self)).transitions == verify::tables_graph(old(self)).transitions.push(view@),
        result matches Err(error) ==> error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed,
        verify::tables_capacity(final(self)) == verify::tables_capacity(old(self)),
        result is Ok ==> verify::tables_slack(final(self)) >= verify::tables_slack(old(self)),
        result matches Err(error) ==> error is ArenaExhausted ==>
            verify::graph_weight(verify::tables_graph(old(self))) + verify::transition_weight(view@)
                - verify::tables_slack(old(self)) > verify::tables_capacity(old(self)))]
    fn push_transition(&mut self, view: TransitionView<'_>) -> KernelResult<TransitionId> {
        vstd::layout::layout_for_type_is_valid::<TransitionNode>();
        proof_decl! { let ghost before = *self; }
        let id = TransitionId::from_index(self.transitions.len())?;
        let node = match view {
            TransitionView::Const(id) => TransitionNode::Const(id),
            TransitionView::If {
                test,
                then_transition,
                else_transition,
            } => TransitionNode::If {
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
                TransitionNode::Union(slot)
            }
            TransitionView::Intersect(ids) => {
                let slot = arena(self.transition_ids.intern(ids))?;
                proof! { verify::lemma_pool_bytes_push(before.transition_ids@, ids@); }
                proof! {
                    assert(verify::pool_bytes(self.transition_ids@) <= verify::pool_bytes(before.transition_ids@)
                        + verify::mul_bytes(ids@.len(), vstd::layout::size_of::<TransitionId>()));
                }
                TransitionNode::Intersect(slot)
            }
            TransitionView::Not(id) => TransitionNode::Not(id),
            TransitionView::Append { transition, suffix } => {
                let slot = arena(self.regex_ids.intern(suffix))?;
                proof! { verify::lemma_pool_bytes_push(before.regex_ids@, suffix@); }
                proof! {
                    assert(verify::pool_bytes(self.regex_ids@) <= verify::pool_bytes(before.regex_ids@)
                        + verify::mul_bytes(suffix@.len(), vstd::layout::size_of::<RegexId>()));
                }
                TransitionNode::Append {
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
            assert(_handle.spec_uid() == id@ as nat);
            assert forall|i: int| 0 <= i < self.transitions@.len() implies
                verify::arena_transition_wf(self, self.transitions@[i]) by {
                if i < before.transitions@.len() { assert(self.transitions@[i] == before.transitions@[i]); }
            }
            verify::lemma_transitions_weight_push(verify::tables_graph(&before).transitions, view@);
            verify::lemma_mul_bytes_succ(before.transitions@.len(), vstd::layout::size_of::<TransitionNode>());
            assert(verify::tables_wf(self));
            assert(verify::arena_live(self) <= verify::arena_live(&before) + verify::transition_weight(view@));
        }
        Ok(id)
    }
    #[verus_spec(requires verify::tables_wf(&self))]
    fn release(self) {
        self.tests.free();
        #[cfg(test)]
        ArenaLifetimeCounts::freed(&self.lifetime_counts);
        self.test_ids.free();
        #[cfg(test)]
        ArenaLifetimeCounts::freed(&self.lifetime_counts);
        self.regexes.free();
        #[cfg(test)]
        ArenaLifetimeCounts::freed(&self.lifetime_counts);
        self.regex_ids.free();
        #[cfg(test)]
        ArenaLifetimeCounts::freed(&self.lifetime_counts);
        self.transitions.free();
        #[cfg(test)]
        ArenaLifetimeCounts::freed(&self.lifetime_counts);
        self.transition_ids.free();
        #[cfg(test)]
        ArenaLifetimeCounts::freed(&self.lifetime_counts);
    }
}
#[verus_verify]
impl ArenaStorage {
    #[verus_spec(result => ensures result matches Ok(s) ==> verify::empty_tables(s.graph())
        && s.has_tables() && s.capacity() == capacity && s.slack() == 0,
        result matches Err(error) ==> error is Invariant || error is AllocationFailed,
        verify::construction_layout(capacity) ==> no_invariant_failure(result))]
    pub(crate) fn with_capacity(capacity: usize) -> KernelResult<Self> {
        Ok(Self {
            tables: Some(ArenaTables::with_capacity(capacity)?),
        })
    }
    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure"
    )]
    #[verus_spec(result => ensures
        result.0 == self.graph().tests.len(),
        result.1 == self.graph().regexes.len(),
        result.2 == self.graph().transitions.len())]
    pub(crate) fn lengths(&self) -> (usize, usize, usize) {
        proof! { use_type_invariant(&*self); }
        match self.tables.as_ref() {
            Some(tables) => (
                tables.tests.len(),
                tables.regexes.len(),
                tables.transitions.len(),
            ),
            None => (0, 0, 0),
        }
    }
}
#[verus_verify]
impl ArenaStorage {
    #[verus_spec(r =>
        ensures r matches Ok(v) ==> id@ < self.graph().tests.len()
            && v@ == self.graph().tests[id@ as int],
            r matches Err(error) ==> error is Invariant,
            self.tables is Some && id@ < self.graph().tests.len() ==> r is Ok
    )]
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>> {
        proof! { use_type_invariant(&*self); }
        let tables = present(self.tables.as_ref(), "arena released")?;
        proof! { TestId::lemma_view(id); }
        tables.test(id.index()?)
    }
    #[verus_spec(r =>
        ensures r matches Ok(Some(id)) ==> id@ < self.graph().tests.len()
            && self.graph().tests[id@ as int] == view@,
            r matches Ok(None) ==> !self.graph().tests.contains(view@),
            r matches Err(error) ==> error is Invariant || error is GraphIndex,
            self.tables is Some ==> no_invariant_failure(r)
    )]
    fn find_test(&self, view: TestView<'_>) -> KernelResult<Option<TestId>> {
        proof! { use_type_invariant(&*self); }
        present(self.tables.as_ref(), "arena released")?.find_test(view)
    }
    #[verus_spec(r =>
        ensures r matches Ok(Some(id)) ==> id@ < self.graph().regexes.len()
            && self.graph().regexes[id@ as int] == view@,
            r matches Ok(None) ==> !self.graph().regexes.contains(view@),
            r matches Err(error) ==> error is Invariant || error is GraphIndex,
            self.tables is Some ==> no_invariant_failure(r)
    )]
    fn find_regex(&self, view: RegexView<'_>) -> KernelResult<Option<RegexId>> {
        proof! { use_type_invariant(&*self); }
        present(self.tables.as_ref(), "arena released")?.find_regex(view)
    }
    #[verus_spec(r =>
        ensures r matches Ok(Some(id)) ==> id@ < self.graph().transitions.len()
            && self.graph().transitions[id@ as int] == view@,
            r matches Ok(None) ==> !self.graph().transitions.contains(view@),
            r matches Err(error) ==> error is Invariant || error is GraphIndex,
            self.tables is Some ==> no_invariant_failure(r)
    )]
    fn find_transition(&self, view: TransitionView<'_>) -> KernelResult<Option<TransitionId>> {
        proof! { use_type_invariant(&*self); }
        present(self.tables.as_ref(), "arena released")?.find_transition(view)
    }
    #[verus_spec(r =>
        requires !old(self).graph().tests.contains(view@),
        ensures
            (final(self).tables is Some) == (old(self).tables is Some),
            old(self).tables is Some ==> no_invariant_failure(r),
            final(self).graph().constants == old(self).graph().constants,
            final(self).graph().regexes == old(self).graph().regexes,
            final(self).graph().transitions == old(self).graph().transitions,
            r is Err ==> final(self).graph() == old(self).graph(),
            r matches Ok(id) ==> id@ == old(self).graph().tests.len()
                && final(self).graph().tests == old(self).graph().tests.push(view@),
            r matches Err(error) ==> error is Invariant || error is GraphBudget || error is GraphIndex
                || error is ArenaExhausted || error is AllocationFailed,
            final(self).capacity() == old(self).capacity(),
            r is Ok ==> final(self).slack() >= old(self).slack(),
            r matches Err(error) ==> error is ArenaExhausted ==>
                verify::graph_weight(old(self).graph()) + verify::test_weight(view@) - old(self).slack()
                    > old(self).capacity()
    )]
    fn push_test(&mut self, view: TestView<'_>) -> KernelResult<TestId> {
        proof! { use_type_invariant(&*self); }
        // Restore table ownership before propagating either success or failure.
        let Some(mut tables) = self.tables.take() else {
            return Err(HistoryError::invariant("arena released"));
        };
        let result = tables.push_test(view);
        self.tables = Some(tables);
        result
    }
    #[verus_spec(r =>
        ensures r matches Ok(v) ==> id@ < self.graph().regexes.len()
            && v@ == self.graph().regexes[id@ as int],
            r matches Err(error) ==> error is Invariant,
            self.tables is Some && id@ < self.graph().regexes.len() ==> r is Ok
    )]
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>> {
        proof! { use_type_invariant(&*self); }
        let tables = present(self.tables.as_ref(), "arena released")?;
        proof! { RegexId::lemma_view(id); }
        tables.regex(id.index()?)
    }
    #[verus_spec(r =>
        requires !old(self).graph().regexes.contains(view@),
        ensures
            (final(self).tables is Some) == (old(self).tables is Some),
            old(self).tables is Some ==> no_invariant_failure(r),
            final(self).graph().constants == old(self).graph().constants,
            final(self).graph().tests == old(self).graph().tests,
            final(self).graph().transitions == old(self).graph().transitions,
            r is Err ==> final(self).graph() == old(self).graph(),
            r matches Ok(id) ==> id@ == old(self).graph().regexes.len()
                && final(self).graph().regexes == old(self).graph().regexes.push(view@),
            r matches Err(error) ==> error is Invariant || error is GraphBudget || error is GraphIndex
                || error is ArenaExhausted || error is AllocationFailed,
            final(self).capacity() == old(self).capacity(),
            r is Ok ==> final(self).slack() >= old(self).slack(),
            r matches Err(error) ==> error is ArenaExhausted ==>
                verify::graph_weight(old(self).graph()) + verify::regex_weight(view@) - old(self).slack()
                    > old(self).capacity()
    )]
    fn push_regex(&mut self, view: RegexView<'_>) -> KernelResult<RegexId> {
        proof! { use_type_invariant(&*self); }
        let Some(mut tables) = self.tables.take() else {
            return Err(HistoryError::invariant("arena released"));
        };
        let result = tables.push_regex(view);
        self.tables = Some(tables);
        result
    }
    #[verus_spec(r =>
        ensures r matches Ok(v) ==> id@ < self.graph().transitions.len()
            && v@ == self.graph().transitions[id@ as int],
            r matches Err(error) ==> error is Invariant,
            self.tables is Some && id@ < self.graph().transitions.len() ==> r is Ok
    )]
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>> {
        proof! { use_type_invariant(&*self); }
        let tables = present(self.tables.as_ref(), "arena released")?;
        proof! { TransitionId::lemma_view(id); }
        tables.transition(id.index()?)
    }
    #[verus_spec(r =>
        requires !old(self).graph().transitions.contains(view@),
        ensures
            (final(self).tables is Some) == (old(self).tables is Some),
            old(self).tables is Some ==> no_invariant_failure(r),
            final(self).graph().constants == old(self).graph().constants,
            final(self).graph().tests == old(self).graph().tests,
            final(self).graph().regexes == old(self).graph().regexes,
            r is Err ==> final(self).graph() == old(self).graph(),
            r matches Ok(id) ==> id@ == old(self).graph().transitions.len()
                && final(self).graph().transitions == old(self).graph().transitions.push(view@),
            r matches Err(error) ==> error is Invariant || error is GraphBudget || error is GraphIndex
                || error is ArenaExhausted || error is AllocationFailed,
            final(self).capacity() == old(self).capacity(),
            r is Ok ==> final(self).slack() >= old(self).slack(),
            r matches Err(error) ==> error is ArenaExhausted ==>
                verify::graph_weight(old(self).graph()) + verify::transition_weight(view@) - old(self).slack()
                    > old(self).capacity()
    )]
    fn push_transition(&mut self, view: TransitionView<'_>) -> KernelResult<TransitionId> {
        proof! { use_type_invariant(&*self); }
        let Some(mut tables) = self.tables.take() else {
            return Err(HistoryError::invariant("arena released"));
        };
        let result = tables.push_transition(view);
        self.tables = Some(tables);
        result
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
pub struct CanonicalStore {
    pub(crate) storage: ArenaStorage,
    // Verus needs every field crate-visible for direct accounting contracts.
    pub(crate) constants: Constants,
    pub(crate) bytes: usize,
    /// Bytes the graph may be charged; each arena holds this many.
    pub(crate) budget: usize,
}
#[verus_verify]
impl CanonicalStore {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn charged(&self) -> nat { self.bytes as nat }
        pub closed spec fn budget(&self) -> nat { self.budget as nat }

        /// Charged native node payloads leave representable room for cache and truth indices.
        #[cfg(target_pointer_width = "64")]
        pub proof fn lemma_node_count_bounds(&self)
            requires self.valid_store(),
            ensures self.graph().tests.len() + 64 <= usize::MAX,
                self.graph().regexes.len() < usize::MAX,
                self.graph().transitions.len() < usize::MAX,
        {
            verify::lemma_tests_weight_count(self.graph().tests);
            verify::lemma_regexes_weight_count(self.graph().regexes);
            verify::lemma_transitions_weight_count(self.graph().transitions);
        }

        /// Every native constant payload is a `u64`, including after graph extension.
        pub proof fn lemma_constant_bounds(&self)
            ensures forall|i: int| #![trigger self.graph().tests[i]]
                0 <= i < self.graph().tests.len() ==> match self.graph().tests[i] {
                model::TestNode::Atom(model::Primitive::Eq(_, model::GTerm::Constant(v)), _) => v <= u64::MAX,
                _ => true,
            },
        {
            match self.storage.tables {
                Some(t) => {
                    assert forall|i: int| #![trigger self.graph().tests[i]]
                        0 <= i < self.graph().tests.len() implies
                        match self.graph().tests[i] {
                            model::TestNode::Atom(model::Primitive::Eq(_, model::GTerm::Constant(v)), _) => v <= u64::MAX,
                            _ => true,
                        } by {
                        match t.tests@[i] {
                            TestNode::Atom { primitive, .. } => {
                                match primitive {
                                    Primitive::Eq { term: Term::Constant(value), .. } => {},
                                    _ => {},
                                }
                            },
                            _ => {},
                        }
                    }
                },
                None => {},
            }
        }
    }

    /// Creates the canonical graph with the runtime's budget, [`MAX_GRAPH_BYTES`], and its
    /// algebraic constants. Live production operations report graph/resource failures, never
    /// internal/owner errors.
    #[verus_spec(result => ensures match result {
        Ok(store) => model::graph_wf(store.graph()) && store.valid_store(),
        Err(error) => error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed,
    }, no_invariant_failure(result),
        result matches Err(error) ==> junco_core::spec::semantics::resource_error(error))]
    pub fn new() -> KernelResult<Self> {
        proof! {
            #[cfg(target_pointer_width = "64")]
            verify::lemma_production_layout();
        }
        Self::with_budget(ARENA_CAPACITY)
    }

    /// Creates a canonical graph that may be charged `budget` bytes, and its algebraic
    /// constants. Each of its six arenas holds `budget` bytes, so the charge rather than arena
    /// space bounds the graph. `budget` must be a multiple of every node alignment, as any
    /// multiple of 16 is; otherwise the arena layout check fails with an internal error.
    #[verus_spec(result => ensures match result {
        Ok(store) => model::graph_wf(store.graph()) && store.valid_store(),
        Err(error) => error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed
            || error is Invariant,
    }, verify::construction_layout(budget) ==> no_invariant_failure(result),
        verify::construction_layout(budget) ==>
            (result matches Err(error) ==> junco_core::spec::semantics::resource_error(error)))]
    pub fn with_budget(budget: usize) -> KernelResult<Self> {
        Self::from_storage(ArenaStorage::with_capacity(budget)?, budget)
    }

    #[verus_spec(result =>
        requires storage.tables is Some, verify::empty_tables(storage.graph()),
        ensures match result {
            Ok(store) => model::graph_wf(store.graph()) && store.valid_store(),
            Err(error) => error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed,
        },
        result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
    )]
    fn from_storage(storage: ArenaStorage, budget: usize) -> KernelResult<Self> {
        proof_decl! { let ghost initial_graph = storage.graph(); }
        let mut store = Self {
            storage,
            bytes: 0,
            budget,
            constants: Constants {
                test_true: TestId::ZERO,
                test_false: TestId::ZERO,
                empty: RegexId::ZERO,
                all: RegexId::ZERO,
                epsilon: RegexId::ZERO,
                transition_empty: TransitionId::ZERO,
                transition_all: TransitionId::ZERO,
                transition_epsilon: TransitionId::ZERO,
            },
        };
        proof! { assert(store.valid_store()); }
        proof! { verify::lemma_tables_wf_same_tables(initial_graph, store.graph()); }
        store.intern_constants()?;
        Ok(store)
    }

    verus! {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
    #[verus_spec(result =>
        requires old(self).valid_store(), verify::empty_tables(old(self).graph()),
            model::tables_wf(old(self).graph()),
        ensures final(self).valid_store(), match result {
            Ok(()) => model::graph_wf(final(self).graph()),
            Err(error) => error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed,
        },
        result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
    )]
    fn intern_constants(&mut self) -> KernelResult<()> {
        // Each interner preserves these predicates through its checked contract.
        // Unfold their quantified/recursive bodies only at the final constant update.
        hide(CanonicalStore::valid_store);
        hide(model::unique_nodes);
        hide(model::tables_wf);
        hide(verify::graph_weight);
        let test_true = self.intern_test(TestView::True)?;
        let test_false = self.intern_test(TestView::False)?;
        let empty = self.intern_regex(RegexKindView::Empty, false)?;
        let all = self.intern_regex(RegexKindView::All, true)?;
        let epsilon = self.intern_regex(RegexKindView::Epsilon, true)?;
        let transition_empty = self.intern_transition(TransitionView::Const(empty))?;
        let transition_all = self.intern_transition(TransitionView::Const(all))?;
        let transition_epsilon = self.intern_transition(TransitionView::Const(epsilon))?;
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
            assert(verify::graph_weight(self.graph()) == verify::graph_weight(built_graph)) by {
                reveal(verify::graph_weight);
            }
            assert(self.valid_store()) by {
                reveal(CanonicalStore::valid_store);
                reveal(model::unique_nodes);
            }
            assert(model::tables_wf(self.graph()));
            assert(model::constants_wf(self.graph()));
            assert(model::unique_nodes(self.graph())) by {
                reveal(CanonicalStore::valid_store);
            }
            model::lemma_graph_wf_intro(self.graph());
        }
        Ok(())
    }
    }

    #[verus_spec(result => ensures match result {
        Ok(total) => total as int == self.charged() as int + bytes as int
            && total as int <= self.budget() as int,
        Err(error) => error matches HistoryError::GraphBudget { limit } && limit as nat == self.budget()
            && self.charged() + bytes > self.budget(),
    }, result matches Err(error) ==> junco_core::spec::semantics::resource_error(error))]
    pub fn projected(&self, bytes: usize) -> KernelResult<usize> {
        let total = self
            .bytes
            .checked_add(bytes)
            .ok_or(HistoryError::GraphBudget { limit: self.budget })?;
        if total > self.budget {
            return Err(HistoryError::GraphBudget { limit: self.budget });
        }
        Ok(total)
    }
    #[verus_spec(result => ensures final(self).graph() == old(self).graph(),
        (final(self).bytes as nat) >= (old(self).bytes as nat),
        old(self).valid_store() ==> final(self).valid_store(),
        result matches Err(error) ==> error matches HistoryError::GraphBudget { limit } && limit as nat == old(self).budget()
            && old(self).charged() + bytes > old(self).budget())]
    pub(crate) fn charge(&mut self, bytes: usize) -> KernelResult<()> {
        self.bytes = self.projected(bytes)?;
        Ok(())
    }
    /// Raises the byte charge to a value previously obtained from `projected` on this store.
    /// The charge never decreases, so `graph_weight(graph) <= bytes` is preserved
    /// even if an intervening checkpoint or intern already charged more.
    #[allow(
        clippy::missing_const_for_fn,
        reason = "Keep the existing mutable operation and its Verus contract unchanged"
    )]
    #[verus_spec(
        ensures final(self).graph() == old(self).graph(),
            old(self).valid_store() ==> final(self).valid_store(),
            final(self).charged() >= old(self).charged(),
            final(self).charged() >= bytes as nat,
    )]
    pub fn set_charged_bytes(&mut self, bytes: usize) {
        if bytes > self.bytes {
            self.bytes = bytes;
        }
    }

    #[verus_spec(result => ensures result@ == self.graph().constants)]
    pub const fn constants(&self) -> Constants {
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
                Ok(id) => id@ < final(self).graph().tests.len()
                    && final(self).graph().tests[id@ as int] == node@,
                Err(_) => final(self).graph() == old(self).graph()
                    && (final(self).bytes as nat) == (old(self).bytes as nat),
            },
            result matches Err(error) ==> error is GraphBudget || error is GraphIndex
                || error is ArenaExhausted || error is AllocationFailed,
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            final(self).storage.capacity() == old(self).storage.capacity(),
            result is Ok ==> final(self).storage.slack() >= old(self).storage.slack(),
            result matches Err(error) ==> error is ArenaExhausted ==>
                old(self).storage.slack() < old(self).budget as int - old(self).storage.capacity(),
    )]
    pub(crate) fn intern_test(&mut self, node: TestView<'_>) -> KernelResult<TestId> {
        proof_decl! { let ghost original = self.graph(); }
        if let Some(id) = self.storage.find_test(node)? {
            return Ok(id);
        }
        let len = match node {
            TestView::And(ids) | TestView::Or(ids) => ids.len(),
            _ => 0,
        };
        let bytes = size_of::<TestNode>()
            .checked_add(sequence_bytes::<TestId>(len)?)
            .ok_or(HistoryError::GraphIndex)?;
        let projected = self.projected(bytes)?;
        proof! {
            assert(model::unique_nodes(original));
            assert(verify::graph_weight(self.storage.graph()) == verify::graph_weight(original));
            assert(bytes as int == verify::test_weight(node@));
            assert(verify::graph_weight(original) + verify::test_weight(node@) <= self.budget as int);
        }
        // Publish the charge only after storage succeeds; failed pushes leave accounting unchanged.
        let id = self.storage.push_test(node)?;
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
                Ok(id) => id@ < final(self).graph().regexes.len()
                    && final(self).graph().regexes[id@ as int] == (model::RegexNode { kind: kind@, nullable }),
                Err(_) => final(self).graph() == old(self).graph()
                    && (final(self).bytes as nat) == (old(self).bytes as nat),
            },
            result matches Err(error) ==> error is GraphBudget || error is GraphIndex
                || error is ArenaExhausted || error is AllocationFailed,
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            final(self).storage.capacity() == old(self).storage.capacity(),
            result is Ok ==> final(self).storage.slack() >= old(self).storage.slack(),
            result matches Err(error) ==> error is ArenaExhausted ==>
                old(self).storage.slack() < old(self).budget as int - old(self).storage.capacity(),
    )]
    pub(crate) fn intern_regex(
        &mut self,
        kind: RegexKindView<'_>,
        nullable: bool,
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
        let bytes = size_of::<RegexNode>()
            .checked_add(sequence_bytes::<RegexId>(len)?)
            .ok_or(HistoryError::GraphIndex)?;
        let projected = self.projected(bytes)?;
        proof! {
            assert(model::unique_nodes(original));
            assert(verify::graph_weight(self.storage.graph()) == verify::graph_weight(original));
            assert(bytes as int == verify::regex_weight(node@));
            assert(verify::graph_weight(original) + verify::regex_weight(node@) <= self.budget as int);
        }
        let id = self.storage.push_regex(node)?;
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
                Ok(id) => id@ < final(self).graph().transitions.len()
                    && final(self).graph().transitions[id@ as int] == node@,
                Err(_) => final(self).graph() == old(self).graph()
                    && (final(self).bytes as nat) == (old(self).bytes as nat),
            },
            result matches Err(error) ==> error is GraphBudget || error is GraphIndex
                || error is ArenaExhausted || error is AllocationFailed,
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            final(self).storage.capacity() == old(self).storage.capacity(),
            result is Ok ==> final(self).storage.slack() >= old(self).storage.slack(),
            result matches Err(error) ==> error is ArenaExhausted ==>
                old(self).storage.slack() < old(self).budget as int - old(self).storage.capacity(),
    )]
    pub(crate) fn intern_transition(
        &mut self,
        node: TransitionView<'_>,
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
        let bytes = size_of::<TransitionNode>()
            .checked_add(children)
            .ok_or(HistoryError::GraphIndex)?;
        let projected = self.projected(bytes)?;
        proof! {
            assert(model::unique_nodes(original));
            assert(verify::graph_weight(self.storage.graph()) == verify::graph_weight(original));
            assert(bytes as int == verify::transition_weight(node@));
            assert(verify::graph_weight(original) + verify::transition_weight(node@) <= self.budget as int);
        }
        let id = self.storage.push_transition(node)?;
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

#[cfg(any(test, feature = "test-util"))]
impl CanonicalStore {
    pub fn replace_graph_byte_pressure(&mut self, bytes: usize) -> usize {
        core::mem::replace(&mut self.bytes, bytes)
    }

    pub fn charged_bytes(&self) -> usize {
        self.bytes
    }
}

#[cfg(any(test, feature = "test-util"))]
impl CanonicalStore {
    pub fn table_counts(&self) -> Option<(usize, usize)> {
        self.storage
            .tables
            .as_ref()
            .map(|tables| (tables.test_ids.slices.len(), tables.tests.len()))
    }
}
#[verus_verify]
pub struct RuntimeKernel<'a, L: Limits> {
    pub store: &'a mut CanonicalStore,
    pub limits: &'a mut L,
    pub world: &'a mut ObservationWorld,
}
#[verus_verify]
impl<L: Limits> KernelStore for RuntimeKernel<'_, L> {
    #[verus_spec(result => ensures result matches Err(error) ==> error is Limit)]
    fn checkpoint(&mut self) -> KernelResult<()> {
        self.limits.checkpoint()?;
        Ok(())
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Limit || error is GraphBudget || error is GraphIndex)]
    fn charge_aux(&mut self, bytes: usize) -> KernelResult<()> {
        self.checkpoint()?;
        self.store.charge(bytes)
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is AllocationFailed)]
    fn reserve_derivatives(
        &mut self,
        values: &mut Vec<Option<TransitionId>>,
        additional: usize,
    ) -> KernelResult<()> {
        allocation(self.world.try_reserve_vec(values, additional))
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is AllocationFailed)]
    fn reserve_atoms(&mut self, values: &mut Vec<TestId>, additional: usize) -> KernelResult<()> {
        allocation(self.world.try_reserve_vec(values, additional))
    }
    fn constants(&self) -> Constants {
        self.store.constants()
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Invariant)]
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>> {
        self.store.storage.test(id)
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Invariant)]
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>> {
        self.store.storage.regex(id)
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Invariant)]
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>> {
        self.store.storage.transition(id)
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Limit
        || error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed)]
    fn intern_test(&mut self, node: TestView<'_>) -> KernelResult<TestId> {
        self.checkpoint()?;
        let id = self.store.intern_test(node)?;
        self.checkpoint()?;
        Ok(id)
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Limit
        || error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed)]
    fn intern_regex(&mut self, kind: RegexKindView<'_>, nullable: bool) -> KernelResult<RegexId> {
        self.checkpoint()?;
        let id = self.store.intern_regex(kind, nullable)?;
        self.checkpoint()?;
        Ok(id)
    }
    #[verus_spec(result => ensures result matches Err(error) ==> error is Limit
        || error is GraphBudget || error is GraphIndex || error is ArenaExhausted || error is AllocationFailed)]
    fn intern_transition(&mut self, node: TransitionView<'_>) -> KernelResult<TransitionId> {
        self.checkpoint()?;
        let id = self.store.intern_transition(node)?;
        self.checkpoint()?;
        Ok(id)
    }
}

#[cfg(test)]
mod storage_tests {
    #![allow(clippy::panic_in_result_fn)]
    use super::*;

    #[test]
    fn atom_key_equality_preserves_full_width_and_domains() {
        use history_syntax::syntax::Component;

        let fixtures = [
            (Component(0), Term::Constant(0), true),
            (Component(0), Term::Constant(1_u64 << 32), true),
            (Component(0), Term::Constant(u64::MAX), true),
            (Component(1), Term::Constant(0), true),
            (Component(2), Term::Constant(0), true),
            (Component(0), Term::Variable(Component(0)), true),
            (Component(0), Term::Variable(Component(1)), true),
            (Component(0), Term::Variable(Component(2)), true),
            (Component(0), Term::Constant(0), false),
        ]
        .map(|(field, term, positive)| TestNode::Atom {
            primitive: Primitive::Eq { field, term },
            positive,
        });
        for (i, left) in fixtures.iter().enumerate() {
            for (j, right) in fixtures.iter().enumerate() {
                assert_eq!(hashconsius::HashKey::key_eq(left, right), i == j);
            }
        }
    }

    fn tracked_store(
        counts: &alloc::sync::Arc<ArenaLifetimeCounts>,
    ) -> KernelResult<CanonicalStore> {
        let mut storage = ArenaStorage::with_capacity(512)?;
        storage.track_lifetime(alloc::sync::Arc::clone(counts))?;
        CanonicalStore::from_storage(storage, MAX_GRAPH_BYTES)
    }

    #[test]
    fn pinned_graph_survives_replacement_and_frees_only_at_last_arc() -> KernelResult<()> {
        use alloc::sync::Arc;

        let counts = Arc::new(ArenaLifetimeCounts::default());
        let mut current = Arc::new(tracked_store(&counts)?);
        let pinned = Arc::clone(&current);
        assert_eq!(counts.snapshot(), (6, 0));

        for generation in 2_usize..=33 {
            current = Arc::new(tracked_store(&counts)?);
            assert_eq!(
                counts.snapshot(),
                (
                    generation.saturating_mul(6),
                    generation.saturating_sub(2).saturating_mul(6)
                )
            );
        }
        drop(current);
        assert_eq!(counts.snapshot(), (198, 192));
        assert!(pinned.storage.regex(pinned.constants().all)?.nullable);
        drop(pinned);
        assert_eq!(counts.snapshot(), (198, 198));
        Ok(())
    }

    #[test]
    fn failed_store_construction_frees_owned_arenas() -> KernelResult<()> {
        use alloc::sync::Arc;

        let counts = Arc::new(ArenaLifetimeCounts::default());
        let mut storage = ArenaStorage::with_capacity(CHUNK_ALIGN)?;
        storage.track_lifetime(Arc::clone(&counts))?;
        assert!(matches!(
            CanonicalStore::from_storage(storage, MAX_GRAPH_BYTES),
            Err(HistoryError::ArenaExhausted)
        ));
        assert_eq!(counts.snapshot(), (6, 6));
        Ok(())
    }

    #[test]
    fn budget_equality_is_allowed_and_failed_growth_is_transactional() -> KernelResult<()> {
        let mut store = CanonicalStore::new()?;
        let payload = size_of::<TestNode>();
        store.bytes = MAX_GRAPH_BYTES
            .checked_sub(payload)
            .ok_or_else(|| HistoryError::invariant("invalid test budget"))?;
        let node = TestView::Atom {
            primitive: Primitive::Eq {
                field: history_syntax::syntax::Component(0),
                term: Term::Constant(0),
            },
            positive: true,
        };
        let id = store.intern_test(node)?;
        assert_eq!(store.bytes, MAX_GRAPH_BYTES);
        assert_eq!(store.intern_test(node)?, id);
        let rows = store.storage.lengths();
        let failed = store.intern_test(TestView::Atom {
            primitive: Primitive::Eq {
                field: history_syntax::syntax::Component(0),
                term: Term::Constant(1),
            },
            positive: true,
        });
        assert!(matches!(
            failed,
            Err(HistoryError::GraphBudget {
                limit: MAX_GRAPH_BYTES
            })
        ));
        assert_eq!(store.bytes, MAX_GRAPH_BYTES);
        assert_eq!(store.storage.lengths(), rows);
        Ok(())
    }

    #[test]
    fn a_store_enforces_its_own_budget() -> KernelResult<()> {
        let atom = |constant| TestView::Atom {
            primitive: Primitive::Eq {
                field: history_syntax::syntax::Component(0),
                term: Term::Constant(constant),
            },
            positive: true,
        };
        let budget = 2 * MAX_GRAPH_BYTES;
        let mut store = CanonicalStore::with_budget(budget)?;
        // Past the runtime's budget, within this store's.
        store.bytes = MAX_GRAPH_BYTES;
        store.intern_test(atom(0))?;
        store.bytes = budget;
        assert!(matches!(
            store.intern_test(atom(1)),
            Err(HistoryError::GraphBudget { limit }) if limit == budget
        ));
        assert!(CanonicalStore::with_budget(MAX_GRAPH_BYTES + 1).is_err());
        Ok(())
    }

    #[test]
    fn arena_allocation_failure_does_not_publish_or_charge() -> KernelResult<()> {
        let mut store =
            CanonicalStore::from_storage(ArenaStorage::with_capacity(512)?, MAX_GRAPH_BYTES)?;
        for path in 0_u32..u32::MAX {
            let before = (store.bytes, store.storage.lengths());
            match store.intern_test(TestView::Atom {
                primitive: Primitive::Eq {
                    field: history_syntax::syntax::Component(0),
                    term: Term::Constant(u64::from(path)),
                },
                positive: true,
            }) {
                Ok(_) => {}
                Err(HistoryError::ArenaExhausted) => {
                    assert_eq!((store.bytes, store.storage.lengths()), before);
                    let constant = store.intern_test(TestView::True);
                    let expected = store.constants().test_true;
                    assert_eq!(constant?, expected);
                    return Ok(());
                }
                Err(error) => return Err(error),
            }
        }
        Err(HistoryError::invariant("512-byte arena did not exhaust"))
    }

    #[test]
    fn arena_round_trips_child_slices() -> KernelResult<()> {
        let mut store = CanonicalStore::new()?;
        let outcome = (|| -> KernelResult<_> {
            let a = store.intern_test(TestView::Atom {
                primitive: Primitive::Eq {
                    field: history_syntax::syntax::Component(0),
                    term: Term::Constant(1),
                },
                positive: true,
            })?;
            let b = store.intern_test(TestView::Atom {
                primitive: Primitive::Eq {
                    field: history_syntax::syntax::Component(0),
                    term: Term::Constant(2),
                },
                positive: true,
            })?;
            let and = store.intern_test(TestView::And(&[a, b]))?;
            let r = store.intern_regex(RegexKindView::Test(a), false)?;
            let epsilon = store.constants().epsilon;
            let union = store.intern_regex(RegexKindView::Union(&[r, epsilon]), true)?;
            let transition_epsilon = store.constants().transition_epsilon;
            let append = TransitionView::Append {
                transition: transition_epsilon,
                suffix: &[r],
            };
            let t = store.intern_transition(append)?;
            assert_eq!(store.storage.test(and)?, TestView::And(&[a, b]));
            assert_eq!(
                store.storage.regex(union)?.kind,
                RegexKindView::Union(&[r, epsilon])
            );
            assert_eq!(store.storage.transition(t)?, append);
            assert_eq!(store.intern_test(TestView::And(&[a, b]))?, and);
            assert_eq!(
                store.intern_regex(RegexKindView::Union(&[r, epsilon]), true)?,
                union
            );
            assert_eq!(store.intern_transition(append)?, t);
            Ok(())
        })();
        outcome?;
        Ok(())
    }
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    use junco_core::kernel::verify as model;

    verus! {

                pub open spec fn storage_constants() -> model::ConstantsModel {
                    model::ConstantsModel {
                        test_true: 0, test_false: 0, empty: 0, all: 0, epsilon: 0,
                        transition_empty: 0, transition_all: 0, transition_epsilon: 0,
                    }
                }


    pub(super) open spec fn arena_test_node(node: TestNode, pools: Seq<Seq<TestId>>) -> model::TestNode {
        match node {
            TestNode::True => model::TestNode::True,
            TestNode::False => model::TestNode::False,
            TestNode::Atom { primitive, positive } => model::TestNode::Atom(primitive@, positive),
            TestNode::And(slot) => model::TestNode::And(model::test_ids(pools[slot as int])),
            TestNode::Or(slot) => model::TestNode::Or(model::test_ids(pools[slot as int])),
        }
    }
    pub(super) open spec fn arena_regex_node(node: RegexNode, pools: Seq<Seq<RegexId>>) -> model::RegexNode {
        model::RegexNode {
            nullable: node.nullable,
            kind: match node.kind {
                RegexKind::Empty => model::RegexKindNode::Empty,
                RegexKind::All => model::RegexKindNode::All,
                RegexKind::Epsilon => model::RegexKindNode::Epsilon,
                RegexKind::Test(id) => model::RegexKindNode::Test(id@),
                RegexKind::Union(slot) => model::RegexKindNode::Union(model::regex_ids(pools[slot as int])),
                RegexKind::Concat(slot) => model::RegexKindNode::Concat(model::regex_ids(pools[slot as int])),
                RegexKind::Star(id) => model::RegexKindNode::Star(id@),
                RegexKind::Intersect(slot) => model::RegexKindNode::Intersect(model::regex_ids(pools[slot as int])),
                RegexKind::Not(id) => model::RegexKindNode::Not(id@),
            },
        }
    }
    pub(super) open spec fn arena_transition_node(node: TransitionNode, ids: Seq<Seq<TransitionId>>, regex_pools: Seq<Seq<RegexId>>) -> model::TransitionNode {
        match node {
            TransitionNode::Const(id) => model::TransitionNode::Const(id@),
            TransitionNode::If { test, then_transition, else_transition } => model::TransitionNode::If(test@, then_transition@, else_transition@),
            TransitionNode::Union(slot) => model::TransitionNode::Union(model::transition_ids(ids[slot as int])),
            TransitionNode::Intersect(slot) => model::TransitionNode::Intersect(model::transition_ids(ids[slot as int])),
            TransitionNode::Not(id) => model::TransitionNode::Not(id@),
            TransitionNode::Append { transition, suffix } => model::TransitionNode::Append(transition@, model::regex_ids(regex_pools[suffix as int])),
        }
    }
    pub(super) open spec fn arena_test_wf(t: &ArenaTables, node: TestNode) -> bool {
        match node {
            TestNode::And(slot) | TestNode::Or(slot) => slot < t.test_ids@.len(),
            _ => true,
        }
    }
    pub(super) open spec fn arena_regex_wf(t: &ArenaTables, node: RegexNode) -> bool {
        match node.kind {
            RegexKind::Union(slot) | RegexKind::Concat(slot) | RegexKind::Intersect(slot) =>
                slot < t.regex_ids@.len(),
            _ => true,
        }
    }
    pub(super) open spec fn arena_transition_wf(t: &ArenaTables, node: TransitionNode) -> bool {
        match node {
            TransitionNode::Union(slot) | TransitionNode::Intersect(slot) => slot < t.transition_ids@.len(),
            TransitionNode::Append { suffix, .. } => suffix < t.regex_ids@.len(),
            _ => true,
        }
    }
    proof fn lemma_pool_slot_eq<T>(pool: Seq<Seq<T>>, a: usize, b: usize)
        requires pool.no_duplicates(), a < pool.len(), b < pool.len(),
        ensures (a == b) == (pool[a as int] == pool[b as int]),
    {}
    pub(super) proof fn lemma_test_id_eq(a: TestId, b: TestId)
        ensures (a == b) == (a@ == b@),
    {
        model::lemma_test_ids_eq(seq![a], seq![b]);
        assert(model::test_ids(seq![a]) =~= seq![a@]);
        assert(model::test_ids(seq![b]) =~= seq![b@]);
        if a@ == b@ {
            assert(model::test_ids(seq![a]) == model::test_ids(seq![b]));
            assert(seq![a] == seq![b]);
            assert(seq![a][0] == seq![b][0]);
            assert(a == b);
        }
    }
    pub(super) proof fn lemma_regex_id_eq(a: RegexId, b: RegexId)
        ensures (a == b) == (a@ == b@),
    {
        model::lemma_regex_ids_eq(seq![a], seq![b]);
        assert(model::regex_ids(seq![a]) =~= seq![a@]);
        assert(model::regex_ids(seq![b]) =~= seq![b@]);
        if a@ == b@ {
            assert(model::regex_ids(seq![a]) == model::regex_ids(seq![b]));
            assert(seq![a] == seq![b]);
            assert(seq![a][0] == seq![b][0]);
            assert(a == b);
        }
    }
    pub(super) proof fn lemma_transition_id_eq(a: TransitionId, b: TransitionId)
        ensures (a == b) == (a@ == b@),
    {
        model::lemma_transition_ids_eq(seq![a], seq![b]);
        assert(model::transition_ids(seq![a]) =~= seq![a@]);
        assert(model::transition_ids(seq![b]) =~= seq![b@]);
        if a@ == b@ {
            assert(model::transition_ids(seq![a]) == model::transition_ids(seq![b]));
            assert(seq![a] == seq![b]);
            assert(seq![a][0] == seq![b][0]);
            assert(a == b);
        }
    }
    proof fn lemma_primitive_eq(a: Primitive, b: Primitive)
        ensures (a == b) == (a@ == b@),
    {
        match (a, b) {
            (Primitive::Eq { term: x, .. }, Primitive::Eq { term: y, .. }) => {
                match (x, y) {
                    (junco_core::kernel::Term::Constant(_), junco_core::kernel::Term::Constant(_)) => {},
                    (junco_core::kernel::Term::Variable(_), junco_core::kernel::Term::Variable(_)) => {},
                    _ => {},
                }
            },
        }
    }
    pub(super) proof fn lemma_arena_test_eq_iff_node_eq(t: &ArenaTables, a: TestNode, b: TestNode)
        requires tables_index_wf(t), arena_test_wf(t, a), arena_test_wf(t, b),
        ensures (a == b) == (arena_test_node(a, t.test_ids@) == arena_test_node(b, t.test_ids@)),
    {
        match (a, b) {
            (TestNode::And(x), TestNode::And(y)) | (TestNode::Or(x), TestNode::Or(y)) => {
                model::lemma_test_ids_eq(t.test_ids@[x as int], t.test_ids@[y as int]);
                lemma_pool_slot_eq(t.test_ids@, x, y);
            },
            (TestNode::Atom { primitive: x, .. }, TestNode::Atom { primitive: y, .. }) => {
                lemma_primitive_eq(x, y);
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_arena_regex_eq_iff_node_eq(t: &ArenaTables, a: RegexNode, b: RegexNode)
        requires tables_index_wf(t), arena_regex_wf(t, a), arena_regex_wf(t, b),
        ensures (a == b) == (arena_regex_node(a, t.regex_ids@) == arena_regex_node(b, t.regex_ids@)),
    {
        match (a.kind, b.kind) {
            (RegexKind::Union(x), RegexKind::Union(y))
            | (RegexKind::Concat(x), RegexKind::Concat(y))
            | (RegexKind::Intersect(x), RegexKind::Intersect(y)) => {
                model::lemma_regex_ids_eq(t.regex_ids@[x as int], t.regex_ids@[y as int]);
                lemma_pool_slot_eq(t.regex_ids@, x, y);
            },
            (RegexKind::Test(x), RegexKind::Test(y)) => {
                lemma_test_id_eq(x, y);
            },
            (RegexKind::Star(x), RegexKind::Star(y))
            | (RegexKind::Not(x), RegexKind::Not(y)) => {
                lemma_regex_id_eq(x, y);
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_arena_transition_eq_iff_node_eq(t: &ArenaTables, a: TransitionNode, b: TransitionNode)
        requires tables_index_wf(t), arena_transition_wf(t, a), arena_transition_wf(t, b),
        ensures (a == b) == (arena_transition_node(a, t.transition_ids@, t.regex_ids@)
            == arena_transition_node(b, t.transition_ids@, t.regex_ids@)),
    {
        match (a, b) {
            (TransitionNode::Union(x), TransitionNode::Union(y))
            | (TransitionNode::Intersect(x), TransitionNode::Intersect(y)) => {
                model::lemma_transition_ids_eq(t.transition_ids@[x as int], t.transition_ids@[y as int]);
                lemma_pool_slot_eq(t.transition_ids@, x, y);
            },
            (TransitionNode::Append { transition: a, suffix: x }, TransitionNode::Append { transition: b, suffix: y }) => {
                lemma_transition_id_eq(a, b);
                model::lemma_regex_ids_eq(t.regex_ids@[x as int], t.regex_ids@[y as int]);
                lemma_pool_slot_eq(t.regex_ids@, x, y);
            },
            (TransitionNode::Const(x), TransitionNode::Const(y)) => {
                lemma_regex_id_eq(x, y);
            },
            (TransitionNode::If { test: t, then_transition: a, else_transition: b },
                TransitionNode::If { test: u, then_transition: c, else_transition: d }) => {
                lemma_test_id_eq(t, u);
                lemma_transition_id_eq(a, c);
                lemma_transition_id_eq(b, d);
            },
            (TransitionNode::Not(x), TransitionNode::Not(y)) => {
                lemma_transition_id_eq(x, y);
            },
            _ => {},
        }
    }
    pub(super) proof fn lemma_test_contains(t: &ArenaTables, node: TestNode)
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
    pub(super) proof fn lemma_regex_contains(t: &ArenaTables, node: RegexNode)
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
    pub(super) proof fn lemma_transition_contains(t: &ArenaTables, node: TransitionNode)
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
                TestNode::And(slot) | TestNode::Or(slot) => {
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
                RegexKind::Union(slot) | RegexKind::Concat(slot) | RegexKind::Intersect(slot) => {
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
                TransitionNode::Union(slot) | TransitionNode::Intersect(slot) => {
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
                TransitionNode::Append { suffix, .. } => {
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
            TestNode::And(slot) | TestNode::Or(slot) => slot < t.test_ids@.len(),
            _ => true,
        }
        &&& forall|i: int| 0 <= i < t.regexes@.len() ==> match (#[trigger] t.regexes@[i]).kind {
            RegexKind::Union(slot) | RegexKind::Concat(slot) | RegexKind::Intersect(slot) => slot < t.regex_ids@.len(),
            _ => true,
        }
        &&& forall|i: int| 0 <= i < t.transitions@.len() ==> match #[trigger] t.transitions@[i] {
            TransitionNode::Union(slot) | TransitionNode::Intersect(slot) => slot < t.transition_ids@.len(),
            TransitionNode::Append { transition, suffix } => suffix < t.regex_ids@.len(),
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
    // push and is 0 for a fresh store, so exhaustion before `GraphBudget` is impossible.

    pub open spec fn mul_bytes(count: nat, size: nat) -> nat { count * size }
    pub proof fn lemma_mul_bytes_succ(count: nat, size: nat)
        ensures mul_bytes(count + 1, size) == mul_bytes(count, size) + size,
    {
        assert((count + 1) * size == count * size + size) by (nonlinear_arith);
    }

    pub open(super) spec fn test_weight(n: model::TestNode) -> nat {
        vstd::layout::size_of::<TestNode>() + match n {
            model::TestNode::And(ids) | model::TestNode::Or(ids) => mul_bytes(ids.len(), vstd::layout::size_of::<TestId>()),
            _ => 0,
        }
    }
    pub open(super) spec fn regex_weight(n: model::RegexNode) -> nat {
        vstd::layout::size_of::<RegexNode>() + match n.kind {
            model::RegexKindNode::Union(ids) | model::RegexKindNode::Concat(ids) | model::RegexKindNode::Intersect(ids) =>
                mul_bytes(ids.len(), vstd::layout::size_of::<RegexId>()),
            _ => 0,
        }
    }
    pub open(super) spec fn transition_weight(n: model::TransitionNode) -> nat {
        vstd::layout::size_of::<TransitionNode>() + match n {
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

    #[cfg(target_pointer_width = "64")]
    pub(super) proof fn lemma_tests_weight_count(s: Seq<model::TestNode>)
        ensures 32 * s.len() <= tests_weight(s),
        decreases s.len(),
    {
        broadcast use super::VERUS_layout_of_TestNode;
        if s.len() > 0 {
            lemma_tests_weight_count(s.drop_last());
            assert(s.drop_last().len() + 1 == s.len());
            assert(test_weight(s.last()) >= 32);
        }
    }

    #[cfg(target_pointer_width = "64")]
    pub(super) proof fn lemma_regexes_weight_count(s: Seq<model::RegexNode>)
        ensures 24 * s.len() <= regexes_weight(s),
        decreases s.len(),
    {
        broadcast use super::VERUS_layout_of_RegexNode;
        if s.len() > 0 {
            lemma_regexes_weight_count(s.drop_last());
            assert(s.drop_last().len() + 1 == s.len());
            assert(regex_weight(s.last()) >= 24);
        }
    }

    #[cfg(target_pointer_width = "64")]
    pub(super) proof fn lemma_transitions_weight_count(s: Seq<model::TransitionNode>)
        ensures 16 * s.len() <= transitions_weight(s),
        decreases s.len(),
    {
        broadcast use super::VERUS_layout_of_TransitionNode;
        if s.len() > 0 {
            lemma_transitions_weight_count(s.drop_last());
            assert(s.drop_last().len() + 1 == s.len());
            assert(transition_weight(s.last()) >= 16);
        }
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

    /// Exact native layout premises checked before allocating any of the six arenas.
    pub open(crate) spec fn construction_layout(capacity: usize) -> bool {
        &&& vstd::layout::size_of::<TestNode>() > 0
        &&& vstd::layout::size_of::<RegexNode>() > 0
        &&& vstd::layout::size_of::<TransitionNode>() > 0
        &&& vstd::layout::align_of::<TestNode>() <= CHUNK_ALIGN
        &&& vstd::layout::align_of::<RegexNode>() <= CHUNK_ALIGN
        &&& vstd::layout::align_of::<TransitionNode>() <= CHUNK_ALIGN
        &&& vstd::layout::align_of::<TestId>() <= CHUNK_ALIGN
        &&& vstd::layout::align_of::<RegexId>() <= CHUNK_ALIGN
        &&& vstd::layout::align_of::<TransitionId>() <= CHUNK_ALIGN
        &&& capacity as int % vstd::layout::align_of::<TestNode>() as int == 0
        &&& capacity as int % vstd::layout::align_of::<RegexNode>() as int == 0
        &&& capacity as int % vstd::layout::align_of::<TransitionNode>() as int == 0
        &&& capacity as int % vstd::layout::align_of::<TestId>() as int == 0
        &&& capacity as int % vstd::layout::align_of::<RegexId>() as int == 0
        &&& capacity as int % vstd::layout::align_of::<TransitionId>() as int == 0
    }

    /// Every 16-byte-aligned budget satisfies the native arena layout checks on the pinned
    /// 64-bit verification target. Small budgets may still report graph/resource exhaustion.
    #[cfg(target_pointer_width = "64")]
    pub proof fn lemma_aligned_budget_layout(capacity: usize)
        requires capacity as int % 16 == 0,
        ensures construction_layout(capacity),
    {
        // Activate the existing global-layout directives' generated theorems locally.
        broadcast use {
            super::VERUS_layout_of_TestNode,
            super::VERUS_layout_of_RegexNode,
            super::VERUS_layout_of_TransitionNode,
            super::VERUS_layout_of_TestId,
            super::VERUS_layout_of_RegexId,
            super::VERUS_layout_of_TransitionId,
        };
        assert(vstd::layout::size_of::<TestNode>() == 32);
        assert(vstd::layout::size_of::<RegexNode>() == 24);
        assert(vstd::layout::size_of::<TransitionNode>() == 16);
        assert(vstd::layout::align_of::<TestNode>() == 8);
        assert(vstd::layout::align_of::<RegexNode>() == 8);
        assert(vstd::layout::align_of::<TransitionNode>() == 8);
        assert(vstd::layout::align_of::<TestId>() == 4);
        assert(vstd::layout::align_of::<RegexId>() == 4);
        assert(vstd::layout::align_of::<TransitionId>() == 4);
        assert(CHUNK_ALIGN == 16) by (compute);
        assert(capacity as int % 8 == 0 && capacity as int % 4 == 0);
    }

    #[cfg(target_pointer_width = "64")]
    pub(super) proof fn lemma_production_layout()
        ensures construction_layout(ARENA_CAPACITY),
    {
        assert(ARENA_CAPACITY == 102400) by (compute);
        assert(102400int % 16 == 0) by (compute);
        lemma_aligned_budget_layout(ARENA_CAPACITY);
    }

    pub(super) open spec fn layout_premises() -> bool {
        &&& vstd::layout::size_of::<TestNode>() > 0
        &&& vstd::layout::size_of::<RegexNode>() > 0
        &&& vstd::layout::size_of::<TransitionNode>() > 0
    }
    pub(super) open spec fn arena_live(t: &ArenaTables) -> nat {
        mul_bytes(t.tests@.len(), vstd::layout::size_of::<TestNode>())
            + mul_bytes(t.regexes@.len(), vstd::layout::size_of::<RegexNode>())
            + mul_bytes(t.transitions@.len(), vstd::layout::size_of::<TransitionNode>())
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
        &&& t.tests.remaining() == cap - mul_bytes(t.tests@.len(), vstd::layout::size_of::<TestNode>())
        &&& t.regexes.remaining() == cap - mul_bytes(t.regexes@.len(), vstd::layout::size_of::<RegexNode>())
        &&& t.transitions.remaining() == cap - mul_bytes(t.transitions@.len(), vstd::layout::size_of::<TransitionNode>())
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
            t.tests@ == Seq::<TestNode>::empty(), t.regexes@ == Seq::<RegexNode>::empty(),
            t.transitions@ == Seq::<TransitionNode>::empty(),
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
                TestNode::And(slot) | TestNode::Or(slot) => {
                    assert(before.test_ids@[slot as int] == after.test_ids@[slot as int]);
                },
                _ => {},
            }
        }
        assert forall|i: int| 0 <= i < before.regexes@.len() implies
            arena_regex_node(before.regexes@[i], before.regex_ids@) ==
            arena_regex_node(after.regexes@[i], after.regex_ids@) by {
            match before.regexes@[i].kind {
                RegexKind::Union(slot) | RegexKind::Concat(slot) | RegexKind::Intersect(slot) => {
                    assert(before.regex_ids@[slot as int] == after.regex_ids@[slot as int]);
                },
                _ => {},
            }
        }
        assert forall|i: int| 0 <= i < before.transitions@.len() implies
            arena_transition_node(before.transitions@[i], before.transition_ids@, before.regex_ids@) ==
            arena_transition_node(after.transitions@[i], after.transition_ids@, after.regex_ids@) by {
            match before.transitions@[i] {
                TransitionNode::Union(slot) | TransitionNode::Intersect(slot) => {
                    assert(before.transition_ids@[slot as int] == after.transition_ids@[slot as int]);
                },
                TransitionNode::Append { transition, suffix } => {
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
    impl ArenaStorage {
        pub(crate) open(super) spec fn graph(&self) -> model::Graph {
            match self.tables {
                Some(t) => tables_graph(&t),
                None => model::Graph {
                    tests: Seq::empty(), regexes: Seq::empty(), transitions: Seq::empty(),
                    constants: storage_constants(),
                },
            }
        }
        pub(crate) open(super) spec fn capacity(&self) -> int {
            match self.tables { Some(t) => tables_capacity(&t), None => 0 }
        }
        pub(crate) open(super) spec fn slack(&self) -> int {
            match self.tables { Some(t) => tables_slack(&t), None => 0 }
        }
    }

                impl CanonicalStore {
                    pub open(super) spec fn graph(&self) -> model::Graph {
                        model::Graph { constants: self.constants@, ..self.storage.graph() }
                    }
                    pub open(super) spec fn valid_store(&self) -> bool {
                        let g = self.graph();
                        self.storage.tables is Some
                            && model::unique_nodes(g) && graph_weight(g) <= (self.bytes as nat)
                    }
                }

                impl<L: Limits> junco_core::verify::history_assumptions::KernelStoreSpec for RuntimeKernel<'_, L> {
                    open spec fn graph(&self) -> model::Graph { self.store.graph() }
                    open spec fn valid_store(&self) -> bool { self.store.valid_store() }
                    open spec fn errors_are_non_owner(&self) -> bool { true }
                    open spec fn errors_are_non_invariant(&self) -> bool { true }
                    open spec fn errors_are_non_invalid_policy(&self) -> bool { true }
                    open spec fn errors_are_resource(&self) -> bool { true }
                    #[verifier::prophetic]
                    open spec fn restoration(&self) -> (model::Graph, bool) {
                        let restored = mut_ref_future(self.store);
                        (restored.graph(), restored.valid_store())
                    }
                }



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

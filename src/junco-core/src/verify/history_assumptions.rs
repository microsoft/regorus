// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Trusted native boundary for history correctness.
//!
//! Allowed leaves: reservation adapters;
//! exact SmallVec sequence operations; concrete successor-cache wrappers
//! (including their opaque default hasher type); the exact native Iterator::position
//! selector for retained cursor keys (the pinned vstd lacks its specification);
//! sort_unstable, dedup and strictly-sorted binary_search, each requiring vstd's
//! `obeys_cmp`/`obeys_eq` laws (a total order, an equivalence) of the element type.
//!
//! Reservations preserve logical contents on success and failure. Cache contracts
//! permit eviction, never a fabricated entry. Event coordinates and bindings are
//! fixed u64 identities; classification needs no Value or path-selection assumptions.
//! hashconsius/verus-bumpalo pointer tables and hash buckets grow with infallible
//! alloc::vec::Vec (OOM aborts; bounded by MAX_GRAPH_BYTES per store); their
//! contracts are verified in the pinned revisions. The native ArenaStorage Drop
//! adapter takes its owned tables and calls verified ArenaTables::release;
//! implicit destructor invocation is outside the Verus model.
//! Native allocator Send/Sync markers rely on exclusive chunk ownership,
//! immutable shared access, and the corresponding element-type bounds outside SMT.
//! History owners isolate borrowed UTF-8 operations, const/static installation and
//! reference identity, mutex callbacks, and Arc/record mechanics in native leaves.
//! Coordinate, history-key and store-ID transitions check successor arithmetic,
//! key absence, exact authority insertion, and consumed-ID failure behavior.
//! Retained persistent receipts prove issuer and independent-owner separation;
//! exclusive registry births and receipt agreement prove foreign checkpoint rejection.
//! Byte interner insertion/rollback and typed history mutation have checked bodies.
//! Full byte-record mutation/read refinement remains a native boundary.
//! Ordered policy/validator construction, selection and transactions are checked;
//! field unpacking and context/diagnostic invocation remain native callback leaves.
//! ArenaStorage inherent operation and KernelStore trait contracts are implemented
//! by verified bodies, not trusted implementations. No compiler, normalizer, derivative,
//! interpreter, matcher, replay, or evaluator may be external_body or assume_specification.

use crate::kernel::verify::Graph;
use crate::observation::{ObservationWorld, SmallVecSpecFns};
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::{alloc::Allocator, ops::Deref};
use smallvec::SmallVec;
use vstd::laws_cmp::obeys_cmp;
use vstd::laws_eq::obeys_eq;
use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec};

verus! {
// Identity fidelity. Verus erases `Arc<T>` and `&T` to `T` in spec (vstd's `Arc::new` ensures
// `*v == t`; `*a == *b` proves `a == b`), so both functions below depend only on the pointee's
// value: two distinct allocations with equal contents would have equal identities while
// `Arc::ptr_eq`/`core::ptr::eq` say they differ. The external_body wrappers that equate the two
// (`share_store`, `borrow_store`, `share_numeric_owner`, `borrow_numeric_owner`,
// `same_numeric_reference`, `CompiledRule::same_owner`) are faithful because every compared type
// has a unique-per-allocation value: `HistoryStore` is constructed only by `HistoryStore::new`,
// one static singleton per arity, and stores of different arity differ in `domains@.len()`;
// `Store<E>` is constructed only by `Store::new`, whose `id` comes from the verified never-recycled
// store-id allocator, and neither type is `Clone`. Keep both facts when adding constructors.
pub uninterp spec fn arc_identity<T>(arc: Arc<T>) -> vstd::resource::Loc;
pub uninterp spec fn reference_identity<T>(value: &T) -> vstd::resource::Loc;


pub assume_specification[ alloc::string::String::try_reserve ](
    value: &mut alloc::string::String, additional: usize,
) -> Result<(), alloc::collections::TryReserveError>
    ensures final(value)@ == old(value)@;




pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::new ]() -> (v: SmallVec<A>)
    ensures v.view() == Seq::<A::Item>::empty();

pub open spec fn spec_smallvec_len<A: smallvec::Array>(v: &SmallVec<A>) -> usize {
    v.view().len() as usize
}

#[verifier::when_used_as_spec(spec_smallvec_len)]
pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::len ](v: &SmallVec<A>)
    -> (n: usize)
    ensures n == v.view().len(), n == spec_smallvec_len(v);

pub open spec fn spec_smallvec_is_empty<A: smallvec::Array>(v: &SmallVec<A>) -> bool {
    v.view().len() == 0
}

#[verifier::when_used_as_spec(spec_smallvec_is_empty)]
pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::is_empty ](v: &SmallVec<A>)
    -> (r: bool)
    ensures r == (v.view().len() == 0);

pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::push ](
    v: &mut SmallVec<A>, value: A::Item,
)
    ensures final(v).view() == old(v).view().push(value);

// SmallVec's Copy-only implementation uses raw copying, not Clone dispatch.
pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::extend_from_slice ](
    v: &mut SmallVec<A>, values: &[A::Item],
)
    where A::Item: Copy,
    ensures final(v).view() == old(v).view() + values@;

pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::remove ](
    v: &mut SmallVec<A>, index: usize,
) -> (result: A::Item)
    requires index < old(v).view().len(),
    ensures result == old(v).view()[index as int],
        final(v).view() == old(v).view().remove(index as int);

pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::pop ](v: &mut SmallVec<A>)
    -> (r: Option<A::Item>)
    ensures
        old(v).view().len() == 0 ==> r is None && final(v).view() == old(v).view(),
        old(v).view().len() > 0 ==> r == Some(old(v).view().last())
            && final(v).view() == old(v).view().drop_last();

pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::truncate ](
    v: &mut SmallVec<A>, len: usize,
)
    ensures
        len <= old(v).view().len() ==> final(v).view() == old(v).view().subrange(0, len as int),
        len > old(v).view().len() ==> final(v).view() == old(v).view();

// Match vstd's Vec::resize: arbitrary Clone implementations need not be identity.
pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::resize ](
    v: &mut SmallVec<A>, len: usize, value: A::Item,
)
    where A::Item: Clone
    ensures
        len <= old(v).view().len() ==> final(v).view() == old(v).view().subrange(0, len as int),
        len > old(v).view().len() ==> {
            &&& final(v).view().len() == len
            &&& final(v).view().subrange(0, old(v).view().len() as int) == old(v).view()
            &&& forall|i: int| #![all_triggers] old(v).view().len() <= i < len
                ==> cloned::<A::Item>(value, final(v).view()[i])
        };

pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::try_reserve_exact ](
    v: &mut SmallVec<A>, additional: usize,
) -> Result<(), smallvec::CollectionAllocErr>
    ensures final(v).view() == old(v).view();

// get/get_mut/first/last are slice methods, covered by these views and vstd.
pub assume_specification<A: smallvec::Array>[ <SmallVec<A> as Deref>::deref ](
    v: &SmallVec<A>,
) -> (s: &[A::Item])
    ensures s@ == v.view(), v.view().len() <= usize::MAX;

// Mutable autoderef triggers the pinned verifier's anyhow dyn-target importer bug.
// The native slice accessor is the same borrow, without importing DerefMut.
pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::as_mut_slice ](
    v: &mut SmallVec<A>,
) -> (s: &mut [A::Item])
    ensures s@ == old(v).view(), final(s)@ == final(v).view();




pub open spec fn strictly_sorted<T: Ord>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].cmp_spec(&s[j]) is Less
}

// Rust's `Ord` contract: a total order; without one, `sort_unstable` may panic.
pub assume_specification<T: Ord>[ <[T]>::sort_unstable ](s: &mut [T])
    requires obeys_cmp::<T>(),
    ensures
        final(s)@.to_multiset() == old(s)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < final(s)@.len()
            ==> !(final(s)@[i].cmp_spec(&final(s)@[j]) is Greater);

pub open spec fn dedup_spec<T: PartialEq>(s: Seq<T>) -> Seq<T>
    decreases s.len(),
{
    if s.len() <= 1 {
        s
    } else if s[s.len() - 1].eq_spec(&s[s.len() - 2]) {
        dedup_spec(s.drop_last())
    } else {
        dedup_spec(s.drop_last()).push(s.last())
    }
}

// std compares each element with the last one kept; for an equivalence that is the
// same as comparing neighbours, which `dedup_spec` does.
pub assume_specification<T: PartialEq, A: Allocator>[ Vec::<T, A>::dedup ](v: &mut Vec<T, A>)
    requires obeys_eq::<T>(),
    ensures final(v)@ == dedup_spec(old(v)@);

pub assume_specification<T: Ord>[ <[T]>::binary_search ](s: &[T], value: &T)
    -> (r: Result<usize, usize>)
    requires obeys_cmp::<T>(), strictly_sorted(s@),
    ensures
        r matches Ok(i) ==> i < s@.len() && s@[i as int].cmp_spec(value) is Equal,
        r is Err ==> forall|i: int| 0 <= i < s@.len() ==> !(s@[i].cmp_spec(value) is Equal);

// Used by kernel slice comparisons; pinned vstd specifies cloned, not copied.
pub assume_specification<'a, T: Copy>[ Option::<&'a T>::copied ](v: Option<&'a T>)
    -> (r: Option<T>)
    ensures r == match v { Some(value) => Some(*value), None => None };

// The pinned vstd lacks these native calls; neither changes logical contents.
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::into_boxed_slice ](
    values: Vec<T, A>,
) -> (result: alloc::boxed::Box<[T], A>)
    ensures result@ == values@;

pub assume_specification<T>[ core::mem::drop ](value: T);


/// Proof observations for checked kernel stores. Error exclusions are opt-in;
/// custom stores that omit a capability retain arbitrary errors in that class.
pub trait KernelStoreSpec {
    spec fn graph(&self) -> Graph;
    spec fn valid_store(&self) -> bool;
    open spec fn errors_are_non_owner(&self) -> bool { false }
    open spec fn errors_are_non_invariant(&self) -> bool { false }
    open spec fn errors_are_non_invalid_policy(&self) -> bool { false }
    /// Valid operations report only graph, allocation, exhaustion, or host-limit errors.
    open spec fn errors_are_resource(&self) -> bool { false }

    // Preserve the abstract store restored when a nested mutable borrow ends.
    #[verifier::prophetic]
    spec fn restoration(&self) -> (Graph, bool);
}

} // verus!

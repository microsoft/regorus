// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Trusted native boundary for history correctness.
//!
//! Allowed leaves: reservation adapters;
//! exact SmallVec sequence operations; concrete successor-cache wrappers
//! (including their opaque default hasher type); the exact native Iterator::position
//! selector for retained cursor keys (the pinned vstd lacks its specification);
//! sort_unstable, dedup, strictly-sorted binary_search, rotate_right.
//! Primitive checked shifts use exact bit-vector results and reject oversized shifts.
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
//! The history owner isolates borrowed UTF-8 BTree operations and mutex-protected
//! allocator freshness/provenance in narrow native adapters. Mutex linearization
//! and the global counter invariant are trusted; allocation arithmetic, interner
//! insertion/rollback, and locked history append/truncate carry executable contracts.
//! Storage and KernelStore trait contracts are implemented by verified bodies,
//! not trusted implementations. No compiler, normalizer, derivative, interpreter,
//! matcher, replay, or evaluator may be external_body or assume_specification.

use crate::kernel::verify::{
    Graph, RegexNode, graph_extends, graph_wf, regex_node_wf, tables_wf, test_node_wf,
    transition_node_wf,
};
use crate::kernel::{
    Constants, KernelResult, RegexId, RegexKindView, RegexView, TestId, TestView, TransitionId,
    TransitionView,
};
use crate::observation::{ObservationWorld, SmallVecSpecFns};
use alloc::vec::Vec;
use core::{alloc::Allocator, ops::Deref};
use smallvec::SmallVec;
use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec};

verus! {

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
    ensures s@ == v.view();

// Mutable autoderef triggers the pinned verifier's anyhow dyn-target importer bug.
// The native slice accessor is the same borrow, without importing DerefMut.
pub assume_specification<A: smallvec::Array>[ SmallVec::<A>::as_mut_slice ](
    v: &mut SmallVec<A>,
) -> (s: &mut [A::Item])
    ensures s@ == old(v).view(), final(s)@ == final(v).view();




pub open spec fn strictly_sorted<T: Ord>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].cmp_spec(&s[j]) is Less
}

pub assume_specification<T: Ord>[ <[T]>::sort_unstable ](s: &mut [T])
    requires T::obeys_cmp_spec(),
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

pub assume_specification<T: PartialEq, A: Allocator>[ Vec::<T, A>::dedup ](v: &mut Vec<T, A>)
    requires T::obeys_eq_spec(),
    ensures final(v)@ == dedup_spec(old(v)@);

pub assume_specification<T: Ord>[ <[T]>::binary_search ](s: &[T], value: &T)
    -> (r: Result<usize, usize>)
    requires T::obeys_cmp_spec(), strictly_sorted(s@),
    ensures
        r matches Ok(i) ==> i < s@.len() && s@[i as int].cmp_spec(value) is Equal,
        r is Err ==> forall|i: int| 0 <= i < s@.len() ==> !(s@[i].cmp_spec(value) is Equal);

pub assume_specification<T>[ <[T]>::rotate_right ](s: &mut [T], k: usize)
    requires k <= old(s)@.len(),
    ensures final(s)@ == old(s)@.subrange(old(s)@.len() - k, old(s)@.len() as int)
        + old(s)@.subrange(0, old(s)@.len() - k);

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


#[verifier::external_trait_specification]
#[verifier::external_trait_extension(KernelStoreSpec via KernelStoreSpecImpl)]
pub trait ExKernelStore {
    type ExternalTraitSpecificationFor: crate::kernel::KernelStore;

    spec fn graph(&self) -> Graph;
    spec fn valid_store(&self) -> bool;

    // Preserve the abstract store restored when a nested mutable borrow ends.
    #[verifier::prophetic]
    spec fn restoration(&self) -> (Graph, bool);

    fn checkpoint(&mut self) -> (r: KernelResult<()>)
        ensures final(self).graph() == old(self).graph(),
            final(self).valid_store() == old(self).valid_store(), final(self).restoration() == old(self).restoration();
    fn charge_aux(&mut self, bytes: usize) -> (r: KernelResult<()>)
        ensures final(self).graph() == old(self).graph(),
            old(self).valid_store() ==> final(self).valid_store(), final(self).restoration() == old(self).restoration();
    fn reserve_derivatives(&mut self, values: &mut Vec<Option<TransitionId>>, additional: usize)
        -> (r: KernelResult<()>)
        ensures final(self).graph() == old(self).graph(), final(values)@ == old(values)@,
            final(self).valid_store() == old(self).valid_store(), final(self).restoration() == old(self).restoration();
    fn reserve_atoms(&mut self, values: &mut Vec<TestId>, additional: usize)
        -> (r: KernelResult<()>)
        ensures final(self).graph() == old(self).graph(), final(values)@ == old(values)@,
            final(self).valid_store() == old(self).valid_store(), final(self).restoration() == old(self).restoration();
    fn constants(&self) -> (r: Constants)
        ensures r@ == self.graph().constants;
    fn test(&self, id: TestId) -> (r: KernelResult<TestView<'_>>)
        ensures r matches Ok(v) ==> id@ < self.graph().tests.len()
            && v@ == self.graph().tests[id@ as int];
    fn regex(&self, id: RegexId) -> (r: KernelResult<RegexView<'_>>)
        ensures r matches Ok(v) ==> id@ < self.graph().regexes.len()
            && v@ == self.graph().regexes[id@ as int];
    fn transition(&self, id: TransitionId) -> (r: KernelResult<TransitionView<'_>>)
        ensures r matches Ok(v) ==> id@ < self.graph().transitions.len()
            && v@ == self.graph().transitions[id@ as int];

    fn intern_test(&mut self, node: TestView<'_>) -> (r: KernelResult<TestId>)
        requires old(self).valid_store(), test_node_wf(old(self).graph(), node@),
        ensures
            final(self).restoration() == old(self).restoration(),
            final(self).valid_store(),
            graph_extends(old(self).graph(), final(self).graph()),
            tables_wf(old(self).graph()) ==> tables_wf(final(self).graph()),
            graph_wf(old(self).graph()) ==> graph_wf(final(self).graph()),
            r matches Ok(id) ==> id@ < final(self).graph().tests.len()
                && final(self).graph().tests[id@ as int] == node@;
    fn intern_regex(&mut self, kind: RegexKindView<'_>, nullable: bool)
        -> (r: KernelResult<RegexId>)
        requires old(self).valid_store(), regex_node_wf(old(self).graph(), RegexNode { kind: kind@, nullable }),
        ensures
            final(self).restoration() == old(self).restoration(),
            final(self).valid_store(),
            graph_extends(old(self).graph(), final(self).graph()),
            tables_wf(old(self).graph()) ==> tables_wf(final(self).graph()),
            graph_wf(old(self).graph()) ==> graph_wf(final(self).graph()),
            r matches Ok(id) ==> id@ < final(self).graph().regexes.len()
                && final(self).graph().regexes[id@ as int] == (RegexNode { kind: kind@, nullable });
    fn intern_transition(&mut self, node: TransitionView<'_>) -> (r: KernelResult<TransitionId>)
        requires old(self).valid_store(), transition_node_wf(old(self).graph(), node@),
        ensures
            final(self).restoration() == old(self).restoration(),
            final(self).valid_store(),
            graph_extends(old(self).graph(), final(self).graph()),
            tables_wf(old(self).graph()) ==> tables_wf(final(self).graph()),
            graph_wf(old(self).graph()) ==> graph_wf(final(self).graph()),
            r matches Ok(id) ==> id@ < final(self).graph().transitions.len()
                && final(self).graph().transitions[id@ as int] == node@;
}

// The pinned vstd release does not specify this primitive integer method.
pub assume_specification[ u64::checked_shr ](value: u64, shift: u32) -> (r: Option<u64>)
    ensures r == if shift < 64 { Some(value >> shift) } else { None };

pub assume_specification[ u64::checked_shl ](value: u64, shift: u32) -> (r: Option<u64>)
    ensures r == if shift < 64 { Some(value << shift) } else { None };

// Moving an owned key out of an indexed vector does not clone or allocate.
pub assume_specification<T>[ core::mem::replace ](destination: &mut T, replacement: T) -> (previous: T)
    ensures previous == *old(destination), *final(destination) == replacement;

} // verus!

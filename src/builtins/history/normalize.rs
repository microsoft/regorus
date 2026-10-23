// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use super::error::normalization_invariant as invariant;
#[cfg(verus_keep_ghost)]
use super::graph::verify::lemma_id_clones;
#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
use super::kernel::*;
use super::work::WorkVec;
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::{dedup_spec, KernelStoreSpec, SmallVecSpecFns};
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use crate::verify::value_specs::Data;
#[cfg(verus_keep_ghost)]
use alloc::boxed::Box;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec};

#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), b@ < old(store).graph().tests.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(found) => found ==> test_opposite(final(store).graph(), a, b), Err(_) => true },
)]
fn complementary<G: KernelStore>(store: &mut G, a: TestId, b: TestId) -> KernelResult<bool> {
    let left = test_head(store, a)?;
    let right = test_head(store, b)?;
    match (left, right) {
        (TestHead::Atom(p, x), TestHead::Atom(q, y)) => {
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| p@ == q@ && x != y
                    implies test_truth(store.graph(), sym, theta, a@, event) != test_truth(store.graph(), sym, theta, b@, event) by {
                    test_lemma_truth(store.graph(), sym, theta, a@, event);
                    test_lemma_truth(store.graph(), sym, theta, b@, event);
                }
            }
            Ok(p == q && x != y)
        }
        (TestHead::And(_), TestHead::Or(_)) | (TestHead::Or(_), TestHead::And(_)) => {
            Ok(test_not(store, a)? == b)
        }
        (TestHead::True, TestHead::False) | (TestHead::False, TestHead::True) => {
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                    test_truth(store.graph(), sym, theta, a@, event) != test_truth(store.graph(), sym, theta, b@, event) by {
                    test_lemma_truth(store.graph(), sym, theta, a@, event);
                    test_lemma_truth(store.graph(), sym, theta, b@, event);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}
#[verus_verify]
#[verus_spec(result => ensures result == test_distinct_heads(left@, right@))]
fn distinct(left: TestHead, right: TestHead) -> bool {
    matches!((left,right),(TestHead::Atom(Primitive::EqCore(p,Term::Constant(c)),_),TestHead::Atom(Primitive::EqCore(q,Term::Constant(d)),_)) if p==q&&c!=d)
}
#[verus_verify]
#[verus_spec(result => ensures result == match head@ {
    model::TestHeadNode::Or(n) => if and { Some(n as usize) } else { None },
    model::TestHeadNode::And(n) => if !and { Some(n as usize) } else { None },
    _ => None,
})]
fn dual_test_count(head: TestHead, and: bool) -> Option<usize> {
    match head {
        TestHead::Or(n) if and => Some(n),
        TestHead::And(n) if !and => Some(n),
        _ => None,
    }
}
#[verus_verify]
#[verus_spec(result => requires low < high,
    ensures match result { Ok(mid) => low <= mid < high, Err(_) => false },
)]
const fn midpoint(low: usize, high: usize) -> KernelResult<usize> {
    match high.saturating_sub(low).checked_div(2) {
        Some(half) => Ok(low.saturating_add(half)),
        None => Err(invariant()),
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), test_child_count(store.graph(), parent, count as nat),
    ensures match result {
        Ok(found) => found == test_children(store.graph(), parent).contains(id@),
        Err(_) => true,
    },
)]
fn test_contains<G: KernelStore>(
    store: &G,
    parent: TestId,
    count: usize,
    id: TestId,
) -> KernelResult<bool> {
    proof! { test_lemma_children(store.graph(), parent, count as nat); }
    let mut low = 0;
    let mut high = count;
    let mut failure = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            model::graph_wf(store.graph()),
            test_child_count(store.graph(), parent, count as nat),
            model::nondecreasing(test_children(store.graph(), parent)),
            low <= high <= count,
            forall|i: int| 0 <= i < low ==> #[trigger] test_children(store.graph(), parent)[i] < id@,
            forall|i: int| high <= i < count ==> #[trigger] test_children(store.graph(), parent)[i] >= id@,
        ensures failure.is_none() ==> low == high,
        decreases high - low,
    ))]
    while low < high {
        let mid = loop_try!(midpoint(low, high), failure);
        let child = loop_try!(test_child(store, parent, mid), failure);
        if child < id {
            proof! {
                assert forall|i: int| 0 <= i <= mid
                    implies #[trigger] test_children(store.graph(), parent)[i] < id@ by {
                    assert(test_children(store.graph(), parent)[i] <= child@);
                }
            }
            low = mid.saturating_add(1)
        } else {
            proof! {
                assert forall|i: int| mid <= i < count
                    implies #[trigger] test_children(store.graph(), parent)[i] >= id@ by {
                    assert(test_children(store.graph(), parent)[i] >= child@);
                }
            }
            high = mid
        }
    }
    if let Some(error) = failure {
        return Err(error);
    }
    if low < count {
        Ok(test_child(store, parent, low)? == id)
    } else {
        Ok(false)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()),
        test_child_count(store.graph(), a, a_count as nat),
        test_child_count(store.graph(), b, b_count as nat),
    ensures match result {
        Ok(included) => included == (forall|i: int| 0 <= i < a_count
            ==> test_children(store.graph(), b).contains(test_children(store.graph(), a)[i]))
            && included == (forall|child: nat| test_children(store.graph(), a).contains(child)
                ==> test_children(store.graph(), b).contains(child)),
        Err(_) => true,
    },
)]
fn test_subset<G: KernelStore>(
    store: &G,
    a: TestId,
    a_count: usize,
    b: TestId,
    b_count: usize,
) -> KernelResult<bool> {
    proof! {
        test_lemma_children(store.graph(), a, a_count as nat);
        test_lemma_children(store.graph(), b, b_count as nat);
    }
    let mut included = true;
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            model::graph_wf(store.graph()),
            test_child_count(store.graph(), a, a_count as nat),
            test_child_count(store.graph(), b, b_count as nat),
            i <= a_count,
            included == (forall|j: int| 0 <= j < i
                ==> test_children(store.graph(), b).contains(test_children(store.graph(), a)[j])),
        ensures failure.is_none() ==> i == a_count,
        decreases a_count - i,
    ))]
    while i < a_count {
        let id = loop_try!(test_child(store, a, i), failure);
        proof! { assert(id@ == test_children(store.graph(), a)[i as int]); }
        included &= loop_try!(test_contains(store, b, b_count, id), failure);
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    proof! {
        assert(included == (forall|child: nat| test_children(store.graph(), a).contains(child)
            ==> test_children(store.graph(), b).contains(child))) by {
            if included {
                assert forall|child: nat| test_children(store.graph(), a).contains(child)
                    implies test_children(store.graph(), b).contains(child) by {
                    let j = choose|j: int| 0 <= j < a_count && test_children(store.graph(), a)[j] == child;
                }
            } else {
                let j = choose|j: int| 0 <= j < a_count
                    && !test_children(store.graph(), b).contains(test_children(store.graph(), a)[j]);
                assert(test_children(store.graph(), a).contains(test_children(store.graph(), a)[j]));
            }
        }
    }
    Ok(included)
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(id) => index < ids@.len() && id == ids@[index as int],
    Err(_) => index >= ids@.len(),
})]
fn test_at(ids: &[TestId], index: usize) -> KernelResult<TestId> {
    match ids.get(index) {
        Some(id) => Ok(*id),
        None => Err(invariant()),
    }
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(id) => index < ids@.len() && id == ids@[index as int],
    Err(_) => index >= ids@.len(),
})]
fn regex_at(ids: &[RegexId], index: usize) -> KernelResult<RegexId> {
    match ids.get(index) {
        Some(id) => Ok(*id),
        None => Err(invariant()),
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@), index < siblings@.len(),
        collapse ==> test_absorbs(old(store).graph(), seq![a] + siblings@, and),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => (collapse ==> out) && (out ==> test_absorbs(final(store).graph(), seq![a] + siblings@, and)), Err(_) => true },
)]
fn test_pair_step<G: KernelStore>(
    store: &mut G,
    a: TestId,
    siblings: &[TestId],
    index: usize,
    and: bool,
    mut collapse: bool,
) -> KernelResult<bool> {
    proof_decl! { let ghost before = store.graph(); let ghost prior = collapse; }
    let b = test_at(siblings, index)?;
    store.checkpoint()?;
    if a != b {
        let av = test_head(store, a)?;
        let bv = test_head(store, b)?;
        collapse |= matches!((av,bv),(TestHead::Atom(_,x),TestHead::Atom(_,y)) if x==and&&y==and)
            && distinct(av, bv);
        collapse |= complementary(store, a, b)?;
    }
    proof! {
        if collapse {
            if prior { test_lemma_absorbs_extends(before, store.graph(), seq![a] + siblings@, and); }
            else {
                test_lemma_pair_absorbs(store.graph(), a, b, and);
                assert(siblings@.contains(b));
                assert forall|id: TestId| seq![a, b].contains(id) implies (seq![a] + siblings@).contains(id) by {
                    if id == a { assert((seq![a] + siblings@)[0] == id); }
                    else { assert(id == b); assert((seq![a] + siblings@)[index as int + 1] == id); }
                }
                test_lemma_absorbs_superset(store.graph(), seq![a, b], seq![a] + siblings@, and);
            }
        }
    }
    Ok(collapse)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => out ==> test_absorbs(final(store).graph(), seq![a] + siblings@, and), Err(_) => true },
)]
fn test_pair_collapse<G: KernelStore>(
    store: &mut G,
    a: TestId,
    siblings: &[TestId],
    and: bool,
) -> KernelResult<bool> {
    let mut state = Ok(false);
    scan!(state,index,siblings.len(),state.is_ok(),prior=>test_pair_step(store,a,siblings,index,and,prior);
        invariant model::graph_extends(old(store).graph(), store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            a@ < store.graph().tests.len(), test_ids_valid(store.graph(), siblings@), index <= siblings.len(),
            match state { Ok(out) => out ==> test_absorbs(store.graph(), seq![a] + siblings@, and), Err(_) => true },
        decreases siblings.len() - index,
    );
    state
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        id@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@), index < siblings@.len(),
        found ==> test_has_opposite(old(store).graph(), id, siblings@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => (found ==> out) && (out ==> test_has_opposite(final(store).graph(), id, siblings@)), Err(_) => true },
)]
fn test_complement_step<G: KernelStore>(
    store: &mut G,
    id: TestId,
    siblings: &[TestId],
    index: usize,
    found: bool,
) -> KernelResult<bool> {
    proof_decl! { let ghost before = store.graph(); }
    let sibling = test_at(siblings, index)?;
    let matched = complementary(store, id, sibling)?;
    proof! {
        if found { test_lemma_has_opposite_extends(before, store.graph(), id, siblings@); }
        if matched { assert(test_opposite(store.graph(), id, siblings@[index as int])); }
    }
    Ok(found || matched)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        id@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => out ==> test_has_opposite(final(store).graph(), id, siblings@), Err(_) => true },
)]
fn test_has_complement<G: KernelStore>(
    store: &mut G,
    id: TestId,
    siblings: &[TestId],
) -> KernelResult<bool> {
    let mut state = Ok(false);
    scan!(state,index,siblings.len(),state.is_ok(),prior=>test_complement_step(store,id,siblings,index,prior);
        invariant model::graph_extends(old(store).graph(), store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            id@ < store.graph().tests.len(), test_ids_valid(store.graph(), siblings@), index <= siblings.len(),
            match state { Ok(out) => out ==> test_has_opposite(store.graph(), id, siblings@), Err(_) => true },
        decreases siblings.len() - index,
    );
    state
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), test_child_count(old(store).graph(), a, test_children(old(store).graph(), a).len()),
        test_ids_valid(old(store).graph(), siblings@), index < test_children(old(store).graph(), a).len(),
        all ==> test_complement_covered(old(store).graph(), test_children(old(store).graph(), a).take(index as int), siblings@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => out ==> test_complement_covered(final(store).graph(), test_children(final(store).graph(), a).take(index as int + 1), siblings@), Err(_) => true },
)]
fn test_compound_step<G: KernelStore>(
    store: &mut G,
    a: TestId,
    siblings: &[TestId],
    index: usize,
    all: bool,
) -> KernelResult<bool> {
    proof_decl! { let ghost before = store.graph(); }
    proof! { test_lemma_children(store.graph(), a, test_children(store.graph(), a).len()); }
    let id = test_child(store, a, index)?;
    let matched = test_has_complement(store, id, siblings)?;
    proof! {
        if all { test_lemma_covered_extends(before, store.graph(), test_children(before, a).take(index as int), siblings@); }
        if matched { assert(test_has_opposite(store.graph(), id, siblings@)); }
        if all && matched {
            assert(id@ == test_children(store.graph(), a)[index as int]);
            assert forall|child: nat| #[trigger] test_children(store.graph(), a).take(index as int + 1).contains(child)
                implies exists|j: int| 0 <= j < siblings.len() && test_opposite_nat(store.graph(), child, siblings@[j]@) by {
                let k = choose|k: int| 0 <= k < index as int + 1 && test_children(store.graph(), a)[k] == child;
                if k < index {
                    assert(test_children(store.graph(), a).take(index as int)[k] == child);
                    assert(test_children(store.graph(), a).take(index as int).contains(child));
                }
                else { assert(child == id@); }
            }
        }
    }
    Ok(all && matched)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => out ==> test_absorbs(final(store).graph(), seq![a] + siblings@, and), Err(_) => true },
)]
fn test_compound_collapse<G: KernelStore>(
    store: &mut G,
    a: TestId,
    siblings: &[TestId],
    and: bool,
) -> KernelResult<bool> {
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)] // Verus-verified match.
    let count = match dual_test_count(test_head(store, a)?, and) {
        Some(n) => n,
        None => 0,
    };
    proof! { if count != 0 {
        test_lemma_children(store.graph(), a, count as nat);
        assert(test_children(store.graph(), a).take(count as int) =~= test_children(store.graph(), a));
    } }
    let mut state = Ok(count != 0);
    scan!(state,index,count,state.is_ok(),prior=>test_compound_step(store,a,siblings,index,prior);
        invariant model::graph_extends(old(store).graph(), store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            a@ < store.graph().tests.len(), test_ids_valid(store.graph(), siblings@), index <= count,
            count != 0 ==> test_dual(store.graph(), a, and) && test_child_count(store.graph(), a, count as nat),
            count != 0 ==> test_children(store.graph(), a).take(count as int) == test_children(store.graph(), a),
            match state { Ok(out) => out ==> count != 0 && test_complement_covered(store.graph(), test_children(store.graph(), a).take(index as int), siblings@), Err(_) => true },
        ensures state is Ok ==> index == count,
            match state { Ok(out) => out ==> test_dual(store.graph(), a, and)
            && test_complement_covered(store.graph(), test_children(store.graph(), a), siblings@), Err(_) => true },
        decreases count - index,
    );
    proof! {
        if state is Ok && state->Ok_0 {
            test_lemma_compound_absorbs(store.graph(), a, siblings@, and);
        }
    }
    state
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@), index < siblings@.len(),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => out == (redundant || test_redundancy(final(store).graph(), a, siblings@[index as int], and)), Err(_) => true },
)]
fn test_redundant_step<G: KernelStore>(
    store: &mut G,
    a: TestId,
    siblings: &[TestId],
    index: usize,
    and: bool,
    mut redundant: bool,
) -> KernelResult<bool> {
    let b = test_at(siblings, index)?;
    store.checkpoint()?;
    if a != b {
        let av = test_head(store, a)?;
        let bv = test_head(store, b)?;
        if let Some(n) = dual_test_count(av, and) {
            redundant |= match dual_test_count(bv, and) {
                Some(m) => test_subset(store, b, m, a, n)?,
                None => test_contains(store, a, n, b)?,
            };
        }
        redundant |= distinct(av, bv)
            && matches!((av,bv),(TestHead::Atom(_,x),TestHead::Atom(_,y)) if x!=and&&y==and);
    }
    Ok(redundant)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().tests.len(), test_ids_valid(old(store).graph(), siblings@),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => out == test_redundant_in(final(store).graph(), a, siblings@, and), Err(_) => true },
)]
fn test_redundant<G: KernelStore>(
    store: &mut G,
    a: TestId,
    siblings: &[TestId],
    and: bool,
) -> KernelResult<bool> {
    proof! { assert(siblings@.take(siblings@.len() as int) =~= siblings@); }
    let mut state = Ok(false);
    scan!(state,index,siblings.len(),state.is_ok(),prior=>{
        proof! {
            test_lemma_redundant_push(store.graph(), a, siblings@.take(index as int), siblings@[index as int], and);
            assert(siblings@.take(index as int).push(siblings@[index as int]) =~= siblings@.take(index as int + 1));
        }
        test_redundant_step(store,a,siblings,index,and,prior)
    };
        invariant store.graph() == old(store).graph(), store.valid_store(),
            store.restoration() == old(store).restoration(),
            model::graph_wf(store.graph()), a@ < store.graph().tests.len(), test_ids_valid(store.graph(), siblings@),
            index <= siblings.len(),
            siblings@.take(siblings@.len() as int) == siblings@,
            match state { Ok(out) => out == test_redundant_in(store.graph(), a, siblings@.take(index as int), and), Err(_) => true },
        ensures state is Ok ==> index == siblings.len(),
            match state { Ok(out) => out == test_redundant_in(store.graph(), a, siblings@, and), Err(_) => true },
        decreases siblings.len() - index,
    );
    state
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), test_child_count(store.graph(), id, count as nat),
    ensures old(flat).view().is_prefix_of(final(flat).view()),
        final(flat).view().len() <= old(flat).view().len() + count,
        forall|j: int| old(flat).view().len() <= j < final(flat).view().len()
            ==> #[trigger] final(flat).view()[j]@ < store.graph().tests.len(),
        forall|j: int| old(flat).view().len() <= j < final(flat).view().len()
            ==> #[trigger] final(flat).view()[j]@ == test_children(store.graph(), id)[j - old(flat).view().len()],
        match result { Ok(()) => final(flat).view().len() == old(flat).view().len() + count, Err(_) => true },
)]
fn collect_test_children<G: KernelStore>(
    store: &G,
    id: TestId,
    count: usize,
    flat: &mut WorkVec<TestId>,
) -> KernelResult<()> {
    proof! { test_lemma_children(store.graph(), id, count as nat); }
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            model::graph_wf(store.graph()), test_child_count(store.graph(), id, count as nat),
            i <= count,
            model::bounded(test_children(store.graph(), id), id@), test_children(store.graph(), id).len() == count,
            flat.view().len() == old(flat).view().len() + i,
            old(flat).view().is_prefix_of(flat.view()),
            forall|j: int| old(flat).view().len() <= j < flat.view().len()
                ==> #[trigger] flat.view()[j]@ == test_children(store.graph(), id)[j - old(flat).view().len()],
            forall|j: int| old(flat).view().len() <= j < flat.view().len() ==> #[trigger] flat.view()[j]@ < store.graph().tests.len(),
        ensures failure.is_none() ==> i == count,
        decreases count - i,
    ))]
    while i < count {
        let child = loop_try!(test_child(store, id, i), failure);
        proof! { assert(child@ == test_children(store.graph(), id)[i as int]); }
        flat.push(child);
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires structural_eq::<T>(), read < old(values).view().len(), state.1 <= read,
        read < usize::MAX,
    ensures match result {
        Ok(next) => {
            let source = old(values).view();
            let duplicate = state.0 == Some(source[read as int]);
            &&& next == if duplicate { state } else { (Some(source[read as int]), (state.1 + 1) as usize) }
            &&& final(values).view() == if duplicate || state.1 == read {
                source
            } else { source.update(state.1 as int, source[read as int]) }
            &&& final(values).view().subrange(0, next.1 as int)
                == if duplicate { source.subrange(0, state.1 as int) }
                    else { source.subrange(0, state.1 as int).push(source[read as int]) }
            &&& final(values).view().subrange(read as int + 1, source.len() as int)
                == source.subrange(read as int + 1, source.len() as int)
        },
        Err(_) => false,
    },
)]
fn dedup_step<T: Copy + Eq>(
    values: &mut WorkVec<T>,
    read: usize,
    state: (Option<T>, usize),
) -> KernelResult<(Option<T>, usize)> {
    proof_decl! { let ghost source = values.view(); }
    let value = match values.get(read) {
        Some(v) => *v,
        None => return Err(invariant()),
    };
    let (previous, write) = state;
    let duplicate = match previous {
        Some(v) => v == value,
        None => false,
    };
    if duplicate {
        Ok((previous, write))
    } else {
        if write != read {
            match values.as_mut_slice().get_mut(write) {
                Some(slot) => *slot = value,
                None => return Err(invariant()),
            }
        }
        proof! {
            assert(values.view().subrange(0, write as int + 1)
                =~= source.subrange(0, write as int).push(value));
            assert(values.view().subrange(read as int + 1, source.len() as int)
                =~= source.subrange(read as int + 1, source.len() as int));
        }
        Ok((Some(value), write.saturating_add(1)))
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires structural_eq::<T>(),
    ensures result is Ok,
        final(values).view() == dedup_spec(old(values).view()),
        forall|v: T| final(values).view().contains(v) <==> old(values).view().contains(v),
        forall|i: int| 0 < i < final(values).view().len()
            ==> final(values).view()[i - 1] != #[trigger] final(values).view()[i],
)]
fn dedup_ids<T: Copy + Eq>(values: &mut WorkVec<T>) -> KernelResult<()> {
    proof_decl! { let ghost original = values.view(); }
    proof! { assert(original.subrange(0, original.len() as int) =~= original); }
    let count = values.len();
    let mut state = Ok((None, 0));
    scan!(state,index,count,state.is_ok(),prior=>{
        proof! {
            if index > 0 { assert(original.subrange(0, index as int).last() == original[index as int - 1]); }
            lemma_dedup_push(old(values).view().subrange(0, index as int),
                old(values).view()[index as int]);
            assert(old(values).view().subrange(0, index as int + 1)
                =~= old(values).view().subrange(0, index as int).push(old(values).view()[index as int]));
        }
        dedup_step(values,index,prior)
    };
        invariant
            structural_eq::<T>(),
            count == old(values).view().len(),
            original == old(values).view(),
            values.view().len() == count,
            index <= count,
            forall|j: int| index <= j < count ==> #[trigger] values.view()[j] == original[j],
            match state {
                Ok((previous, write)) => write <= index
                    && previous == (if index == 0 { None } else { Some(old(values).view()[index as int - 1]) })
                    && values.view().subrange(0, write as int)
                        == dedup_spec(old(values).view().subrange(0, index as int)),
                Err(_) => false,
            },
        decreases count - index,
    );
    let (_, len) = state?;
    values.truncate(len);
    proof! { lemma_dedup_properties(old(values).view()); }
    Ok(())
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
struct TestMode {
    and: bool,
    identity: TestId,
    absorber: TestId,
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        test_ids_valid(old(store).graph(), children@), test_ids_valid(old(store).graph(), old(flat).view()), index < children@.len(),
        mode.identity@ == if mode.and { old(store).graph().constants.test_true } else { old(store).graph().constants.test_false },
        mode.absorber@ == if mode.and { old(store).graph().constants.test_false } else { old(store).graph().constants.test_true },
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(true) => children@[index as int] == mode.absorber && final(flat).view() == old(flat).view()
                && test_absorbs(final(store).graph(), children@, mode.and),
            Ok(false) => test_ids_valid(final(store).graph(), final(flat).view())
                && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                    test_combo(final(store).graph(), sym, theta, final(flat).view(), event, mode.and)
                        == test_combo(final(store).graph(), sym, theta, old(flat).view().push(children@[index as int]), event, mode.and)),
            Err(_) => true,
        },
)]
fn collect_test_step<G: KernelStore>(
    store: &mut G,
    children: &[TestId],
    index: usize,
    mode: TestMode,
    flat: &mut WorkVec<TestId>,
) -> KernelResult<bool> {
    proof_decl! { let ghost prior = flat.view(); }
    proof! { model::lemma_graph_wf_elim(store.graph()); }
    let id = test_at(children, index)?;
    store.checkpoint()?;
    if id == mode.absorber {
        proof! {
            test_lemma_constants_semantics(store.graph());
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                implies test_combo(store.graph(), sym, theta, seq![id], event, mode.and) == !mode.and by {
                test_lemma_combo_push(store.graph(), sym, theta, event, Seq::empty(), id, mode.and);
            }
            test_lemma_absorbs_superset(store.graph(), seq![id], children@, mode.and);
        }
        return Ok(true);
    }
    if id != mode.identity {
        match test_head(store, id)? {
            TestHead::And(n) if mode.and => collect_test_children(store, id, n, flat)?,
            TestHead::Or(n) if !mode.and => collect_test_children(store, id, n, flat)?,
            _ => flat.push(id),
        }
    }
    proof! {
        if id != mode.identity {
            match store.graph().tests[id@ as int] {
                model::TestNode::And(_) => { if mode.and { test_lemma_flatten(store.graph(), prior, flat.view(), id, mode.and); } },
                model::TestNode::Or(_) => { if !mode.and { test_lemma_flatten(store.graph(), prior, flat.view(), id, mode.and); } },
                _ => {},
            }
        } else {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(store.graph(), sym, theta, flat.view(), event, mode.and)
                    == test_combo(store.graph(), sym, theta, prior.push(id), event, mode.and) by {
                test_lemma_truth(store.graph(), sym, theta, id@, event);
                test_lemma_combo_push(store.graph(), sym, theta, event, prior, id, mode.and);
            }
        }
        assert forall|i: int| 0 <= i < flat.view().len() implies flat.view()[i]@ < store.graph().tests.len() by {
            if i < prior.len() { assert(flat.view()[i] == prior[i]); }
            else {
                match store.graph().tests[id@ as int] {
                    model::TestNode::And(_) => {
                        if !mode.and { assert(flat.view()[i] == id); }
                        else { assert(flat.view()[i]@ < store.graph().tests.len()); }
                    },
                    model::TestNode::Or(_) => {
                        if mode.and { assert(flat.view()[i] == id); }
                        else { assert(flat.view()[i]@ < store.graph().tests.len()); }
                    },
                    _ => { assert(flat.view()[i] == id); },
                }
            }
        }
    }
    Ok(false)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), flat@), index < flat@.len(),
        prior ==> test_absorbs(old(store).graph(), flat@, and),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(out) => (prior ==> out) && (out ==> test_absorbs(final(store).graph(), flat@, and))
            && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(old(store).graph(), sym, theta, flat@, event, and)
                    == test_combo(final(store).graph(), sym, theta, flat@, event, and)), Err(_) => true },
)]
fn collapse_test_step<G: KernelStore>(
    store: &mut G,
    flat: &[TestId],
    index: usize,
    and: bool,
    prior: bool,
) -> KernelResult<bool> {
    proof_decl! { let ghost before = store.graph(); }
    let id = test_at(flat, index)?;
    let pair = test_pair_collapse(store, id, flat, and)?;
    proof_decl! { let ghost after_pair = store.graph(); }
    let compound = test_compound_collapse(store, id, flat, and)?;
    proof! {
        if prior { test_lemma_absorbs_extends(before, store.graph(), flat@, and); }
        if pair {
            test_lemma_absorbs_extends(after_pair, store.graph(), seq![id] + flat@, and);
            test_lemma_absorbs_superset(store.graph(), seq![id] + flat@, flat@, and);
        }
        if compound { test_lemma_absorbs_superset(store.graph(), seq![id] + flat@, flat@, and); }
        test_lemma_combo_extends(before, store.graph(), flat@);
    }
    Ok(prior || pair || compound)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), flat@), index < flat@.len(),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(()) => final(kept).view() == if test_redundant_in(final(store).graph(), flat@[index as int], flat@, and) {
            old(kept).view()
        } else { old(kept).view().push(flat@[index as int]) }, Err(_) => true },
)]
fn retain_test_step<G: KernelStore>(
    store: &mut G,
    flat: &[TestId],
    index: usize,
    and: bool,
    kept: &mut WorkVec<TestId>,
) -> KernelResult<()> {
    let id = test_at(flat, index)?;
    if !test_redundant(store, id, flat, and)? {
        kept.push(id);
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), children@),
        model::strictly_increasing(model::test_ids(children@)),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(id) => id@ < final(store).graph().tests.len()
            && (forall|i: nat| i < old(store).graph().tests.len()
                ==> model::lift_test(old(store).graph(), i) == model::lift_test(final(store).graph(), i))
            && (forall|ids: Seq<TestId>, sym: model::Symbols, theta: Seq<Data>, event: Data, mode: bool|
                test_ids_valid(old(store).graph(), ids) ==> test_combo(old(store).graph(), sym, theta, ids, event, mode)
                    == test_combo(final(store).graph(), sym, theta, ids, event, mode))
            && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_truth(final(store).graph(), sym, theta, id@, event)
                    == test_combo(final(store).graph(), sym, theta, children@, event, and)), Err(_) => true },
)]
fn test_intern_step<G: KernelStore>(
    store: &mut G,
    children: &[TestId],
    and: bool,
) -> KernelResult<TestId> {
    proof_decl! { let ghost before = store.graph(); }
    let id = store.intern_test(if and {
        TestView::And(children)
    } else {
        TestView::Or(children)
    })?;
    proof! {
        assert forall|ids: Seq<TestId>, sym: model::Symbols, theta: Seq<Data>, event: Data, mode: bool|
            test_ids_valid(before, ids) implies test_combo(before, sym, theta, ids, event, mode)
                == test_combo(store.graph(), sym, theta, ids, event, mode) by {
            test_lemma_combo_extends(before, store.graph(), ids);
        }
        assert forall|i: nat| i < before.tests.len()
            implies model::lift_test(before, i) == model::lift_test(store.graph(), i) by {
            model::lemma_lift_test_stable(before, store.graph(), i);
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_truth(store.graph(), sym, theta, id@, event)
                == test_combo(store.graph(), sym, theta, children@, event, and) by {
            test_lemma_compound_semantics(store.graph(), sym, theta, event, id, children@, and);
        }
    }
    Ok(id)
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(id) => id@ < final(store).graph().tests.len()
            && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> test_truth(final(store).graph(), sym, theta, id@, event)
                    == test_combo(final(store).graph(), sym, theta, children@, event, and)), Err(_) => true },
)]
fn test_connective<G: KernelStore>(
    store: &mut G,
    children: &[TestId],
    and: bool,
) -> KernelResult<TestId> {
    proof! { test_lemma_constants_semantics(store.graph()); }
    let c = store.constants();
    let identity = if and { c.test_true } else { c.test_false };
    let absorber = if and { c.test_false } else { c.test_true };
    let mode = TestMode {
        and,
        identity,
        absorber,
    };
    let mut flat = WorkVec::new();
    proof! { assert(children@.take(children@.len() as int) =~= children@); }
    let mut collecting = Ok(false);
    scan!(collecting,index,children.len(),matches!(collecting,Ok(false)),_prior=>{
        proof! {
            assert(children@.take(index as int).push(children@[index as int]) =~= children@.take(index as int + 1));
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(store.graph(), sym, theta, flat.view().push(children@[index as int]), event, and)
                    == test_combo(store.graph(), sym, theta, children@.take(index as int + 1), event, and) by {
                test_lemma_combo_push(store.graph(), sym, theta, event, flat.view(), children@[index as int], and);
                test_lemma_combo_push(store.graph(), sym, theta, event, children@.take(index as int), children@[index as int], and);
            }
        }
        collect_test_step(store,children,index,mode,&mut flat)
    };
        invariant store.graph() == old(store).graph(), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            c@ == store.graph().constants, mode.and == and, mode.identity == identity, mode.absorber == absorber,
            identity@ == if and { c.test_true@ } else { c.test_false@ }, absorber@ == if and { c.test_false@ } else { c.test_true@ },
            test_ids_valid(store.graph(), children@), index <= children.len(),
            children@.take(children@.len() as int) == children@,
            match collecting {
                Ok(true) => test_absorbs(store.graph(), children@, and),
                Ok(false) => test_ids_valid(store.graph(), flat.view())
                    && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                        test_combo(store.graph(), sym, theta, flat.view(), event, and)
                            == test_combo(store.graph(), sym, theta, children@.take(index as int), event, and)),
                Err(_) => true,
            },
        ensures matches!(collecting, Ok(false)) ==> index == children.len(),
            match collecting { Ok(false) => test_ids_valid(store.graph(), flat.view())
            && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(store.graph(), sym, theta, flat.view(), event, and) == test_combo(store.graph(), sym, theta, children@, event, and)), _ => true },
        decreases children.len() - index,
    );
    if collecting? {
        return Ok(absorber);
    }
    proof_decl! { let ghost collected = flat.view(); }
    flat.as_mut_slice().sort_unstable();
    proof_decl! { let ghost sorted = flat.view(); }
    dedup_ids(&mut flat)?;
    proof! {
        lemma_multiset_members(collected, sorted);
        assert forall|i: int, j: int| 0 <= i < j < sorted.len() implies sorted[i]@ <= sorted[j]@ by {
            assert(!(sorted[i].cmp_spec(&sorted[j]) is Greater));
        }
        assert forall|id: TestId| flat.view().contains(id) <==> collected.contains(id) by {
            assert(flat.view().contains(id) == sorted.contains(id));
        }
        assert forall|i: int| 0 <= i < flat.view().len() implies flat.view()[i]@ < store.graph().tests.len() by {
            assert(collected.contains(flat.view()[i]));
            let j = choose|j: int| 0 <= j < collected.len() && collected[j] == flat.view()[i];
        }
        lemma_dedup_strict(sorted, |id: TestId| id@);
        assert forall|i: int, j: int| 0 <= i < j < flat.view().len()
            implies flat.view()[i]@ < flat.view()[j]@ by {
            assert(dedup_spec(sorted)[i] == flat.view()[i]);
            assert(dedup_spec(sorted)[j] == flat.view()[j]);
            assert((|id: TestId| id@)(dedup_spec(sorted)[i])
                < (|id: TestId| id@)(dedup_spec(sorted)[j]));
        }
        assert forall|i: int, j: int| 0 <= i < j < model::test_ids(flat.view()).len()
            implies model::test_ids(flat.view())[i] < model::test_ids(flat.view())[j] by {
            assert(model::test_ids(flat.view())[i] == flat.view()[i]@);
            assert(model::test_ids(flat.view())[j] == flat.view()[j]@);
        }
        assert(model::strictly_increasing(model::test_ids(flat.view())));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_combo(store.graph(), sym, theta, flat.view(), event, and)
                == test_combo(store.graph(), sym, theta, children@, event, and) by {
            test_lemma_combo_membership(store.graph(), sym, theta, event, flat.view(), collected, and);
        }
    }
    let mut collapse = Ok(false);
    scan!(collapse,index,flat.len(),collapse.is_ok(),prior=>collapse_test_step(store,&flat,index,and,prior);
        invariant model::graph_extends(old(store).graph(), store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            test_ids_valid(store.graph(), flat.view()), test_ids_valid(store.graph(), children@), index <= flat.len(),
            model::strictly_increasing(model::test_ids(flat.view())),
            collapse is Ok ==> (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(store.graph(), sym, theta, flat.view(), event, and)
                    == test_combo(old(store).graph(), sym, theta, children@, event, and)),
            match collapse { Ok(out) => out ==> test_absorbs(store.graph(), flat.view(), and), Err(_) => true },
        decreases flat.len() - index,
    );
    proof! {
        test_lemma_combo_extends(old(store).graph(), store.graph(), children@);
        test_lemma_constants_semantics(store.graph());
    }
    if collapse? {
        return Ok(absorber);
    }
    let mut kept = WorkVec::new();
    let mut retaining = Ok(());
    proof! { assert(flat.view().take(flat.view().len() as int) =~= flat.view()); }
    scan!(retaining,index,flat.len(),retaining.is_ok(),_prior=>{
        proof! {
            flat.view().take(index as int).lemma_filter_push(flat.view()[index as int],
                |id: TestId| !test_redundant_in(store.graph(), id, flat.view(), and));
            assert(flat.view().take(index as int).push(flat.view()[index as int]) =~= flat.view().take(index as int + 1));
        }
        retain_test_step(store,&flat,index,and,&mut kept)
    };
        invariant model::graph_extends(old(store).graph(), store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            store.restoration() == old(store).restoration(),
            test_ids_valid(store.graph(), flat.view()), index <= flat.len(),
            model::strictly_increasing(model::test_ids(flat.view())),
            flat.view().take(flat.view().len() as int) == flat.view(),
            retaining is Ok ==> kept.view() == flat.view().take(index as int).filter(
                |id: TestId| !test_redundant_in(store.graph(), id, flat.view(), and)),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(store.graph(), sym, theta, flat.view(), event, and)
                    == test_combo(store.graph(), sym, theta, children@, event, and),
        ensures retaining is Ok ==> index == flat.len(),
            retaining is Ok ==> kept.view() == test_retained(store.graph(), flat.view(), and),
        decreases flat.len() - index,
    );
    retaining?;
    proof! {
        test_lemma_retained_members(store.graph(), flat.view(), and);
        test_lemma_retention(store.graph(), flat.view(), kept.view(), and);
        test_lemma_filter_ordered(flat.view(), |id: TestId| !test_redundant_in(store.graph(), id, flat.view(), and), |id: TestId| id@);
        assert(kept.view() == test_retained(store.graph(), flat.view(), and));
        assert forall|i: int| 0 <= i < kept.view().len() implies kept.view()[i]@ < store.graph().tests.len() by {
            assert(kept.view().contains(kept.view()[i]));
            assert(flat.view().contains(kept.view()[i]));
            let j = choose|j: int| 0 <= j < flat.view().len() && flat.view()[j] == kept.view()[i];
        }
        assert forall|i: int, j: int| 0 <= i < j < model::test_ids(kept.view()).len()
            implies model::test_ids(kept.view())[i] < model::test_ids(kept.view())[j] by {
            assert(model::test_ids(kept.view())[i] == kept.view()[i]@);
            assert(model::test_ids(kept.view())[j] == kept.view()[j]@);
            assert((|id: TestId| id@)(kept.view()[i]) < (|id: TestId| id@)(kept.view()[j]));
        }
        if kept.len() == 1 {
            assert(kept.view() =~= seq![kept.view()[0]]);
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_combo(store.graph(), sym, theta, kept.view(), event, and)
                    == test_truth(store.graph(), sym, theta, kept.view()[0]@, event) by {
                test_lemma_combo_push(store.graph(), sym, theta, event, Seq::empty(), kept.view()[0], and);
            }
        }
        assert(test_ids_valid(store.graph(), kept.view()));
        assert(model::strictly_increasing(model::test_ids(kept.view())));
        test_lemma_constants_semantics(store.graph());
        assert(identity@ == if and { store.graph().constants.test_true } else { store.graph().constants.test_false });
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies test_combo(store.graph(), sym, theta, kept.view(), event, and)
                == test_combo(store.graph(), sym, theta, children@, event, and) by {}
    }
    if kept.is_empty() {
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                implies test_truth(store.graph(), sym, theta, identity@, event)
                    == test_combo(store.graph(), sym, theta, children@, event, and) by {}
        }
        Ok(identity)
    } else if kept.len() == 1 {
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                implies test_truth(store.graph(), sym, theta, kept.view()[0]@, event)
                    == test_combo(store.graph(), sym, theta, children@, event, and) by {}
        }
        test_at(&kept, 0)
    } else {
        test_intern_step(store, &kept, and)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(id) => id@ < final(store).graph().tests.len()
            && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> test_truth(final(store).graph(), sym, theta, id@, event)
                    == test_combo(final(store).graph(), sym, theta, children@, event, true)), Err(_) => true },
)]
pub(crate) fn test_and<G: KernelStore>(store: &mut G, children: &[TestId]) -> KernelResult<TestId> {
    test_connective(store, children, true)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(id) => id@ < final(store).graph().tests.len()
            && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> test_truth(final(store).graph(), sym, theta, id@, event)
                    == test_combo(final(store).graph(), sym, theta, children@, event, false)), Err(_) => true },
)]
pub(crate) fn test_or<G: KernelStore>(store: &mut G, children: &[TestId]) -> KernelResult<TestId> {
    test_connective(store, children, false)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), test_child_count(store.graph(), id, count as nat),
    ensures old(tasks).view().is_prefix_of(final(tasks).view()),
        forall|j: int| old(tasks).view().len() <= j < final(tasks).view().len()
            ==> #[trigger] final(tasks).view()[j].0@ < store.graph().tests.len()
                && !final(tasks).view()[j].1,
        match result {
            Ok(()) => test_schedule_extension(store.graph(), id, old(tasks).view(), final(tasks).view())
                && final(tasks).view().len() == old(tasks).view().len() + count
                && (forall|j: int| 0 <= j < count
                    ==> #[trigger] final(tasks).view()[old(tasks).view().len() + j].0@
                        == test_children(store.graph(), id)[count as int - 1 - j]),
            Err(_) => true,
        },
)]
fn schedule_test_children<G: KernelStore>(
    store: &G,
    id: TestId,
    count: usize,
    tasks: &mut WorkVec<(TestId, bool)>,
) -> KernelResult<()> {
    proof! { test_lemma_children(store.graph(), id, count as nat); }
    let mut failure = None;
    let mut remaining = count;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            model::graph_wf(store.graph()), test_child_count(store.graph(), id, count as nat),
            model::bounded(test_children(store.graph(), id), id@), test_children(store.graph(), id).len() == count,
            remaining <= count,
            old(tasks).view().is_prefix_of(tasks.view()),
            forall|j: int| old(tasks).view().len() <= j < tasks.view().len()
                ==> #[trigger] tasks.view()[j].0@ < store.graph().tests.len() && !tasks.view()[j].1,
            forall|j: int| #![trigger tasks.view()[j]] old(tasks).view().len() <= j < tasks.view().len()
                ==> !tasks.view()[j].1,
            failure is None ==> tasks.view().len() == old(tasks).view().len() + count - remaining
                && (forall|j: int| 0 <= j < count - remaining
                    ==> #[trigger] tasks.view()[old(tasks).view().len() + j].0@
                        == test_children(store.graph(), id)[count as int - 1 - j]),
        ensures failure.is_none() ==> remaining == 0,
        decreases remaining,
    ))]
    while remaining != 0 {
        let i = loop_try!(
            match remaining.checked_sub(1) {
                Some(value) => Ok(value),
                None => Err(invariant()),
            },
            failure
        );
        remaining = i;
        let child = loop_try!(test_child(store, id, i), failure);
        proof! { assert(child@ == test_children(store.graph(), id)[i as int]); }
        tasks.push((child, false));
    }
    if let Some(error) = failure {
        return Err(error);
    }
    proof! {
        assert forall|j: int| #![trigger tasks.view()[j]] old(tasks).view().len() <= j < tasks.view().len()
            implies !tasks.view()[j].1 by {
            assert(tasks.view()[j].0@ < store.graph().tests.len());
        }
        test_lemma_schedule_extension_intro(store.graph(), id, count as nat, old(tasks).view(), tasks.view());
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        count <= old(values).view().len(), test_ids_valid(old(store).graph(), old(values).view()),
        old(values).view().subrange(old(values).view().len() as int - count, old(values).view().len() as int).no_duplicates(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(()) => {
                let source = old(values).view().subrange(old(values).view().len() as int - count,
                    old(values).view().len() as int);
                &&& final(values).view().len() == old(values).view().len() - count + 1
                &&& final(values).view().drop_last() == old(values).view().subrange(0,
                    old(values).view().len() as int - count)
                &&& test_ids_valid(final(store).graph(), final(values).view())
                &&& exists|sorted: Seq<TestId>| sorted.to_multiset() == source.to_multiset()
                    && final(store).graph().tests[final(values).view().last()@ as int]
                        == if and { model::TestNode::And(model::test_ids(sorted)) }
                            else { model::TestNode::Or(model::test_ids(sorted)) }
                &&& forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                    test_truth(final(store).graph(), sym, theta, final(values).view().last()@, event)
                    == test_combo(final(store).graph(), sym, theta, source, event, and)
            },
            Err(_) => true,
        },
)]
fn finish_test_not<G: KernelStore>(
    store: &mut G,
    count: usize,
    and: bool,
    values: &mut WorkVec<TestId>,
) -> KernelResult<()> {
    proof_decl! { let ghost original = values.view(); }
    let start = match values.len().checked_sub(count) {
        Some(v) => v,
        None => return Err(invariant()),
    };
    let children = match values.as_mut_slice().get_mut(start..) {
        Some(v) => v,
        None => return Err(invariant()),
    };
    // De Morgan preserves every normalized reduction; only canonical ID ordering changes.
    children.sort_unstable();
    proof_decl! { let ghost sorted = children@; }
    proof! {
        let source = original.subrange(start as int, original.len() as int);
        lemma_multiset_members(source, sorted);
        source.lemma_multiset_has_no_duplicates();
        assert(sorted.no_duplicates()) by {
            sorted.lemma_multiset_has_no_duplicates_conv();
        }
        assert forall|i: int| 0 <= i < sorted.len() implies sorted[i]@ < store.graph().tests.len() by {
            assert(sorted.contains(sorted[i]));
            assert(source.contains(sorted[i]));
            let j = choose|j: int| 0 <= j < source.len() && source[j] == sorted[i];
            assert(original[start as int + j] == source[j]);
        }
        assert forall|i: int, j: int| 0 <= i < j < sorted.len() implies sorted[i]@ < sorted[j]@ by {
            assert(!(sorted[i].cmp_spec(&sorted[j]) is Greater));
            assert(sorted[i] != sorted[j]);
        }
        assert(test_ids_valid(store.graph(), sorted));
        assert(model::strictly_increasing(model::test_ids(sorted)));
        assert(model::test_node_wf(store.graph(), if and {
            model::TestNode::And(model::test_ids(sorted))
        } else { model::TestNode::Or(model::test_ids(sorted)) }));
    }
    let out = store.intern_test(if and {
        TestView::And(children)
    } else {
        TestView::Or(children)
    })?;
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_truth(store.graph(), sym, theta, out@, event)
                == test_combo(store.graph(), sym, theta,
                    original.subrange(start as int, original.len() as int), event, and) by {
            test_lemma_compound_semantics(store.graph(), sym, theta, event, out, sorted, and);
            test_lemma_combo_permutation(store.graph(), sym, theta, event,
                sorted, original.subrange(start as int, original.len() as int), and);
        }
    }
    values.truncate(start);
    values.push(out);
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        test_not_ready(old(store).graph(), id, finish, old(values).view()),
        forall|i: int| 0 <= i < old(tasks).view().len() ==> #[trigger] old(tasks).view()[i].0@ < old(store).graph().tests.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(()) => test_ids_valid(final(store).graph(), final(values).view())
                && test_not_effect(final(store).graph(), id, finish,
                    old(tasks).view(), old(values).view(), final(tasks).view(), final(values).view())
                && test_not_work(final(store).graph(), final(tasks).view())
                    < test_not_work(old(store).graph(), old(tasks).view().push((id, finish)))
                && (forall|root: TestId| test_not_state(old(store).graph(), old(tasks).view().push((id, finish)), old(values).view(), root)
                    ==> test_not_state(final(store).graph(), final(tasks).view(), final(values).view(), root)),
            Err(_) => true,
        },
)]
fn test_not_step<G: KernelStore>(
    store: &mut G,
    id: TestId,
    finish: bool,
    tasks: &mut WorkVec<(TestId, bool)>,
    values: &mut WorkVec<TestId>,
) -> KernelResult<()> {
    proof_decl! {
        let ghost before = store.graph();
        let ghost pending = tasks.view();
        let ghost prior_values = values.view();
    }
    proof! { test_lemma_not_constant_rows(store.graph()); }
    store.checkpoint()?;
    match test_head(store, id)? {
        TestHead::True => {
            values.push(store.constants().test_false);
            proof! {
                assert(values.view().drop_last() =~= prior_values);
                test_lemma_not_leaf_effect(store.graph(), id, pending, prior_values, values.view(), finish);
            }
        }
        TestHead::False => {
            values.push(store.constants().test_true);
            proof! {
                assert(values.view().drop_last() =~= prior_values);
                test_lemma_not_leaf_effect(store.graph(), id, pending, prior_values, values.view(), finish);
            }
        }
        TestHead::Atom(primitive, positive) => {
            values.push(store.intern_test(TestView::Atom {
                primitive,
                positive: !positive,
            })?);
            proof! {
                assert(before.tests[id@ as int] == store.graph().tests[id@ as int]);
                assert(values.view().drop_last() =~= prior_values);
                test_lemma_not_leaf_effect(store.graph(), id, pending, prior_values, values.view(), finish);
            }
        }
        TestHead::And(n) => {
            if finish {
                finish_test_not(store, n, false, values)?;
                proof! {
                    assert(before.tests[id@ as int] == store.graph().tests[id@ as int]);
                    test_lemma_not_finish_effect(store.graph(), id, pending, prior_values, values.view(), n as nat, false);
                }
            } else {
                tasks.push((id, true));
                proof_decl! { let ghost scheduled_base = tasks.view(); }
                schedule_test_children(store, id, n, tasks)?;
                proof! {
                    test_lemma_not_scheduled_extension(store.graph(), id, pending, scheduled_base, tasks.view(), prior_values);
                }
            }
        }
        TestHead::Or(n) => {
            if finish {
                finish_test_not(store, n, true, values)?;
                proof! {
                    assert(before.tests[id@ as int] == store.graph().tests[id@ as int]);
                    test_lemma_not_finish_effect(store.graph(), id, pending, prior_values, values.view(), n as nat, true);
                }
            } else {
                tasks.push((id, true));
                proof_decl! { let ghost scheduled_base = tasks.view(); }
                schedule_test_children(store, id, n, tasks)?;
                proof! {
                    test_lemma_not_scheduled_extension(store.graph(), id, pending, scheduled_base, tasks.view(), prior_values);
                }
            }
        }
    }
    proof! {
        test_lemma_not_step_post(before, store.graph(), id, finish, pending, prior_values, tasks.view(), values.view());
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), old(tasks).view().len() > 0,
        exists|root: TestId| test_not_state(old(store).graph(), old(tasks).view(), old(values).view(), root),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(()) => test_not_work(final(store).graph(), final(tasks).view())
                < test_not_work(old(store).graph(), old(tasks).view())
                && (forall|root: TestId| test_not_state(old(store).graph(), old(tasks).view(), old(values).view(), root)
                    ==> test_not_state(final(store).graph(), final(tasks).view(), final(values).view(), root)),
            Err(_) => true,
        },
)]
fn test_not_next<G: KernelStore>(
    store: &mut G,
    tasks: &mut WorkVec<(TestId, bool)>,
    values: &mut WorkVec<TestId>,
) -> KernelResult<()> {
    proof_decl! { let ghost pending = tasks.view(); }
    let (id, finish) = match tasks.pop() {
        Some(v) => v,
        None => return Err(invariant()),
    };
    proof! {
        assert(tasks.view().push((id, finish)) =~= pending);
        let root = choose|root: TestId| test_not_state(store.graph(), pending, values.view(), root);
        test_lemma_not_state_ready(store.graph(), tasks.view(), id, finish, values.view(), root);
        assert forall|i: int| 0 <= i < tasks.view().len() implies tasks.view()[i].0@ < store.graph().tests.len() by {
            assert(tasks.view()[i] == pending[i]);
        }
    }
    test_not_step(store, id, finish, tasks, values)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test@ < old(store).graph().tests.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().tests.len()
                && (forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                    test_truth(final(store).graph(), sym, theta, id@, event)
                        != test_truth(final(store).graph(), sym, theta, test@, event)),
            Err(_) => true,
        },
)]
pub(crate) fn test_not<G: KernelStore>(store: &mut G, test: TestId) -> KernelResult<TestId> {
    let mut tasks = WorkVec::new();
    let mut values = WorkVec::new();
    tasks.push((test, false));
    proof! { test_lemma_not_initial(store.graph(), test); }
    let mut state = Ok(());
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            store.restoration() == old(store).restoration(),
            model::graph_extends(old(store).graph(), store.graph()), model::graph_wf(store.graph()), store.valid_store(),
            state is Ok ==> test_not_state(store.graph(), tasks.view(), values.view(), test),
        decreases if state is Ok { test_not_work(store.graph(), tasks.view()) + 1 } else { 0 },
    ))]
    while !tasks.is_empty() && state.is_ok() {
        state = test_not_next(store, &mut tasks, &mut values);
    }
    state?;
    proof! { test_lemma_not_done(store.graph(), values.view(), test); }
    match values.pop() {
        Some(v) => Ok(v),
        None => Err(invariant()),
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        model::regex_node_wf(old(store).graph(), model::RegexNode { kind: kind@, nullable: n }),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && final(store).graph().regexes[id@ as int] == (model::RegexNode { kind: kind@, nullable: n })
                && model::lift_regex(final(store).graph(), id@) == regex_unbounded_kind(final(store).graph(), kind@),
            Err(_) => true,
        },
)]
fn intern_regex_step<G: KernelStore>(
    store: &mut G,
    kind: RegexKindView<'_>,
    n: bool,
) -> KernelResult<RegexId> {
    let id = store.intern_regex(kind, n)?;
    proof! { regex_unfold(store.graph(), id@); }
    Ok(id)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), regex@ < store.graph().regexes.len(),
    ensures match result {
        Ok(value) => value == language::nullable(model::lift_regex(store.graph(), regex@)),
        Err(_) => true,
    },
)]
pub(crate) fn nullable<G: KernelStore>(store: &G, regex: RegexId) -> KernelResult<bool> {
    proof! { regex_unfold(store.graph(), regex@); }
    Ok(store.regex(regex)?.nullable)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), test@ < old(store).graph().tests.len(),
        old(store).valid_store(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        model::graph_wf(final(store).graph()),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == (word.len() == 1 && model::test_holds(sym, theta,
                            model::lift_test(final(store).graph(), test@), word[0])),
            Err(_) => true,
        },
)]
pub(crate) fn regex_test<G: KernelStore>(store: &mut G, test: TestId) -> KernelResult<RegexId> {
    proof! { regex_constants(store.graph()); }
    store.checkpoint()?;
    if test == store.constants().test_false {
        Ok(store.constants().empty)
    } else {
        intern_regex_step(store, RegexKindView::Test(test), false)
    }
}
#[verus_verify]
#[verus_spec(result => ensures result == match head {
    RegexHead::Union(n) => if intersect { Some(n) } else { None },
    RegexHead::Intersect(n) => if !intersect { Some(n) } else { None },
    _ => None,
})]
fn dual_regex_count(head: RegexHead, intersect: bool) -> Option<usize> {
    match head {
        RegexHead::Union(n) if intersect => Some(n),
        RegexHead::Intersect(n) if !intersect => Some(n),
        _ => None,
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), parent@ < store.graph().regexes.len(),
        count == regex_children(store.graph(), parent@).len(),
        model::strictly_increasing(regex_children(store.graph(), parent@)),
    ensures match result {
        Ok(found) => found == regex_children(store.graph(), parent@).contains(id@),
        Err(_) => true,
    },
)]
fn regex_contains<G: KernelStore>(
    store: &G,
    parent: RegexId,
    count: usize,
    id: RegexId,
) -> KernelResult<bool> {
    let mut low = 0;
    let mut high = count;
    let mut failure = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant low <= high <= count,
            model::graph_wf(store.graph()), parent@ < store.graph().regexes.len(),
            count == regex_children(store.graph(), parent@).len(), model::strictly_increasing(regex_children(store.graph(), parent@)),
            forall|i: int| 0 <= i < low ==> regex_children(store.graph(), parent@)[i] < id@,
            forall|i: int| high <= i < count ==> regex_children(store.graph(), parent@)[i] >= id@,
        ensures failure.is_none() ==> low == high,
        decreases high - low,
    ))]
    while low < high {
        let mid = loop_try!(midpoint(low, high), failure);
        let child = loop_try!(regex_child(store, parent, mid), failure);
        proof! { regex_child_exact(store.graph(), parent@, mid as nat, child@); }
        if child < id {
            low = mid.saturating_add(1)
        } else {
            high = mid
        }
    }
    if let Some(error) = failure {
        return Err(error);
    }
    if low < count {
        let child = regex_child(store, parent, low)?;
        proof! { regex_child_exact(store.graph(), parent@, low as nat, child@); }
        Ok(child == id)
    } else {
        Ok(false)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), a@ < store.graph().regexes.len(), b@ < store.graph().regexes.len(),
        a_count == regex_children(store.graph(), a@).len(), b_count == regex_children(store.graph(), b@).len(),
        model::strictly_increasing(regex_children(store.graph(), b@)),
    ensures match result {
        Ok(included) => included == (forall|i: int| 0 <= i < a_count
            ==> regex_children(store.graph(), b@).contains(regex_children(store.graph(), a@)[i])),
        Err(_) => true,
    },
)]
fn regex_subset<G: KernelStore>(
    store: &G,
    a: RegexId,
    a_count: usize,
    b: RegexId,
    b_count: usize,
) -> KernelResult<bool> {
    let mut included = true;
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= a_count,
            model::graph_wf(store.graph()), a@ < store.graph().regexes.len(), b@ < store.graph().regexes.len(),
            a_count == regex_children(store.graph(), a@).len(), b_count == regex_children(store.graph(), b@).len(),
            model::strictly_increasing(regex_children(store.graph(), b@)),
            included == (forall|j: int| 0 <= j < i
                ==> regex_children(store.graph(), b@).contains(regex_children(store.graph(), a@)[j])),
        ensures failure.is_none() ==> i == a_count,
        decreases a_count - i,
    ))]
    while i < a_count {
        let id = loop_try!(regex_child(store, a, i), failure);
        proof! { regex_child_exact(store.graph(), a@, i as nat, id@); }
        included &= loop_try!(regex_contains(store, b, b_count, id), failure);
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(included)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), inner@ < old(store).graph().regexes.len(),
        old(store).valid_store(),
        regex_ids_valid(old(store).graph(), siblings@), index < siblings.len(),
    ensures final(store).graph() == old(store).graph(),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(value) => value == (found || siblings@[index as int] == inner)
                && (found == siblings@.subrange(0, index as int).contains(inner)
                    ==> value == siblings@.subrange(0, index as int + 1).contains(inner)),
            Err(_) => true,
        },
)]
fn regex_complement_step<G: KernelStore>(
    store: &mut G,
    inner: RegexId,
    siblings: &[RegexId],
    index: usize,
    found: bool,
) -> KernelResult<bool> {
    proof! { regex_contains_prefix(siblings@, index as int, inner); }
    store.checkpoint()?;
    Ok(found || regex_at(siblings, index)? == inner)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), a@ < old(store).graph().regexes.len(),
        old(store).valid_store(),
        regex_ids_valid(old(store).graph(), siblings@),
    ensures final(store).graph() == old(store).graph(),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(found) => found == match old(store).graph().regexes[a@ as int].kind {
                model::RegexKindNode::Not(inner) => model::regex_ids(siblings@).contains(inner),
                _ => false,
            },
            Err(_) => true,
        },
)]
fn regex_has_complement<G: KernelStore>(
    store: &mut G,
    a: RegexId,
    siblings: &[RegexId],
) -> KernelResult<bool> {
    proof! { regex_unfold(store.graph(), a@); }
    store.checkpoint()?;
    if let RegexHead::Not(inner) = regex_head(store, a)? {
        proof! { regex_ids_contains(siblings@, inner); }
        let mut state = Ok(false);
        scan!(state,index,siblings.len(),state.is_ok(),prior=>regex_complement_step(store,inner,siblings,index,prior);
            invariant store.graph() == old(store).graph(), index <= siblings.len(),
                store.restoration() == old(store).restoration(),
                store.valid_store(), model::graph_wf(store.graph()), regex_ids_valid(store.graph(), siblings@),
                inner@ < store.graph().regexes.len(),
                match state { Ok(found) => found == siblings@.subrange(0, index as int).contains(inner), Err(_) => true },
            decreases siblings.len() - index,
        );
        proof! { assert(siblings@.subrange(0, siblings.len() as int) =~= siblings@); }
        state
    } else {
        Ok(false)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().regexes.len(), regex_ids_valid(old(store).graph(), siblings@), index < siblings.len(),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(value) => value == (redundant || regex_absorbed_by(final(store).graph(), a@, siblings@[index as int]@, intersect)),
            Err(_) => true,
        },
)]
fn regex_absorbed_step<G: KernelStore>(
    store: &mut G,
    a: RegexId,
    siblings: &[RegexId],
    index: usize,
    intersect: bool,
    mut redundant: bool,
) -> KernelResult<bool> {
    let b = regex_at(siblings, index)?;
    store.checkpoint()?;
    proof! {
        regex_children_count(store.graph(), a@);
        regex_children_count(store.graph(), b@);
    }
    if a != b {
        let av = regex_head(store, a)?;
        let bv = regex_head(store, b)?;
        if let Some(n) = dual_regex_count(av, intersect) {
            proof! { regex_dual_order(store.graph(), a@, intersect); }
            redundant |= match dual_regex_count(bv, intersect) {
                Some(m) => regex_subset(store, b, m, a, n)?,
                None => regex_contains(store, a, n, b)?,
            };
        }
    }
    Ok(redundant)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        a@ < old(store).graph().regexes.len(), regex_ids_valid(old(store).graph(), siblings@),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(value) => value == (exists|i: int| 0 <= i < siblings.len()
                && regex_absorbed_by(final(store).graph(), a@, siblings@[i]@, intersect)),
            Err(_) => true,
        },
)]
fn regex_absorbed<G: KernelStore>(
    store: &mut G,
    a: RegexId,
    siblings: &[RegexId],
    intersect: bool,
) -> KernelResult<bool> {
    let mut state = Ok(false);
    scan!(state,index,siblings.len(),state.is_ok(),prior=>regex_absorbed_step(store,a,siblings,index,intersect,prior);
        invariant store.graph() == old(store).graph(), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            a@ < store.graph().regexes.len(), regex_ids_valid(store.graph(), siblings@), index <= siblings.len(),
            match state { Ok(value) => value == (exists|i: int| 0 <= i < index
                && regex_absorbed_by(store.graph(), a@, siblings@[i]@, intersect)), Err(_) => true },
        decreases siblings.len() - index,
    );
    state
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), id@ < store.graph().regexes.len(),
        index < regex_children(store.graph(), id@).len(), regex_ids_valid(store.graph(), old(flat).view()),
    ensures regex_ids_valid(store.graph(), final(flat).view()),
        old(flat).view().is_prefix_of(final(flat).view()),
        match result {
            Ok(()) => model::regex_ids(final(flat).view())
                == model::regex_ids(old(flat).view()).push(regex_children(store.graph(), id@)[index as int]),
            Err(_) => final(flat).view() == old(flat).view(),
        },
)]
fn collect_regex_child_step<G: KernelStore>(
    store: &G,
    id: RegexId,
    index: usize,
    flat: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    let child = regex_child(store, id, index)?;
    proof! { regex_child_exact(store.graph(), id@, index as nat, child@); }
    flat.push(child);
    proof! {
        regex_ids_push(flat.view().drop_last(), child);
        assert(flat.view() == flat.view().drop_last().push(child));
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), id@ < store.graph().regexes.len(),
        count == regex_children(store.graph(), id@).len(), regex_ids_valid(store.graph(), old(flat).view()),
    ensures regex_ids_valid(store.graph(), final(flat).view()),
        old(flat).view().is_prefix_of(final(flat).view()),
        match result {
            Ok(()) => model::regex_ids(final(flat).view())
                == model::regex_ids(old(flat).view()) + regex_children(store.graph(), id@),
            Err(_) => true,
        },
)]
fn collect_regex_children<G: KernelStore>(
    store: &G,
    id: RegexId,
    count: usize,
    flat: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    proof! { regex_children_wf(store.graph(), id@); }
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= count, regex_ids_valid(store.graph(), flat.view()),
            model::graph_wf(store.graph()), id@ < store.graph().regexes.len(),
            count == regex_children(store.graph(), id@).len(), regex_ids_valid(store.graph(), old(flat).view()),
            old(flat).view().is_prefix_of(flat.view()),
            model::regex_ids(flat.view()) == model::regex_ids(old(flat).view())
                + regex_children(store.graph(), id@).subrange(0, i as int),
        ensures failure.is_none() ==> i == count,
        decreases count - i,
    ))]
    while i < count {
        loop_try!(collect_regex_child_step(store, id, i, flat), failure);
        proof! {
            assert(regex_children(store.graph(), id@).subrange(0, i as int + 1)
                =~= regex_children(store.graph(), id@).subrange(0, i as int).push(regex_children(store.graph(), id@)[i as int]));
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    proof! {
        assert(i == count);
        assert(model::regex_ids(flat.view()) == model::regex_ids(old(flat).view())
            + regex_children(store.graph(), id@).subrange(0, i as int));
        assert(regex_children(store.graph(), id@).subrange(0, count as int) =~= regex_children(store.graph(), id@));
    }
    Ok(())
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
struct RegexMode {
    intersect: bool,
    identity: RegexId,
    absorber: RegexId,
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), regex_mode_wf(old(store).graph(), mode@),
        regex_ids_valid(old(store).graph(), children@), index < children.len(), regex_ids_valid(old(store).graph(), old(flat).view()),
        regex_equivalent(old(store).graph(), old(flat).view(), children@.subrange(0, index as int), mode.intersect),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        regex_ids_valid(final(store).graph(), final(flat).view()), old(flat).view().is_prefix_of(final(flat).view()),
        match result {
            Ok(absorbed) => absorbed == (children@[index as int] == mode.absorber)
                && (!absorbed ==> model::regex_ids(final(flat).view()) == model::regex_ids(old(flat).view())
                    + regex_set_piece(final(store).graph(), children@[index as int]@, mode@))
                && (!absorbed ==> regex_equivalent(final(store).graph(), final(flat).view(), children@.subrange(0, index as int + 1), mode.intersect)),
            Err(_) => true,
        },
)]
fn collect_regex_step<G: KernelStore>(
    store: &mut G,
    children: &[RegexId],
    index: usize,
    mode: RegexMode,
    flat: &mut WorkVec<RegexId>,
) -> KernelResult<bool> {
    let id = regex_at(children, index)?;
    store.checkpoint()?;
    proof! { regex_children_count(store.graph(), id@); }
    if id == mode.absorber {
        return Ok(true);
    }
    if id != mode.identity {
        match regex_head(store, id)? {
            RegexHead::Union(n) if !mode.intersect => {
                collect_regex_children(store, id, n, flat)?;
                proof! { assert(regex_set_piece(store.graph(), id@, mode@) == regex_children(store.graph(), id@)); }
            }
            RegexHead::Intersect(n) if mode.intersect => {
                collect_regex_children(store, id, n, flat)?;
                proof! { assert(regex_set_piece(store.graph(), id@, mode@) == regex_children(store.graph(), id@)); }
            }
            _ => {
                flat.push(id);
                proof! {
                    regex_ids_push(old(flat).view(), id);
                    assert(regex_set_piece(store.graph(), id@, mode@) == seq![id@]);
                }
            }
        }
    }
    proof! {
        assert(model::regex_ids(old(flat).view()).push(id@) =~= model::regex_ids(old(flat).view()) + seq![id@]);
        assert(model::regex_ids(old(flat).view()) + Seq::<nat>::empty() =~= model::regex_ids(old(flat).view()));
        regex_collect_preserves(store.graph(), id, old(flat).view(), flat.view(), mode@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            implies regex_combo(store.graph(), sym, theta, flat.view(), word, mode.intersect)
                == regex_combo(store.graph(), sym, theta, children@.subrange(0, index as int + 1), word, mode.intersect) by {
            regex_combo_push(store.graph(), old(flat).view(), id, sym, theta, word, mode.intersect);
            regex_combo_prefix(store.graph(), children@, index as int, sym, theta, word, mode.intersect);
        }
    }
    Ok(false)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), regex_ids_valid(old(store).graph(), flat@),
        index < flat.len(), test_ids_valid(old(store).graph(), old(tests).view()), regex_ids_valid(old(store).graph(), old(others).view()),
        regex_split_prefix(old(store).graph(), flat@, old(tests).view(), old(others).view(), index as nat),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        test_ids_valid(final(store).graph(), final(tests).view()), regex_ids_valid(final(store).graph(), final(others).view()),
        match result {
            Ok(()) => (match final(store).graph().regexes[flat@[index as int]@ as int].kind {
                model::RegexKindNode::Test(t) => model::test_ids(final(tests).view()) == model::test_ids(old(tests).view()).push(t)
                    && final(others).view() == old(others).view(),
                _ => final(tests).view() == old(tests).view() && final(others).view() == old(others).view().push(flat@[index as int]),
            }) && regex_split_prefix(final(store).graph(), flat@, final(tests).view(), final(others).view(), index as nat + 1),
            Err(_) => final(tests).view() == old(tests).view() && final(others).view() == old(others).view(),
        },
)]
fn split_regex_step<G: KernelStore>(
    store: &mut G,
    flat: &[RegexId],
    index: usize,
    tests: &mut WorkVec<TestId>,
    others: &mut WorkVec<RegexId>,
) -> KernelResult<()> {
    store.checkpoint()?;
    let id = regex_at(flat, index)?;
    proof! { model::lemma_graph_regex_wf(store.graph(), id@); }
    match regex_head(store, id)? {
        RegexHead::Test(t) => {
            tests.push(t);
            proof! { regex_test_ids_push(old(tests).view(), t); }
        }
        _ => others.push(id),
    }
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>, intersect: bool|
            regex_group_combo(store.graph(), sym, theta, tests.view(), others.view(), word, intersect)
                == regex_combo(store.graph(), sym, theta, flat@.subrange(0, index as int + 1), word, intersect) by {
            regex_split_preserves(store.graph(), id, old(tests).view(), old(others).view(), tests.view(), others.view(), intersect);
            regex_combo_prefix(store.graph(), flat@, index as int, sym, theta, word, intersect);
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
struct RegexStats {
    all_nullable: bool,
    any_nullable: bool,
    epsilon: bool,
    complement: bool,
    has_nonnullable: bool,
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), regex_ids_valid(old(store).graph(), ids@), index < ids.len(),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(next) => next@ == regex_stats_update(final(store).graph(), ids@, index as int, epsilon, stats@, complements)
            && (regex_stats_prefix(old(store).graph(), ids@, index as nat, epsilon, stats@, complements)
                ==> regex_stats_prefix(final(store).graph(), ids@, index as nat + 1, epsilon, next@, complements)), Err(_) => true },
)]
fn regex_stats_step<G: KernelStore>(
    store: &mut G,
    ids: &[RegexId],
    index: usize,
    epsilon: RegexId,
    complements: bool,
    mut stats: RegexStats,
) -> KernelResult<RegexStats> {
    proof! {
        if regex_stats_prefix(store.graph(), ids@, index as nat, epsilon, stats@, complements) {
            regex_stats_prefix_step(store.graph(), ids@, index as int, epsilon, stats@, complements);
        }
    }
    store.checkpoint()?;
    let id = regex_at(ids, index)?;
    let n = nullable(store, id)?;
    stats.all_nullable &= n;
    stats.any_nullable |= id != epsilon && n;
    stats.epsilon |= id == epsilon;
    let head = regex_head(store, id)?;
    if !n {
        match head {
            RegexHead::Not(inner) if inner == epsilon => {}
            _ => stats.has_nonnullable = true,
        }
    }
    if complements {
        stats.complement |= regex_has_complement(store, id, ids)?;
    }
    Ok(stats)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), regex_ids_valid(old(store).graph(), old(ids).view()),
        index < old(ids).view().len(),
        model::strictly_increasing(model::regex_ids(old(ids).view())),
    ensures final(store).graph() == old(store).graph(), final(store).valid_store(), regex_ids_valid(final(store).graph(), final(ids).view()),
        final(store).restoration() == old(store).restoration(),
        model::strictly_increasing(model::regex_ids(final(ids).view())),
        match result {
            Ok(removed) => final(ids).view() == (if removed { old(ids).view().remove(index as int) } else { old(ids).view() })
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> regex_combo(final(store).graph(), sym, theta, final(ids).view(), word, mode.intersect)
                        == regex_combo(final(store).graph(), sym, theta, old(ids).view(), word, mode.intersect),
            Err(_) => final(ids).view() == old(ids).view(),
        },
)]
fn retain_regex_step<G: KernelStore>(
    store: &mut G,
    ids: &mut WorkVec<RegexId>,
    index: usize,
    mode: RegexMode,
) -> KernelResult<bool> {
    store.checkpoint()?;
    let id = regex_at(ids, index)?;
    let epsilon = store.constants().epsilon;
    let mut stats = Ok(RegexStats {
        all_nullable: true,
        any_nullable: false,
        epsilon: false,
        complement: false,
        has_nonnullable: false,
    });
    scan!(stats,scan_index,ids.len(),stats.is_ok(),prior=>regex_stats_step(store,ids,scan_index,epsilon,false,prior);
        invariant store.graph() == old(store).graph(), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            ids.view() == old(ids).view(), regex_ids_valid(store.graph(), ids.view()), scan_index <= ids.len(),
            match stats { Ok(value) => regex_stats_prefix(store.graph(), ids.view(), scan_index as nat, epsilon, value@, false), Err(_) => true },
        decreases ids.len() - scan_index,
    );
    let stats = stats?;
    let head = regex_head(store, id)?;
    let redundant = (!mode.intersect && id == epsilon && stats.any_nullable)
        || (mode.intersect
            && stats.has_nonnullable
            && matches!(head,RegexHead::Not(inner) if inner==epsilon));
    let absorbed = regex_absorbed(store, id, ids, mode.intersect)?;
    if redundant || absorbed {
        proof! {
            regex_retention_remove(store.graph(), ids.view(), index as int, mode@, epsilon, stats@);
            regex_remove_strict(ids.view(), index as int);
            assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies regex_combo(store.graph(), sym, theta, ids.view().remove(index as int), word, mode.intersect)
                    == regex_combo(store.graph(), sym, theta, ids.view(), word, mode.intersect) by {
                assert(mode@.intersect == mode.intersect);
            }
        }
        ids.remove(index);
        Ok(true)
    } else {
        Ok(false)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), regex_ids_valid(store.graph(), ids@), index < ids.len(),
    ensures match result {
        Ok(value) => value == (if and { prior && language::nullable(model::lift_regex(store.graph(), ids@[index as int]@)) }
            else { prior || language::nullable(model::lift_regex(store.graph(), ids@[index as int]@)) })
            && (prior == regex_nullable_combo(store.graph(), ids@.subrange(0, index as int), and)
                ==> value == regex_nullable_combo(store.graph(), ids@.subrange(0, index as int + 1), and)),
        Err(_) => true,
    },
)]
fn nullable_step<G: KernelStore>(
    store: &G,
    ids: &[RegexId],
    index: usize,
    and: bool,
    prior: bool,
) -> KernelResult<bool> {
    proof! { regex_nullable_prefix(store.graph(), ids@, index as int, and); }
    let n = nullable(store, regex_at(ids, index)?)?;
    Ok(if and { prior && n } else { prior || n })
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), test_ids_valid(old(store).graph(), tests@), tests.len() > 0,
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result { Ok(id) => id@ < final(store).graph().regexes.len()
            && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                    == regex_test_combo(final(store).graph(), sym, theta, tests@, word, intersect), Err(_) => true },
)]
fn regex_group_test_step<G: KernelStore>(
    store: &mut G,
    tests: &[TestId],
    intersect: bool,
) -> KernelResult<RegexId> {
    let test = test_connective(store, tests, intersect)?;
    proof_decl! { let ghost test_graph = store.graph(); }
    proof! {
        assert forall|next: model::Graph| model::graph_extends(test_graph, next)
            implies forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> model::test_holds(sym, theta, model::lift_test(next, test@), event)
                    == test_combo(next, sym, theta, tests@, event, intersect) by {
            regex_test_connective_extends(test_graph, next, tests@, test, intersect);
        }
    }
    let id = regex_test(store, test)?;
    Ok(id)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), regex_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len() && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
                model::symbols_wf(sym) ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                    == regex_combo(final(store).graph(), sym, theta, children@, word, intersect),
            Err(_) => true,
        },
)]
fn regex_set<G: KernelStore>(
    store: &mut G,
    children: &[RegexId],
    intersect: bool,
) -> KernelResult<RegexId> {
    let c = store.constants();
    proof! { regex_constants(store.graph()); }
    let identity = if intersect { c.all } else { c.empty };
    let absorber = if intersect { c.empty } else { c.all };
    let mode = RegexMode {
        intersect,
        identity,
        absorber,
    };
    let mut flat = WorkVec::new();
    let mut collecting = Ok(false);
    scan!(collecting,index,children.len(),matches!(collecting,Ok(false)),_prior=>collect_regex_step(store,children,index,mode,&mut flat);
        invariant store.graph() == old(store).graph(), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            regex_mode_wf(store.graph(), mode@), regex_ids_valid(store.graph(), children@), regex_ids_valid(store.graph(), flat.view()), index <= children.len(),
            mode.intersect == intersect, mode.absorber == absorber,
            match collecting {
                Ok(false) => regex_equivalent(store.graph(), flat.view(), children@.subrange(0, index as int), intersect),
                Ok(true) => exists|i: int| 0 <= i < index && children@[i] == absorber,
                Err(_) => true,
            },
        decreases children.len() - index,
    );
    if collecting? {
        proof! {
            let i = choose|i: int| 0 <= i < children.len() && children@[i] == absorber;
            regex_absorber_member(store.graph(), children@, i, mode@);
        }
        return Ok(absorber);
    }
    proof! { assert(children@.subrange(0, children.len() as int) =~= children@); }
    let mut tests = WorkVec::new();
    let mut others = WorkVec::new();
    let mut splitting = Ok(());
    scan!(splitting,index,flat.len(),splitting.is_ok(),_prior=>split_regex_step(store,&flat,index,&mut tests,&mut others);
        invariant store.graph() == old(store).graph(), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            regex_ids_valid(store.graph(), flat.view()), regex_ids_valid(store.graph(), children@),
            regex_equivalent(store.graph(), flat.view(), children@, intersect),
            test_ids_valid(store.graph(), tests.view()), regex_ids_valid(store.graph(), others.view()), index <= flat.len(),
            match splitting { Ok(()) => regex_split_prefix(store.graph(), flat.view(), tests.view(), others.view(), index as nat), Err(_) => true },
        decreases flat.len() - index,
    );
    splitting?;
    proof_decl! { let ghost grouped_graph = store.graph(); let ghost grouped_others = others.view(); }
    proof! {
        assert(flat.view().subrange(0, flat.view().len() as int) =~= flat.view());
        regex_group_equivalence_extends(grouped_graph, grouped_graph, children@, tests.view(), grouped_others, intersect);
        assert forall|next: model::Graph| model::graph_extends(grouped_graph, next)
            implies forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> regex_group_combo(next, sym, theta, tests.view(), grouped_others, word, intersect)
                    == regex_combo(next, sym, theta, children@, word, intersect) by {
            regex_group_equivalence_extends(grouped_graph, next, children@, tests.view(), grouped_others, intersect);
        }
    }
    if !tests.is_empty() {
        let r = regex_group_test_step(store, &tests, intersect)?;
        proof! {
            regex_constants(store.graph());
            assert(model::graph_extends(grouped_graph, store.graph()));
            regex_group_equivalence_extends(grouped_graph, store.graph(), children@, tests.view(), grouped_others, intersect);
            assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies model::regex_lang(store.graph(), sym, theta, r@, word)
                    == regex_test_combo(store.graph(), sym, theta, tests.view(), word, intersect) by {};
        }
        if intersect && r == c.empty {
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    implies !regex_combo(store.graph(), sym, theta, children@, word, intersect) by {
                    assert(regex_group_combo(store.graph(), sym, theta, tests.view(), grouped_others, word, intersect)
                        == regex_combo(store.graph(), sym, theta, children@, word, intersect));
                    assert(!model::regex_lang(store.graph(), sym, theta, r@, word));
                }
            }
            return Ok(c.empty);
        }
        if r != c.empty {
            others.push(r);
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    implies regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                        == regex_combo(store.graph(), sym, theta, children@, word, intersect) by {
                    regex_combo_push(store.graph(), grouped_others, r, sym, theta, word, intersect);
                    assert(regex_group_combo(store.graph(), sym, theta, tests.view(), grouped_others, word, intersect)
                        == regex_combo(store.graph(), sym, theta, children@, word, intersect));
                }
            }
        }
        proof! {
            if r == c.empty {
                assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    implies regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                        == regex_combo(store.graph(), sym, theta, children@, word, intersect) by {
                    assert(!intersect);
                    assert(!model::regex_lang(store.graph(), sym, theta, r@, word));
                    assert(regex_group_combo(store.graph(), sym, theta, tests.view(), grouped_others, word, intersect)
                        == regex_combo(store.graph(), sym, theta, children@, word, intersect));
                }
            }
        }
    }
    proof! {
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            implies regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                == regex_combo(store.graph(), sym, theta, children@, word, intersect) by {
            assert(regex_group_combo(store.graph(), sym, theta, tests.view(), grouped_others, word, intersect)
                == regex_combo(store.graph(), sym, theta, children@, word, intersect));
        }
    }
    proof_decl! { let ghost unsorted = others.view(); }
    others.as_mut_slice().sort_unstable();
    proof! {
        regex_multiset_members(unsorted, others.view());
        regex_member_ids_valid(store.graph(), unsorted, others.view());
        regex_combo_permutation(store.graph(), unsorted, others.view(), intersect);
        assert forall|i: int, j: int| 0 <= i < j < others.view().len() implies others.view()[i]@ <= others.view()[j]@ by {
            assert(!(OrdSpec::cmp_spec(&others.view()[i], &others.view()[j]) is Greater));
            assert(others.view()[i].0 <= others.view()[j].0);
        }
    }
    proof_decl! { let ghost sorted = others.view(); }
    dedup_ids(&mut others)?;
    proof! {
        regex_member_ids_valid(store.graph(), sorted, others.view());
        regex_combo_members(store.graph(), sorted, others.view(), intersect);
        regex_dedup_strict(sorted, others.view());
    }
    let mut stats = Ok(RegexStats {
        all_nullable: true,
        any_nullable: false,
        epsilon: false,
        complement: false,
        has_nonnullable: false,
    });
    scan!(stats,index,others.len(),stats.is_ok(),prior=>regex_stats_step(store,&others,index,c.epsilon,true,prior);
        invariant model::graph_extends(old(store).graph(), store.graph()), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            store.graph().constants == c@, regex_ids_valid(store.graph(), others.view()), regex_ids_valid(store.graph(), children@),
            regex_equivalent(store.graph(), others.view(), children@, intersect), model::strictly_increasing(model::regex_ids(others.view())), index <= others.len(),
            match stats { Ok(value) => regex_stats_prefix(store.graph(), others.view(), index as nat, c.epsilon, value@, true), Err(_) => true },
        decreases others.len() - index,
    );
    let stats = stats?;
    proof! {
        regex_constants(store.graph());
        regex_stats_decisions(store.graph(), others.view(), c.epsilon, stats@, intersect);
    }
    if stats.complement {
        return Ok(absorber);
    }
    if intersect && stats.epsilon {
        return Ok(if stats.all_nullable {
            c.epsilon
        } else {
            c.empty
        });
    }
    let mut index = 0;
    let mut failure = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant model::graph_extends(old(store).graph(), store.graph()), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            regex_ids_valid(store.graph(), others.view()), index <= others.len(),
            mode.intersect == intersect, regex_ids_valid(store.graph(), children@),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                    == regex_combo(store.graph(), sym, theta, children@, word, intersect),
            model::strictly_increasing(model::regex_ids(others.view())),
        decreases others.len() - index,
    ))]
    while index < others.len() {
        proof_decl! { let ghost previous = others.view(); }
        let removed = loop_try!(retain_regex_step(store, &mut others, index, mode), failure);
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                    == regex_combo(store.graph(), sym, theta, children@, word, intersect) by {
                assert(regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                    == regex_combo(store.graph(), sym, theta, previous, word, intersect));
            }
        }
        if !removed {
            index = index.saturating_add(1);
        }
    }
    if let Some(error) = failure {
        return Err(error);
    }
    let mut n = Ok(intersect);
    scan!(n,index,others.len(),n.is_ok(),prior=>nullable_step(store,&others,index,intersect,prior);
        invariant model::graph_extends(old(store).graph(), store.graph()), store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            regex_ids_valid(store.graph(), others.view()), regex_ids_valid(store.graph(), children@),
            regex_equivalent(store.graph(), others.view(), children@, intersect), model::strictly_increasing(model::regex_ids(others.view())), index <= others.len(),
            match n { Ok(value) => value == regex_nullable_combo(store.graph(), others.view().subrange(0, index as int), intersect), Err(_) => true },
        decreases others.len() - index,
    );
    let n = n?;
    proof! {
        regex_constants(store.graph());
        assert(others.view().subrange(0, others.view().len() as int) =~= others.view());
        regex_set_node_wf(store.graph(), others.view(), n, intersect);
        regex_set_result(store.graph(), others.view(), children@, intersect);
        assert forall|next: model::Graph| model::graph_extends(store.graph(), next)
            implies regex_equivalent(next, others.view(), children@, intersect) by {
            regex_equivalence_extends(store.graph(), next, others.view(), children@, intersect);
        }
    }
    if others.is_empty() {
        Ok(identity)
    } else if others.len() == 1 {
        regex_at(&others, 0)
    } else {
        let id = intern_regex_step(
            store,
            if intersect {
                RegexKindView::Intersect(&others)
            } else {
                RegexKindView::Union(&others)
            },
            n,
        )?;
        proof! {
            assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies model::regex_lang(store.graph(), sym, theta, id@, word)
                    == regex_combo(store.graph(), sym, theta, children@, word, intersect) by {
                regex_node_language(store.graph(), id@, sym, theta, word);
                regex_combo_ids(store.graph(), others.view(), sym, theta, word, intersect);
                assert(model::regex_lang(store.graph(), sym, theta, id@, word)
                    == regex_combo_nats(store.graph(), sym, theta, model::regex_ids(others.view()), word, intersect));
                assert(regex_combo(store.graph(), sym, theta, others.view(), word, intersect)
                    == regex_combo(store.graph(), sym, theta, children@, word, intersect));
            }
        }
        Ok(id)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), regex_ids_valid(old(store).graph(), children@),
        old(store).valid_store(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == regex_combo(final(store).graph(), sym, theta, children@, word, false),
            Err(_) => true,
        },
)]
pub(crate) fn regex_union<G: KernelStore>(
    store: &mut G,
    children: &[RegexId],
) -> KernelResult<RegexId> {
    regex_set(store, children, false)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), regex_ids_valid(old(store).graph(), children@),
        old(store).valid_store(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == regex_combo(final(store).graph(), sym, theta, children@, word, true),
            Err(_) => true,
        },
)]
pub(crate) fn regex_intersect<G: KernelStore>(
    store: &mut G,
    children: &[RegexId],
) -> KernelResult<RegexId> {
    regex_set(store, children, true)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), regex_ids_valid(old(store).graph(), ids@), index < ids.len(),
        old(store).valid_store(),
        regex_ids_valid(old(store).graph(), old(flat).view()),
        model::regex_ids(old(flat).view()) == regex_concat_flat(old(store).graph(), ids@.subrange(0, index as int)),
    ensures final(store).graph() == old(store).graph(),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        regex_ids_valid(final(store).graph(), final(flat).view()),
        old(flat).view().is_prefix_of(final(flat).view()),
        match result {
            Ok(absorbed) => absorbed == (old(store).graph().regexes[ids@[index as int]@ as int].kind == model::RegexKindNode::Empty)
                && (!absorbed ==> model::regex_ids(final(flat).view()) == model::regex_ids(old(flat).view())
                    + regex_concat_piece(final(store).graph(), ids@[index as int]@)
                    && model::regex_ids(final(flat).view()) == regex_concat_flat(final(store).graph(), ids@.subrange(0, index as int + 1))),
            Err(_) => true,
        },
)]
fn concat_collect_step<G: KernelStore>(
    store: &mut G,
    ids: &[RegexId],
    index: usize,
    flat: &mut WorkVec<RegexId>,
) -> KernelResult<bool> {
    proof! { regex_concat_flat_prefix(store.graph(), ids@, index as int); }
    store.checkpoint()?;
    let id = regex_at(ids, index)?;
    match regex_head(store, id)? {
        RegexHead::Empty => Ok(true),
        RegexHead::Epsilon => Ok(false),
        RegexHead::Concat(n) => {
            proof! { regex_children_count(store.graph(), id@); }
            collect_regex_children(store, id, n, flat)?;
            Ok(false)
        }
        _ => {
            flat.push(id);
            Ok(false)
        }
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), regex_ids_valid(old(store).graph(), children@),
        old(store).valid_store(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == concat_combo(final(store).graph(), sym, theta, children@, word),
            Err(_) => true,
        },
)]
pub(crate) fn regex_concat<G: KernelStore>(
    store: &mut G,
    children: &[RegexId],
) -> KernelResult<RegexId> {
    let c = store.constants();
    proof! { regex_constants(store.graph()); }
    let mut flat = WorkVec::new();
    let mut collecting = Ok(false);
    scan!(collecting,index,children.len(),matches!(collecting,Ok(false)),_prior=>concat_collect_step(store,children,index,&mut flat);
        invariant store.graph() == old(store).graph(), index <= children.len(),
            store.restoration() == old(store).restoration(),
            store.valid_store(),
            model::graph_wf(store.graph()), regex_ids_valid(store.graph(), children@),
            regex_ids_valid(store.graph(), flat.view()),
            match collecting {
                Ok(false) => model::regex_ids(flat.view()) == regex_concat_flat(store.graph(), children@.subrange(0, index as int)),
                Ok(true) => exists|i: int| 0 <= i < index
                    && store.graph().regexes[children@[i]@ as int].kind == model::RegexKindNode::Empty,
                Err(_) => true,
            },
        decreases children.len() - index,
    );
    if collecting? {
        proof! {
            let i = choose|i: int| 0 <= i < children.len()
                && store.graph().regexes[children@[i]@ as int].kind == model::RegexKindNode::Empty;
            regex_concat_absorber(store.graph(), children@, i);
        }
        return Ok(c.empty);
    }
    proof! {
        assert(children@.subrange(0, children@.len() as int) =~= children@);
        assert(model::regex_ids(flat.view()) == regex_concat_flat(store.graph(), children@));
    }
    let mut n = Ok(true);
    scan!(n,index,flat.len(),n.is_ok(),prior=>nullable_step(store,&flat,index,true,prior);
        invariant store.graph() == old(store).graph(), index <= flat.len(),
            store.restoration() == old(store).restoration(),
            store.valid_store(),
            model::graph_wf(store.graph()), regex_ids_valid(store.graph(), children@),
            regex_ids_valid(store.graph(), flat.view()),
            model::regex_ids(flat.view()) == regex_concat_flat(store.graph(), children@),
            match n { Ok(value) => value == regex_nullable_combo(store.graph(), flat.view().subrange(0, index as int), true), Err(_) => true },
        decreases flat.len() - index,
    );
    let n = n?;
    proof! {
        assert(flat.view().subrange(0, flat.view().len() as int) =~= flat.view());
        assert(n == regex_nullable_combo(store.graph(), flat.view(), true));
        regex_concat_node_wf(store.graph(), flat.view(), n);
        assert forall|next: model::Graph| model::graph_extends(store.graph(), next)
            implies forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
                concat_combo(next, sym, theta, flat.view(), word) == concat_combo(next, sym, theta, children@, word) by {
            regex_concat_normalization_extends(store.graph(), next, children@, flat.view());
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            concat_combo(store.graph(), sym, theta, flat.view(), word)
                == concat_combo(store.graph(), sym, theta, children@, word) by {
            regex_concat_flat_law(store.graph(), children@, sym, theta, word);
        }
        assert(model::lift_regexes_bounded(store.graph(), model::regex_ids(flat.view()), store.graph().regexes.len())
            =~= model::lift_regexes(store.graph(), model::regex_ids(flat.view())));
        assert(model::regex_node_wf(store.graph(), model::RegexNode { kind: model::RegexKindNode::Concat(model::regex_ids(flat.view())), nullable: n }));
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            flat.view().len() == 0 implies concat_combo(store.graph(), sym, theta, children@, word) == (word.len() == 0) by {
            regex_concat_empty::<model::Test>(model::gsem(sym, theta), word);
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            flat.view().len() == 1 implies concat_combo(store.graph(), sym, theta, children@, word)
                == model::regex_lang(store.graph(), sym, theta, flat.view()[0]@, word) by {
            if flat.view().len() == 1 {
                assert(model::lift_regexes(store.graph(), model::regex_ids(flat.view())) =~= seq![model::lift_regex(store.graph(), flat.view()[0]@)]);
                language::lemma_concat_singleton(model::gsem(sym, theta), model::lift_regex(store.graph(), flat.view()[0]@), word);
            }
        }
    }
    if flat.is_empty() {
        Ok(c.epsilon)
    } else if flat.len() == 1 {
        regex_at(&flat, 0)
    } else {
        intern_regex_step(store, RegexKindView::Concat(&flat), n)
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), regex@ < old(store).graph().regexes.len(),
        old(store).valid_store(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(
                            model::lift_regex(final(store).graph(), regex@))), word),
            Err(_) => true,
        },
)]
pub(crate) fn regex_star<G: KernelStore>(store: &mut G, regex: RegexId) -> KernelResult<RegexId> {
    proof! {
        regex_unfold(store.graph(), regex@);
        regex_constants(store.graph());
        regex_star_laws(store.graph(), regex@);
    }
    store.checkpoint()?;
    let c = store.constants();
    match regex_head(store, regex)? {
        RegexHead::Empty | RegexHead::Epsilon => Ok(c.epsilon),
        RegexHead::All => Ok(c.all),
        RegexHead::Test(t) if t == c.test_true => Ok(c.all),
        RegexHead::Star(_) => Ok(regex),
        _ => intern_regex_step(store, RegexKindView::Star(regex), true),
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), regex@ < old(store).graph().regexes.len(),
        old(store).valid_store(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().regexes.len()
                && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                    ==> model::regex_lang(final(store).graph(), sym, theta, id@, word)
                        == !model::regex_lang(final(store).graph(), sym, theta, regex@, word),
            Err(_) => true,
        },
)]
pub(crate) fn regex_not<G: KernelStore>(store: &mut G, regex: RegexId) -> KernelResult<RegexId> {
    proof! {
        regex_unfold(store.graph(), regex@);
        regex_constants(store.graph());
    }
    store.checkpoint()?;
    let c = store.constants();
    match regex_head(store, regex)? {
        RegexHead::Empty => Ok(c.all),
        RegexHead::All => Ok(c.empty),
        RegexHead::Not(inner) => Ok(inner),
        _ => {
            let n = !nullable(store, regex)?;
            intern_regex_step(store, RegexKindView::Not(regex), n)
        }
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        model::transition_node_wf(old(store).graph(), node@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().transitions.len()
                && final(store).graph().transitions[id@ as int] == node@
                && model::lift_transition(final(store).graph(), id@)
                    == transition_unbounded_node(final(store).graph(), node@)
                && tdepth(final(store).graph(), id@) == tdepth_node(final(store).graph(), node@),
            Err(_) => true,
        },
)]
fn intern_transition_step<G: KernelStore>(
    store: &mut G,
    node: TransitionView<'_>,
) -> KernelResult<TransitionId> {
    let id = store.intern_transition(node)?;
    proof! { transition_unfold(store.graph(), id@); tdepth_lemma_unfold(store.graph(), id@); }
    Ok(id)
}

#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), regex@ < old(store).graph().regexes.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().transitions.len()
                && final(store).graph().transitions[id@ as int] is Const
                && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> transition_lang(final(store).graph(), sym, theta, id, event, word)
                        == model::regex_lang(final(store).graph(), sym, theta, regex@, word),
            Err(_) => true,
        },
)]
pub(crate) fn transition_const<G: KernelStore>(
    store: &mut G,
    regex: RegexId,
) -> KernelResult<TransitionId> {
    proof! { model::lemma_graph_wf_elim(store.graph()); }
    store.checkpoint()?;
    let c = store.constants();
    if regex == c.empty {
        Ok(c.transition_empty)
    } else if regex == c.all {
        Ok(c.transition_all)
    } else if regex == c.epsilon {
        Ok(c.transition_epsilon)
    } else {
        intern_transition_step(store, TransitionView::Const(regex))
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        test@ < old(store).graph().tests.len(), a@ < old(store).graph().transitions.len(), b@ < old(store).graph().transitions.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result {
            Ok(id) => id@ < final(store).graph().transitions.len()
                && tdepth(final(store).graph(), id@)
                    <= if_bound(tdepth(old(store).graph(), a@), tdepth(old(store).graph(), b@))
                && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> transition_lang(final(store).graph(), sym, theta, id, event, word)
                        == transition_if_combo(final(store).graph(), sym, theta, test, a, b, event, word),
            Err(_) => true,
        },
)]
fn local_if<G: KernelStore>(
    store: &mut G,
    test: TestId,
    a: TransitionId,
    b: TransitionId,
) -> KernelResult<TransitionId> {
    proof! { model::lemma_graph_wf_elim(store.graph()); tdepth_lemma_extends_forall(store.graph()); }
    let c = store.constants();
    if test == c.test_true || a == b {
        Ok(a)
    } else if test == c.test_false {
        Ok(b)
    } else {
        intern_transition_step(
            store,
            TransitionView::If {
                test,
                then_transition: a,
                else_transition: b,
            },
        )
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), transition_child_count(store.graph(), id@, count as nat),
        transition_ids_valid(store.graph(), old(flat).view()),
    ensures old(flat).view().is_prefix_of(final(flat).view()), transition_ids_valid(store.graph(), final(flat).view()),
        match result {
            Ok(()) => model::transition_ids(final(flat).view())
                == model::transition_ids(old(flat).view()) + transition_children(store.graph(), id@),
            Err(_) => true,
        },
)]
fn collect_transition_children<G: KernelStore>(
    store: &G,
    id: TransitionId,
    count: usize,
    flat: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof! { transition_lemma_children(store.graph(), id@); }
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= count,
            model::graph_wf(store.graph()), transition_child_count(store.graph(), id@, count as nat),
            transition_children(store.graph(), id@).len() == count,
            old(flat).view().is_prefix_of(flat.view()), transition_ids_valid(store.graph(), flat.view()),
            flat.view().len() == old(flat).view().len() + i,
            model::transition_ids(flat.view()) == model::transition_ids(old(flat).view())
                + transition_children(store.graph(), id@).take(i as int),
        ensures failure.is_none() ==> i == count,
        decreases count - i,
    ))]
    while i < count {
        let child = loop_try!(transition_child(store, id, i), failure);
        proof_decl! { let ghost prior = flat.view(); }
        proof! { transition_lemma_child(store.graph(), id@, i as nat, child@); }
        flat.push(child);
        proof! {
            transition_ids_push(prior, child);
            assert(transition_children(store.graph(), id@).take(i as int).push(child@)
                =~= transition_children(store.graph(), id@).take(i as int + 1));
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(())
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
struct TransitionMode {
    intersect: bool,
    identity: TransitionId,
    absorber: TransitionId,
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition_mode_valid(old(store).graph(), mode@),
        transition_ids_valid(old(store).graph(), old(pending).view()), old(pending).view().len() > 0,
        transition_ids_valid(old(store).graph(), old(flat).view()), regex_ids_valid(old(store).graph(), old(constants).view()),
    ensures final(store).graph() == old(store).graph(), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store() == old(store).valid_store(),
        transition_ids_valid(final(store).graph(), final(pending).view()),
        transition_ids_valid(final(store).graph(), final(flat).view()), regex_ids_valid(final(store).graph(), final(constants).view()),
        match result {
            Ok(collapsed) => transition_collect_effect(final(store).graph(), mode@,
                old(pending).view(), old(flat).view(), old(constants).view(),
                final(pending).view(), final(flat).view(), final(constants).view(), collapsed)
                && (!collapsed ==> collect_total(final(store).graph(), final(pending).view(), final(flat).view(),
                        final(constants).view(), mode.intersect)
                    <= collect_total(old(store).graph(), old(pending).view(), old(flat).view(),
                        old(constants).view(), mode.intersect)),
            Err(_) => true,
        },
)]
fn transition_collect_step<G: KernelStore>(
    store: &mut G,
    mode: TransitionMode,
    pending: &mut WorkVec<TransitionId>,
    flat: &mut WorkVec<TransitionId>,
    constants: &mut WorkVec<RegexId>,
) -> KernelResult<bool> {
    proof_decl! {
        let ghost p0 = pending.view();
        let ghost f0 = flat.view();
        let ghost rs0 = constants.view();
    }
    let id = match pending.pop() {
        Some(v) => v,
        None => return Err(invariant()),
    };
    store.checkpoint()?;
    proof_decl! { let ghost prefix = pending.view(); }
    proof! {
        transition_lemma_identities(store.graph(), mode@);
        model::lemma_graph_transition_wf(store.graph(), id@);
        assert(p0 =~= prefix.push(id));
    }
    if id == mode.absorber {
        proof! { transition_lemma_collect_absorber(store.graph(), mode@, p0, f0, rs0); }
        return Ok(true);
    }
    if id != mode.identity {
        match transition_head(store, id)? {
            TransitionHead::Union(n) if !mode.intersect => {
                collect_transition_children(store, id, n, pending)?;
                proof! {
                    let children = pending.view().subrange(prefix.len() as int, pending.view().len() as int);
                    assert(prefix + children =~= pending.view());
                    assert(model::transition_ids(prefix + children)
                        =~= model::transition_ids(prefix) + model::transition_ids(children));
                    transition_lemma_image_suffix(prefix, pending.view(), transition_children(store.graph(), id@));
                    assert(model::transition_ids(children) =~= transition_children(store.graph(), id@));
                    reveal(transition_children);
                    transition_lemma_collect_expand(store.graph(), mode@, p0, f0, rs0, children);
                    collect_lemma_expand(store.graph(), prefix, id, children, f0, rs0, mode.intersect);
                }
            }
            TransitionHead::Intersect(n) if mode.intersect => {
                collect_transition_children(store, id, n, pending)?;
                proof! {
                    let children = pending.view().subrange(prefix.len() as int, pending.view().len() as int);
                    assert(prefix + children =~= pending.view());
                    assert(model::transition_ids(prefix + children)
                        =~= model::transition_ids(prefix) + model::transition_ids(children));
                    transition_lemma_image_suffix(prefix, pending.view(), transition_children(store.graph(), id@));
                    assert(model::transition_ids(children) =~= transition_children(store.graph(), id@));
                    reveal(transition_children);
                    transition_lemma_collect_expand(store.graph(), mode@, p0, f0, rs0, children);
                    collect_lemma_expand(store.graph(), prefix, id, children, f0, rs0, mode.intersect);
                }
            }
            TransitionHead::Const(r) => {
                constants.push(r);
                proof! {
                    transition_lemma_collect_constant(store.graph(), mode@, p0, f0, rs0, r);
                    collect_lemma_constant(store.graph(), prefix, id, f0, rs0, r, mode.intersect);
                }
            }
            _ => {
                flat.push(id);
                proof! {
                    transition_lemma_collect_leaf(store.graph(), mode@, p0, f0, rs0);
                    collect_lemma_leaf(store.graph(), prefix, id, f0, rs0, mode.intersect);
                }
            }
        }
    }
    proof! {
        if id == mode.identity {
            transition_lemma_collect_identity(store.graph(), mode@, p0, f0, rs0);
            collect_lemma_drop(store.graph(), prefix, id, f0, rs0, mode.intersect);
        }
    }
    Ok(false)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition_mode_valid(old(store).graph(), mode@),
        transition_ids_valid(old(store).graph(), old(pending).view()),
        transition_ids_valid(old(store).graph(), old(flat).view()), regex_ids_valid(old(store).graph(), old(constants).view()),
    ensures final(store).graph() == old(store).graph(), model::graph_wf(final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        final(store).valid_store() == old(store).valid_store(),
        transition_ids_valid(final(store).graph(), final(pending).view()),
        transition_ids_valid(final(store).graph(), final(flat).view()), regex_ids_valid(final(store).graph(), final(constants).view()),
        match result {
            Ok(collapsed) => transition_collect_effect(final(store).graph(), mode@,
                old(pending).view(), old(flat).view(), old(constants).view(),
                final(pending).view(), final(flat).view(), final(constants).view(), collapsed)
                && (!collapsed ==> final(pending).view().len() == 0)
                && (!collapsed ==> collect_total(final(store).graph(), final(pending).view(), final(flat).view(),
                        final(constants).view(), mode.intersect)
                    <= collect_total(old(store).graph(), old(pending).view(), old(flat).view(),
                        old(constants).view(), mode.intersect)),
            Err(_) => true,
        },
)]
fn transition_collect_nodes<G: KernelStore>(
    store: &mut G,
    mode: TransitionMode,
    pending: &mut WorkVec<TransitionId>,
    flat: &mut WorkVec<TransitionId>,
    constants: &mut WorkVec<RegexId>,
) -> KernelResult<bool> {
    proof_decl! {
        let ghost p0 = pending.view();
        let ghost f0 = flat.view();
        let ghost rs0 = constants.view();
    }
    proof! {
        if p0.len() > 0 { transition_lemma_pending_work_pop(store.graph(), p0, mode.intersect); }
    }
    let mut state = Ok(false);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant store.graph() == old(store).graph(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            store.valid_store(), transition_mode_valid(store.graph(), mode@),
            transition_ids_valid(store.graph(), pending.view()), transition_ids_valid(store.graph(), flat.view()),
            regex_ids_valid(store.graph(), constants.view()),
            match state {
                Ok(collapsed) => forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> transition_collect_combo(store.graph(), sym, theta, p0, f0, rs0, event, word, mode.intersect)
                        == if collapsed { !mode.intersect } else {
                            transition_collect_combo(store.graph(), sym, theta, pending.view(), flat.view(), constants.view(), event, word, mode.intersect)
                        },
                Err(_) => true,
            },
            match state {
                Ok(false) => collect_total(store.graph(), pending.view(), flat.view(), constants.view(), mode.intersect)
                    <= collect_total(store.graph(), p0, f0, rs0, mode.intersect),
                _ => true,
            },
        decreases match state { Ok(false) => transition_pending_work(store.graph(), pending.view(), mode.intersect) + 1, _ => 0nat },
    ))]
    while !pending.is_empty() && matches!(state, Ok(false)) {
        state = transition_collect_step(store, mode, pending, flat, constants);
    }
    state
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(id) => id@ < final(store).graph().transitions.len()
                && tdepth(final(store).graph(), id@) <= collect_bound(old(store).graph(), children@, intersect)
                && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> transition_lang(final(store).graph(), sym, theta, id, event, word)
                        == transition_combo(final(store).graph(), sym, theta, children@, event, word, intersect),
            Err(_) => true,
        },
)]
fn transition_collect<G: KernelStore>(
    store: &mut G,
    children: &[TransitionId],
    intersect: bool,
) -> KernelResult<TransitionId> {
    proof_decl! { let ghost original = children@; let ghost entry = store.graph(); }
    proof! {
        tdepth_lemma_constants(entry);
        collect_lemma_bound(entry, original, intersect);
    }
    let c = store.constants();
    let identity = if intersect {
        c.transition_all
    } else {
        c.transition_empty
    };
    let absorber = if intersect {
        c.transition_empty
    } else {
        c.transition_all
    };
    let mode = TransitionMode {
        intersect,
        identity,
        absorber,
    };
    proof! {
        assert(transition_mode_valid(store.graph(), mode@));
        transition_lemma_identities(store.graph(), mode@);
    }
    let mut flat = WorkVec::new();
    let mut constants = WorkVec::new();
    let mut pending = WorkVec::new();
    pending.extend_from_slice(children);
    proof! {
        assert(pending.view() == original);
        assert(flat.view() == Seq::<TransitionId>::empty());
        assert(constants.view() == Seq::<RegexId>::empty());
    }
    if transition_collect_nodes(store, mode, &mut pending, &mut flat, &mut constants)? {
        proof! {
            transition_lemma_initial_collection(store.graph(), mode@, original,
                pending.view(), flat.view(), constants.view(), true);
        }
        return Ok(absorber);
    }
    proof! {
        transition_lemma_initial_collection(store.graph(), mode@, original,
            pending.view(), flat.view(), constants.view(), false);
        collect_lemma_flat(store.graph(), original, pending.view(), flat.view(), constants.view(), intersect);
    }
    if !constants.is_empty() {
        proof_decl! { let ghost before_group = store.graph(); let ghost prior_flat = flat.view(); }
        let r = regex_set(store, &constants, intersect)?;
        proof_decl! { let ghost after_regex = store.graph(); }
        proof! {
            regex_combo_extends(before_group, after_regex, constants.view(), intersect);
            regex_set_result(after_regex, seq![r], seq![r], intersect);
            assert(regex_equivalent(after_regex, seq![r], constants.view(), intersect));
        }
        let t = transition_const(store, r)?;
        proof! {
            transition_lemma_extends_transitive(before_group, after_regex, store.graph());
            transition_collected_extends(before_group, store.graph(), original, prior_flat, constants.view(), intersect);
            regex_equivalence_extends(after_regex, store.graph(), seq![r], constants.view(), intersect);
            regex_combo_extends(after_regex, store.graph(), seq![r], intersect);
            regex_set_result(store.graph(), seq![r], constants.view(), intersect);
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                implies transition_lang(store.graph(), sym, theta, t, event, word)
                    == regex_combo(store.graph(), sym, theta, constants.view(), word, intersect) by {}
            transition_lemma_group_result(store.graph(), original, prior_flat, constants.view(), mode@, t);
            tdepth_lemma_constants(store.graph());
            collect_lemma_const_result(before_group, store.graph(), original, prior_flat, t, t != identity, intersect);
        }
        if t == absorber {
            return Ok(absorber);
        }
        if t != identity {
            flat.push(t);
        }
    }
    proof! {
        if constants.view().len() == 0 { assert(transition_equivalent(store.graph(), original, flat.view(), intersect)); }
        assert(transition_equivalent(store.graph(), original, flat.view(), intersect));
        assert(transition_ids_valid(store.graph(), original));
        assert(transition_ids_valid(store.graph(), flat.view()));
        tdepth_lemma_extends_forall(entry);
        assert(collect_weight(store.graph(), flat.view(), intersect) <= collect_weight(store.graph(), original, intersect));
    }
    proof_decl! { let ghost unsorted = flat.view(); }
    flat.as_mut_slice().sort_unstable();
    proof! {
        transition_multiset_members(unsorted, flat.view());
        transition_member_ids_valid(store.graph(), unsorted, flat.view());
        transition_combo_members(store.graph(), unsorted, flat.view(), intersect);
        assert forall|i: int, j: int| 0 <= i < j < flat.view().len() implies flat.view()[i]@ <= flat.view()[j]@ by {
            assert(!(flat.view()[i].cmp_spec(&flat.view()[j]) is Greater));
        }
    }
    proof_decl! { let ghost sorted = flat.view(); }
    dedup_ids(&mut flat)?;
    proof! {
        transition_member_ids_valid(store.graph(), sorted, flat.view());
        transition_combo_members(store.graph(), sorted, flat.view(), intersect);
        transition_dedup_strict(sorted, flat.view());
        assert(transition_equivalent(store.graph(), original, flat.view(), intersect));
        transition_lemma_set_result(store.graph(), flat.view(), original, intersect);
        transition_equivalence_future(store.graph(), original, flat.view(), intersect);
        transition_set_law(flat.view(), intersect);
        transition_lemma_identities(store.graph(), mode@);
        assert forall|id: TransitionId| flat.view().contains(id) implies unsorted.contains(id) by {
            assert(sorted.contains(id));
        }
        assert(flat.view().no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < flat.view().len() && 0 <= j < flat.view().len() && i != j
                implies flat.view()[i] != flat.view()[j] by {
                assert(model::transition_ids(flat.view())[i] == flat.view()[i]@);
                assert(model::transition_ids(flat.view())[j] == flat.view()[j]@);
            }
        }
        collect_lemma_subset(store.graph(), flat.view(), unsorted, intersect);
        collect_lemma_final(entry, store.graph(), original, flat.view(), intersect);
        tdepths_lemma_extends_forall(store.graph(), flat.view());
    }
    if flat.is_empty() {
        Ok(identity)
    } else if flat.len() == 1 {
        match flat.first() {
            Some(id) => Ok(*id),
            None => Err(invariant()),
        }
    } else {
        intern_transition_step(
            store,
            if intersect {
                TransitionView::Intersect(&flat)
            } else {
                TransitionView::Union(&flat)
            },
        )
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()), model::graph_wf(final(store).graph()), final(store).valid_store(),
        final(store).restoration() == old(store).restoration(),
        match result {
            Ok(id) => id@ < final(store).graph().transitions.len()
                && tdepth(final(store).graph(), id@) <= collect_bound(old(store).graph(), children@, false)
                && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                    ==> transition_lang(final(store).graph(), sym, theta, id, event, word)
                        == transition_combo(final(store).graph(), sym, theta, children@, event, word, false),
            Err(_) => true,
        },
)]
pub(crate) fn transition_union<G: KernelStore>(
    store: &mut G,
    children: &[TransitionId],
) -> KernelResult<TransitionId> {
    transition_collect(store, children, false)
}
#[verus_verify]
enum Action {
    Clean(TransitionId, TestId),
    Not(TransitionId),
    Append(TransitionId, RegexId),
    Pair(TransitionId, TransitionId),
    Union(usize),
    Intersect(usize),
    If(TestId),
    CleanIf(TestId, TestId),
    Fold(WorkVec<TransitionId>, usize),
    NotResult,
    AppendResult(RegexId),
    SwapThen,
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
enum ChildAction {
    Clean(TestId),
    Not,
    Append(RegexId),
    PairLeft(TransitionId),
    PairRight(TransitionId),
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), transition_child_count(store.graph(), id@, count as nat),
        transition_child_action_valid(store.graph(), action@),
        transition_tasks_valid(store.graph(), transition_action_views(old(tasks).view())),
    ensures transition_tasks_valid(store.graph(), transition_action_views(final(tasks).view())),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_action_views(final(tasks).view())
                == transition_action_views(old(tasks).view()) + transition_child_actions(store.graph(), id@, action@),
            Err(_) => true,
        },
)]
fn schedule_transition_children<G: KernelStore>(
    store: &G,
    id: TransitionId,
    count: usize,
    action: ChildAction,
    tasks: &mut WorkVec<Action>,
) -> KernelResult<()> {
    proof_decl! { let ghost base = transition_action_views(tasks.view()); }
    proof! {
        transition_lemma_children(store.graph(), id@);
        transition_lemma_child_actions_valid(store.graph(), id@, action@);
    }
    let mut failure = None;
    let mut remaining = count;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining <= count, model::graph_wf(store.graph()),
            transition_child_count(store.graph(), id@, count as nat),
            transition_child_action_valid(store.graph(), action@),
            transition_child_actions(store.graph(), id@, action@).len() == count,
            transition_tasks_valid(store.graph(), transition_action_views(tasks.view())),
            base.is_prefix_of(transition_action_views(tasks.view())),
            failure.is_none() ==> transition_action_views(tasks.view())
                == base + transition_child_actions(store.graph(), id@, action@).take(count as int - remaining as int),
        ensures failure.is_none() ==> remaining == 0,
        decreases remaining,
    ))]
    while remaining != 0 {
        proof_decl! { let ghost prior = tasks.view(); }
        let i = loop_try!(
            match remaining.checked_sub(1) {
                Some(value) => Ok(value),
                None => Err(invariant()),
            },
            failure
        );
        remaining = i;
        let child = loop_try!(transition_child(store, id, i), failure);
        proof! { transition_lemma_child(store.graph(), id@, i as nat, child@); }
        tasks.push(match action {
            ChildAction::Clean(path) => Action::Clean(child, path),
            ChildAction::Not => Action::Not(child),
            ChildAction::Append(r) => Action::Append(child, r),
            ChildAction::PairLeft(other) => Action::Pair(child, other),
            ChildAction::PairRight(other) => Action::Pair(other, child),
        });
        proof! {
            let shape = transition_child_shape(action@, child@);
            transition_lemma_child_action_valid(store.graph(), action@, child@);
            assert(tasks.view().last()@ == shape);
            assert(tasks.view() == prior.push(tasks.view().last()));
            transition_action_views_push(prior, tasks.view().last());
            let index = count as int - remaining as int - 1;
            assert(0 <= index < count);
            assert(transition_child_actions(store.graph(), id@, action@)[index] == shape);
            assert(transition_child_actions(store.graph(), id@, action@).take(index).push(shape)
                =~= transition_child_actions(store.graph(), id@, action@).take(index + 1));
        }
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(taken) => count <= old(values).view().len()
        && taken.view() == old(values).view().subrange(old(values).view().len() as int - count, old(values).view().len() as int)
        && final(values).view() == old(values).view().take(old(values).view().len() as int - count),
    Err(_) => final(values).view() == old(values).view(),
})]
fn take_values(
    values: &mut WorkVec<TransitionId>,
    count: usize,
) -> KernelResult<WorkVec<TransitionId>> {
    proof! { lemma_id_clones(); }
    let start = match values.len().checked_sub(count) {
        Some(v) => v,
        None => return Err(invariant()),
    };
    let mut result = WorkVec::new();
    match values.get(start..) {
        Some(xs) => result.extend_from_slice(xs),
        None => return Err(invariant()),
    }
    values.truncate(start);
    Ok(result)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), transition_suffix_count(store.graph(), id@, count as nat),
    ensures match result {
        Ok(values) => regex_ids_valid(store.graph(), values.view())
            && model::regex_ids(values.view()) == transition_suffix(store.graph(), id@),
        Err(_) => true,
    },
)]
fn suffix_values<G: KernelStore>(
    store: &G,
    id: TransitionId,
    count: usize,
) -> KernelResult<WorkVec<RegexId>> {
    proof! { transition_lemma_suffix(store.graph(), id@); }
    let mut values = WorkVec::new();
    let mut failure = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= count, regex_ids_valid(store.graph(), values.view()), values.view().len() == i,
            model::graph_wf(store.graph()), transition_suffix_count(store.graph(), id@, count as nat),
            transition_suffix(store.graph(), id@).len() == count,
            model::regex_ids(values.view()) == transition_suffix(store.graph(), id@).take(i as int),
        ensures failure.is_none() ==> i == count,
        decreases count - i,
    ))]
    while i < count {
        let child = loop_try!(suffix_child(store, id, i), failure);
        proof_decl! { let ghost prior = values.view(); }
        proof! { transition_lemma_suffix_child(store.graph(), id@, i as nat, child@); }
        values.push(child);
        proof! {
            regex_ids_push(prior, child);
            assert(transition_suffix(store.graph(), id@).take(i as int).push(child@)
                =~= transition_suffix(store.graph(), id@).take(i as int + 1));
        }
        i = i.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    Ok(values)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(store.graph()), transition_child_count(store.graph(), id@, count as nat), path@ < store.graph().tests.len(),
        transition_tasks_valid(store.graph(), transition_action_views(old(tasks).view())),
        match store.graph().transitions[id@ as int] {
            model::TransitionNode::Union(ids) => !intersect,
            model::TransitionNode::Intersect(ids) => intersect,
            _ => false,
        },
    ensures transition_tasks_valid(store.graph(), transition_action_views(final(tasks).view())),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_action_views(final(tasks).view())
                    == transition_clean_child_tasks(store.graph(), id, path, intersect, transition_action_views(old(tasks).view()))
                && forall|prior: Seq<TransitionId>| transition_effect(store.graph(), ActionShape::Clean(id@, path@),
                transition_action_views(old(tasks).view()), prior, transition_action_views(final(tasks).view()), prior),
            Err(_) => true,
        },
)]
fn clean_children<G: KernelStore>(
    store: &G,
    id: TransitionId,
    count: usize,
    intersect: bool,
    path: TestId,
    tasks: &mut WorkVec<Action>,
) -> KernelResult<()> {
    proof_decl! { let ghost initial = tasks.view(); let ghost base = transition_action_views(initial); }
    proof! {
        transition_lemma_children(store.graph(), id@);
        transition_lemma_clean_children_effect(store.graph(), id, path, intersect, base);
    }
    tasks.push(if intersect {
        Action::Intersect(count)
    } else {
        Action::Union(count)
    });
    proof! {
        assert(tasks.view() == initial.push(tasks.view().last()));
        transition_action_views_push(initial, tasks.view().last());
        assert(tasks.view().last()@ == if intersect { ActionShape::Intersect(count as nat) } else { ActionShape::Union(count as nat) });
    }
    schedule_transition_children(store, id, count, ChildAction::Clean(path), tasks)?;
    proof! {
        assert(transition_action_views(tasks.view()) == transition_clean_child_tasks(store.graph(), id, path, intersect, base));
        assert forall|prior: Seq<TransitionId>| transition_effect(store.graph(), ActionShape::Clean(id@, path@),
            base, prior, transition_action_views(tasks.view()), prior) by {
            assert(transition_effect(store.graph(), ActionShape::Clean(id@, path@), base, prior,
                transition_clean_child_tasks(store.graph(), id, path, intersect, base), prior));
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
        a@ < old(store).graph().transitions.len(),
        b@ < old(store).graph().transitions.len(),
        left@ == model::transition_node_head(old(store).graph().transitions[a@ as int]),
        right@ == model::transition_node_head(old(store).graph().transitions[b@ as int]),
        match left { TransitionHead::If(_, _, _) => true, _ => false },
        match right { TransitionHead::If(_, _, _) => true, _ => false },
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), ActionShape::Pair(a@, b@),
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()),
                    ActionShape::Pair(a@, b@), old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn pair_conditionals<G: KernelStore>(
    store: &mut G,
    a: TransitionId,
    b: TransitionId,
    left: TransitionHead,
    right: TransitionHead,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost p0 = transition_action_views(tasks.view()); let ghost v0 = values.view();
    let ghost entry = store.graph(); }
    proof! {
        transition_lemma_constants(store.graph());
        transition_configuration_future(store.graph(), p0, v0);
        model::lemma_graph_transition_wf(store.graph(), a@);
        model::lemma_graph_transition_wf(store.graph(), b@);
        graph_lemma_extends_refl(entry);
        tdepth_lemma_constants(entry);
    }
    let c = store.constants();
    if let (TransitionHead::If(x, xt, xe), TransitionHead::If(y, yt, ye)) = (left, right) {
        proof! {
            assert(store.graph().transitions[a@ as int] == model::TransitionNode::If(x@, xt@, xe@));
            assert(store.graph().transitions[b@ as int] == model::TransitionNode::If(y@, yt@, ye@));
            machine_pair_if_language(store.graph(), a, x, xt, xe);
            machine_pair_if_language(store.graph(), b, y, yt, ye);
        }
        if xe == c.transition_empty && ye == c.transition_empty {
            let guard = test_and(store, &[x, y])?;
            proof! {
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                    implies model::test_holds(sym, theta, model::lift_test(store.graph(), guard@), event)
                        == test_combo(store.graph(), sym, theta, seq![x, y], event, true) by {
                    assert(test_truth(store.graph(), sym, theta, guard@, event)
                        == test_combo(store.graph(), sym, theta, seq![x, y], event, true));
                }
                machine_pair_empty_branches(store.graph(), a, b, x, xt, y, yt, c.transition_empty, guard);
                tdepth_lemma_extends(entry, store.graph(), c.transition_empty@);
                tdepth_lemma_pos(entry, a@);
                tdepth_lemma_pos(entry, b@);
                lemma_pair_bound_ge(tdepth(entry, a@), tdepth(entry, b@));
            }
            if guard == c.test_false {
                values.push(c.transition_empty);
                proof! {
                    transition_lemma_push_result(store.graph(), ActionShape::Pair(a@, b@), p0, v0, c.transition_empty);
                    machine_value_result(entry, store.graph(), p0, ActionShape::Pair(a@, b@), v0, c.transition_empty);
                }
            } else {
                tasks.push(Action::CleanIf(guard, c.test_true));
                values.push(c.transition_empty);
                tasks.push(Action::SwapThen);
                tasks.push(Action::Pair(xt, yt));
                proof! {
                    machine_pair_empty_effect(store.graph(), a, b, xt, yt, guard, c.transition_empty, p0, v0);
                    assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::CleanIf(guard@, c.test_true@))
                        .push(ActionShape::SwapThen).push(ActionShape::Pair(xt@, yt@)));
                    machine_pair_empty(entry, store.graph(), p0, a, b, x, xt, xe, y, yt, ye, guard, c.test_true,
                        c.transition_empty, v0);
                }
            }
        } else if x == y {
            tasks.push(Action::CleanIf(x, c.test_true));
            tasks.push(Action::Pair(xe, ye));
            tasks.push(Action::Pair(xt, yt));
            proof! {
                machine_pair_if_effect(store.graph(), a, b, x, xt, yt, xe, ye, p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::CleanIf(x@, c.test_true@))
                    .push(ActionShape::Pair(xe@, ye@)).push(ActionShape::Pair(xt@, yt@)));
                machine_pair_both(entry, store.graph(), p0, a, b, x, xt, xe, y, yt, ye, c.test_true, v0);
            }
        } else if xe == c.transition_empty || (ye != c.transition_empty && x < y) {
            tasks.push(Action::CleanIf(x, c.test_true));
            tasks.push(Action::Pair(xe, b));
            tasks.push(Action::Pair(xt, b));
            proof! {
                machine_pair_if_effect(store.graph(), a, b, x, xt, b, xe, b, p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::CleanIf(x@, c.test_true@))
                    .push(ActionShape::Pair(xe@, b@)).push(ActionShape::Pair(xt@, b@)));
                machine_pair_split(entry, store.graph(), p0, a, b, x, xt, xe, c.test_true, true, v0);
            }
        } else {
            tasks.push(Action::CleanIf(y, c.test_true));
            tasks.push(Action::Pair(a, ye));
            tasks.push(Action::Pair(a, yt));
            proof! {
                machine_pair_if_effect(store.graph(), a, b, y, a, yt, a, ye, p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::CleanIf(y@, c.test_true@))
                    .push(ActionShape::Pair(a@, ye@)).push(ActionShape::Pair(a@, yt@)));
                machine_pair_split(entry, store.graph(), p0, a, b, y, yt, ye, c.test_true, false, v0);
            }
        }
        Ok(())
    } else {
        Err(invariant())
    }
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
        transition_ids_valid(old(store).graph(), xs.view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), ActionShape::Fold(model::transition_ids(xs.view()), index as nat),
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()),
                    ActionShape::Fold(model::transition_ids(xs.view()), index as nat), old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn transition_fold_step<G: KernelStore>(
    store: &mut G,
    xs: WorkVec<TransitionId>,
    index: usize,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost p0 = transition_action_views(tasks.view()); let ghost v0 = values.view(); let ghost original = xs.view(); }
    proof_decl! { let ghost entry = store.graph(); }
    proof! {
        transition_configuration_future(store.graph(), p0, v0);
        graph_lemma_extends_refl(entry);
        assert(value_depths(entry, original) =~= tdepths(entry, model::transition_ids(original)));
    }
    {
        if index == 0 {
            let flat = transition_collect(store, &xs, true)?;
            proof! { model::lemma_graph_transition_wf(store.graph(), flat@); }
            match transition_head(store, flat)? {
                TransitionHead::Intersect(n) => {
                    let mut children = WorkVec::new();
                    collect_transition_children(store, flat, n, &mut children)?;
                    let first = match children.first() {
                        Some(v) => *v,
                        None => return Err(invariant()),
                    };
                    proof_decl! { let ghost cs = children.view(); }
                    proof! {
                        assert(model::transition_ids(cs) == transition_children(store.graph(), flat@));
                        transition_lemma_children(store.graph(), flat@);
                        assert(store.graph().transitions[flat@ as int] == model::TransitionNode::Intersect(model::transition_ids(cs)));
                        machine_pair_fold_collection_effect(store.graph(), original, flat, cs, p0, v0);
                        machine_fold_start(entry, store.graph(), p0, model::transition_ids(original), flat, cs, v0);
                    }
                    values.push(first);
                    tasks.push(Action::Fold(children, 1));
                    proof! {
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Fold(model::transition_ids(cs), 1)));
                    }
                }
                _ => {
                    values.push(flat);
                    proof! {
                        machine_pair_set_result(store.graph(), original, ActionShape::Fold(model::transition_ids(original), 0), flat);
                        transition_lemma_push_result(store.graph(), ActionShape::Fold(model::transition_ids(original), 0), p0, v0, flat);
                        machine_fold_flat(entry, store.graph(), p0, model::transition_ids(original), v0, flat);
                    }
                }
            }
        } else if let Some(next) = xs.get(index) {
            let a = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            let b = *next;
            let next_index = match index.checked_add(1) {
                Some(v) => v,
                None => return Err(invariant()),
            };
            tasks.push(Action::Fold(xs, next_index));
            tasks.push(Action::Pair(a, b));
            proof! {
                machine_pair_fold_next_effect(store.graph(), original, index as nat, p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Fold(model::transition_ids(original), next_index as nat))
                    .push(ActionShape::Pair(a@, b@)));
                assert(model::transition_ids(original)[index as int] == b@);
                assert(values.view() == v0.drop_last());
                machine_fold_next(store.graph(), p0, model::transition_ids(original), index as nat, v0);
            }
        }
        proof! {
            if index != 0 && index >= original.len() {
                machine_pair_fold_noop(store.graph(), original, index as nat, p0, v0);
                machine_fold_noop(store.graph(), p0, model::transition_ids(original), index as nat, v0);
            }
        }
    }
    Ok(())
}

#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
        id@ < old(store).graph().transitions.len(),
        path@ < old(store).graph().tests.len(),
        c@ == old(store).graph().constants,
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), ActionShape::Clean(id@, path@),
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()),
                    ActionShape::Clean(id@, path@), old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn transition_clean_step<G: KernelStore>(
    store: &mut G,
    id: TransitionId,
    path: TestId,
    c: &Constants,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost p0 = transition_action_views(tasks.view()); let ghost v0 = values.view(); }
    proof_decl! { let ghost entry = store.graph(); }
    proof! { transition_lemma_constants(store.graph()); model::lemma_graph_transition_wf(store.graph(), id@); }
    proof! { transition_configuration_future(store.graph(), p0, v0); graph_lemma_extends_refl(entry); }
    match transition_head(store, id)? {
        TransitionHead::Const(_) => {
            values.push(id);
            proof! {
                transition_lemma_clean_identity(store.graph(), id, path);
                transition_lemma_push_result(store.graph(), ActionShape::Clean(id@, path@), p0, v0, id);
                machine_value_result(entry, store.graph(), p0, ActionShape::Clean(id@, path@), v0, id);
            }
        }
        TransitionHead::If(test, a, b) => {
            let yes = test_and(store, &[path, test])?;
            proof_decl! { let ghost after_yes = store.graph(); }
            let neg = test_not(store, test)?;
            proof_decl! { let ghost after_negated = store.graph(); }
            let no = test_and(store, &[path, neg])?;
            proof! {
                transition_lemma_extends_transitive(after_yes, after_negated, store.graph());
                transition_lemma_extends_transitive(entry, after_yes, store.graph());
                regex_test_connective_extends(after_yes, store.graph(), seq![path, test], yes, true);
                transition_test_not_extends(after_negated, store.graph(), test, neg);
                assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                    implies (model::test_holds(sym, theta, model::lift_test(store.graph(), yes@), event)
                        == (model::test_holds(sym, theta, model::lift_test(store.graph(), path@), event)
                            && model::test_holds(sym, theta, model::lift_test(store.graph(), test@), event)))
                    && (model::test_holds(sym, theta, model::lift_test(store.graph(), no@), event)
                        == (model::test_holds(sym, theta, model::lift_test(store.graph(), path@), event)
                            && !model::test_holds(sym, theta, model::lift_test(store.graph(), test@), event))) by {
                    transition_lemma_test_pair(store.graph(), sym, theta, path, test, event);
                    transition_lemma_test_pair(store.graph(), sym, theta, path, neg, event);
                }
                transition_lemma_clean_if_effect(store.graph(), id, path, test, a, b, yes, no, p0);
            }
            if yes == c.test_false {
                tasks.push(Action::Clean(b, no));
            } else if no == c.test_false {
                tasks.push(Action::Clean(a, yes));
            } else {
                tasks.push(Action::If(test));
                tasks.push(Action::Clean(b, no));
                tasks.push(Action::Clean(a, yes));
            }
            proof! {
                assert(transition_action_views(tasks.view()) == transition_clean_if_tasks(store.graph(), test, a, b, yes, no, p0));
                machine_clean_if(entry, store.graph(), p0, id, path, test, a, b, yes, no, v0);
            }
        }
        TransitionHead::Union(n) => {
            clean_children(store, id, n, false, path, tasks)?;
            proof! { machine_clean_children(store.graph(), p0, id, path, false, v0); }
        }
        TransitionHead::Intersect(n) => {
            clean_children(store, id, n, true, path, tasks)?;
            proof! { machine_clean_children(store.graph(), p0, id, path, true, v0); }
        }
        TransitionHead::Not(inner) => {
            tasks.push(Action::NotResult);
            tasks.push(Action::Clean(inner, path));
            proof! {
                transition_lemma_clean_not_effect(store.graph(), id, path, inner, p0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@)));
                machine_clean_not(entry, store.graph(), p0, id, path, inner, v0);
            }
        }
        TransitionHead::Append(inner, n) => {
            let xs = suffix_values(store, id, n)?;
            proof! { transition_lemma_suffix(store.graph(), id@); }
            let r = regex_concat(store, &xs)?;
            tasks.push(Action::AppendResult(r));
            tasks.push(Action::Clean(inner, path));
            proof! {
                transition_lemma_suffix(store.graph(), id@);
                transition_lemma_clean_append_effect(store.graph(), id, path, inner, xs.view(), r, p0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::AppendResult(r@)).push(ActionShape::Clean(inner@, path@)));
                machine_clean_append(entry, store.graph(), p0, id, path, inner, r, v0);
            }
        }
    }
    Ok(())
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
        id@ < old(store).graph().transitions.len(),
        c@ == old(store).graph().constants,
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), ActionShape::Not(id@),
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()),
                    ActionShape::Not(id@), old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn transition_not_step<G: KernelStore>(
    store: &mut G,
    id: TransitionId,
    c: &Constants,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost entry = store.graph(); let ghost initial = tasks.view();
    let ghost base = transition_action_views(initial); let ghost prior = values.view(); }
    proof! {
        transition_lemma_constants(store.graph());
        model::lemma_graph_transition_wf(store.graph(), id@);
        transition_configuration_future(entry, base, prior);
        graph_lemma_extends_refl(entry);
    }
    match transition_head(store, id)? {
        TransitionHead::Const(r) => {
            proof_decl! { let ghost head = r; }
            let r = regex_not(store, r)?;
            proof_decl! { let ghost before_const = store.graph(); }
            values.push(transition_const(store, r)?);
            proof! {
                machine_unary_not_const_result(before_const, store.graph(), id, head, r, values.view().last());
                transition_lemma_push_result(store.graph(), ActionShape::Not(id@), base, prior, values.view().last());
                transition_lemma_extends_transitive(entry, before_const, store.graph());
                assert(values.view() == prior.push(values.view().last()));
                machine_value_result(entry, store.graph(), base, ActionShape::Not(id@), prior, values.view().last());
            }
        }
        TransitionHead::Not(inner) => {
            values.push(inner);
            proof! {
                machine_unary_double_not_result(store.graph(), id, inner);
                transition_lemma_push_result(store.graph(), ActionShape::Not(id@), base, prior, inner);
                machine_not_double(entry, store.graph(), base, id, inner, prior);
            }
        }
        TransitionHead::Append(_, _) => {
            values.push(intern_transition_step(store, TransitionView::Not(id))?);
            proof! {
                transition_lemma_result_same_term(store.graph(), ActionShape::Not(id@), values.view().last());
                transition_lemma_push_result(store.graph(), ActionShape::Not(id@), base, prior, values.view().last());
                assert(values.view() == prior.push(values.view().last()));
                machine_wrap_interned(entry, store.graph(), base, ActionShape::Not(id@), prior, values.view().last());
            }
        }
        TransitionHead::If(test, a, b) => {
            if a == c.transition_all && b == c.transition_empty {
                let guard = test_not(store, test)?;
                proof! {
                    assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                        implies model::test_holds(sym, theta, model::lift_test(store.graph(), guard@), event)
                            == !model::test_holds(sym, theta, model::lift_test(store.graph(), test@), event) by {
                        assert(test_truth(store.graph(), sym, theta, guard@, event)
                            != test_truth(store.graph(), sym, theta, test@, event));
                    }
                }
                proof_decl! { let ghost before_if = store.graph(); }
                let out = local_if(store, guard, a, b)?;
                tasks.push(Action::Clean(out, c.test_true));
                proof! {
                    machine_unary_flip_result(before_if, store.graph(), id, test, a, b, guard, out);
                    machine_unary_clean_result_effect(store.graph(), ActionShape::Not(id@), out, base, prior);
                    assert(transition_action_views(tasks.view()) =~= base.push(ActionShape::Clean(out@, c.test_true@)));
                    transition_lemma_extends_transitive(entry, before_if, store.graph());
                    tdepth_lemma_constants(before_if);
                    machine_not_flip(entry, store.graph(), base, id, test, a, b, out, c.test_true, prior);
                }
            } else {
                tasks.push(Action::CleanIf(test, c.test_true));
                tasks.push(Action::Not(b));
                tasks.push(Action::Not(a));
                proof! {
                    machine_unary_if_effect(store.graph(), id, test, a, b, None, base, prior);
                    assert(transition_action_views(tasks.view()) =~= machine_unary_if_tasks(store.graph(), test, a, b, None, base));
                    machine_unary_if(entry, store.graph(), base, id, test, a, b, None, prior);
                }
            }
        }
        TransitionHead::Union(n) => {
            tasks.push(Action::Intersect(n));
            proof! {
                transition_lemma_children(store.graph(), id@);
                assert(transition_action_views(tasks.view()) =~= base.push(ActionShape::Intersect(n as nat)));
                assert(transition_tasks_valid(store.graph(), transition_action_views(tasks.view())));
            }
            schedule_transition_children(store, id, n, ChildAction::Not, tasks)?;
            proof! {
                machine_unary_children_effect(store.graph(), id, None, true, base, prior);
                assert(transition_action_views(tasks.view()) =~= machine_unary_child_tasks(store.graph(), id, None, true, base));
                machine_unary_children(store.graph(), base, id, None, true, prior);
            }
        }
        TransitionHead::Intersect(n) => {
            tasks.push(Action::Union(n));
            proof! {
                transition_lemma_children(store.graph(), id@);
                assert(transition_action_views(tasks.view()) =~= base.push(ActionShape::Union(n as nat)));
                assert(transition_tasks_valid(store.graph(), transition_action_views(tasks.view())));
            }
            schedule_transition_children(store, id, n, ChildAction::Not, tasks)?;
            proof! {
                machine_unary_children_effect(store.graph(), id, None, false, base, prior);
                assert(transition_action_views(tasks.view()) =~= machine_unary_child_tasks(store.graph(), id, None, false, base));
                machine_unary_children(store.graph(), base, id, None, false, prior);
            }
        }
    }
    Ok(())
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
        id@ < old(store).graph().transitions.len(),
        r@ < old(store).graph().regexes.len(),
        c@ == old(store).graph().constants,
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), ActionShape::Append(id@, r@),
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()),
                    ActionShape::Append(id@, r@), old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn transition_append_step<G: KernelStore>(
    store: &mut G,
    id: TransitionId,
    r: RegexId,
    c: &Constants,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost entry = store.graph(); let ghost initial = tasks.view();
    let ghost base = transition_action_views(initial); let ghost prior = values.view(); }
    proof! {
        transition_lemma_constants(store.graph());
        model::lemma_graph_transition_wf(store.graph(), id@);
        model::lemma_graph_regex_wf(store.graph(), r@);
        transition_configuration_future(entry, base, prior);
        graph_lemma_extends_refl(entry);
        tdepth_lemma_constants(entry);
    }
    {
        if r == c.epsilon {
            values.push(id);
            proof! {
                machine_unary_append_identity_result(store.graph(), id, r, id);
                transition_lemma_push_result(store.graph(), ActionShape::Append(id@, r@), base, prior, id);
                machine_value_result(entry, store.graph(), base, ActionShape::Append(id@, r@), prior, id);
            }
        } else if r == c.empty {
            values.push(c.transition_empty);
            proof! {
                machine_unary_append_identity_result(store.graph(), id, r, c.transition_empty);
                transition_lemma_push_result(store.graph(), ActionShape::Append(id@, r@), base, prior, c.transition_empty);
                machine_value_result(entry, store.graph(), base, ActionShape::Append(id@, r@), prior, c.transition_empty);
            }
        } else {
            match transition_head(store, id)? {
                TransitionHead::Const(head) => {
                    let out = regex_concat(store, &[head, r])?;
                    proof_decl! { let ghost before_const = store.graph(); }
                    values.push(transition_const(store, out)?);
                    proof! {
                        machine_unary_append_const_result(before_const, store.graph(), id, head, r, out, values.view().last());
                        transition_lemma_push_result(store.graph(), ActionShape::Append(id@, r@), base, prior, values.view().last());
                        transition_lemma_extends_transitive(entry, before_const, store.graph());
                        assert(values.view() == prior.push(values.view().last()));
                        machine_value_result(entry, store.graph(), base, ActionShape::Append(id@, r@), prior, values.view().last());
                    }
                }
                TransitionHead::If(test, a, b) => {
                    tasks.push(Action::CleanIf(test, c.test_true));
                    tasks.push(Action::Append(b, r));
                    tasks.push(Action::Append(a, r));
                    proof! {
                        machine_unary_if_effect(store.graph(), id, test, a, b, Some(r), base, prior);
                        assert(transition_action_views(tasks.view()) =~= machine_unary_if_tasks(store.graph(), test, a, b, Some(r), base));
                        machine_unary_if(entry, store.graph(), base, id, test, a, b, Some(r), prior);
                    }
                }
                TransitionHead::Union(n) => {
                    tasks.push(Action::Union(n));
                    proof! {
                        transition_lemma_children(store.graph(), id@);
                        assert(transition_action_views(tasks.view()) =~= base.push(ActionShape::Union(n as nat)));
                        assert(transition_tasks_valid(store.graph(), transition_action_views(tasks.view())));
                    }
                    schedule_transition_children(store, id, n, ChildAction::Append(r), tasks)?;
                    proof! {
                        machine_unary_children_effect(store.graph(), id, Some(r), false, base, prior);
                        assert(transition_action_views(tasks.view()) =~= machine_unary_child_tasks(store.graph(), id, Some(r), false, base));
                        machine_unary_children(store.graph(), base, id, Some(r), false, prior);
                    }
                }
                TransitionHead::Append(inner, n) => {
                    let mut xs = suffix_values(store, id, n)?;
                    proof_decl! { let ghost children = xs.view(); }
                    proof! { transition_lemma_suffix(store.graph(), id@); }
                    xs.push(r);
                    let combined = regex_concat(store, &xs)?;
                    tasks.push(Action::Append(inner, combined));
                    proof! {
                        machine_unary_append_nested_effect(store.graph(), id, inner, r, combined, children, base, prior);
                        assert(transition_action_views(tasks.view()) =~= base.push(ActionShape::Append(inner@, combined@)));
                        machine_append_nested(entry, store.graph(), base, id, r, inner, combined, prior);
                    }
                }
                TransitionHead::Intersect(_) | TransitionHead::Not(_) => {
                    let mut xs = WorkVec::new();
                    match regex_head(store, r)? {
                        RegexHead::Concat(n) => {
                            proof! { regex_children_count(store.graph(), r@); }
                            collect_regex_children(store, r, n, &mut xs)?
                        }
                        _ => xs.push(r),
                    }
                    proof! {
                        regex_children_count(store.graph(), r@);
                        machine_unary_suffix_language(store.graph(), r, xs.view());
                    }
                    proof_decl! { let ghost before_intern = store.graph(); }
                    values.push(intern_transition_step(
                        store,
                        TransitionView::Append {
                            transition: id,
                            suffix: &xs,
                        },
                    )?);
                    proof! {
                        machine_unary_append_raw_result(before_intern, store.graph(), id, r, xs.view(), values.view().last());
                        transition_lemma_push_result(store.graph(), ActionShape::Append(id@, r@), base, prior, values.view().last());
                        transition_lemma_extends_transitive(entry, before_intern, store.graph());
                        assert(values.view() == prior.push(values.view().last()));
                        machine_wrap_interned(entry, store.graph(), base, ActionShape::Append(id@, r@), prior, values.view().last());
                    }
                }
            }
        }
    }
    Ok(())
}

#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
        a@ < old(store).graph().transitions.len(),
        b@ < old(store).graph().transitions.len(),
        c@ == old(store).graph().constants,
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), ActionShape::Pair(a@, b@),
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()),
                    ActionShape::Pair(a@, b@), old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn transition_pair_step<G: KernelStore>(
    store: &mut G,
    a: TransitionId,
    b: TransitionId,
    c: &Constants,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost p0 = transition_action_views(tasks.view()); let ghost v0 = values.view();
    let ghost entry = store.graph(); }
    proof! {
        transition_lemma_constants(store.graph());
        transition_configuration_future(store.graph(), p0, v0);
        model::lemma_graph_transition_wf(store.graph(), a@);
        model::lemma_graph_transition_wf(store.graph(), b@);
        graph_lemma_extends_refl(entry);
        tdepth_lemma_constants(entry);
        tdepth_lemma_pos(entry, a@);
        tdepth_lemma_pos(entry, b@);
        lemma_pair_bound_ge(tdepth(entry, a@), tdepth(entry, b@));
    }
    {
        if a == b || b == c.transition_all {
            values.push(a);
            proof! {
                machine_pair_identity_result(store.graph(), a, b, a, c.transition_all, c.transition_empty);
                transition_lemma_push_result(store.graph(), ActionShape::Pair(a@, b@), p0, v0, a);
                machine_value_result(entry, store.graph(), p0, ActionShape::Pair(a@, b@), v0, a);
            }
        } else if a == c.transition_all {
            values.push(b);
            proof! {
                machine_pair_identity_result(store.graph(), a, b, b, c.transition_all, c.transition_empty);
                transition_lemma_push_result(store.graph(), ActionShape::Pair(a@, b@), p0, v0, b);
                machine_value_result(entry, store.graph(), p0, ActionShape::Pair(a@, b@), v0, b);
            }
        } else if a == c.transition_empty || b == c.transition_empty {
            values.push(c.transition_empty);
            proof! {
                machine_pair_identity_result(store.graph(), a, b, c.transition_empty, c.transition_all, c.transition_empty);
                transition_lemma_push_result(store.graph(), ActionShape::Pair(a@, b@), p0, v0, c.transition_empty);
                machine_value_result(entry, store.graph(), p0, ActionShape::Pair(a@, b@), v0, c.transition_empty);
            }
        } else {
            let left = transition_head(store, a)?;
            let right = transition_head(store, b)?;
            match (left, right) {
                (TransitionHead::Const(x), TransitionHead::Const(y)) => {
                    let r = regex_intersect(store, &[x, y])?;
                    proof_decl! { let ghost after_regex = store.graph(); }
                    values.push(transition_const(store, r)?);
                    proof! {
                        let out = values.view().last();
                        machine_pair_constant_result(after_regex, store.graph(), a, b, x, y, r, out);
                        transition_lemma_push_result(store.graph(), ActionShape::Pair(a@, b@), p0, v0, out);
                        transition_lemma_extends_transitive(entry, after_regex, store.graph());
                        machine_value_result(entry, store.graph(), p0, ActionShape::Pair(a@, b@), v0, out);
                    }
                }
                (TransitionHead::If(_, _, _), TransitionHead::If(_, _, _)) => {
                    pair_conditionals(store, a, b, left, right, tasks, values)?
                }
                (TransitionHead::Union(n), _) => {
                    tasks.push(Action::Union(n));
                    proof! {
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Union(n as nat)));
                        assert(transition_tasks_valid(store.graph(), transition_action_views(tasks.view())));
                        transition_lemma_children(store.graph(), a@);
                        assert(transition_children(store.graph(), a@).len() == n);
                    }
                    schedule_transition_children(store, a, n, ChildAction::PairLeft(b), tasks)?;
                    proof! {
                        machine_pair_union_effect(store.graph(), a, b, true, p0, v0);
                        assert(transition_effect(store.graph(), ActionShape::Pair(a@, b@), p0, v0,
                            transition_action_views(tasks.view()), values.view()));
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Union(
                            transition_children(store.graph(), a@).len())) + transition_child_actions(store.graph(), a@,
                            ChildShape::PairLeft(b@)));
                        machine_pair_union(store.graph(), p0, a, b, true, v0);
                    }
                }
                (_, TransitionHead::Union(n)) => {
                    tasks.push(Action::Union(n));
                    proof! {
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Union(n as nat)));
                        assert(transition_tasks_valid(store.graph(), transition_action_views(tasks.view())));
                        transition_lemma_children(store.graph(), b@);
                        assert(transition_children(store.graph(), b@).len() == n);
                    }
                    schedule_transition_children(store, b, n, ChildAction::PairRight(a), tasks)?;
                    proof! {
                        machine_pair_union_effect(store.graph(), a, b, false, p0, v0);
                        assert(transition_effect(store.graph(), ActionShape::Pair(a@, b@), p0, v0,
                            transition_action_views(tasks.view()), values.view()));
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Union(
                            transition_children(store.graph(), b@).len())) + transition_child_actions(store.graph(), b@,
                            ChildShape::PairRight(a@)));
                        machine_pair_union(store.graph(), p0, a, b, false, v0);
                    }
                }
                (TransitionHead::If(test, t, e), _) => {
                    tasks.push(Action::CleanIf(test, c.test_true));
                    tasks.push(Action::Pair(e, b));
                    tasks.push(Action::Pair(t, b));
                    proof! {
                        machine_pair_if_language(store.graph(), a, test, t, e);
                        machine_pair_if_effect(store.graph(), a, b, test, t, b, e, b, p0, v0);
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::CleanIf(test@, c.test_true@))
                            .push(ActionShape::Pair(e@, b@)).push(ActionShape::Pair(t@, b@)));
                        machine_pair_split(entry, store.graph(), p0, a, b, test, t, e, c.test_true, true, v0);
                    }
                }
                (_, TransitionHead::If(test, t, e)) => {
                    tasks.push(Action::CleanIf(test, c.test_true));
                    tasks.push(Action::Pair(a, e));
                    tasks.push(Action::Pair(a, t));
                    proof! {
                        machine_pair_if_language(store.graph(), b, test, t, e);
                        machine_pair_if_effect(store.graph(), a, b, test, a, t, a, e, p0, v0);
                        assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::CleanIf(test@, c.test_true@))
                            .push(ActionShape::Pair(a@, e@)).push(ActionShape::Pair(a@, t@)));
                        machine_pair_split(entry, store.graph(), p0, a, b, test, t, e, c.test_true, false, v0);
                    }
                }
                _ => {
                    values.push(transition_collect(store, &[a, b], true)?);
                    proof! {
                        let out = values.view().last();
                        machine_pair_set_result(store.graph(), seq![a, b], ActionShape::Pair(a@, b@), out);
                        transition_lemma_push_result(store.graph(), ActionShape::Pair(a@, b@), p0, v0, out);
                        collect_lemma_pair_bound(entry, a, b);
                        machine_value_result(entry, store.graph(), p0, ActionShape::Pair(a@, b@), v0, out);
                    }
                }
            }
        }
    }
    Ok(())
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_action_valid(old(store).graph(), task@),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        transition_action_views(old(tasks).view()).is_prefix_of(transition_action_views(final(tasks).view())),
        match result {
            Ok(()) => transition_effect(final(store).graph(), task@,
                transition_action_views(old(tasks).view()), old(values).view(),
                transition_action_views(final(tasks).view()), final(values).view())
                && machine_progress(old(store).graph(), transition_action_views(old(tasks).view()), task@, old(values).view(),
                    final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
            Err(_) => true,
        },
)]
fn transition_step<G: KernelStore>(
    store: &mut G,
    task: Action,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost p0 = transition_action_views(tasks.view()); let ghost v0 = values.view();
    let ghost entry = store.graph(); }
    proof! { transition_configuration_future(store.graph(), p0, v0); graph_lemma_extends_refl(entry); }
    store.checkpoint()?;
    let c = store.constants();
    match task {
        Action::Union(n) => {
            let xs = take_values(values, n)?;
            values.push(transition_union(store, &xs)?);
            proof! {
                machine_driver_union_effect(store.graph(), n as nat, p0, v0, values.view().last());
                assert(values.view() == v0.take(v0.len() as int - n as int).push(values.view().last()));
                machine_driver_union(entry, store.graph(), p0, n as nat, v0, values.view().last());
            }
        }
        Action::Intersect(n) => {
            let xs = take_values(values, n)?;
            tasks.push(Action::Fold(xs, 0));
            proof! {
                machine_driver_intersect_effect(store.graph(), n as nat, p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Fold(
                    model::transition_ids(v0.subrange(v0.len() as int - n as int, v0.len() as int)), 0)));
                machine_driver_intersect(store.graph(), p0, n as nat, v0);
            }
        }
        Action::Fold(xs, index) => {
            proof! {
                assert forall|i: int| 0 <= i < xs.view().len() implies xs.view()[i]@ < store.graph().transitions.len() by {
                    assert(model::transition_ids(xs.view())[i] == xs.view()[i]@);
                }
            }
            transition_fold_step(store, xs, index, tasks, values)?;
        }
        Action::If(test) => {
            let b = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            let a = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            proof! {
                assert(values.view() =~= v0.take(v0.len() as int - 2));
                assert(a == v0[v0.len() - 2] && b == v0[v0.len() - 1]);
            }
            values.push(local_if(store, test, a, b)?);
            proof! {
                machine_driver_if_effect(store.graph(), test, None, p0, v0, values.view().last());
                assert(values.view() == v0.take(v0.len() as int - 2).push(values.view().last()));
                machine_driver_if(entry, store.graph(), p0, ActionShape::If(test@), v0, values.view().last());
            }
        }
        Action::CleanIf(test, path) => {
            let b = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            let a = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            proof! {
                assert(values.view() =~= v0.take(v0.len() as int - 2));
                assert(a == v0[v0.len() - 2] && b == v0[v0.len() - 1]);
            }
            let out = local_if(store, test, a, b)?;
            tasks.push(Action::Clean(out, path));
            proof! {
                machine_driver_if_effect(store.graph(), test, Some(path), p0, v0, out);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Clean(out@, path@)));
                machine_driver_clean_if(entry, store.graph(), p0, test, path, v0, out);
            }
        }
        Action::Clean(id, path) => transition_clean_step(store, id, path, &c, tasks, values)?,
        Action::Not(id) => transition_not_step(store, id, &c, tasks, values)?,
        Action::Append(id, r) => transition_append_step(store, id, r, &c, tasks, values)?,
        Action::Pair(a, b) => transition_pair_step(store, a, b, &c, tasks, values)?,
        Action::NotResult => {
            let id = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            proof! { assert(values.view() =~= v0.drop_last()); }
            tasks.push(Action::Not(id));
            proof! {
                machine_driver_result_effect(store.graph(), ActionShape::NotResult, p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Not(id@)));
                machine_driver_result(store.graph(), p0, None, v0);
            }
        }
        Action::AppendResult(r) => {
            let id = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            proof! { assert(values.view() =~= v0.drop_last()); }
            tasks.push(Action::Append(id, r));
            proof! {
                machine_driver_result_effect(store.graph(), ActionShape::AppendResult(r@), p0, v0);
                assert(transition_action_views(tasks.view()) =~= p0.push(ActionShape::Append(id@, r@)));
                machine_driver_result(store.graph(), p0, Some(r@), v0);
            }
        }
        Action::SwapThen => {
            let a = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            let b = match values.pop() {
                Some(v) => v,
                None => return Err(invariant()),
            };
            proof! { assert(values.view() =~= v0.take(v0.len() as int - 2)); }
            values.push(a);
            values.push(b);
            proof! {
                machine_driver_swap_effect(store.graph(), p0, v0);
                assert(values.view() =~= v0.take(v0.len() as int - 2).push(v0[v0.len() - 1]).push(v0[v0.len() - 2]));
                machine_driver_swap(store.graph(), p0, v0);
            }
        }
    }
    Ok(())
}
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_configuration_valid(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        transition_configuration_valid(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()),
        match result {
            Ok(()) => transition_program_refines(
                transition_program(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
                transition_program(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view()))
                && machine_cost(final(store).graph(), transition_action_views(final(tasks).view()), final(values).view())
                    < machine_cost(old(store).graph(), transition_action_views(old(tasks).view()), old(values).view()),
            Err(_) => true,
        },
)]
fn transition_next<G: KernelStore>(
    store: &mut G,
    tasks: &mut WorkVec<Action>,
    values: &mut WorkVec<TransitionId>,
) -> KernelResult<()> {
    proof_decl! { let ghost entry = store.graph(); let ghost p0 = transition_action_views(tasks.view()); let ghost v0 = values.view(); }
    let task = match tasks.pop() {
        Some(v) => v,
        None => return Err(invariant()),
    };
    proof_decl! { let ghost shape = task@; let ghost pending = transition_action_views(tasks.view()); }
    proof! { assert(p0 =~= pending.push(shape)); }
    proof! {
        assert forall|i: int| 0 <= i < pending.len() implies transition_action_valid(store.graph(), pending[i]) by {
            assert(p0[i] == pending[i]);
            assert(transition_action_valid(store.graph(), p0[i]));
        }
    }
    transition_step(store, task, tasks, values)?;
    proof! {
        transition_lemma_program_stable(entry, store.graph(), p0, v0);
        transition_lemma_effect_frame(store.graph(), shape, pending, v0, transition_action_views(tasks.view()), values.view());
    }
    Ok(())
}
#[verus_verify]
// Only successful-return correctness is claimed; each step lowers `verify::machine_cost`.
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition_action_valid(old(store).graph(), initial@), transition_action_pushes(initial@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(id) => id@ < final(store).graph().transitions.len()
            && transition_result(final(store).graph(), initial@, id), Err(_) => true },
)]
fn transition_machine<G: KernelStore>(
    store: &mut G,
    initial: Action,
) -> KernelResult<TransitionId> {
    proof_decl! { let ghost entry = store.graph(); let ghost shape = initial@;
    let ghost original = transition_program(entry, seq![shape], Seq::empty()); }
    let mut tasks = WorkVec::new();
    let mut values = WorkVec::new();
    tasks.push(initial);
    proof! {
        assert(tasks.view() =~= seq![initial]);
        assert(transition_action_views(tasks.view())[0] == shape);
        assert(transition_action_views(tasks.view()) =~= seq![shape]);
    }
    let mut state = Ok(());
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            store.restoration() == old(store).restoration(),
            model::graph_wf(store.graph()), store.valid_store(), model::graph_extends(entry, store.graph()),
            transition_configuration_valid(store.graph(), transition_action_views(tasks.view()), values.view()),
            state.is_ok() ==> transition_program_refines(original,
                transition_program(store.graph(), transition_action_views(tasks.view()), values.view())),
        decreases if state.is_ok() {
            machine_cost(store.graph(), transition_action_views(tasks.view()), values.view()) + 1
        } else { 0 },
    ))]
    while !tasks.is_empty() && state.is_ok() {
        proof_decl! { let ghost before = store.graph();
        let ghost before_program = transition_program(before, transition_action_views(tasks.view()), values.view()); }
        state = transition_next(store, &mut tasks, &mut values);
        proof! {
            transition_lemma_extends_transitive(entry, before, store.graph());
            if state.is_ok() {
                guarded_lemma_program_transitive(transition_context_sem(), transition_context_valid(), original,
                    before_program, transition_program(store.graph(), transition_action_views(tasks.view()), values.view()));
            }
        }
    }
    state?;
    proof! {
        assert(tasks.view().len() == 0);
        assert(transition_freeze_tasks(store.graph(), transition_action_views(tasks.view())) =~= Seq::<TransitionAction>::empty());
        transition_lemma_program_stable(entry, store.graph(), seq![shape], Seq::empty());
        machine_driver_complete(store.graph(), shape, values.view());
    }
    match values.pop() {
        Some(v) => Ok(v),
        None => Err(invariant()),
    }
}
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        test@ < old(store).graph().tests.len(), then_id@ < old(store).graph().transitions.len(),
        else_id@ < old(store).graph().transitions.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(id) => id@ < final(store).graph().transitions.len()
            && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(final(store).graph(), sym, theta, id, event, word)
                    == transition_if_combo(final(store).graph(), sym, theta, test, then_id, else_id, event, word), Err(_) => true },
)]
pub(crate) fn transition_if<G: KernelStore>(
    store: &mut G,
    test: TestId,
    then_id: TransitionId,
    else_id: TransitionId,
) -> KernelResult<TransitionId> {
    proof_decl! { let ghost entry = store.graph(); }
    let id = local_if(store, test, then_id, else_id)?;
    let path = store.constants().test_true;
    proof! {
        transition_lemma_constants(store.graph());
        machine_driver_extension_future(entry, store.graph());
        machine_driver_if_future(store.graph(), test, then_id, else_id, id);
    }
    clean_transition_path(store, id, path)
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(),
        transition@ < old(store).graph().transitions.len(), path@ < old(store).graph().tests.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(id) => id@ < final(store).graph().transitions.len()
            && transition_result(final(store).graph(), ActionShape::Clean(transition@, path@), id), Err(_) => true },
)]
pub(crate) fn clean_transition_path<G: KernelStore>(
    store: &mut G,
    transition: TransitionId,
    path: TestId,
) -> KernelResult<TransitionId> {
    transition_machine(store, Action::Clean(transition, path))
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition_ids_valid(old(store).graph(), children@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(id) => id@ < final(store).graph().transitions.len()
            && transition_result(final(store).graph(), ActionShape::Fold(model::transition_ids(children@), 0), id), Err(_) => true },
)]
pub(crate) fn transition_intersect<G: KernelStore>(
    store: &mut G,
    children: &[TransitionId],
) -> KernelResult<TransitionId> {
    proof! { lemma_id_clones(); }
    let mut xs = WorkVec::new();
    xs.extend_from_slice(children);
    transition_machine(store, Action::Fold(xs, 0))
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition@ < old(store).graph().transitions.len(),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(id) => id@ < final(store).graph().transitions.len()
            && transition_result(final(store).graph(), ActionShape::Not(transition@), id), Err(_) => true },
)]
pub(crate) fn transition_not<G: KernelStore>(
    store: &mut G,
    transition: TransitionId,
) -> KernelResult<TransitionId> {
    transition_machine(store, Action::Not(transition))
}
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires model::graph_wf(old(store).graph()), old(store).valid_store(), transition@ < old(store).graph().transitions.len(),
        regex_ids_valid(old(store).graph(), suffix@),
    ensures model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        model::graph_wf(final(store).graph()), final(store).valid_store(),
        match result { Ok(id) => id@ < final(store).graph().transitions.len()
            && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(final(store).graph(), sym, theta, id, event, word)
                    == transition_append_combo(final(store).graph(), sym, theta, transition, suffix@, event, word), Err(_) => true },
)]
pub(crate) fn transition_append<G: KernelStore>(
    store: &mut G,
    transition: TransitionId,
    suffix: &[RegexId],
) -> KernelResult<TransitionId> {
    proof_decl! { let ghost entry = store.graph(); }
    let r = regex_concat(store, suffix)?;
    proof! {
        machine_driver_extension_future(entry, store.graph());
        machine_driver_append_future(store.graph(), transition, suffix@, r);
    }
    transition_machine(store, Action::Append(transition, r))
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;

    verus! {
            pub open spec fn test_ids_valid(g: model::Graph, ids: Seq<TestId>) -> bool {
                forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.tests.len()
            }
            pub open spec fn regex_ids_valid(g: model::Graph, ids: Seq<RegexId>) -> bool {
                forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.regexes.len()
            }
            pub open spec fn transition_ids_valid(g: model::Graph, ids: Seq<TransitionId>) -> bool {
                forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.transitions.len()
            }
            pub open spec fn test_combo(
                g: model::Graph, sym: model::Symbols, theta: Seq<Data>, ids: Seq<TestId>, e: Data, and: bool,
            ) -> bool {
                if and {
                    forall|i: int| 0 <= i < ids.len()
                        ==> model::test_holds(sym, theta, model::lift_test(g, ids[i]@), e)
                } else {
                    exists|i: int| 0 <= i < ids.len()
                        && model::test_holds(sym, theta, model::lift_test(g, ids[i]@), e)
                }
            }
            pub open spec fn regex_combo(
                g: model::Graph, sym: model::Symbols, theta: Seq<Data>, ids: Seq<RegexId>, w: Seq<Data>, intersect: bool,
            ) -> bool {
                if intersect {
                    forall|i: int| 0 <= i < ids.len() ==> model::regex_lang(g, sym, theta, ids[i]@, w)
                } else {
                    exists|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, ids[i]@, w)
                }
            }
            pub open spec fn concat_combo(
                g: model::Graph, sym: model::Symbols, theta: Seq<Data>, ids: Seq<RegexId>, w: Seq<Data>,
            ) -> bool {
                language::lang(model::gsem(sym, theta),
                    language::Regex::Concat(model::lift_regexes(g, model::regex_ids(ids))), w)
            }
            pub open spec fn transition_lang(
                g: model::Graph, sym: model::Symbols, theta: Seq<Data>, id: TransitionId, e: Data, w: Seq<Data>,
            ) -> bool {
                language::lang(model::gsem(sym, theta), language::interp_transition(
                    model::gsem(sym, theta), e, model::lift_transition(g, id@)), w)
            }
            pub open spec fn transition_combo(
                g: model::Graph, sym: model::Symbols, theta: Seq<Data>, ids: Seq<TransitionId>, e: Data, w: Seq<Data>, intersect: bool,
            ) -> bool {
                if intersect {
                    forall|i: int| 0 <= i < ids.len() ==> transition_lang(g, sym, theta, ids[i], e, w)
                } else {
                    exists|i: int| 0 <= i < ids.len() && transition_lang(g, sym, theta, ids[i], e, w)
                }
            }

    // Boolean normalization proofs.
    pub open spec fn test_distinct_heads(left: model::TestHeadNode, right: model::TestHeadNode) -> bool {
        match (left, right) {
            (model::TestHeadNode::Atom(model::Primitive::EqCore(p, model::GTerm::Constant(c)), _),
                model::TestHeadNode::Atom(model::Primitive::EqCore(q, model::GTerm::Constant(d)), _))
                => p == q && c != d,
            _ => false,
        }
    }

    pub proof fn test_lemma_distinct_atoms(
        sym: model::Symbols, theta: Seq<Data>, left: model::TestHeadNode,
        right: model::TestHeadNode, event: Data,
    )
        requires model::symbols_wf(sym), test_distinct_heads(left, right),
        ensures match (left, right) {
            (model::TestHeadNode::Atom(p, _), model::TestHeadNode::Atom(q, _))
                => !(model::primitive_holds(sym, theta, p, event)
                    && model::primitive_holds(sym, theta, q, event)),
            _ => false,
        },
    {
        match (left, right) {
            (model::TestHeadNode::Atom(model::Primitive::EqCore(p, model::GTerm::Constant(c)), _),
                model::TestHeadNode::Atom(model::Primitive::EqCore(q, model::GTerm::Constant(d)), _)) => {
                model::lemma_constant_atoms_disjoint(sym, theta, p, c, d, event);
            },
            _ => {},
        }
    }

    pub open spec fn structural_eq<T: PartialEq>() -> bool {
        T::obeys_eq_spec() && forall|a: T, b: T| a.eq_spec(&b) == (a == b)
    }

    pub proof fn lemma_dedup_push<T: PartialEq>(s: Seq<T>, value: T)
        requires structural_eq::<T>(),
        ensures dedup_spec(s.push(value))
            == if s.len() != 0 && s.last() == value {
                dedup_spec(s)
            } else {
                dedup_spec(s).push(value)
            },
    {
        reveal(dedup_spec);
        assert(s.push(value).drop_last() =~= s);
    }

    pub proof fn lemma_dedup_properties<T: PartialEq>(s: Seq<T>)
        requires structural_eq::<T>(),
        ensures
            dedup_spec(s).len() <= s.len(),
            dedup_spec(s).len() == 0 <==> s.len() == 0,
            s.len() > 0 ==> dedup_spec(s).last() == s.last(),
            forall|v: T| dedup_spec(s).contains(v) <==> s.contains(v),
            forall|i: int| 0 < i < dedup_spec(s).len()
                ==> dedup_spec(s)[i - 1]
                    != #[trigger] dedup_spec(s)[i],
        decreases s.len(),
    {
        if s.len() > 0 {
            let prior = s.drop_last();
            lemma_dedup_properties(prior);
            lemma_dedup_push(prior, s.last());
            assert(prior.push(s.last()) =~= s);
            let dedup = dedup_spec(prior);
            let out = dedup_spec(s);
            assert forall|v: T| out.contains(v) <==> s.contains(v) by {
                if out.contains(v) {
                    let i = choose|i: int| 0 <= i < out.len() && out[i] == v;
                    if i < dedup.len() {
                        assert(dedup.contains(v));
                        assert(prior.contains(v));
                        let j = choose|j: int| 0 <= j < prior.len() && prior[j] == v;
                        assert(s[j] == v);
                    } else { assert(s[s.len() - 1] == v); }
                }
                if s.contains(v) {
                    let i = choose|i: int| 0 <= i < s.len() && s[i] == v;
                    if i < prior.len() || (prior.len() > 0 && prior.last() == s.last()) {
                        if i < prior.len() { assert(prior[i] == v); }
                        else { assert(prior[prior.len() - 1] == v); }
                        assert(prior.contains(v));
                        assert(dedup.contains(v));
                        let j = choose|j: int| 0 <= j < dedup.len() && dedup[j] == v;
                        assert(out[j] == v);
                    } else { assert(out[out.len() - 1] == v); }
                }
            }
        }
    }

    pub proof fn lemma_dedup_ordered<T: PartialEq>(s: Seq<T>, relation: spec_fn(T, T) -> bool)
        requires structural_eq::<T>(),
            forall|i: int, j: int| 0 <= i < j < s.len() ==> relation(s[i], s[j]),
        ensures forall|i: int, j: int|
            0 <= i < j < dedup_spec(s).len()
            ==> relation(dedup_spec(s)[i],
                dedup_spec(s)[j]),
        decreases s.len(),
    {
        if s.len() > 0 {
            let prior = s.drop_last();
            lemma_dedup_properties(prior);
            lemma_dedup_ordered(prior, relation);
            lemma_dedup_push(prior, s.last());
            assert(prior.push(s.last()) =~= s);
            assert forall|i: int, j: int|
                0 <= i < j < dedup_spec(s).len()
                implies relation(dedup_spec(s)[i],
                    dedup_spec(s)[j]) by {
                let dedup = dedup_spec(prior);
                if j == dedup.len() {
                    assert(dedup.contains(dedup[i]));
                    assert(prior.contains(dedup[i]));
                    let k = choose|k: int| 0 <= k < prior.len() && prior[k] == dedup[i];
                    assert(relation(s[k], s[s.len() - 1]));
                }
            }
        }
    }

    pub proof fn lemma_dedup_strict<T: PartialEq>(s: Seq<T>, key: spec_fn(T) -> nat)
        requires structural_eq::<T>(),
            forall|a: T, b: T| #[trigger] key(a) == #[trigger] key(b) ==> a == b,
            forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] key(s[i]) <= #[trigger] key(s[j]),
        ensures forall|i: int, j: int|
            0 <= i < j < dedup_spec(s).len()
            ==> #[trigger] key(dedup_spec(s)[i])
                < #[trigger] key(dedup_spec(s)[j]),
    {
        lemma_dedup_properties(s);
        lemma_dedup_ordered(s, |a: T, b: T| key(a) <= key(b));
        let out = dedup_spec(s);
        assert forall|i: int, j: int| 0 <= i < j < out.len()
            implies key(out[i]) < key(out[j]) by {
            if key(out[i]) == key(out[j]) {
                assert(key(out[i]) == key(out[i + 1]));
                assert(out[i] == out[i + 1]);
            }
        }
    }


    pub open spec fn test_children(g: model::Graph, id: TestId) -> Seq<nat> {
        if id@ < g.tests.len() {
            match g.tests[id@ as int] {
                model::TestNode::And(cs) | model::TestNode::Or(cs) => cs,
                _ => Seq::empty(),
            }
        } else { Seq::empty() }
    }

    pub open spec fn test_child_count(g: model::Graph, id: TestId, count: nat) -> bool {
        id@ < g.tests.len() && match g.tests[id@ as int] {
            model::TestNode::And(cs) | model::TestNode::Or(cs) => cs.len() == count,
            _ => false,
        }
    }

    pub proof fn test_lemma_children(g: model::Graph, id: TestId, count: nat)
        requires model::graph_wf(g), test_child_count(g, id, count),
        ensures test_children(g, id).len() == count,
            model::nondecreasing(test_children(g, id)),
            model::bounded(test_children(g, id), id@),
            forall|i: int| 0 <= i < count
                ==> model::test_node_child(g.tests[id@ as int], i as nat) == Some(test_children(g, id)[i]),
    {
        model::lemma_graph_test_wf(g, id@);
    }

    pub proof fn lemma_multiset_members<T>(left: Seq<T>, right: Seq<T>)
        requires left.to_multiset() == right.to_multiset(),
        ensures forall|v: T| left.contains(v) <==> right.contains(v),
    {
        assert forall|v: T| left.contains(v) <==> right.contains(v) by {
            vstd::seq_lib::to_multiset_contains(left, v);
            vstd::seq_lib::to_multiset_contains(right, v);
        }
    }

    pub proof fn test_lemma_combo_inclusion(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data,
        left: Seq<TestId>, right: Seq<TestId>, and: bool,
    )
        requires forall|id: TestId| left.contains(id) ==> right.contains(id),
        ensures if and {
            test_combo(g, sym, theta, right, event, and) ==> test_combo(g, sym, theta, left, event, and)
        } else {
            test_combo(g, sym, theta, left, event, and) ==> test_combo(g, sym, theta, right, event, and)
        },
    {
        if and {
            if test_combo(g, sym, theta, right, event, and) {
                assert forall|i: int| 0 <= i < left.len()
                    implies model::test_holds(sym, theta, model::lift_test(g, left[i]@), event) by {
                    assert(left.contains(left[i]));
                    assert(right.contains(left[i]));
                    let j = choose|j: int| 0 <= j < right.len() && right[j] == left[i];
                }
            }
        } else if test_combo(g, sym, theta, left, event, and) {
            let i = choose|i: int| 0 <= i < left.len()
                && model::test_holds(sym, theta, model::lift_test(g, left[i]@), event);
            assert(left.contains(left[i]));
            assert(right.contains(left[i]));
            let j = choose|j: int| 0 <= j < right.len() && right[j] == left[i];
            assert(model::test_holds(sym, theta, model::lift_test(g, right[j]@), event));
        }
    }

    pub proof fn test_lemma_combo_membership(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data,
        left: Seq<TestId>, right: Seq<TestId>, and: bool,
    )
        requires forall|id: TestId| left.contains(id) <==> right.contains(id),
        ensures test_combo(g, sym, theta, left, event, and) == test_combo(g, sym, theta, right, event, and),
    {
        test_lemma_combo_inclusion(g, sym, theta, event, left, right, and);
        test_lemma_combo_inclusion(g, sym, theta, event, right, left, and);
    }

    pub proof fn test_lemma_combo_permutation(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data,
        left: Seq<TestId>, right: Seq<TestId>, and: bool,
    )
        requires left.to_multiset() == right.to_multiset(),
        ensures test_combo(g, sym, theta, left, event, and) == test_combo(g, sym, theta, right, event, and),
    {
        lemma_multiset_members(left, right);
        test_lemma_combo_membership(g, sym, theta, event, left, right, and);
    }

    pub proof fn test_lemma_semantics_unfold(sym: model::Symbols, theta: Seq<Data>, event: Data, test: model::Test)
        ensures match test {
            model::Test::And(cs) => model::test_holds(sym, theta, test, event)
                == (forall|i: int| 0 <= i < cs.len() ==> model::test_holds(sym, theta, cs[i], event)),
            model::Test::Or(cs) => model::test_holds(sym, theta, test, event)
                == (exists|i: int| 0 <= i < cs.len() && model::test_holds(sym, theta, cs[i], event)),
            _ => true,
        },
    {
        match test { model::Test::And(_) => {}, model::Test::Or(_) => {}, _ => {} }
    }

    pub proof fn test_lemma_compound_child(sym: model::Symbols, theta: Seq<Data>, event: Data,
        children: Seq<model::Test>, index: int)
        requires 0 <= index < children.len(),
        ensures model::test_holds(sym, theta, model::Test::And(children), event)
            ==> model::test_holds(sym, theta, children[index], event),
            model::test_holds(sym, theta, children[index], event)
            ==> model::test_holds(sym, theta, model::Test::Or(children), event),
    {
        test_lemma_semantics_unfold(sym, theta, event, model::Test::And(children));
        test_lemma_semantics_unfold(sym, theta, event, model::Test::Or(children));
    }

    pub proof fn test_lemma_compound_semantics(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data,
        parent: TestId, children: Seq<TestId>, and: bool,
    )
        requires model::graph_wf(g), parent@ < g.tests.len(),
            g.tests[parent@ as int] == if and { model::TestNode::And(model::test_ids(children)) }
                else { model::TestNode::Or(model::test_ids(children)) },
        ensures model::test_holds(sym, theta, model::lift_test(g, parent@), event)
            == test_combo(g, sym, theta, children, event, and),
    {
        model::lemma_graph_test_wf(g, parent@);
        let lifted = model::lift_tests(g, model::test_ids(children), parent@);
        assert forall|i: int| 0 <= i < children.len()
            implies lifted[i] == model::lift_test(g, children[i]@) by {}
        assert(model::lift_test(g, parent@) == if and { model::Test::And(lifted) } else { model::Test::Or(lifted) });
        assert(lifted.len() == children.len());
        test_lemma_semantics_unfold(sym, theta, event, model::Test::And(lifted));
        test_lemma_semantics_unfold(sym, theta, event, model::Test::Or(lifted));
        if and {
            if test_combo(g, sym, theta, children, event, true) {
                assert forall|i: int| 0 <= i < lifted.len()
                    implies model::test_holds(sym, theta, lifted[i], event) by {
                    assert(model::test_holds(sym, theta, model::lift_test(g, children[i]@), event));
                }
                assert(model::test_holds(sym, theta, model::Test::And(lifted), event));
            } else {
                let i = choose|i: int| 0 <= i < children.len()
                    && !model::test_holds(sym, theta, model::lift_test(g, children[i]@), event);
                test_lemma_compound_child(sym, theta, event, lifted, i);
                assert(!model::test_holds(sym, theta, model::Test::And(lifted), event));
            }
        } else {
            if test_combo(g, sym, theta, children, event, false) {
                let i = choose|i: int| 0 <= i < children.len()
                    && model::test_holds(sym, theta, model::lift_test(g, children[i]@), event);
                test_lemma_compound_child(sym, theta, event, lifted, i);
                assert(model::test_holds(sym, theta, model::Test::Or(lifted), event));
            } else {
                assert forall|i: int| 0 <= i < lifted.len()
                    implies !model::test_holds(sym, theta, lifted[i], event) by {
                    assert(!model::test_holds(sym, theta, model::lift_test(g, children[i]@), event));
                }
                assert(!model::test_holds(sym, theta, model::Test::Or(lifted), event));
            }
        }
    }

    pub proof fn test_lemma_strict_members_equal(left: Seq<nat>, right: Seq<nat>)
        requires
            forall|i: int, j: int| 0 <= i < j < left.len() ==> #[trigger] left[i] < #[trigger] left[j],
            forall|i: int, j: int| 0 <= i < j < right.len() ==> #[trigger] right[i] < #[trigger] right[j],
            forall|v: nat| left.contains(v) <==> right.contains(v),
        ensures left == right,
    {
        assert(left.no_duplicates());
        assert(right.no_duplicates());
        left.lemma_multiset_has_no_duplicates();
        right.lemma_multiset_has_no_duplicates();
        assert forall|v: nat| left.to_multiset().count(v) == right.to_multiset().count(v) by {
            vstd::seq_lib::to_multiset_contains(left, v);
            vstd::seq_lib::to_multiset_contains(right, v);
        }
        assert(left.to_multiset() =~= right.to_multiset());
        vstd::seq_lib::lemma_sorted_unique(left, right, |a: nat, b: nat| a <= b);
    }

    pub proof fn test_lemma_strict_subset_length(left: Seq<nat>, right: Seq<nat>)
        requires
            forall|i: int, j: int| 0 <= i < j < left.len() ==> #[trigger] left[i] < #[trigger] left[j],
            forall|i: int, j: int| 0 <= i < j < right.len() ==> #[trigger] right[i] < #[trigger] right[j],
            forall|v: nat| left.contains(v) ==> right.contains(v),
        ensures left.len() <= right.len(), left != right ==> left.len() < right.len(),
    {
        assert(left.no_duplicates());
        assert(right.no_duplicates());
        left.unique_seq_to_set();
        right.unique_seq_to_set();
        left.to_set_ensures();
        right.to_set_ensures();
        assert(left.to_set().subset_of(right.to_set()));
        vstd::set_lib::lemma_len_subset(left.to_set(), right.to_set());
        if left.len() == right.len() {
            vstd::set_lib::lemma_subset_equality(left.to_set(), right.to_set());
            assert forall|v: nat| left.contains(v) <==> right.contains(v) by {
                assert(left.to_set().contains(v) == right.to_set().contains(v));
            }
            test_lemma_strict_members_equal(left, right);
        }
    }


    pub open spec fn test_dual(g: model::Graph, id: TestId, and: bool) -> bool {
        id@ < g.tests.len() && match g.tests[id@ as int] {
            model::TestNode::Or(_) => and,
            model::TestNode::And(_) => !and,
            _ => false,
        }
    }

    pub open spec fn test_redundancy(g: model::Graph, a: TestId, b: TestId, and: bool) -> bool {
        a != b && a@ < g.tests.len() && b@ < g.tests.len() && (
            (test_dual(g, a, and) && if test_dual(g, b, and) {
                forall|child: nat| #[trigger] test_children(g, b).contains(child)
                    ==> test_children(g, a).contains(child)
            } else { test_children(g, a).contains(b@) })
            || (test_distinct_heads(model::test_node_head(g.tests[a@ as int]), model::test_node_head(g.tests[b@ as int]))
                && match (g.tests[a@ as int], g.tests[b@ as int]) {
                    (model::TestNode::Atom(_, x), model::TestNode::Atom(_, y)) => x != and && y == and,
                    _ => false,
                })
        )
    }

    pub open spec fn test_redundant_in(g: model::Graph, a: TestId, siblings: Seq<TestId>, and: bool) -> bool {
        exists|i: int| 0 <= i < siblings.len() && test_redundancy(g, a, siblings[i], and)
    }

    pub open spec fn test_redundancy_rank(g: model::Graph, id: TestId, and: bool) -> nat {
        if test_dual(g, id, and) { test_children(g, id).len() + 2 } else {
            if id@ < g.tests.len() && match g.tests[id@ as int] {
                model::TestNode::Atom(_, positive) => positive == and,
                _ => false,
            } { 0 } else { 1 }
        }
    }

    pub open spec fn test_dominates(g: model::Graph, a: TestId, b: TestId, and: bool) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            ==> if and { test_truth(g, sym, theta, b@, event) ==> test_truth(g, sym, theta, a@, event) }
                else { test_truth(g, sym, theta, a@, event) ==> test_truth(g, sym, theta, b@, event) }
    }

    pub proof fn test_lemma_redundancy(g: model::Graph, a: TestId, b: TestId, and: bool)
        requires model::graph_wf(g), test_redundancy(g, a, b, and),
        ensures test_redundancy_rank(g, b, and) < test_redundancy_rank(g, a, and),
            test_dominates(g, a, b, and),
    {
        model::lemma_graph_wf_elim(g);
        model::lemma_graph_test_wf(g, a@);
        model::lemma_graph_test_wf(g, b@);
        if test_dual(g, a, and) {
            if test_dual(g, b, and) {
                let ac = test_children(g, a);
                let bc = test_children(g, b);
                assert(ac != bc) by {
                    if ac == bc { assert(g.tests[a@ as int] == g.tests[b@ as int]); }
                }
                test_lemma_strict_subset_length(bc, ac);
            }
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies if and { test_truth(g, sym, theta, b@, event) ==> test_truth(g, sym, theta, a@, event) }
                else { test_truth(g, sym, theta, a@, event) ==> test_truth(g, sym, theta, b@, event) } by {
            test_lemma_truth(g, sym, theta, a@, event);
            test_lemma_truth(g, sym, theta, b@, event);
            if !test_dual(g, a, and) {
                test_lemma_distinct_atoms(sym, theta, model::test_node_head(g.tests[a@ as int]),
                    model::test_node_head(g.tests[b@ as int]), event);
            }
        }
    }

    pub proof fn test_lemma_surviving_factor(g: model::Graph, siblings: Seq<TestId>, a: TestId, and: bool)
        requires model::graph_wf(g), test_ids_valid(g, siblings), siblings.contains(a),
        ensures exists|b: TestId| siblings.contains(b) && !test_redundant_in(g, b, siblings, and)
            && test_dominates(g, a, b, and),
        decreases test_redundancy_rank(g, a, and),
    {
        if test_redundant_in(g, a, siblings, and) {
            let i = choose|i: int| 0 <= i < siblings.len() && test_redundancy(g, a, siblings[i], and);
            let b = siblings[i];
            test_lemma_redundancy(g, a, b, and);
            assert(siblings.contains(b));
            test_lemma_surviving_factor(g, siblings, b, and);
            let survivor = choose|c: TestId| siblings.contains(c) && !test_redundant_in(g, c, siblings, and)
                && test_dominates(g, b, c, and);
            assert(test_dominates(g, a, survivor, and));
        } else { assert(test_dominates(g, a, a, and)); }
    }

    pub open spec fn test_retained(g: model::Graph, siblings: Seq<TestId>, and: bool) -> Seq<TestId> {
        siblings.filter(|id: TestId| !test_redundant_in(g, id, siblings, and))
    }

    pub proof fn test_lemma_retention(g: model::Graph, siblings: Seq<TestId>, kept: Seq<TestId>, and: bool)
        requires model::graph_wf(g), test_ids_valid(g, siblings),
            forall|id: TestId| kept.contains(id) <==> siblings.contains(id) && !test_redundant_in(g, id, siblings, and),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            ==> test_combo(g, sym, theta, kept, event, and) == test_combo(g, sym, theta, siblings, event, and),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies test_combo(g, sym, theta, kept, event, and) == test_combo(g, sym, theta, siblings, event, and) by {
            test_lemma_combo_inclusion(g, sym, theta, event, kept, siblings, and);
            if and && test_combo(g, sym, theta, kept, event, and) {
                assert forall|i: int| 0 <= i < siblings.len() implies test_truth(g, sym, theta, siblings[i]@, event) by {
                    assert(siblings.contains(siblings[i]));
                    test_lemma_surviving_factor(g, siblings, siblings[i], and);
                    let b = choose|b: TestId| siblings.contains(b) && !test_redundant_in(g, b, siblings, and)
                        && test_dominates(g, siblings[i], b, and);
                    let j = choose|j: int| 0 <= j < kept.len() && kept[j] == b;
                }
            } else if !and && test_combo(g, sym, theta, siblings, event, and) {
                let i = choose|i: int| 0 <= i < siblings.len() && test_truth(g, sym, theta, siblings[i]@, event);
                assert(siblings.contains(siblings[i]));
                test_lemma_surviving_factor(g, siblings, siblings[i], and);
                let b = choose|b: TestId| siblings.contains(b) && !test_redundant_in(g, b, siblings, and)
                    && test_dominates(g, siblings[i], b, and);
                let j = choose|j: int| 0 <= j < kept.len() && kept[j] == b;
                assert(test_truth(g, sym, theta, kept[j]@, event));
            }
        }
    }

    pub open spec fn test_opposite_nat(g: model::Graph, a: nat, b: nat) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_truth(g, sym, theta, a, event) != test_truth(g, sym, theta, b, event)
    }

    pub open spec fn test_opposite(g: model::Graph, a: TestId, b: TestId) -> bool {
        test_opposite_nat(g, a@, b@)
    }

    pub open spec fn test_absorbs(g: model::Graph, ids: Seq<TestId>, and: bool) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            ==> test_combo(g, sym, theta, ids, event, and) == !and
    }

    pub open spec fn test_complement_covered(g: model::Graph, children: Seq<nat>, siblings: Seq<TestId>) -> bool {
        forall|child: nat| #[trigger] children.contains(child)
            ==> exists|i: int| 0 <= i < siblings.len() && test_opposite_nat(g, child, siblings[i]@)
    }

    pub proof fn test_lemma_combo_push(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data,
        ids: Seq<TestId>, id: TestId, and: bool)
        ensures test_combo(g, sym, theta, ids.push(id), event, and)
            == if and { test_combo(g, sym, theta, ids, event, and) && test_truth(g, sym, theta, id@, event) }
                else { test_combo(g, sym, theta, ids, event, and) || test_truth(g, sym, theta, id@, event) },
    {
        if and {
            if test_combo(g, sym, theta, ids.push(id), event, and) {
                assert(test_truth(g, sym, theta, ids.push(id)[ids.len() as int]@, event));
                assert forall|i: int| 0 <= i < ids.len() implies test_truth(g, sym, theta, ids[i]@, event) by {
                    assert(ids.push(id)[i] == ids[i]);
                }
            } else {
                let i = choose|i: int| 0 <= i < ids.push(id).len() && !test_truth(g, sym, theta, ids.push(id)[i]@, event);
            }
        } else {
            if test_combo(g, sym, theta, ids.push(id), event, and) {
                let i = choose|i: int| 0 <= i < ids.push(id).len() && test_truth(g, sym, theta, ids.push(id)[i]@, event);
            } else {
                assert(!test_truth(g, sym, theta, ids.push(id)[ids.len() as int]@, event));
                assert forall|i: int| 0 <= i < ids.len() implies !test_truth(g, sym, theta, ids[i]@, event) by {
                    assert(ids.push(id)[i] == ids[i]);
                }
            }
        }
    }

    pub proof fn test_lemma_combo_extends(a: model::Graph, b: model::Graph, ids: Seq<TestId>)
        requires model::graph_extends(a, b), test_ids_valid(a, ids),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, and: bool|
            test_combo(a, sym, theta, ids, event, and) == test_combo(b, sym, theta, ids, event, and),
    {
        assert forall|i: int| 0 <= i < ids.len()
            implies model::lift_test(a, ids[i]@) == model::lift_test(b, ids[i]@) by {
            model::lemma_lift_test_stable(a, b, ids[i]@);
        }
    }

    pub proof fn test_lemma_opposite_extends(a: model::Graph, b: model::Graph, x: TestId, y: TestId)
        requires model::graph_extends(a, b), x@ < a.tests.len(), y@ < a.tests.len(), test_opposite(a, x, y),
        ensures test_opposite(b, x, y),
    {
        model::lemma_lift_test_stable(a, b, x@);
        model::lemma_lift_test_stable(a, b, y@);
    }

    pub proof fn test_lemma_absorbs_extends(a: model::Graph, b: model::Graph, ids: Seq<TestId>, and: bool)
        requires model::graph_extends(a, b), test_ids_valid(a, ids), test_absorbs(a, ids, and),
        ensures test_absorbs(b, ids, and),
    {
        test_lemma_combo_extends(a, b, ids);
    }

    pub proof fn test_lemma_absorbs_superset(g: model::Graph, left: Seq<TestId>, right: Seq<TestId>, and: bool)
        requires test_absorbs(g, left, and), forall|id: TestId| left.contains(id) ==> right.contains(id),
        ensures test_absorbs(g, right, and),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies test_combo(g, sym, theta, right, event, and) == !and by {
            test_lemma_combo_inclusion(g, sym, theta, event, left, right, and);
        }
    }

    pub proof fn test_lemma_pair_absorbs(g: model::Graph, a: TestId, b: TestId, and: bool)
        requires model::graph_wf(g), a@ < g.tests.len(), b@ < g.tests.len(),
            test_opposite(g, a, b) || (
                test_distinct_heads(model::test_node_head(g.tests[a@ as int]), model::test_node_head(g.tests[b@ as int]))
                    && match (g.tests[a@ as int], g.tests[b@ as int]) {
                        (model::TestNode::Atom(_, x), model::TestNode::Atom(_, y)) => x == and && y == and,
                        _ => false,
                    }),
        ensures test_absorbs(g, seq![a, b], and),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies test_combo(g, sym, theta, seq![a, b], event, and) == !and by {
            test_lemma_truth(g, sym, theta, a@, event);
            test_lemma_truth(g, sym, theta, b@, event);
            if !test_opposite(g, a, b) {
                test_lemma_distinct_atoms(sym, theta, model::test_node_head(g.tests[a@ as int]),
                    model::test_node_head(g.tests[b@ as int]), event);
            }
        }
    }

    pub open spec fn test_has_opposite(g: model::Graph, id: TestId, siblings: Seq<TestId>) -> bool {
        exists|i: int| 0 <= i < siblings.len() && test_opposite(g, id, siblings[i])
    }

    pub proof fn test_lemma_has_opposite_extends(a: model::Graph, b: model::Graph, id: TestId, siblings: Seq<TestId>)
        requires model::graph_extends(a, b), id@ < a.tests.len(), test_ids_valid(a, siblings), test_has_opposite(a, id, siblings),
        ensures test_has_opposite(b, id, siblings),
    {
        let i = choose|i: int| 0 <= i < siblings.len() && test_opposite(a, id, siblings[i]);
        test_lemma_opposite_extends(a, b, id, siblings[i]);
    }

    pub proof fn test_lemma_covered_extends(a: model::Graph, b: model::Graph, children: Seq<nat>, siblings: Seq<TestId>)
        requires model::graph_extends(a, b), model::bounded(children, a.tests.len()), test_ids_valid(a, siblings),
            test_complement_covered(a, children, siblings),
        ensures test_complement_covered(b, children, siblings),
    {
        assert forall|child: nat| children.contains(child) implies exists|i: int| 0 <= i < siblings.len()
            && test_opposite_nat(b, child, siblings[i]@) by {
            let j = choose|j: int| 0 <= j < children.len() && children[j] == child;
            let i = choose|i: int| 0 <= i < siblings.len() && test_opposite_nat(a, child, siblings[i]@);
            model::lemma_lift_test_stable(a, b, child);
            model::lemma_lift_test_stable(a, b, siblings[i]@);
        }
    }

    pub proof fn test_lemma_compound_absorbs(g: model::Graph, a: TestId, siblings: Seq<TestId>, and: bool)
        requires model::graph_wf(g), a@ < g.tests.len(), test_dual(g, a, and),
            test_complement_covered(g, test_children(g, a), siblings),
        ensures test_absorbs(g, seq![a] + siblings, and),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies test_combo(g, sym, theta, seq![a] + siblings, event, and) == !and by {
            test_lemma_truth(g, sym, theta, a@, event);
            test_lemma_combo_concat(g, sym, theta, event, seq![a], siblings, and);
            test_lemma_combo_push(g, sym, theta, event, Seq::empty(), a, and);
            if and {
                if test_combo(g, sym, theta, siblings, event, and) {
                    assert forall|child: nat| test_children(g, a).contains(child)
                        implies !test_truth(g, sym, theta, child, event) by {
                        let i = choose|i: int| 0 <= i < siblings.len() && test_opposite_nat(g, child, siblings[i]@);
                    }
                    assert(!test_truth(g, sym, theta, a@, event));
                }
            } else if !test_combo(g, sym, theta, siblings, event, and) {
                assert forall|child: nat| test_children(g, a).contains(child)
                    implies test_truth(g, sym, theta, child, event) by {
                    let i = choose|i: int| 0 <= i < siblings.len() && test_opposite_nat(g, child, siblings[i]@);
                }
                assert(test_truth(g, sym, theta, a@, event));
            }
        }
    }

    pub proof fn test_lemma_flatten(g: model::Graph, before: Seq<TestId>, after: Seq<TestId>, id: TestId, and: bool)
        requires model::graph_wf(g), id@ < g.tests.len(),
            g.tests[id@ as int] == if and { model::TestNode::And(test_children(g, id)) }
                else { model::TestNode::Or(test_children(g, id)) },
            before.is_prefix_of(after), after.len() == before.len() + test_children(g, id).len(),
            forall|i: int| 0 <= i < test_children(g, id).len()
                ==> #[trigger] after[before.len() + i]@ == test_children(g, id)[i],
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_combo(g, sym, theta, after, event, and) == test_combo(g, sym, theta, before.push(id), event, and),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_combo(g, sym, theta, after, event, and) == test_combo(g, sym, theta, before.push(id), event, and) by {
            test_lemma_truth(g, sym, theta, id@, event);
            test_lemma_combo_push(g, sym, theta, event, before, id, and);
            if and {
                if test_combo(g, sym, theta, after, event, and) {
                    assert forall|i: int| 0 <= i < before.len() implies test_truth(g, sym, theta, before[i]@, event) by {
                        assert(after[i] == before[i]);
                    }
                    assert forall|child: nat| test_children(g, id).contains(child) implies test_truth(g, sym, theta, child, event) by {
                        let i = choose|i: int| 0 <= i < test_children(g, id).len() && test_children(g, id)[i] == child;
                        assert(test_truth(g, sym, theta, after[before.len() + i]@, event));
                    }
                } else {
                    let i = choose|i: int| 0 <= i < after.len() && !test_truth(g, sym, theta, after[i]@, event);
                    if i < before.len() { assert(after[i] == before[i]); }
                    else {
                        let j = i - before.len() as int;
                        assert(0 <= j < test_children(g, id).len());
                        assert(before.len() + j == i);
                        assert(after[before.len() + j]@ == test_children(g, id)[j]);
                        assert(after[i]@ == test_children(g, id)[i - before.len() as int]);
                        assert(test_children(g, id).contains(after[i]@));
                    }
                }
            } else {
                if test_combo(g, sym, theta, after, event, and) {
                    let i = choose|i: int| 0 <= i < after.len() && test_truth(g, sym, theta, after[i]@, event);
                    if i < before.len() { assert(after[i] == before[i]); }
                    else {
                        let j = i - before.len() as int;
                        assert(0 <= j < test_children(g, id).len());
                        assert(before.len() + j == i);
                        assert(after[before.len() + j]@ == test_children(g, id)[j]);
                        assert(after[i]@ == test_children(g, id)[i - before.len() as int]);
                        assert(test_children(g, id).contains(after[i]@));
                    }
                } else {
                    assert forall|i: int| 0 <= i < before.len() implies !test_truth(g, sym, theta, before[i]@, event) by {
                        assert(after[i] == before[i]);
                    }
                    assert forall|child: nat| test_children(g, id).contains(child) implies !test_truth(g, sym, theta, child, event) by {
                        let i = choose|i: int| 0 <= i < test_children(g, id).len() && test_children(g, id)[i] == child;
                        assert(!test_truth(g, sym, theta, after[before.len() + i]@, event));
                    }
                }
            }
        }
    }

    pub proof fn test_lemma_filter_ordered<T>(s: Seq<T>, predicate: spec_fn(T) -> bool, key: spec_fn(T) -> nat)
        requires forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] key(s[i]) < #[trigger] key(s[j]),
        ensures forall|i: int, j: int| 0 <= i < j < s.filter(predicate).len()
            ==> #[trigger] key(s.filter(predicate)[i]) < #[trigger] key(s.filter(predicate)[j]),
        decreases s.len(),
    {
        if s.len() > 0 {
            let prior = s.drop_last();
            test_lemma_filter_ordered(prior, predicate, key);
            prior.lemma_filter_push(s.last(), predicate);
            assert(prior.push(s.last()) =~= s);
            assert forall|i: int, j: int| 0 <= i < j < s.filter(predicate).len()
                implies key(s.filter(predicate)[i]) < key(s.filter(predicate)[j]) by {
                if predicate(s.last()) && j == prior.filter(predicate).len() {
                    prior.lemma_filter_contains_rev(predicate, prior.filter(predicate)[i]);
                    let k = choose|k: int| 0 <= k < prior.len() && prior[k] == prior.filter(predicate)[i];
                    assert(key(s[k]) < key(s[s.len() - 1]));
                }
            }
        }
    }

    pub proof fn test_lemma_retained_members(g: model::Graph, siblings: Seq<TestId>, and: bool)
        ensures forall|id: TestId| test_retained(g, siblings, and).contains(id)
            <==> siblings.contains(id) && !test_redundant_in(g, id, siblings, and),
    {
        let predicate = |id: TestId| !test_redundant_in(g, id, siblings, and);
        assert forall|id: TestId| siblings.filter(predicate).contains(id)
            <==> siblings.contains(id) && predicate(id) by {
            if siblings.filter(predicate).contains(id) {
                siblings.lemma_filter_contains_rev(predicate, id);
                let i = choose|i: int| 0 <= i < siblings.filter(predicate).len() && siblings.filter(predicate)[i] == id;
                siblings.lemma_filter_pred(predicate, i);
            } else if siblings.contains(id) && predicate(id) {
                let i = choose|i: int| 0 <= i < siblings.len() && siblings[i] == id;
                siblings.lemma_filter_contains(predicate, i);
            }
        }
    }

    pub proof fn test_lemma_constants_semantics(g: model::Graph)
        requires model::graph_wf(g),
        ensures g.constants.test_true < g.tests.len(), g.constants.test_false < g.tests.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_truth(g, sym, theta, g.constants.test_true, event)
                    && !test_truth(g, sym, theta, g.constants.test_false, event),
    {
        model::lemma_graph_wf_elim(g);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_truth(g, sym, theta, g.constants.test_true, event)
                && !test_truth(g, sym, theta, g.constants.test_false, event) by {
            test_lemma_truth(g, sym, theta, g.constants.test_true, event);
            test_lemma_truth(g, sym, theta, g.constants.test_false, event);
        }
    }


    #[verifier::opaque]
    pub open spec fn test_negation_row(g: model::Graph, relation: Set<(nat, nat)>, left: nat, right: nat) -> bool {
        left < g.tests.len() && right < g.tests.len() && match (g.tests[left as int], g.tests[right as int]) {
            (model::TestNode::True, model::TestNode::False) => true,
            (model::TestNode::False, model::TestNode::True) => true,
            (model::TestNode::Atom(p, x), model::TestNode::Atom(q, y)) => p == q && x != y,
            (model::TestNode::And(cs), model::TestNode::Or(ds)) => {
                model::bounded(cs, left) && model::bounded(ds, right)
                    && test_negation_children(relation, cs, ds)
            },
            (model::TestNode::Or(cs), model::TestNode::And(ds)) => {
                model::bounded(cs, left) && model::bounded(ds, right)
                    && test_negation_children(relation, cs, ds)
            },
            _ => false,
        }
    }

    pub open spec fn test_negation_functional(relation: Set<(nat, nat)>) -> bool {
        forall|input: nat, a: nat, b: nat|
            #[trigger] relation.contains((input, a)) && #[trigger] relation.contains((input, b)) ==> a == b
    }

    pub open spec fn test_negation_injective(relation: Set<(nat, nat)>) -> bool {
        forall|output: nat, a: nat, b: nat|
            #[trigger] relation.contains((a, output)) && #[trigger] relation.contains((b, output)) ==> a == b
    }

    pub open spec fn test_negation_children(relation: Set<(nat, nat)>, cs: Seq<nat>, ds: Seq<nat>) -> bool {
        (forall|x: nat| #[trigger] cs.contains(x) ==> exists|y: nat| ds.contains(y) && relation.contains((x, y)))
        && (forall|y: nat| #[trigger] ds.contains(y) ==> exists|x: nat| cs.contains(x) && relation.contains((x, y)))
    }

    pub proof fn test_lemma_functional_children(relation: Set<(nat, nat)>,
        cs: Seq<nat>, ds: Seq<nat>, es: Seq<nat>)
        requires test_negation_functional(relation),
            model::strictly_increasing(ds), model::strictly_increasing(es),
            test_negation_children(relation, cs, ds), test_negation_children(relation, cs, es),
        ensures ds == es,
    {
        assert forall|v: nat| ds.contains(v) <==> es.contains(v) by {
            if ds.contains(v) {
                let x = choose|x: nat| cs.contains(x) && relation.contains((x, v));
                let y = choose|y: nat| es.contains(y) && relation.contains((x, y));
                assert(v == y);
            }
            if es.contains(v) {
                let x = choose|x: nat| cs.contains(x) && relation.contains((x, v));
                let y = choose|y: nat| ds.contains(y) && relation.contains((x, y));
                assert(v == y);
            }
        }
        test_lemma_strict_members_equal(ds, es);
    }

    pub proof fn test_lemma_negation_row_functional(g: model::Graph,
        relation: Set<(nat, nat)>, pivot: nat, left: nat, right: nat)
        requires model::graph_wf(g), test_negation_functional(relation),
            test_negation_row(g, relation, pivot, left), test_negation_row(g, relation, pivot, right),
        ensures left == right,
    {
        reveal(test_negation_row);
        model::lemma_graph_wf_elim(g);
        model::lemma_graph_test_wf(g, pivot);
        model::lemma_graph_test_wf(g, left);
        model::lemma_graph_test_wf(g, right);
        match (g.tests[pivot as int], g.tests[left as int], g.tests[right as int]) {
            (model::TestNode::And(cs), model::TestNode::Or(ds), model::TestNode::Or(es)) => {
                test_lemma_functional_children(relation, cs, ds, es);
            },
            (model::TestNode::Or(cs), model::TestNode::And(ds), model::TestNode::And(es)) => {
                test_lemma_functional_children(relation, cs, ds, es);
            },
            _ => {},
        }
        assert(g.tests[left as int] == g.tests[right as int]);
    }

    pub open spec fn test_negation_reverse(relation: Set<(nat, nat)>) -> Set<(nat, nat)> {
        relation.map(|pair: (nat, nat)| (pair.1, pair.0))
    }

    pub proof fn test_lemma_negation_reverse(relation: Set<(nat, nat)>)
        ensures forall|a: nat, b: nat| #[trigger] test_negation_reverse(relation).contains((a, b))
            <==> relation.contains((b, a)),
            test_negation_injective(relation) ==> test_negation_functional(test_negation_reverse(relation)),
    {
        assert forall|a: nat, b: nat| test_negation_reverse(relation).contains((a, b))
            <==> relation.contains((b, a)) by {
            relation.lemma_map_contains(|pair: (nat, nat)| (pair.1, pair.0), (a, b));
        }
    }

    pub proof fn test_lemma_negation_row_reverse(g: model::Graph, relation: Set<(nat, nat)>, a: nat, b: nat)
        requires test_negation_row(g, relation, a, b),
        ensures test_negation_row(g, test_negation_reverse(relation), b, a),
    {
        reveal(test_negation_row);
        test_lemma_negation_reverse(relation);
        match (g.tests[a as int], g.tests[b as int]) {
            (model::TestNode::And(cs), model::TestNode::Or(ds)) => {
                assert(test_negation_children(test_negation_reverse(relation), ds, cs));
            },
            (model::TestNode::Or(cs), model::TestNode::And(ds)) => {
                assert(test_negation_children(test_negation_reverse(relation), ds, cs));
            },
            _ => {},
        }
    }

    #[verifier::opaque]
    pub open spec fn test_negation_witness(g: model::Graph, relation: Set<(nat, nat)>) -> bool {
        test_negation_functional(relation) && test_negation_injective(relation)
        && forall|pair: (nat, nat)| #[trigger] relation.contains(pair)
            ==> test_negation_row(g, relation, pair.0, pair.1)
    }

    pub proof fn test_lemma_negation_witness_elim(g: model::Graph, relation: Set<(nat, nat)>)
        requires test_negation_witness(g, relation),
        ensures test_negation_functional(relation), test_negation_injective(relation),
            forall|pair: (nat, nat)| #[trigger] relation.contains(pair)
                ==> test_negation_row(g, relation, pair.0, pair.1),
    {
        reveal(test_negation_witness);
    }

    pub proof fn test_lemma_negation_row_monotone(g: model::Graph, old: Set<(nat, nat)>, new: Set<(nat, nat)>, a: nat, b: nat)
        requires test_negation_row(g, old, a, b), old.subset_of(new),
        ensures test_negation_row(g, new, a, b),
    {
        reveal(test_negation_row);
        match (g.tests[a as int], g.tests[b as int]) {
            (model::TestNode::And(cs), model::TestNode::Or(ds)) => {
                assert(test_negation_children(new, cs, ds));
            },
            (model::TestNode::Or(cs), model::TestNode::And(ds)) => {
                assert(test_negation_children(new, cs, ds));
            },
            _ => {},
        }
    }

    pub proof fn test_lemma_negation_insert(g: model::Graph, relation: Set<(nat, nat)>, a: nat, b: nat)
        requires model::graph_wf(g), test_negation_witness(g, relation), test_negation_row(g, relation, a, b),
        ensures test_negation_witness(g, relation.insert((a, b))),
    {
        reveal(test_negation_witness);
        let next = relation.insert((a, b));
        assert forall|pivot: nat, x: nat, y: nat|
            next.contains((pivot, x)) && next.contains((pivot, y)) implies x == y by {
            if pivot == a {
                if relation.contains((a, x)) { test_lemma_negation_row_functional(g, relation, a, x, b); }
                if relation.contains((a, y)) { test_lemma_negation_row_functional(g, relation, a, y, b); }
            }
        }
        test_lemma_negation_reverse(relation);
        test_lemma_negation_row_reverse(g, relation, a, b);
        assert forall|pivot: nat, x: nat, y: nat|
            next.contains((x, pivot)) && next.contains((y, pivot)) implies x == y by {
            if pivot == b {
                if relation.contains((x, b)) {
                    test_lemma_negation_row_reverse(g, relation, x, b);
                    test_lemma_negation_row_functional(g, test_negation_reverse(relation), b, x, a);
                }
                if relation.contains((y, b)) {
                    test_lemma_negation_row_reverse(g, relation, y, b);
                    test_lemma_negation_row_functional(g, test_negation_reverse(relation), b, y, a);
                }
            }
        }
        assert(relation.subset_of(next));
        assert forall|pair: (nat, nat)| next.contains(pair) implies test_negation_row(g, next, pair.0, pair.1) by {
            test_lemma_negation_row_monotone(g, relation, next, pair.0, pair.1);
        }
    }

    #[verifier::inline]
    pub open spec fn test_truth(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, id: nat, event: Data) -> bool {
        model::test_holds(sym, theta, model::lift_test(g, id), event)
    }

    pub proof fn test_lemma_truth(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, id: nat, event: Data)
        requires model::graph_wf(g), id < g.tests.len(),
        ensures test_truth(g, sym, theta, id, event) == match g.tests[id as int] {
            model::TestNode::True => true,
            model::TestNode::False => false,
            model::TestNode::Atom(p, b) => model::primitive_holds(sym, theta, p, event) == b,
            model::TestNode::And(cs) => forall|child: nat| #[trigger] cs.contains(child)
                ==> test_truth(g, sym, theta, child, event),
            model::TestNode::Or(cs) => exists|child: nat| cs.contains(child)
                && test_truth(g, sym, theta, child, event),
        },
    {
        model::lemma_graph_test_wf(g, id);
        match g.tests[id as int] {
            model::TestNode::And(cs) => {
                let lifted = model::lift_tests(g, cs, id);
                test_lemma_semantics_unfold(sym, theta, event, model::Test::And(lifted));
                assert forall|i: int| 0 <= i < cs.len()

                    implies lifted[i] == model::lift_test(g, cs[i]) by {}
                if test_truth(g, sym, theta, id, event) {
                    assert forall|child: nat| cs.contains(child) implies test_truth(g, sym, theta, child, event) by {
                        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == child;
                        test_lemma_compound_child(sym, theta, event, lifted, i);
                    }
                } else {
                    let i = choose|i: int| 0 <= i < lifted.len() && !model::test_holds(sym, theta, lifted[i], event);
                    assert(cs.contains(cs[i]));
                }
            },
            model::TestNode::Or(cs) => {
                let lifted = model::lift_tests(g, cs, id);
                test_lemma_semantics_unfold(sym, theta, event, model::Test::Or(lifted));
                assert forall|i: int| 0 <= i < cs.len()
                    implies lifted[i] == model::lift_test(g, cs[i]) by {}
                if test_truth(g, sym, theta, id, event) {
                    let i = choose|i: int| 0 <= i < lifted.len() && model::test_holds(sym, theta, lifted[i], event);
                    assert(cs.contains(cs[i]));
                } else {
                    assert forall|child: nat| cs.contains(child) implies !test_truth(g, sym, theta, child, event) by {
                        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == child;
                        test_lemma_compound_child(sym, theta, event, lifted, i);
                    }
                }
            },
            _ => {},
        }
    }

    pub proof fn test_lemma_negation_semantics(g: model::Graph, relation: Set<(nat, nat)>,
        left: nat, right: nat, sym: model::Symbols, theta: Seq<Data>, event: Data)
        requires model::graph_wf(g), test_negation_witness(g, relation), relation.contains((left, right)),
        ensures test_truth(g, sym, theta, left, event) != test_truth(g, sym, theta, right, event),
        decreases left,
    {
        test_lemma_negation_witness_elim(g, relation);
        reveal(test_negation_row);
        assert(test_negation_row(g, relation, left, right));
        test_lemma_truth(g, sym, theta, left, event);
        test_lemma_truth(g, sym, theta, right, event);
        match (g.tests[left as int], g.tests[right as int]) {
            (model::TestNode::And(cs), model::TestNode::Or(ds)) => {
                assert forall|a: nat, b: nat| cs.contains(a) && ds.contains(b) && relation.contains((a, b))
                    implies test_truth(g, sym, theta, a, event) != test_truth(g, sym, theta, b, event) by {
                    let i = choose|i: int| 0 <= i < cs.len() && cs[i] == a;
                    test_lemma_negation_semantics(g, relation, a, b, sym, theta, event);
                }
                if test_truth(g, sym, theta, left, event) {
                    assert forall|b: nat| ds.contains(b) implies !test_truth(g, sym, theta, b, event) by {
                        let a = choose|a: nat| cs.contains(a) && relation.contains((a, b));
                    }
                } else {
                    let a = choose|a: nat| cs.contains(a) && !test_truth(g, sym, theta, a, event);
                    let b = choose|b: nat| ds.contains(b) && relation.contains((a, b));
                    assert(test_truth(g, sym, theta, b, event));
                }
            },
            (model::TestNode::Or(cs), model::TestNode::And(ds)) => {
                assert forall|a: nat, b: nat| cs.contains(a) && ds.contains(b) && relation.contains((a, b))
                    implies test_truth(g, sym, theta, a, event) != test_truth(g, sym, theta, b, event) by {
                    let i = choose|i: int| 0 <= i < cs.len() && cs[i] == a;
                    test_lemma_negation_semantics(g, relation, a, b, sym, theta, event);
                }
                if test_truth(g, sym, theta, left, event) {
                    let a = choose|a: nat| cs.contains(a) && test_truth(g, sym, theta, a, event);
                    let b = choose|b: nat| ds.contains(b) && relation.contains((a, b));
                    assert(!test_truth(g, sym, theta, b, event));
                } else {
                    assert forall|b: nat| ds.contains(b) implies test_truth(g, sym, theta, b, event) by {
                        let a = choose|a: nat| cs.contains(a) && relation.contains((a, b));
                    }
                }
            },
            _ => {},
        }
    }

    pub open spec fn test_not_plan(g: model::Graph, tasks: Seq<(TestId, bool)>, origins: Seq<nat>) -> Option<Seq<nat>>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(origins) } else {
            let task = tasks.last();
            if task.0@ >= g.tests.len() { None } else if !task.1 {
                test_not_plan(g, tasks.drop_last(), origins.push(task.0@))
            } else {
                let cs = test_children(g, task.0);
                if !test_child_count(g, task.0, cs.len()) || cs.len() > origins.len()
                    || origins.subrange(origins.len() as int - cs.len() as int, origins.len() as int) != cs {
                    None
                } else {
                    test_not_plan(g, tasks.drop_last(), origins.subrange(0,
                        origins.len() as int - cs.len() as int).push(task.0@))
                }
            }
        }
    }

    pub open spec fn test_not_state(g: model::Graph, tasks: Seq<(TestId, bool)>, values: Seq<TestId>, root: TestId) -> bool {
        (forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].0@ < g.tests.len())
        && exists|origins: Seq<nat>, relation: Set<(nat, nat)>|
            origins.len() == values.len() && test_negation_witness(g, relation)
            && (forall|i: int| 0 <= i < values.len() ==> #[trigger] relation.contains((origins[i], values[i]@)))
            && test_not_plan(g, tasks, origins) == Some(seq![root@])
    }

    pub open spec fn test_not_node_work(g: model::Graph, id: nat) -> nat
        decreases id, 1nat,
    {
        if id >= g.tests.len() { 0 } else {
            match g.tests[id as int] {
                model::TestNode::And(cs) => 2 + test_not_children_work(g, cs, id),
                model::TestNode::Or(cs) => 2 + test_not_children_work(g, cs, id),
                _ => 1,
            }
        }
    }

    pub open spec fn test_not_children_work(g: model::Graph, children: Seq<nat>, bound: nat) -> nat
        decreases bound, 0nat, children.len(),
    {
        if children.len() == 0 { 0 } else {
            test_not_children_work(g, children.skip(1), bound)
                + if children[0] < bound { test_not_node_work(g, children[0]) } else { 0 }
        }
    }

    pub open spec fn test_not_work(g: model::Graph, tasks: Seq<(TestId, bool)>) -> nat
        decreases tasks.len(),
    {
        if tasks.len() == 0 { 0 } else {
            test_not_work(g, tasks.drop_last())
                + if tasks.last().1 { 1 } else { test_not_node_work(g, tasks.last().0@) }
        }
    }

    pub proof fn test_lemma_negation_witness_extends(a: model::Graph, b: model::Graph, relation: Set<(nat, nat)>)
        requires model::graph_extends(a, b), test_negation_witness(a, relation),
        ensures test_negation_witness(b, relation),
    {
        reveal(test_negation_witness);
        reveal(test_negation_row);
        assert forall|pair: (nat, nat)| relation.contains(pair) implies test_negation_row(b, relation, pair.0, pair.1) by {
            assert(test_negation_row(a, relation, pair.0, pair.1));
            assert(a.tests[pair.0 as int] == b.tests[pair.0 as int]);
            assert(a.tests[pair.1 as int] == b.tests[pair.1 as int]);
        }
    }

    pub open spec fn test_not_ready(g: model::Graph, id: TestId, finish: bool, values: Seq<TestId>) -> bool {
        id@ < g.tests.len() && test_ids_valid(g, values)
        && if finish {
            let cs = test_children(g, id);
            test_child_count(g, id, cs.len()) && cs.len() <= values.len()
                && values.subrange(values.len() as int - cs.len() as int, values.len() as int).no_duplicates()
        } else { true }
    }

    pub proof fn test_lemma_not_state_ready(g: model::Graph, tasks: Seq<(TestId, bool)>,
        id: TestId, finish: bool, values: Seq<TestId>, root: TestId)
        requires model::graph_wf(g), test_not_state(g, tasks.push((id, finish)), values, root),
        ensures test_not_ready(g, id, finish, values),
    {
        let (origins, relation) = choose|origins: Seq<nat>, relation: Set<(nat, nat)>|
            origins.len() == values.len() && test_negation_witness(g, relation)
            && (forall|i: int| 0 <= i < values.len() ==> relation.contains((origins[i], values[i]@)))
            && test_not_plan(g, tasks.push((id, finish)), origins) == Some(seq![root@]);
        test_lemma_negation_witness_elim(g, relation);
        reveal(test_negation_row);
        assert forall|i: int| 0 <= i < values.len() implies values[i]@ < g.tests.len() by {
            assert(test_negation_row(g, relation, origins[i], values[i]@));
        }
        if finish {
            reveal_with_fuel(test_not_plan, 2);
            let cs = test_children(g, id);
            let start = values.len() as int - cs.len() as int;
            test_lemma_children(g, id, cs.len());
            model::lemma_graph_test_wf(g, id@);
            let suffix = values.subrange(start, values.len() as int);
            assert forall|i: int, j: int| 0 <= i < j < suffix.len() implies suffix[i] != suffix[j] by {
                assert(origins[start + i] == cs[i]);
                assert(origins[start + j] == cs[j]);
                assert(cs[i] < cs[j]);
                assert(relation.contains((cs[i], suffix[i]@)));
                assert(relation.contains((cs[j], suffix[j]@)));
            }
        }
    }

    pub open spec fn test_not_schedule(g: model::Graph, id: TestId, scheduled: Seq<(TestId, bool)>) -> bool {
        let cs = test_children(g, id);
        test_child_count(g, id, cs.len()) && scheduled.len() == cs.len()
        && forall|i: int| 0 <= i < scheduled.len()
            ==> #[trigger] scheduled[i].0@ == cs[cs.len() as int - 1 - i] && !scheduled[i].1
    }

    pub open spec fn test_not_effect(g: model::Graph, id: TestId, finish: bool,
        tasks0: Seq<(TestId, bool)>, values0: Seq<TestId>, tasks1: Seq<(TestId, bool)>, values1: Seq<TestId>) -> bool {
        if id@ >= g.tests.len() { false } else {

            match g.tests[id@ as int] {
                model::TestNode::And(cs) => if finish {
                    tasks1 == tasks0 && cs.len() <= values0.len()
                    && values1.len() == values0.len() - cs.len() + 1
                    && values1.drop_last() == values0.subrange(0, values0.len() as int - cs.len() as int)
                    && (exists|sorted: Seq<TestId>|
                        sorted.to_multiset() == values0.subrange(values0.len() as int - cs.len() as int,
                            values0.len() as int).to_multiset()
                        && g.tests[values1.last()@ as int] == model::TestNode::Or(model::test_ids(sorted)))
                } else {
                    values1 == values0 && tasks0.push((id, true)).is_prefix_of(tasks1)
                        && test_not_schedule(g, id, tasks1.subrange(tasks0.len() as int + 1, tasks1.len() as int))
                },
                model::TestNode::Or(cs) => if finish {
                    tasks1 == tasks0 && cs.len() <= values0.len()
                    && values1.len() == values0.len() - cs.len() + 1
                    && values1.drop_last() == values0.subrange(0, values0.len() as int - cs.len() as int)
                    && (exists|sorted: Seq<TestId>|
                        sorted.to_multiset() == values0.subrange(values0.len() as int - cs.len() as int,
                            values0.len() as int).to_multiset()
                        && g.tests[values1.last()@ as int] == model::TestNode::And(model::test_ids(sorted)))
                } else {
                    values1 == values0 && tasks0.push((id, true)).is_prefix_of(tasks1)
                        && test_not_schedule(g, id, tasks1.subrange(tasks0.len() as int + 1, tasks1.len() as int))
                },
                _ => tasks1 == tasks0 && values1.len() == values0.len() + 1
                    && values1.drop_last() == values0
                    && test_negation_row(g, Set::empty(), id@, values1.last()@),
            }
        }
    }

    pub proof fn test_lemma_not_plan_extends(a: model::Graph, b: model::Graph,
        tasks: Seq<(TestId, bool)>, origins: Seq<nat>)
        requires model::graph_extends(a, b),
            forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].0@ < a.tests.len(),
        ensures test_not_plan(a, tasks, origins) == test_not_plan(b, tasks, origins),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            let task = tasks.last();
            assert(a.tests[task.0@ as int] == b.tests[task.0@ as int]);
            if !task.1 {
                test_lemma_not_plan_extends(a, b, tasks.drop_last(), origins.push(task.0@));
            } else {
                let cs = test_children(a, task.0);
                if test_child_count(a, task.0, cs.len()) && cs.len() <= origins.len()
                    && origins.subrange(origins.len() as int - cs.len() as int, origins.len() as int) == cs {
                    test_lemma_not_plan_extends(a, b, tasks.drop_last(), origins.subrange(0,
                        origins.len() as int - cs.len() as int).push(task.0@));
                }
            }
        }
    }

    pub proof fn test_lemma_not_state_extends(a: model::Graph, b: model::Graph,
        tasks: Seq<(TestId, bool)>, values: Seq<TestId>, root: TestId)
        requires model::graph_extends(a, b), test_not_state(a, tasks, values, root),
        ensures test_not_state(b, tasks, values, root),
    {
        let (origins, relation) = choose|origins: Seq<nat>, relation: Set<(nat, nat)>|
            origins.len() == values.len() && test_negation_witness(a, relation)
            && (forall|i: int| 0 <= i < values.len() ==> relation.contains((origins[i], values[i]@)))
            && test_not_plan(a, tasks, origins) == Some(seq![root@]);
        test_lemma_negation_witness_extends(a, b, relation);
        test_lemma_not_plan_extends(a, b, tasks, origins);
        assert(forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].0@ < b.tests.len());
    }

    pub proof fn test_lemma_not_plan_schedule(g: model::Graph, tasks: Seq<(TestId, bool)>,
        scheduled: Seq<(TestId, bool)>, origins: Seq<nat>, children: Seq<nat>)
        requires scheduled.len() == children.len(), model::bounded(children, g.tests.len()),
            forall|i: int| 0 <= i < scheduled.len()
                ==> #[trigger] scheduled[i].0@ == children[children.len() as int - 1 - i] && !scheduled[i].1,
        ensures test_not_plan(g, tasks + scheduled, origins) == test_not_plan(g, tasks, origins + children),
        decreases scheduled.len(),
    {
        if scheduled.len() == 0 {
            assert(tasks + scheduled =~= tasks);
            assert(origins + children =~= origins);
        } else {
            assert((tasks + scheduled).last() == scheduled.last());
            assert((tasks + scheduled).drop_last() =~= tasks + scheduled.drop_last());
            test_lemma_not_plan_schedule(g, tasks, scheduled.drop_last(), origins.push(children[0]), children.skip(1));
            assert(origins.push(children[0]) + children.skip(1) =~= origins + children);
        }
    }

    pub proof fn test_lemma_not_parent_row(g: model::Graph, relation: Set<(nat, nat)>,
        id: TestId, origins: Seq<nat>, values: Seq<TestId>, sorted: Seq<TestId>, out: TestId)
        requires model::graph_wf(g), id@ < g.tests.len(), out@ < g.tests.len(),
            origins == test_children(g, id), test_child_count(g, id, origins.len()),
            origins.len() == values.len(), sorted.to_multiset() == values.to_multiset(),
            forall|i: int| 0 <= i < values.len() ==> #[trigger] relation.contains((origins[i], values[i]@)),
            match g.tests[id@ as int] {
                model::TestNode::And(_) => g.tests[out@ as int] == model::TestNode::Or(model::test_ids(sorted)),
                model::TestNode::Or(_) => g.tests[out@ as int] == model::TestNode::And(model::test_ids(sorted)),
                _ => false,
            },
        ensures test_negation_row(g, relation, id@, out@),
    {
        reveal(test_negation_row);
        model::lemma_graph_test_wf(g, id@);
        model::lemma_graph_test_wf(g, out@);
        lemma_multiset_members(sorted, values);
        let output = model::test_ids(sorted);
        assert forall|x: nat| origins.contains(x) implies exists|y: nat|
            output.contains(y) && relation.contains((x, y)) by {
            let i = choose|i: int| 0 <= i < origins.len() && origins[i] == x;
            assert(values.contains(values[i]));
            assert(sorted.contains(values[i]));
            let j = choose|j: int| 0 <= j < sorted.len() && sorted[j] == values[i];
            assert(output[j] == values[i]@);
            assert(output.contains(values[i]@));
        }
        assert forall|y: nat| output.contains(y) implies exists|x: nat|
            origins.contains(x) && relation.contains((x, y)) by {
            let j = choose|j: int| 0 <= j < output.len() && output[j] == y;
            assert(sorted.contains(sorted[j]));
            assert(values.contains(sorted[j]));
            let i = choose|i: int| 0 <= i < values.len() && values[i] == sorted[j];
            assert(origins.contains(origins[i]));
            assert(relation.contains((origins[i], y)));
        }
        match g.tests[id@ as int] {
            model::TestNode::And(_) => {},
            model::TestNode::Or(_) => {},
            _ => {},
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub proof fn test_lemma_not_effect_compound(g: model::Graph, id: TestId, finish: bool,
        tasks0: Seq<(TestId, bool)>, values0: Seq<TestId>, tasks1: Seq<(TestId, bool)>, values1: Seq<TestId>,
        root: TestId, origins: Seq<nat>, relation: Set<(nat, nat)>, cs: Seq<nat>)
        requires model::graph_wf(g), test_ids_valid(g, values1),
            test_not_effect(g, id, finish, tasks0, values0, tasks1, values1),
            id@ < g.tests.len(), test_child_count(g, id, cs.len()), cs == test_children(g, id),
            origins.len() == values0.len(), test_negation_witness(g, relation),
            forall|i: int| 0 <= i < values0.len() ==> #[trigger] relation.contains((origins[i], values0[i]@)),
            forall|i: int| 0 <= i < tasks0.len() ==> #[trigger] tasks0[i].0@ < g.tests.len(),
            test_not_plan(g, tasks0.push((id, finish)), origins) == Some(seq![root@]),
        ensures test_not_state(g, tasks1, values1, root),
    {
        reveal_with_fuel(test_not_plan, 3);
        match g.tests[id@ as int] {
            model::TestNode::And(_) => {},
            model::TestNode::Or(_) => {},
            _ => {},
        }
        if finish {
            assert(tasks1 == tasks0);
            assert(values1.drop_last() == values0.subrange(0, values0.len() as int - cs.len() as int));
        } else { assert(values1 == values0); }
        test_lemma_not_plan_push(g, tasks0, id, finish, origins);
        test_lemma_children(g, id, cs.len());
        if finish {
            let start = origins.len() as int - cs.len() as int;
            assert(origins.subrange(start, origins.len() as int) == cs);
            let source = values0.subrange(start, values0.len() as int);
            let sorted = choose|sorted: Seq<TestId>| sorted.to_multiset() == source.to_multiset()
                && match g.tests[id@ as int] {
                    model::TestNode::And(_) => g.tests[values1.last()@ as int] == model::TestNode::Or(model::test_ids(sorted)),
                    model::TestNode::Or(_) => g.tests[values1.last()@ as int] == model::TestNode::And(model::test_ids(sorted)),
                    _ => false,
                };
            test_lemma_not_parent_row(g, relation, id, cs, source, sorted, values1.last());
            test_lemma_negation_insert(g, relation, id@, values1.last()@);
            let next_origins = origins.subrange(0, start).push(id@);
            let next_relation = relation.insert((id@, values1.last()@));
            assert forall|i: int| 0 <= i < values1.len()
                implies next_relation.contains((next_origins[i], values1[i]@)) by {
                if i < next_origins.len() - 1 {
                    assert(values1.drop_last()[i] == values0.subrange(0, start)[i]);
                }
            }
            assert(test_not_plan(g, tasks1, next_origins) == Some(seq![root@]));
        } else {
            let scheduled = tasks1.subrange(tasks0.len() as int + 1, tasks1.len() as int);
            assert(tasks1 =~= tasks0.push((id, true)) + scheduled);
            test_lemma_not_plan_schedule(g, tasks0.push((id, true)), scheduled, origins, cs);
            assert((origins + cs).subrange(origins.len() as int, origins.len() as int + cs.len() as int) =~= cs);
            assert((origins + cs).subrange(0, origins.len() as int) =~= origins);
            test_lemma_not_plan_push(g, tasks0, id, true, origins + cs);
            test_lemma_not_plan_push(g, tasks0, id, false, origins);
            assert(test_not_plan(g, tasks1, origins) == Some(seq![root@]));
            assert forall|i: int| 0 <= i < tasks1.len() implies tasks1[i].0@ < g.tests.len() by {
                if i >= tasks0.len() + 1 {
                    let j = i - tasks0.len() as int - 1;
                    assert(tasks1[i] == scheduled[j]);
                    assert(tasks1[i].0@ < id@);
                }
            }
        }
    }

    pub proof fn test_lemma_not_effect_state(g: model::Graph, id: TestId, finish: bool,
        tasks0: Seq<(TestId, bool)>, values0: Seq<TestId>, tasks1: Seq<(TestId, bool)>, values1: Seq<TestId>, root: TestId)

        requires model::graph_wf(g), test_ids_valid(g, values1),
            test_not_state(g, tasks0.push((id, finish)), values0, root),
            test_not_effect(g, id, finish, tasks0, values0, tasks1, values1),
        ensures test_not_state(g, tasks1, values1, root),
    {
        reveal_with_fuel(test_not_plan, 3);
        assert forall|i: int| 0 <= i < tasks0.len() implies tasks0[i].0@ < g.tests.len() by {
            assert(tasks0.push((id, finish))[i] == tasks0[i]);
        }
        let (origins, relation) = choose|origins: Seq<nat>, relation: Set<(nat, nat)>|
            origins.len() == values0.len() && test_negation_witness(g, relation)
            && (forall|i: int| 0 <= i < values0.len() ==> relation.contains((origins[i], values0[i]@)))
            && test_not_plan(g, tasks0.push((id, finish)), origins) == Some(seq![root@]);
        match g.tests[id@ as int] {
            model::TestNode::And(cs) => {
                test_lemma_not_effect_compound(g, id, finish, tasks0, values0, tasks1, values1, root, origins, relation, cs);
            },
            model::TestNode::Or(cs) => {
                test_lemma_not_effect_compound(g, id, finish, tasks0, values0, tasks1, values1, root, origins, relation, cs);
            },
            _ => {
                test_lemma_not_plan_push(g, tasks0, id, finish, origins);
                assert(!finish);
                assert(tasks1 == tasks0);
                reveal(test_negation_row);
                test_lemma_negation_row_monotone(g, Set::empty(), relation, id@, values1.last()@);
                test_lemma_negation_insert(g, relation, id@, values1.last()@);
                let next_origins = origins.push(id@);
                let next_relation = relation.insert((id@, values1.last()@));
                assert forall|i: int| 0 <= i < values1.len()
                    implies next_relation.contains((next_origins[i], values1[i]@)) by {
                    if i < origins.len() { assert(values1[i] == values0[i]); }
                }
                assert(test_not_plan(g, tasks1, next_origins) == Some(seq![root@]));
            },
        }
    }

    pub proof fn test_lemma_not_initial(g: model::Graph, root: TestId)
        requires root@ < g.tests.len(),
        ensures test_not_state(g, seq![(root, false)], Seq::empty(), root),
    {
        reveal_with_fuel(test_not_plan, 3);
        reveal(test_negation_witness);
        assert(test_negation_witness(g, Set::empty()));
        assert(test_not_plan(g, seq![(root, false)], Seq::empty()) == Some(seq![root@]));
    }

    pub proof fn test_lemma_not_done(g: model::Graph, values: Seq<TestId>, root: TestId)
        requires model::graph_wf(g), test_not_state(g, Seq::empty(), values, root),
        ensures values.len() == 1, values[0]@ < g.tests.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
                test_truth(g, sym, theta, values[0]@, event) != test_truth(g, sym, theta, root@, event),
    {
        let (origins, relation) = choose|origins: Seq<nat>, relation: Set<(nat, nat)>|
            origins.len() == values.len() && test_negation_witness(g, relation)
            && (forall|i: int| 0 <= i < values.len() ==> relation.contains((origins[i], values[i]@)))
            && test_not_plan(g, Seq::empty(), origins) == Some(seq![root@]);
        assert(origins == seq![root@]);
        assert(relation.contains((origins[0], values[0]@)));
        test_lemma_negation_witness_elim(g, relation);
        reveal(test_negation_row);
        assert(test_negation_row(g, relation, root@, values[0]@));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            test_truth(g, sym, theta, values[0]@, event) != test_truth(g, sym, theta, root@, event) by {
            test_lemma_negation_semantics(g, relation, root@, values[0]@, sym, theta, event);
        }
    }

    pub proof fn test_lemma_not_plan_push(g: model::Graph, tasks: Seq<(TestId, bool)>, id: TestId,
        finish: bool, origins: Seq<nat>)
        requires id@ < g.tests.len(),
        ensures test_not_plan(g, tasks.push((id, finish)), origins)
            == if !finish { test_not_plan(g, tasks, origins.push(id@)) } else {
                let cs = test_children(g, id);
                if !test_child_count(g, id, cs.len()) || cs.len() > origins.len()
                    || origins.subrange(origins.len() as int - cs.len() as int, origins.len() as int) != cs {
                    None
                } else {
                    test_not_plan(g, tasks, origins.subrange(0, origins.len() as int - cs.len() as int).push(id@))
                }
            },
    {
        assert(tasks.push((id, finish)).last() == (id, finish));
        assert(tasks.push((id, finish)).drop_last() =~= tasks);
        reveal_with_fuel(test_not_plan, 2);
    }

    pub proof fn test_lemma_not_work_schedule(g: model::Graph, tasks: Seq<(TestId, bool)>,
        scheduled: Seq<(TestId, bool)>, children: Seq<nat>, bound: nat)
        requires scheduled.len() == children.len(), model::bounded(children, bound),
            forall|i: int| 0 <= i < scheduled.len()
                ==> #[trigger] scheduled[i].0@ == children[children.len() as int - 1 - i] && !scheduled[i].1,
        ensures test_not_work(g, tasks + scheduled) == test_not_work(g, tasks) + test_not_children_work(g, children, bound),
        decreases scheduled.len(),
    {
        if scheduled.len() == 0 {
            assert(tasks + scheduled =~= tasks);
        } else {
            assert((tasks + scheduled).drop_last() =~= tasks + scheduled.drop_last());
            assert((tasks + scheduled).last() == scheduled.last());
            test_lemma_not_work_schedule(g, tasks, scheduled.drop_last(), children.skip(1), bound);
        }
    }

    pub proof fn test_lemma_not_node_work_extends(a: model::Graph, b: model::Graph, id: nat)
        requires model::graph_extends(a, b), id < a.tests.len(),
        ensures test_not_node_work(a, id) == test_not_node_work(b, id),
        decreases id, 1nat,
    {
        assert(a.tests[id as int] == b.tests[id as int]);
        match a.tests[id as int] {
            model::TestNode::And(cs) => { test_lemma_not_children_work_extends(a, b, cs, id); },
            model::TestNode::Or(cs) => { test_lemma_not_children_work_extends(a, b, cs, id); },
            _ => {},
        }
    }

    pub proof fn test_lemma_not_children_work_extends(a: model::Graph, b: model::Graph, children: Seq<nat>, bound: nat)
        requires model::graph_extends(a, b), bound <= a.tests.len(),
        ensures test_not_children_work(a, children, bound) == test_not_children_work(b, children, bound),
        decreases bound, 0nat, children.len(),
    {
        if children.len() > 0 {
            if children[0] < bound { test_lemma_not_node_work_extends(a, b, children[0]); }
            test_lemma_not_children_work_extends(a, b, children.skip(1), bound);
        }
    }

    pub proof fn test_lemma_not_work_extends(a: model::Graph, b: model::Graph, tasks: Seq<(TestId, bool)>)
        requires model::graph_extends(a, b),
            forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].0@ < a.tests.len(),
        ensures test_not_work(a, tasks) == test_not_work(b, tasks),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            if !tasks.last().1 { test_lemma_not_node_work_extends(a, b, tasks.last().0@); }
            test_lemma_not_work_extends(a, b, tasks.drop_last());
        }
    }

    pub proof fn test_lemma_not_effect_work(g: model::Graph, id: TestId, finish: bool,
        tasks0: Seq<(TestId, bool)>, values0: Seq<TestId>, tasks1: Seq<(TestId, bool)>, values1: Seq<TestId>)
        requires model::graph_wf(g), id@ < g.tests.len(),
            test_not_effect(g, id, finish, tasks0, values0, tasks1, values1),
        ensures test_not_work(g, tasks1) < test_not_work(g, tasks0.push((id, finish))),
    {
        model::lemma_graph_test_wf(g, id@);
        assert(tasks0.push((id, finish)).drop_last() =~= tasks0);
        assert(tasks0.push((id, finish)).last() == (id, finish));
        reveal_with_fuel(test_not_work, 2);
        reveal_with_fuel(test_not_node_work, 2);
        assert(tasks0.push((id, true)).last() == (id, true));
        assert(tasks0.push((id, true)).drop_last() =~= tasks0);
        match g.tests[id@ as int] {
            model::TestNode::And(cs) => {
                if !finish {
                    let scheduled = tasks1.subrange(tasks0.len() as int + 1, tasks1.len() as int);
                    assert(tasks1 =~= tasks0.push((id, true)) + scheduled);
                    test_lemma_not_work_schedule(g, tasks0.push((id, true)), scheduled, cs, id@);
                    assert(test_not_work(g, tasks1) == test_not_work(g, tasks0) + 1 + test_not_children_work(g, cs, id@));
                    assert(test_not_node_work(g, id@) == 2 + test_not_children_work(g, cs, id@));
                }
            },
            model::TestNode::Or(cs) => {
                if !finish {
                    let scheduled = tasks1.subrange(tasks0.len() as int + 1, tasks1.len() as int);
                    assert(tasks1 =~= tasks0.push((id, true)) + scheduled);
                    test_lemma_not_work_schedule(g, tasks0.push((id, true)), scheduled, cs, id@);
                    assert(test_not_work(g, tasks1) == test_not_work(g, tasks0) + 1 + test_not_children_work(g, cs, id@));
                    assert(test_not_node_work(g, id@) == 2 + test_not_children_work(g, cs, id@));
                }
            },
            _ => {},
        }
    }

    pub proof fn test_lemma_combo_concat(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data,
        left: Seq<TestId>, right: Seq<TestId>, and: bool)
        ensures test_combo(g, sym, theta, left + right, event, and)
            == if and { test_combo(g, sym, theta, left, event, and) && test_combo(g, sym, theta, right, event, and) }
                else { test_combo(g, sym, theta, left, event, and) || test_combo(g, sym, theta, right, event, and) },
        decreases right.len(),
    {
        if right.len() == 0 { assert(left + right =~= left); }
        else {
            test_lemma_combo_concat(g, sym, theta, event, left, right.drop_last(), and);
            test_lemma_combo_push(g, sym, theta, event, right.drop_last(), right.last(), and);
            test_lemma_combo_push(g, sym, theta, event, left + right.drop_last(), right.last(), and);
            assert(right.drop_last().push(right.last()) =~= right);
            assert((left + right.drop_last()).push(right.last()) =~= left + right);
        }
    }

    pub proof fn test_lemma_redundant_push(g: model::Graph, a: TestId, siblings: Seq<TestId>, b: TestId, and: bool)
        ensures test_redundant_in(g, a, siblings.push(b), and)
            == (test_redundant_in(g, a, siblings, and) || test_redundancy(g, a, b, and)),
    {
        if test_redundant_in(g, a, siblings.push(b), and) {
            let i = choose|i: int| 0 <= i < siblings.push(b).len() && test_redundancy(g, a, siblings.push(b)[i], and);
        } else {
            assert(!test_redundancy(g, a, siblings.push(b)[siblings.len() as int], and));
            assert forall|i: int| 0 <= i < siblings.len() implies !test_redundancy(g, a, siblings[i], and) by {
                assert(siblings.push(b)[i] == siblings[i]);
            }
        }
    }

    // Regex normalization proofs.
    pub struct RegexModeModel {
        pub intersect: bool,
        pub identity: RegexId,
        pub absorber: RegexId,
    }
    pub struct RegexStatsModel {
        pub all_nullable: bool,
        pub any_nullable: bool,
        pub epsilon: bool,
        pub complement: bool,
        pub has_nonnullable: bool,
    }
    impl View for RegexMode {
        type V = RegexModeModel;
        open(super) spec fn view(&self) -> RegexModeModel {
            RegexModeModel { intersect: self.intersect, identity: self.identity, absorber: self.absorber }
        }
    }
    impl View for RegexStats {
        type V = RegexStatsModel;
        open(super) spec fn view(&self) -> RegexStatsModel {
            RegexStatsModel { all_nullable: self.all_nullable, any_nullable: self.any_nullable,
                epsilon: self.epsilon, complement: self.complement, has_nonnullable: self.has_nonnullable }
        }
    }

    pub open spec fn regex_unbounded_kind(g: model::Graph, kind: model::RegexKindNode) -> language::Regex<model::Test> {
        match kind {
            model::RegexKindNode::Empty => language::Regex::Empty,
            model::RegexKindNode::All => language::Regex::All,
            model::RegexKindNode::Epsilon => language::Regex::Epsilon,
            model::RegexKindNode::Test(t) => language::Regex::Test(model::lift_test(g, t)),
            model::RegexKindNode::Union(cs) => language::Regex::Union(model::lift_regexes(g, cs)),
            model::RegexKindNode::Intersect(cs) => language::Regex::Intersect(model::lift_regexes(g, cs)),
            model::RegexKindNode::Concat(cs) => language::Regex::Concat(model::lift_regexes(g, cs)),
            model::RegexKindNode::Star(r) => language::Regex::Star(Box::new(model::lift_regex(g, r))),
            model::RegexKindNode::Not(r) => language::Regex::Not(Box::new(model::lift_regex(g, r))),
        }
    }

    pub proof fn regex_unfold(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.regexes.len(),
        ensures model::lift_regex(g, id) == model::lift_regex_kind(g, g.regexes[id as int].kind),
            model::lift_regex(g, id) == regex_unbounded_kind(g, g.regexes[id as int].kind),
            g.regexes[id as int].nullable == language::nullable(model::lift_regex(g, id)),
            model::regex_node_wf_at(g, g.regexes[id as int], id),
    {
        model::lemma_graph_regex_wf(g, id);
        let node = g.regexes[id as int];
        assert(model::regex_node_wf_at(g, node, id));
        match node.kind {
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Concat(cs) | model::RegexKindNode::Intersect(cs) => {
                assert(model::lift_regexes_bounded(g, cs, id) =~= model::lift_regexes(g, cs));
                assert(model::lift_regexes_bounded(g, cs, g.regexes.len()) =~= model::lift_regexes(g, cs));
            },
            _ => {},
        }
    }

    pub proof fn regex_constants(g: model::Graph)
        requires model::graph_wf(g),
        ensures model::lift_regex(g, g.constants.empty) == language::Regex::Empty,
            model::lift_regex(g, g.constants.all) == language::Regex::All,
            model::lift_regex(g, g.constants.epsilon) == language::Regex::Epsilon,
            model::lift_test(g, g.constants.test_true) == model::Test::True,
            model::lift_test(g, g.constants.test_false) == model::Test::False,
            g.constants.empty < g.regexes.len(), g.constants.all < g.regexes.len(), g.constants.epsilon < g.regexes.len(),
            g.constants.test_true < g.tests.len(), g.constants.test_false < g.tests.len(),
    {
        model::lemma_graph_wf_elim(g);
    }

    pub proof fn regex_star_nil<L>(sem: spec_fn(L, Data) -> bool, r: language::Regex<L>)
        ensures language::lang(sem, language::Regex::Star(Box::new(r)), Seq::empty()),
    {
        let parts = Seq::<Seq<Data>>::empty();
        assert(parts.flatten() == Seq::<Data>::empty());
        assert(forall|i: int| 0 <= i < parts.len() ==> language::lang(sem, r, parts[i]));
    }

    pub proof fn regex_star_single<L>(sem: spec_fn(L, Data) -> bool, r: language::Regex<L>, word: Seq<Data>)
        requires language::lang(sem, r, word),
        ensures language::lang(sem, language::Regex::Star(Box::new(r)), word),
    {
        let parts = seq![word];
        parts.lemma_flatten_one_element();
        assert forall|i: int| 0 <= i < parts.len() implies language::lang(sem, r, parts[i]) by {
            assert(i == 0);
        }
    }

    pub proof fn regex_star_join<L>(sem: spec_fn(L, Data) -> bool, r: language::Regex<L>, a: Seq<Data>, b: Seq<Data>)
        requires language::lang(sem, language::Regex::Star(Box::new(r)), a),
            language::lang(sem, language::Regex::Star(Box::new(r)), b),
        ensures language::lang(sem, language::Regex::Star(Box::new(r)), a + b),
    {
        let ap = choose|p: Seq<Seq<Data>>| a == p.flatten()
            && forall|i: int| 0 <= i < p.len() ==> language::lang(sem, r, p[i]);
        let bp = choose|p: Seq<Seq<Data>>| b == p.flatten()
            && forall|i: int| 0 <= i < p.len() ==> language::lang(sem, r, p[i]);
        let parts = ap + bp;
        vstd::seq_lib::lemma_flatten_concat(ap, bp);
        assert(parts.flatten() == a + b);
        assert forall|i: int| 0 <= i < parts.len() implies language::lang(sem, r, parts[i]) by {
            if i < ap.len() { assert(parts[i] == ap[i]); }
            else { assert(parts[i] == bp[i - ap.len()]); }
        }
    }

    pub proof fn regex_star_parts<L>(sem: spec_fn(L, Data) -> bool, r: language::Regex<L>, parts: Seq<Seq<Data>>)
        requires forall|i: int| 0 <= i < parts.len() ==> language::lang(sem, language::Regex::Star(Box::new(r)), parts[i]),
        ensures language::lang(sem, language::Regex::Star(Box::new(r)), parts.flatten()),
        decreases parts.len(),
    {
        if parts.len() == 0 {
            regex_star_nil(sem, r);
        } else {
            assert forall|i: int| 0 <= i < parts.drop_first().len()
                implies language::lang(sem, language::Regex::Star(Box::new(r)), parts.drop_first()[i]) by {
                assert(parts.drop_first()[i] == parts[i + 1]);
            }
            regex_star_parts(sem, r, parts.drop_first());
            regex_star_join(sem, r, parts[0], parts.drop_first().flatten());
        }
    }

    pub proof fn regex_star_collapse<L>(sem: spec_fn(L, Data) -> bool, r: language::Regex<L>, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Star(Box::new(language::Regex::Star(Box::new(r)))), word)
            == language::lang(sem, language::Regex::Star(Box::new(r)), word),
    {
        if language::lang(sem, language::Regex::Star(Box::new(language::Regex::Star(Box::new(r)))), word) {
            let parts = choose|p: Seq<Seq<Data>>| word == p.flatten()
                && forall|i: int| 0 <= i < p.len() ==> language::lang(sem, language::Regex::Star(Box::new(r)), p[i]);
            regex_star_parts(sem, r, parts);
        }
        if language::lang(sem, language::Regex::Star(Box::new(r)), word) {
            regex_star_single(sem, language::Regex::Star(Box::new(r)), word);
        }
    }

    pub proof fn regex_star_constants<L>(sem: spec_fn(L, Data) -> bool, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Star(Box::new(language::Regex::<L>::Empty)), word) == (word.len() == 0),
            language::lang(sem, language::Regex::Star(Box::new(language::Regex::<L>::Epsilon)), word) == (word.len() == 0),
            language::lang(sem, language::Regex::Star(Box::new(language::Regex::<L>::All)), word),
    {
        if language::lang(sem, language::Regex::Star(Box::new(language::Regex::<L>::Empty)), word) {
            let parts = choose|p: Seq<Seq<Data>>| word == p.flatten()
                && forall|i: int| 0 <= i < p.len() ==> language::lang(sem, language::Regex::<L>::Empty, p[i]);
            assert(parts.len() == 0) by { if parts.len() > 0 { assert(language::lang(sem, language::Regex::<L>::Empty, parts[0])); } }
        }
        if language::lang(sem, language::Regex::Star(Box::new(language::Regex::<L>::Epsilon)), word) {
            let parts = choose|p: Seq<Seq<Data>>| word == p.flatten()
                && forall|i: int| 0 <= i < p.len() ==> language::lang(sem, language::Regex::<L>::Epsilon, p[i]);
            language::lemma_flatten_empty(parts);
        }
        if word.len() == 0 {
            assert(word =~= Seq::<Data>::empty());
            regex_star_nil(sem, language::Regex::<L>::Empty);
            regex_star_nil(sem, language::Regex::<L>::Epsilon);
        }
        regex_star_single(sem, language::Regex::<L>::All, word);
    }

    pub proof fn regex_star_test_true<L>(sem: spec_fn(L, Data) -> bool, leaf: L, word: Seq<Data>)
        requires forall|event: Data| #[trigger] sem(leaf, event),
        ensures language::lang(sem, language::Regex::Star(Box::new(language::Regex::Test(leaf))), word),
        decreases word.len(),
    {
        if word.len() == 0 {
            assert(word =~= Seq::<Data>::empty());
            regex_star_nil(sem, language::Regex::Test(leaf));
        } else {
            let tail = word.drop_first();
            regex_star_test_true(sem, leaf, tail);
            assert(language::lang(sem, language::Regex::Test(leaf), seq![word[0]]));
            regex_star_single(sem, language::Regex::Test(leaf), seq![word[0]]);
            regex_star_join(sem, language::Regex::Test(leaf), seq![word[0]], tail);
            assert(word =~= seq![word[0]] + tail);
        }
    }

    pub proof fn regex_star_laws(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.regexes.len(),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            #![trigger language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word)]
            match g.regexes[id as int].kind {
                model::RegexKindNode::Empty | model::RegexKindNode::Epsilon =>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word)
                        == (word.len() == 0),
                model::RegexKindNode::All =>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word),
                model::RegexKindNode::Test(t) => t == g.constants.test_true ==>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word),
                model::RegexKindNode::Star(_) =>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word)
                        == model::regex_lang(g, sym, theta, id, word),
                _ => true,
            },
    {
        regex_unfold(g, id);
        regex_constants(g);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            #![trigger language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word)]
            match g.regexes[id as int].kind {
                model::RegexKindNode::Empty | model::RegexKindNode::Epsilon =>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word)
                        == (word.len() == 0),
                model::RegexKindNode::All =>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word),
                model::RegexKindNode::Test(t) => t == g.constants.test_true ==>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word),
                model::RegexKindNode::Star(_) =>
                    language::lang(model::gsem(sym, theta), language::Regex::Star(Box::new(model::lift_regex(g, id))), word)
                        == model::regex_lang(g, sym, theta, id, word),
                _ => true,
            } by {
            let sem = model::gsem(sym, theta);
            match g.regexes[id as int].kind {
                model::RegexKindNode::Empty | model::RegexKindNode::Epsilon | model::RegexKindNode::All => {
                    regex_star_constants(sem, word);
                },
                model::RegexKindNode::Test(t) => if t == g.constants.test_true {
                    assert(forall|event: Data| #[trigger] sem(model::Test::True, event));
                    regex_star_test_true(sem, model::Test::True, word);
                },
                model::RegexKindNode::Star(r) => { regex_star_collapse(sem, model::lift_regex(g, r), word); },
                _ => {},
            }
        }
    }

    #[verifier::opaque]
    pub open spec fn regex_children(g: model::Graph, id: nat) -> Seq<nat> {
        match g.regexes[id as int].kind {
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Concat(cs) | model::RegexKindNode::Intersect(cs) => cs,
            _ => Seq::empty(),
        }
    }

    pub open spec fn regex_concat_nats(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, ids: Seq<nat>, word: Seq<Data>) -> bool {
        language::lang(model::gsem(sym, theta), language::Regex::Concat(model::lift_regexes(g, ids)), word)
    }

    pub proof fn regex_concat_append<L>(sem: spec_fn(L, Data) -> bool, a: Seq<language::Regex<L>>, b: Seq<language::Regex<L>>, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Concat(a + b), word)
            == (exists|u: Seq<Data>, v: Seq<Data>| word == u + v
                && language::lang(sem, language::Regex::Concat(a), u)
                && language::lang(sem, language::Regex::Concat(b), v)),
    {
        if language::lang(sem, language::Regex::Concat(a + b), word) {
            let parts = choose|p: Seq<Seq<Data>>| p.len() == (a + b).len() && word == p.flatten()
                && forall|i: int| 0 <= i < (a + b).len() ==> language::lang(sem, (a + b)[i], p[i]);
            let ap = parts.subrange(0, a.len() as int);
            let bp = parts.subrange(a.len() as int, parts.len() as int);
            assert(parts =~= ap + bp);
            vstd::seq_lib::lemma_flatten_concat(ap, bp);
            assert(parts.flatten() == ap.flatten() + bp.flatten());
            assert forall|i: int| 0 <= i < a.len() implies language::lang(sem, a[i], ap[i]) by {
                assert(a[i] == (a + b)[i]);
            }
            assert forall|i: int| 0 <= i < b.len() implies language::lang(sem, b[i], bp[i]) by {
                assert(b[i] == (a + b)[a.len() + i]);
                assert(bp[i] == parts[a.len() + i]);
            }
            assert(language::lang(sem, language::Regex::Concat(a), ap.flatten()));
            assert(language::lang(sem, language::Regex::Concat(b), bp.flatten()));
        }
        if exists|u: Seq<Data>, v: Seq<Data>| word == u + v
            && language::lang(sem, language::Regex::Concat(a), u)
            && language::lang(sem, language::Regex::Concat(b), v) {
            let (u, v) = choose|u: Seq<Data>, v: Seq<Data>| word == u + v
                && language::lang(sem, language::Regex::Concat(a), u)
                && language::lang(sem, language::Regex::Concat(b), v);
            let ap = choose|p: Seq<Seq<Data>>| p.len() == a.len() && u == p.flatten()
                && forall|i: int| 0 <= i < a.len() ==> language::lang(sem, a[i], p[i]);
            let bp = choose|p: Seq<Seq<Data>>| p.len() == b.len() && v == p.flatten()
                && forall|i: int| 0 <= i < b.len() ==> language::lang(sem, b[i], p[i]);
            let parts = ap + bp;
            vstd::seq_lib::lemma_flatten_concat(ap, bp);
            assert(parts.flatten() == word);
            assert forall|i: int| 0 <= i < (a + b).len() implies language::lang(sem, (a + b)[i], parts[i]) by {
                if i < a.len() { assert((a + b)[i] == a[i]); assert(parts[i] == ap[i]); }
                else { assert((a + b)[i] == b[i - a.len()]); assert(parts[i] == bp[i - a.len()]); }
            }
        }
    }

    pub proof fn regex_concat_empty<L>(sem: spec_fn(L, Data) -> bool, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Concat(Seq::<language::Regex<L>>::empty()), word) == (word.len() == 0),
    {
        if language::lang(sem, language::Regex::Concat(Seq::<language::Regex<L>>::empty()), word) {
            let parts = choose|p: Seq<Seq<Data>>| p.len() == 0 && word == p.flatten()
                && forall|i: int| 0 <= i < 0 ==> language::lang(sem, Seq::<language::Regex<L>>::empty()[i], p[i]);
            assert(parts =~= Seq::<Seq<Data>>::empty());
        }
        if word.len() == 0 {
            let parts = Seq::<Seq<Data>>::empty();
            assert(word =~= parts.flatten());
            assert(forall|i: int| 0 <= i < 0 ==> language::lang(sem, Seq::<language::Regex<L>>::empty()[i], parts[i]));
        }
    }

    pub proof fn regex_concat_replace<L>(sem: spec_fn(L, Data) -> bool, prefix: Seq<language::Regex<L>>, tail: Seq<language::Regex<L>>, r: language::Regex<L>)
        requires forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(tail), word) == language::lang(sem, r, word),
        ensures forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(prefix + tail), word)
            == language::lang(sem, language::Regex::Concat(prefix.push(r)), word),
    {
        assert forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(prefix + tail), word)
            == language::lang(sem, language::Regex::Concat(prefix.push(r)), word) by {
            assert(prefix.push(r) =~= prefix + seq![r]);
            regex_concat_append(sem, prefix, tail, word);
            regex_concat_append(sem, prefix, seq![r], word);
            if language::lang(sem, language::Regex::Concat(prefix + tail), word) {
                let (u, v) = choose|u: Seq<Data>, v: Seq<Data>| word == u + v
                    && language::lang(sem, language::Regex::Concat(prefix), u)
                    && language::lang(sem, language::Regex::Concat(tail), v);
                assert(language::lang(sem, r, v));
                language::lemma_concat_singleton(sem, r, v);
                assert(exists|u: Seq<Data>, v: Seq<Data>| word == u + v
                    && language::lang(sem, language::Regex::Concat(prefix), u)
                    && language::lang(sem, language::Regex::Concat(seq![r]), v));
            }
            if language::lang(sem, language::Regex::Concat(prefix.push(r)), word) {
                let (u, v) = choose|u: Seq<Data>, v: Seq<Data>| word == u + v
                    && language::lang(sem, language::Regex::Concat(prefix), u)
                    && language::lang(sem, language::Regex::Concat(seq![r]), v);
                language::lemma_concat_singleton(sem, r, v);
                assert(language::lang(sem, language::Regex::Concat(tail), v));
                assert(exists|u: Seq<Data>, v: Seq<Data>| word == u + v
                    && language::lang(sem, language::Regex::Concat(prefix), u)
                    && language::lang(sem, language::Regex::Concat(tail), v));
            }
        }
    }

    pub proof fn regex_concat_append_congruent<L>(sem: spec_fn(L, Data) -> bool, left: Seq<language::Regex<L>>, right: Seq<language::Regex<L>>, suffix: Seq<language::Regex<L>>)
        requires forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(left), word)
            == language::lang(sem, language::Regex::Concat(right), word),
        ensures forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(left + suffix), word)
            == language::lang(sem, language::Regex::Concat(right + suffix), word),
    {
        assert forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(left + suffix), word)
            == language::lang(sem, language::Regex::Concat(right + suffix), word) by {
            regex_concat_append(sem, left, suffix, word);
            regex_concat_append(sem, right, suffix, word);
        }
    }

    pub proof fn regex_concat_step_law(g: model::Graph, before: Seq<nat>, id: nat, after: Seq<nat>)
        requires model::graph_wf(g), id < g.regexes.len(),
            after == before + match g.regexes[id as int].kind {
                model::RegexKindNode::Epsilon => Seq::empty(),
                model::RegexKindNode::Concat(cs) => cs,
                _ => seq![id],
            },
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            regex_concat_nats(g, sym, theta, after, word)
                == regex_concat_nats(g, sym, theta, before.push(id), word),
    {
        hide(language::lang);
        hide(model::tables_wf);
        hide(model::lift_regex);
        regex_unfold(g, id);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            regex_concat_nats(g, sym, theta, after, word)
                == regex_concat_nats(g, sym, theta, before.push(id), word) by {
            let sem = model::gsem(sym, theta);
            let lhs = model::lift_regexes(g, before);
            let rhs = match g.regexes[id as int].kind {
                model::RegexKindNode::Epsilon => Seq::empty(),
                model::RegexKindNode::Concat(cs) => model::lift_regexes(g, cs),
                _ => seq![model::lift_regex(g, id)],
            };
            assert(model::lift_regexes(g, after) =~= lhs + rhs);
            assert(model::lift_regexes(g, before.push(id)) =~= lhs + seq![model::lift_regex(g, id)]);
            assert(lhs.push(model::lift_regex(g, id)) =~= lhs + seq![model::lift_regex(g, id)]);
            assert forall|v: Seq<Data>| language::lang(sem, language::Regex::Concat(rhs), v)
                == language::lang(sem, model::lift_regex(g, id), v) by {
                language::lemma_concat_singleton(sem, model::lift_regex(g, id), v);
                match g.regexes[id as int].kind {
                    model::RegexKindNode::Epsilon => {
                        regex_concat_empty::<model::Test>(sem, v);
                        reveal(language::lang);
                    },
                    _ => {},
                }
            }
            regex_concat_replace(sem, lhs, rhs, model::lift_regex(g, id));
        }
    }

    pub open spec fn regex_concat_piece(g: model::Graph, id: nat) -> Seq<nat> {
        match g.regexes[id as int].kind {
            model::RegexKindNode::Epsilon => Seq::empty(),
            model::RegexKindNode::Concat(cs) => cs,
            _ => seq![id],
        }
    }

    pub open spec fn regex_concat_flat(g: model::Graph, ids: Seq<RegexId>) -> Seq<nat>
        decreases ids.len(),
    {
        if ids.len() == 0 { Seq::empty() }
        else { regex_concat_flat(g, ids.drop_last()) + regex_concat_piece(g, ids.last()@) }
    }

    pub proof fn regex_children_wf(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.regexes.len(),
        ensures model::bounded(regex_children(g, id), g.regexes.len()),
    {
        reveal(regex_children);
        model::lemma_graph_regex_wf(g, id);
        assert(model::regex_node_wf_at(g, g.regexes[id as int], id));
    }

    pub proof fn regex_concat_flat_wf(g: model::Graph, ids: Seq<RegexId>)
        requires model::graph_wf(g), regex_ids_valid(g, ids),
        ensures model::bounded(regex_concat_flat(g, ids), g.regexes.len()),
        decreases ids.len(),
    {
        if ids.len() > 0 {
            regex_concat_flat_wf(g, ids.drop_last());
            regex_children_wf(g, ids.last()@);
            regex_children_count(g, ids.last()@);
        }
    }

    pub proof fn regex_concat_flat_law(g: model::Graph, ids: Seq<RegexId>, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>)
        requires model::graph_wf(g), regex_ids_valid(g, ids),
        ensures regex_concat_nats(g, sym, theta, regex_concat_flat(g, ids), word)
            == concat_combo(g, sym, theta, ids, word),
        decreases ids.len(),
    {
        hide(language::lang);
        hide(model::tables_wf);
        hide(model::lift_regex);
        if ids.len() > 0 {
            let before = ids.drop_last();
            let id = ids.last()@;
            let flat = regex_concat_flat(g, before);
            regex_concat_step_law(g, flat, id, flat + regex_concat_piece(g, id));
            let sem = model::gsem(sym, theta);
            let flat_lifts = model::lift_regexes(g, flat);
            let input_lifts = model::lift_regexes(g, model::regex_ids(before));
            let last_lifts = seq![model::lift_regex(g, id)];
            assert(model::lift_regexes(g, flat.push(id)) =~= flat_lifts + last_lifts);
            assert(model::lift_regexes(g, model::regex_ids(ids)) =~= input_lifts + last_lifts);
            assert forall|v: Seq<Data>| language::lang(sem, language::Regex::Concat(flat_lifts), v)
                == language::lang(sem, language::Regex::Concat(input_lifts), v) by {
                regex_concat_flat_law(g, before, sym, theta, v);
            }
            regex_concat_append_congruent(sem, flat_lifts, input_lifts, last_lifts);
        } else {
            assert(model::regex_ids(ids) =~= regex_concat_flat(g, ids));
        }
    }

    pub proof fn regex_concat_absorber(g: model::Graph, ids: Seq<RegexId>, index: int)
        requires model::graph_wf(g), regex_ids_valid(g, ids), 0 <= index < ids.len(),
            g.regexes[ids[index]@ as int].kind == model::RegexKindNode::Empty,
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| !concat_combo(g, sym, theta, ids, word),
    {
        regex_unfold(g, ids[index]@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            !concat_combo(g, sym, theta, ids, word) by {
            if concat_combo(g, sym, theta, ids, word) {
                let lifts = model::lift_regexes(g, model::regex_ids(ids));
                let parts = choose|p: Seq<Seq<Data>>| p.len() == lifts.len() && word == p.flatten()
                    && forall|i: int| 0 <= i < lifts.len() ==> language::lang(model::gsem(sym, theta), lifts[i], p[i]);
                assert(lifts[index] == language::Regex::Empty);
                assert(language::lang(model::gsem(sym, theta), lifts[index], parts[index]));
            }
        }
    }

    pub open spec fn regex_nullable_combo(g: model::Graph, ids: Seq<RegexId>, and: bool) -> bool {
        if and { forall|i: int| 0 <= i < ids.len() ==> language::nullable(model::lift_regex(g, ids[i]@)) }
        else { exists|i: int| 0 <= i < ids.len() && language::nullable(model::lift_regex(g, ids[i]@)) }
    }

    pub proof fn regex_concat_congruent<L>(
        sem: spec_fn(L, Data) -> bool, left: Seq<language::Regex<L>>, right: Seq<language::Regex<L>>,
    )
        requires left.len() == right.len(),
            forall|i: int, word: Seq<Data>| 0 <= i < left.len()
                ==> language::lang(sem, left[i], word) == language::lang(sem, right[i], word),
        ensures forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(left), word)
            == language::lang(sem, language::Regex::Concat(right), word),
    {
        assert forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(left), word)
            == language::lang(sem, language::Regex::Concat(right), word) by {
            if language::lang(sem, language::Regex::Concat(left), word) {
                let parts = choose|p: Seq<Seq<Data>>| p.len() == left.len() && word == p.flatten()
                    && forall|i: int| 0 <= i < left.len() ==> language::lang(sem, left[i], p[i]);
                assert forall|i: int| 0 <= i < right.len() implies language::lang(sem, right[i], parts[i]) by {
                    assert(language::lang(sem, left[i], parts[i]));
                }
                assert(language::lang(sem, language::Regex::Concat(right), word));
            }
            if language::lang(sem, language::Regex::Concat(right), word) {
                let parts = choose|p: Seq<Seq<Data>>| p.len() == right.len() && word == p.flatten()
                    && forall|i: int| 0 <= i < right.len() ==> language::lang(sem, right[i], p[i]);
                assert forall|i: int| 0 <= i < left.len() implies language::lang(sem, left[i], parts[i]) by {
                    assert(language::lang(sem, right[i], parts[i]));
                }
                assert(language::lang(sem, language::Regex::Concat(left), word));
            }
        }
    }

    pub proof fn regex_child_exact(g: model::Graph, id: nat, index: nat, child: nat)
        requires model::graph_wf(g), id < g.regexes.len(),
            model::regex_node_child(g.regexes[id as int].kind, index) == Some(child),
        ensures index < regex_children(g, id).len(), regex_children(g, id)[index as int] == child,
            child < g.regexes.len(),
    {
        reveal(regex_children);
        regex_children_wf(g, id);
        match g.regexes[id as int].kind {
            model::RegexKindNode::Union(_) | model::RegexKindNode::Concat(_) | model::RegexKindNode::Intersect(_) => {},
            _ => {},
        }
    }

    pub proof fn regex_ids_push(ids: Seq<RegexId>, id: RegexId)
        ensures model::regex_ids(ids.push(id)) == model::regex_ids(ids).push(id@),
    {
        assert(model::regex_ids(ids.push(id)) =~= model::regex_ids(ids).push(id@));
    }

    pub proof fn regex_concat_flat_prefix(g: model::Graph, ids: Seq<RegexId>, index: int)
        requires 0 <= index < ids.len(),
        ensures regex_concat_flat(g, ids.subrange(0, index + 1))
            == regex_concat_flat(g, ids.subrange(0, index)) + regex_concat_piece(g, ids[index]@),
    {
        assert(ids.subrange(0, index + 1).drop_last() =~= ids.subrange(0, index));
    }

    pub proof fn regex_nullable_prefix(g: model::Graph, ids: Seq<RegexId>, index: int, and: bool)
        requires 0 <= index < ids.len(),
        ensures regex_nullable_combo(g, ids.subrange(0, index + 1), and)
            == if and { regex_nullable_combo(g, ids.subrange(0, index), and) && language::nullable(model::lift_regex(g, ids[index]@)) }
                else { regex_nullable_combo(g, ids.subrange(0, index), and) || language::nullable(model::lift_regex(g, ids[index]@)) },
    {
        hide(model::lift_regex);
        hide(language::nullable);
        let prefix = ids.subrange(0, index);
        let full = ids.subrange(0, index + 1);
        assert(full =~= prefix.push(ids[index]));
        if and {
            if regex_nullable_combo(g, full, true) {
                assert(language::nullable(model::lift_regex(g, full[index]@)));
                assert forall|i: int| 0 <= i < prefix.len() implies language::nullable(model::lift_regex(g, prefix[i]@)) by {
                    assert(prefix[i] == full[i]);
                }
            }
            if regex_nullable_combo(g, prefix, true) && language::nullable(model::lift_regex(g, ids[index]@)) {
                assert forall|i: int| 0 <= i < full.len() implies language::nullable(model::lift_regex(g, full[i]@)) by {
                    if i < index { assert(full[i] == prefix[i]); }
                    else { assert(full[i] == ids[index]); }
                }
            }
        } else {
            if regex_nullable_combo(g, full, false) {
                let i = choose|i: int| 0 <= i < full.len() && language::nullable(model::lift_regex(g, full[i]@));
                if i < index {
                    assert(prefix[i] == full[i]);
                    assert(regex_nullable_combo(g, prefix, false));
                } else { assert(full[i] == ids[index]); }
            }
            if regex_nullable_combo(g, prefix, false) {
                let i = choose|i: int| 0 <= i < prefix.len() && language::nullable(model::lift_regex(g, prefix[i]@));
                assert(prefix[i] == full[i]);
                assert(regex_nullable_combo(g, full, false));
            }
            if language::nullable(model::lift_regex(g, ids[index]@)) {
                assert(full[index] == ids[index]);
                assert(regex_nullable_combo(g, full, false));
            }
        }
    }

    pub proof fn regex_children_count(g: model::Graph, id: nat)
        requires id < g.regexes.len(),
        ensures match g.regexes[id as int].kind {
            model::RegexKindNode::Union(cs) | model::RegexKindNode::Concat(cs) | model::RegexKindNode::Intersect(cs) => regex_children(g, id) == cs,
            _ => regex_children(g, id).len() == 0,
        },
    {
        reveal(regex_children);
    }

    pub open spec fn regex_dual(g: model::Graph, id: nat, intersect: bool) -> bool {
        match g.regexes[id as int].kind {
            model::RegexKindNode::Union(_) => intersect,
            model::RegexKindNode::Intersect(_) => !intersect,
            _ => false,
        }
    }

    pub open spec fn regex_absorbed_by(g: model::Graph, a: nat, b: nat, intersect: bool) -> bool {
        a != b && regex_dual(g, a, intersect)
            && if regex_dual(g, b, intersect) {
                forall|i: int| 0 <= i < regex_children(g, b).len() ==> regex_children(g, a).contains(regex_children(g, b)[i])
            } else { regex_children(g, a).contains(b) }
    }

    pub proof fn regex_dual_order(g: model::Graph, id: nat, intersect: bool)
        requires model::graph_wf(g), id < g.regexes.len(), regex_dual(g, id, intersect),
        ensures model::strictly_increasing(regex_children(g, id)),
    {
        reveal(regex_children);
        model::lemma_graph_regex_wf(g, id);
        assert(model::regex_node_wf_at(g, g.regexes[id as int], id));
    }

    pub proof fn regex_ids_contains(ids: Seq<RegexId>, id: RegexId)
        ensures model::regex_ids(ids).contains(id@) == ids.contains(id),
    {
        if model::regex_ids(ids).contains(id@) {
            let i = choose|i: int| 0 <= i < ids.len() && model::regex_ids(ids)[i] == id@;
            assert(ids[i] == id);
        }
        if ids.contains(id) {
            let i = choose|i: int| 0 <= i < ids.len() && ids[i] == id;
            assert(model::regex_ids(ids)[i] == id@);
        }
    }

    pub open spec fn regex_mode_wf(g: model::Graph, mode: RegexModeModel) -> bool {
        mode.identity@ == (if mode.intersect { g.constants.all } else { g.constants.empty })
            && mode.absorber@ == (if mode.intersect { g.constants.empty } else { g.constants.all })
    }

    pub open spec fn regex_set_piece(g: model::Graph, id: nat, mode: RegexModeModel) -> Seq<nat> {
        if id == mode.identity@ { Seq::empty() }
        else { match g.regexes[id as int].kind {
            model::RegexKindNode::Union(cs) => if !mode.intersect { cs } else { seq![id] },
            model::RegexKindNode::Intersect(cs) => if mode.intersect { cs } else { seq![id] },
            _ => seq![id],
        } }
    }

    pub open spec fn regex_nonnullable_except_not_epsilon(g: model::Graph, id: nat, epsilon: nat) -> bool {
        !language::nullable(model::lift_regex(g, id)) && g.regexes[id as int].kind != model::RegexKindNode::Not(epsilon)
    }

    pub open spec fn regex_has_complement_model(g: model::Graph, id: nat, siblings: Seq<RegexId>) -> bool {
        match g.regexes[id as int].kind {
            model::RegexKindNode::Not(inner) => model::regex_ids(siblings).contains(inner),
            _ => false,
        }
    }

    pub open spec fn regex_stats_update(g: model::Graph, ids: Seq<RegexId>, index: int, epsilon: RegexId, prior: RegexStatsModel, complements: bool) -> RegexStatsModel {
        let id = ids[index]@;
        let nullable = language::nullable(model::lift_regex(g, id));
        RegexStatsModel {
            all_nullable: prior.all_nullable && nullable,
            any_nullable: prior.any_nullable || (id != epsilon@ && nullable),
            epsilon: prior.epsilon || id == epsilon@,
            complement: prior.complement || (complements && regex_has_complement_model(g, id, ids)),
            has_nonnullable: prior.has_nonnullable || regex_nonnullable_except_not_epsilon(g, id, epsilon@),
        }
    }

    pub open spec fn regex_retained(g: model::Graph, ids: Seq<RegexId>, index: int, mode: RegexModeModel, stats: RegexStatsModel) -> bool {
        let id = ids[index]@;
        let redundant = (!mode.intersect && id == g.constants.epsilon && stats.any_nullable)
            || (mode.intersect && stats.has_nonnullable && g.regexes[id as int].kind == model::RegexKindNode::Not(g.constants.epsilon));
        !redundant && !(exists|i: int| 0 <= i < ids.len() && regex_absorbed_by(g, id, ids[i]@, mode.intersect))
    }

    pub proof fn regex_nullable_concat_unfold<L>(regex: language::Regex<L>)
        ensures match regex {
            language::Regex::Concat(children) => language::nullable(regex)
                == (forall|i: int| 0 <= i < children.len() ==> language::nullable(children[i])),
            _ => true,
        },
    {
        match regex { language::Regex::Concat(_) => {}, _ => {} }
    }

    pub proof fn regex_concat_node_wf(g: model::Graph, ids: Seq<RegexId>, nullable: bool)
        requires regex_ids_valid(g, ids), nullable == regex_nullable_combo(g, ids, true),
        ensures model::regex_node_wf(g, model::RegexNode { kind: model::RegexKindNode::Concat(model::regex_ids(ids)), nullable }),
    {
        assert(model::bounded(model::regex_ids(ids), g.regexes.len()));
        assert(model::lift_regexes_bounded(g, model::regex_ids(ids), g.regexes.len()) =~= model::lift_regexes(g, model::regex_ids(ids)));
        let lifts = model::lift_regexes(g, model::regex_ids(ids));
        let regex = language::Regex::Concat(lifts);
        assert(model::lift_regex_kind_bounded(g, model::RegexKindNode::Concat(model::regex_ids(ids)), g.regexes.len()) == regex);
        regex_nullable_concat_unfold(regex);
        assert(language::nullable(regex) == (forall|i: int| 0 <= i < lifts.len() ==> language::nullable(lifts[i])));
        if regex_nullable_combo(g, ids, true) {
            assert forall|i: int| 0 <= i < lifts.len() implies language::nullable(lifts[i]) by {
                assert(lifts[i] == model::lift_regex(g, ids[i]@));
            }
        }
        if language::nullable(regex) {
            assert forall|i: int| 0 <= i < ids.len() implies language::nullable(model::lift_regex(g, ids[i]@)) by {
                assert(language::nullable(lifts[i]));
            }
        }
        assert forall|i: int| 0 <= i < ids.len() implies
            language::nullable(model::lift_regexes(g, model::regex_ids(ids))[i])
                == language::nullable(model::lift_regex(g, ids[i]@)) by {};
    }

    pub proof fn regex_concat_extends(a: model::Graph, b: model::Graph, ids: Seq<RegexId>)
        requires model::graph_wf(a), model::graph_extends(a, b), regex_ids_valid(a, ids),
        ensures regex_ids_valid(b, ids),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
                concat_combo(a, sym, theta, ids, word) == concat_combo(b, sym, theta, ids, word),
    {
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
        assert(model::lift_regexes(a, model::regex_ids(ids)) =~= model::lift_regexes(b, model::regex_ids(ids)));
    }

    pub proof fn regex_concat_normalization_extends(a: model::Graph, b: model::Graph, original: Seq<RegexId>, flat: Seq<RegexId>)
        requires model::graph_wf(a), model::graph_extends(a, b), regex_ids_valid(a, original), regex_ids_valid(a, flat),
            model::regex_ids(flat) == regex_concat_flat(a, original),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            concat_combo(b, sym, theta, flat, word) == concat_combo(b, sym, theta, original, word),
    {
        regex_concat_extends(a, b, original);
        regex_concat_extends(a, b, flat);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            concat_combo(b, sym, theta, flat, word) == concat_combo(b, sym, theta, original, word) by {
            regex_concat_flat_law(a, original, sym, theta, word);
        }
    }

    pub proof fn regex_contains_prefix(ids: Seq<RegexId>, index: int, id: RegexId)
        requires 0 <= index < ids.len(),
        ensures ids.subrange(0, index + 1).contains(id)
            == (ids.subrange(0, index).contains(id) || ids[index] == id),
    {
        assert(ids.subrange(0, index + 1) =~= ids.subrange(0, index).push(ids[index]));
        if ids.subrange(0, index + 1).contains(id) {
            let i = choose|i: int| 0 <= i < index + 1 && #[trigger] ids.subrange(0, index + 1)[i] == id;
            if i < index {
                assert(ids.subrange(0, index)[i] == id);
                assert(ids.subrange(0, index).contains(id));
            }
            else { assert(ids[index] == id); }
        }
        if ids.subrange(0, index).contains(id) {
            let i = choose|i: int| 0 <= i < index && #[trigger] ids.subrange(0, index)[i] == id;
            assert(ids.subrange(0, index + 1)[i] == id);
            assert(ids.subrange(0, index + 1).contains(id));
        }
        if ids[index] == id {
            assert(ids.subrange(0, index + 1)[index] == id);
            assert(ids.subrange(0, index + 1).contains(id));
        }
    }

    pub open spec fn regex_combo_nats(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, ids: Seq<nat>, word: Seq<Data>, intersect: bool) -> bool {
        if intersect { forall|i: int| 0 <= i < ids.len() ==> model::regex_lang(g, sym, theta, ids[i], word) }
        else { exists|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, ids[i], word) }
    }

    pub proof fn regex_language_unfold<L>(sem: spec_fn(L, Data) -> bool, regex: language::Regex<L>, word: Seq<Data>)
        ensures match regex {
            language::Regex::Union(cs) => language::lang(sem, regex, word) == (exists|i: int| 0 <= i < cs.len() && language::lang(sem, cs[i], word)),
            language::Regex::Intersect(cs) => language::lang(sem, regex, word) == (forall|i: int| 0 <= i < cs.len() ==> language::lang(sem, cs[i], word)),
            language::Regex::Test(t) => language::lang(sem, regex, word) == (word.len() == 1 && sem(t, word[0])),
            language::Regex::Not(r) => language::lang(sem, regex, word) == !language::lang(sem, *r, word),
            language::Regex::Epsilon => language::lang(sem, regex, word) == (word.len() == 0),
            language::Regex::Empty => !language::lang(sem, regex, word),
            language::Regex::All => language::lang(sem, regex, word),
            _ => true,
        },
    {
        match regex {
            language::Regex::Union(_) | language::Regex::Intersect(_) | language::Regex::Test(_) | language::Regex::Not(_) | language::Regex::Epsilon => {},
            _ => {},
        }
    }

    pub proof fn regex_node_language(g: model::Graph, id: nat, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>)
        requires model::graph_wf(g), id < g.regexes.len(),
        ensures match g.regexes[id as int].kind {
            model::RegexKindNode::Union(cs) => model::regex_lang(g, sym, theta, id, word) == regex_combo_nats(g, sym, theta, cs, word, false),
            model::RegexKindNode::Intersect(cs) => model::regex_lang(g, sym, theta, id, word) == regex_combo_nats(g, sym, theta, cs, word, true),
            model::RegexKindNode::Test(t) => model::regex_lang(g, sym, theta, id, word)
                == (word.len() == 1 && model::test_holds(sym, theta, model::lift_test(g, t), word[0])),
            model::RegexKindNode::Not(r) => model::regex_lang(g, sym, theta, id, word) == !model::regex_lang(g, sym, theta, r, word),
            model::RegexKindNode::Empty => !model::regex_lang(g, sym, theta, id, word),
            model::RegexKindNode::All => model::regex_lang(g, sym, theta, id, word),
            model::RegexKindNode::Epsilon => model::regex_lang(g, sym, theta, id, word) == (word.len() == 0),
            _ => true,
        },
    {
        regex_unfold(g, id);
        let sem = model::gsem(sym, theta);
        regex_language_unfold(sem, model::lift_regex(g, id), word);
        match g.regexes[id as int].kind {
            model::RegexKindNode::Union(cs) => {
                if model::regex_lang(g, sym, theta, id, word) {
                    let i = choose|i: int| 0 <= i < cs.len() && language::lang(sem, model::lift_regexes(g, cs)[i], word);
                    assert(model::regex_lang(g, sym, theta, cs[i], word));
                }
                if regex_combo_nats(g, sym, theta, cs, word, false) {
                    let i = choose|i: int| 0 <= i < cs.len() && model::regex_lang(g, sym, theta, cs[i], word);
                    assert(language::lang(sem, model::lift_regexes(g, cs)[i], word));
                }
            },
            model::RegexKindNode::Intersect(cs) => {
                if model::regex_lang(g, sym, theta, id, word) {
                    assert forall|i: int| 0 <= i < cs.len() implies model::regex_lang(g, sym, theta, cs[i], word) by {
                        assert(language::lang(sem, model::lift_regexes(g, cs)[i], word));
                    }
                }
                if regex_combo_nats(g, sym, theta, cs, word, true) {
                    assert forall|i: int| 0 <= i < cs.len() implies language::lang(sem, model::lift_regexes(g, cs)[i], word) by {
                        assert(model::regex_lang(g, sym, theta, cs[i], word));
                    }
                }
            },
            _ => {},
        }
    }

    pub proof fn regex_absorption_implication(g: model::Graph, a: nat, b: nat, intersect: bool, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>)
        requires model::graph_wf(g), a < g.regexes.len(), b < g.regexes.len(), regex_absorbed_by(g, a, b, intersect),
        ensures if intersect { model::regex_lang(g, sym, theta, b, word) ==> model::regex_lang(g, sym, theta, a, word) }
            else { model::regex_lang(g, sym, theta, a, word) ==> model::regex_lang(g, sym, theta, b, word) },
    {
        regex_node_language(g, a, sym, theta, word);
        regex_node_language(g, b, sym, theta, word);
        regex_children_count(g, a);
        regex_children_count(g, b);
        let ac = regex_children(g, a);
        let bc = regex_children(g, b);
        if intersect && model::regex_lang(g, sym, theta, b, word) {
            if regex_dual(g, b, intersect) {
                let j = choose|j: int| 0 <= j < bc.len() && model::regex_lang(g, sym, theta, bc[j], word);
                let k = choose|k: int| 0 <= k < ac.len() && ac[k] == bc[j];
                assert(model::regex_lang(g, sym, theta, ac[k], word));
            } else {
                let k = choose|k: int| 0 <= k < ac.len() && ac[k] == b;
                assert(model::regex_lang(g, sym, theta, ac[k], word));
            }
        }
        if !intersect && model::regex_lang(g, sym, theta, a, word) {
            if regex_dual(g, b, intersect) {
                assert forall|j: int| 0 <= j < bc.len() implies model::regex_lang(g, sym, theta, bc[j], word) by {
                    let k = choose|k: int| 0 <= k < ac.len() && ac[k] == bc[j];
                    assert(model::regex_lang(g, sym, theta, ac[k], word));
                }
            } else {
                let k = choose|k: int| 0 <= k < ac.len() && ac[k] == b;
                assert(model::regex_lang(g, sym, theta, ac[k], word));
            }
        }
    }

    pub open spec fn regex_stats_prefix(g: model::Graph, ids: Seq<RegexId>, count: nat, epsilon: RegexId, stats: RegexStatsModel, complements: bool) -> bool {
        count <= ids.len()
            && stats.all_nullable == regex_nullable_combo(g, ids.subrange(0, count as int), true)
            && stats.any_nullable == (exists|i: int| 0 <= i < count && ids[i] != epsilon && language::nullable(model::lift_regex(g, ids[i]@)))
            && stats.epsilon == (exists|i: int| 0 <= i < count && ids[i] == epsilon)
            && stats.complement == (complements && exists|i: int| 0 <= i < count && regex_has_complement_model(g, ids[i]@, ids))
            && stats.has_nonnullable == (exists|i: int| 0 <= i < count && regex_nonnullable_except_not_epsilon(g, ids[i]@, epsilon@))
    }

    pub proof fn regex_exists_prefix(predicate: spec_fn(int) -> bool, index: int)
        requires index >= 0,
        ensures (exists|i: int| 0 <= i < index + 1 && #[trigger] predicate(i))
            == ((exists|i: int| 0 <= i < index && #[trigger] predicate(i)) || predicate(index)),
    {
        if exists|i: int| 0 <= i < index + 1 && #[trigger] predicate(i) {
            let i = choose|i: int| 0 <= i < index + 1 && #[trigger] predicate(i);
            if i < index { assert(exists|j: int| 0 <= j < index && #[trigger] predicate(j)); }
        }
    }

    pub proof fn regex_stats_prefix_step(g: model::Graph, ids: Seq<RegexId>, index: int, epsilon: RegexId, prior: RegexStatsModel, complements: bool)
        requires 0 <= index < ids.len(), regex_stats_prefix(g, ids, index as nat, epsilon, prior, complements),
        ensures regex_stats_prefix(g, ids, (index + 1) as nat, epsilon, regex_stats_update(g, ids, index, epsilon, prior, complements), complements),
    {
        regex_nullable_prefix(g, ids, index, true);
        regex_exists_prefix(|i: int| ids[i] != epsilon && language::nullable(model::lift_regex(g, ids[i]@)), index);
        regex_exists_prefix(|i: int| ids[i] == epsilon, index);
        regex_exists_prefix(|i: int| regex_has_complement_model(g, ids[i]@, ids), index);
        regex_exists_prefix(|i: int| regex_nonnullable_except_not_epsilon(g, ids[i]@, epsilon@), index);
    }

    pub proof fn regex_remove_covered(g: model::Graph, ids: Seq<RegexId>, index: int, witness: int, intersect: bool, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>)
        requires 0 <= index < ids.len(), 0 <= witness < ids.len(), witness != index,
            if intersect { model::regex_lang(g, sym, theta, ids[witness]@, word) ==> model::regex_lang(g, sym, theta, ids[index]@, word) }
            else { model::regex_lang(g, sym, theta, ids[index]@, word) ==> model::regex_lang(g, sym, theta, ids[witness]@, word) },
        ensures regex_combo(g, sym, theta, ids.remove(index), word, intersect) == regex_combo(g, sym, theta, ids, word, intersect),
    {
        let reduced = ids.remove(index);
        let witness_after = if witness < index { witness } else { witness - 1 };
        assert(reduced[witness_after] == ids[witness]);
        if intersect {
            if regex_combo(g, sym, theta, reduced, word, true) {
                assert(model::regex_lang(g, sym, theta, ids[witness]@, word));
                assert forall|i: int| 0 <= i < ids.len() implies model::regex_lang(g, sym, theta, ids[i]@, word) by {
                    if i != index {
                        let j = if i < index { i } else { i - 1 };
                        assert(reduced[j] == ids[i]);
                        assert(model::regex_lang(g, sym, theta, reduced[j]@, word));
                    }
                }
            }
            if regex_combo(g, sym, theta, ids, word, true) {
                assert forall|j: int| 0 <= j < reduced.len() implies model::regex_lang(g, sym, theta, reduced[j]@, word) by {
                    let i = if j < index { j } else { j + 1 };
                    assert(reduced[j] == ids[i]);
                }
            }
        } else {
            if regex_combo(g, sym, theta, ids, word, false) {
                let i = choose|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, ids[i]@, word);
                let j = if i == index { witness_after } else if i < index { i } else { i - 1 };
                assert(model::regex_lang(g, sym, theta, reduced[j]@, word));
            }
            if regex_combo(g, sym, theta, reduced, word, false) {
                let j = choose|j: int| 0 <= j < reduced.len() && model::regex_lang(g, sym, theta, reduced[j]@, word);
                let i = if j < index { j } else { j + 1 };
                assert(reduced[j] == ids[i]);
                assert(model::regex_lang(g, sym, theta, ids[i]@, word));
            }
        }
    }

    pub proof fn regex_retention_remove(g: model::Graph, ids: Seq<RegexId>, index: int, mode: RegexModeModel, epsilon: RegexId, stats: RegexStatsModel)
        requires model::graph_wf(g), regex_ids_valid(g, ids), 0 <= index < ids.len(),
            regex_stats_prefix(g, ids, ids.len(), epsilon, stats, false), epsilon@ == g.constants.epsilon,
            !regex_retained(g, ids, index, mode, stats),
        ensures regex_ids_valid(g, ids.remove(index)),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> regex_combo(g, sym, theta, ids.remove(index), word, mode.intersect) == regex_combo(g, sym, theta, ids, word, mode.intersect),
    {
        regex_constants(g);
        let a = ids[index]@;
        regex_unfold(g, a);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            implies regex_combo(g, sym, theta, ids.remove(index), word, mode.intersect) == regex_combo(g, sym, theta, ids, word, mode.intersect) by {
            let sem = model::gsem(sym, theta);
            if exists|i: int| 0 <= i < ids.len() && regex_absorbed_by(g, a, ids[i]@, mode.intersect) {
                let witness = choose|i: int| 0 <= i < ids.len() && regex_absorbed_by(g, a, ids[i]@, mode.intersect);
                regex_absorption_implication(g, a, ids[witness]@, mode.intersect, sym, theta, word);
                regex_remove_covered(g, ids, index, witness, mode.intersect, sym, theta, word);
            } else if !mode.intersect {
                let witness = choose|i: int| 0 <= i < ids.len() && ids[i]@ != g.constants.epsilon && language::nullable(model::lift_regex(g, ids[i]@));
                language::lemma_nullable_iff_nil(sem, model::lift_regex(g, ids[witness]@));
                if model::regex_lang(g, sym, theta, a, word) {
                    assert(word =~= Seq::<Data>::empty());
                }
                regex_remove_covered(g, ids, index, witness, false, sym, theta, word);
            } else {
                let witness = choose|i: int| 0 <= i < ids.len() && regex_nonnullable_except_not_epsilon(g, ids[i]@, g.constants.epsilon);
                regex_unfold(g, ids[witness]@);
                language::lemma_nullable_iff_nil(sem, model::lift_regex(g, ids[witness]@));
                regex_node_language(g, a, sym, theta, word);
                regex_language_unfold(sem, model::lift_regex(g, g.constants.epsilon), word);
                if model::regex_lang(g, sym, theta, ids[witness]@, word) {
                    if word.len() == 0 { assert(word =~= Seq::<Data>::empty()); }
                }
                regex_remove_covered(g, ids, index, witness, true, sym, theta, word);
            }
        }
        assert forall|i: int| 0 <= i < ids.remove(index).len() implies ids.remove(index)[i]@ < g.regexes.len() by {
            let j = if i < index { i } else { i + 1 };
            assert(ids.remove(index)[i] == ids[j]);
        }
    }

    pub open spec fn regex_equivalent(g: model::Graph, left: Seq<RegexId>, right: Seq<RegexId>, intersect: bool) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            ==> regex_combo(g, sym, theta, left, word, intersect) == regex_combo(g, sym, theta, right, word, intersect)
    }

    pub proof fn regex_ids_shape(ids: Seq<RegexId>)
        ensures model::regex_ids(ids).len() == ids.len(),
            forall|i: int| 0 <= i < ids.len() ==> model::regex_ids(ids)[i] == ids[i]@,
    {}

    pub proof fn regex_test_ids_shape(ids: Seq<TestId>)
        ensures model::test_ids(ids).len() == ids.len(),
            forall|i: int| 0 <= i < ids.len() ==> model::test_ids(ids)[i] == ids[i]@,
    {}

    pub proof fn regex_combo_members(g: model::Graph, left: Seq<RegexId>, right: Seq<RegexId>, intersect: bool)
        requires forall|id: RegexId| left.contains(id) == right.contains(id),
        ensures regex_equivalent(g, left, right, intersect),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            implies regex_combo(g, sym, theta, left, word, intersect) == regex_combo(g, sym, theta, right, word, intersect) by {
            if intersect {
                if regex_combo(g, sym, theta, left, word, true) {
                    assert forall|i: int| 0 <= i < right.len() implies model::regex_lang(g, sym, theta, right[i]@, word) by {
                        assert(right.contains(right[i]));
                        assert(left.contains(right[i]));
                        let j = choose|j: int| 0 <= j < left.len() && left[j] == right[i];
                        assert(model::regex_lang(g, sym, theta, left[j]@, word));
                    }
                }
                if regex_combo(g, sym, theta, right, word, true) {
                    assert forall|i: int| 0 <= i < left.len() implies model::regex_lang(g, sym, theta, left[i]@, word) by {
                        assert(left.contains(left[i]));
                        assert(right.contains(left[i]));
                        let j = choose|j: int| 0 <= j < right.len() && right[j] == left[i];
                        assert(model::regex_lang(g, sym, theta, right[j]@, word));
                    }
                }
            } else {
                if regex_combo(g, sym, theta, left, word, false) {
                    let i = choose|i: int| 0 <= i < left.len() && model::regex_lang(g, sym, theta, left[i]@, word);
                    assert(left.contains(left[i]));
                    assert(right.contains(left[i]));
                    let j = choose|j: int| 0 <= j < right.len() && right[j] == left[i];
                    assert(model::regex_lang(g, sym, theta, right[j]@, word));
                }
                if regex_combo(g, sym, theta, right, word, false) {
                    let i = choose|i: int| 0 <= i < right.len() && model::regex_lang(g, sym, theta, right[i]@, word);
                    assert(right.contains(right[i]));
                    assert(left.contains(right[i]));
                    let j = choose|j: int| 0 <= j < left.len() && left[j] == right[i];
                    assert(model::regex_lang(g, sym, theta, left[j]@, word));
                }
            }
        }
    }

    pub proof fn regex_combo_permutation(g: model::Graph, left: Seq<RegexId>, right: Seq<RegexId>, intersect: bool)
        requires left.to_multiset() == right.to_multiset(),
        ensures regex_equivalent(g, left, right, intersect),
    {
        assert forall|id: RegexId| left.contains(id) == right.contains(id) by {
            vstd::seq_lib::to_multiset_contains(left, id);
            vstd::seq_lib::to_multiset_contains(right, id);
        }
        regex_combo_members(g, left, right, intersect);
    }

    pub proof fn regex_combo_push(g: model::Graph, ids: Seq<RegexId>, id: RegexId, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>, intersect: bool)
        ensures regex_combo(g, sym, theta, ids.push(id), word, intersect)
            == if intersect { regex_combo(g, sym, theta, ids, word, true) && model::regex_lang(g, sym, theta, id@, word) }
                else { regex_combo(g, sym, theta, ids, word, false) || model::regex_lang(g, sym, theta, id@, word) },
    {
        regex_exists_prefix(|i: int| model::regex_lang(g, sym, theta, ids.push(id)[i]@, word), ids.len() as int);
        if intersect {
            if regex_combo(g, sym, theta, ids.push(id), word, true) {
                assert(model::regex_lang(g, sym, theta, ids.push(id)[ids.len() as int]@, word));
                assert forall|i: int| 0 <= i < ids.len() implies model::regex_lang(g, sym, theta, ids[i]@, word) by {
                    assert(ids.push(id)[i] == ids[i]);
                }
            }
            if regex_combo(g, sym, theta, ids, word, true) && model::regex_lang(g, sym, theta, id@, word) {
                assert forall|i: int| 0 <= i < ids.push(id).len() implies model::regex_lang(g, sym, theta, ids.push(id)[i]@, word) by {
                    if i < ids.len() { assert(ids.push(id)[i] == ids[i]); }
                    else { assert(ids.push(id)[i] == id); }
                }
            }
        } else {
            if regex_combo(g, sym, theta, ids.push(id), word, false) {
                let i = choose|i: int| 0 <= i < ids.push(id).len() && model::regex_lang(g, sym, theta, ids.push(id)[i]@, word);
                if i < ids.len() { assert(ids.push(id)[i] == ids[i]); assert(regex_combo(g, sym, theta, ids, word, false)); }
                else { assert(ids.push(id)[i] == id); }
            }
            if regex_combo(g, sym, theta, ids, word, false) {
                let i = choose|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, ids[i]@, word);
                assert(ids.push(id)[i] == ids[i]); assert(regex_combo(g, sym, theta, ids.push(id), word, false));
            }
            if model::regex_lang(g, sym, theta, id@, word) {
                assert(ids.push(id)[ids.len() as int] == id); assert(regex_combo(g, sym, theta, ids.push(id), word, false));
            }
        }
    }

    pub proof fn regex_set_node_wf(g: model::Graph, ids: Seq<RegexId>, nullable: bool, intersect: bool)
        requires regex_ids_valid(g, ids), model::strictly_increasing(model::regex_ids(ids)), nullable == regex_nullable_combo(g, ids, intersect),
        ensures model::regex_node_wf(g, model::RegexNode {
            kind: if intersect { model::RegexKindNode::Intersect(model::regex_ids(ids)) } else { model::RegexKindNode::Union(model::regex_ids(ids)) }, nullable }),
    {
        regex_ids_shape(ids);
        assert(model::bounded(model::regex_ids(ids), g.regexes.len()));
        assert(model::lift_regexes_bounded(g, model::regex_ids(ids), g.regexes.len()) =~= model::lift_regexes(g, model::regex_ids(ids)));
        let cs = model::lift_regexes(g, model::regex_ids(ids));
        let sem = |test: model::Test, event: Data| true;
        let word = Seq::<Data>::empty();
        let root = if intersect { language::Regex::Intersect(cs) } else { language::Regex::Union(cs) };
        language::lemma_nullable_iff_nil(sem, root);
        regex_language_unfold(sem, root, word);
        assert forall|i: int| 0 <= i < ids.len() implies language::lang(sem, cs[i], word)
            == language::nullable(model::lift_regex(g, ids[i]@)) by {
            assert(cs[i] == model::lift_regex(g, ids[i]@));
            language::lemma_nullable_iff_nil(sem, cs[i]);
        }
        if intersect {
            if nullable {
                assert forall|i: int| 0 <= i < cs.len() implies language::lang(sem, cs[i], word) by {};
            }
            if language::lang(sem, root, word) {
                assert forall|i: int| 0 <= i < ids.len() implies language::nullable(model::lift_regex(g, ids[i]@)) by {
                    assert(language::lang(sem, cs[i], word));
                }
            }
        } else {
            if nullable {
                let i = choose|i: int| 0 <= i < ids.len() && language::nullable(model::lift_regex(g, ids[i]@));
                assert(language::lang(sem, cs[i], word));
            }
            if language::lang(sem, root, word) {
                let i = choose|i: int| 0 <= i < cs.len() && language::lang(sem, cs[i], word);
                assert(language::nullable(model::lift_regex(g, ids[i]@)));
            }
        }
    }

    pub open spec fn regex_test_combo(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, tests: Seq<TestId>, word: Seq<Data>, intersect: bool) -> bool {
        if tests.len() == 0 { intersect }
        else { word.len() == 1 && test_combo(g, sym, theta, tests, word[0], intersect) }
    }

    pub open spec fn regex_group_combo(g: model::Graph, sym: model::Symbols, theta: Seq<Data>, tests: Seq<TestId>, others: Seq<RegexId>, word: Seq<Data>, intersect: bool) -> bool {
        if intersect { regex_test_combo(g, sym, theta, tests, word, true) && regex_combo(g, sym, theta, others, word, true) }
        else { regex_test_combo(g, sym, theta, tests, word, false) || regex_combo(g, sym, theta, others, word, false) }
    }

    pub proof fn regex_split_preserves(g: model::Graph, id: RegexId, tests: Seq<TestId>, others: Seq<RegexId>, next_tests: Seq<TestId>, next_others: Seq<RegexId>, intersect: bool)
        requires model::graph_wf(g), id@ < g.regexes.len(),
            match g.regexes[id@ as int].kind {
                model::RegexKindNode::Test(t) => model::test_ids(next_tests) == model::test_ids(tests).push(t) && next_others == others,
                _ => next_tests == tests && next_others == others.push(id),
            },
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            #![trigger regex_group_combo(g, sym, theta, next_tests, next_others, word, intersect)]
            regex_group_combo(g, sym, theta, next_tests, next_others, word, intersect)
                == if intersect { regex_group_combo(g, sym, theta, tests, others, word, true) && model::regex_lang(g, sym, theta, id@, word) }
                    else { regex_group_combo(g, sym, theta, tests, others, word, false) || model::regex_lang(g, sym, theta, id@, word) },
    {
        hide(language::lang);
        hide(model::test_holds);
        regex_test_ids_shape(tests);
        regex_test_ids_shape(next_tests);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            #![trigger regex_group_combo(g, sym, theta, next_tests, next_others, word, intersect)]
            regex_group_combo(g, sym, theta, next_tests, next_others, word, intersect)
                == if intersect { regex_group_combo(g, sym, theta, tests, others, word, true) && model::regex_lang(g, sym, theta, id@, word) }
                    else { regex_group_combo(g, sym, theta, tests, others, word, false) || model::regex_lang(g, sym, theta, id@, word) } by {
            regex_node_language(g, id@, sym, theta, word);
            match g.regexes[id@ as int].kind {
                model::RegexKindNode::Test(t) => {
                    assert(next_tests.len() == tests.len() + 1);
                    assert forall|i: int| 0 <= i < tests.len() implies next_tests[i] == tests[i] by {
                        assert(model::test_ids(next_tests)[i] == model::test_ids(tests)[i]);
                        assert(next_tests[i]@ == tests[i]@);
                    }
                    assert(model::test_ids(next_tests)[tests.len() as int] == t);
                    assert(next_tests[tests.len() as int]@ == t);
                    if word.len() == 1 {
                        let event = word[0];
                        if intersect {
                            if test_combo(g, sym, theta, next_tests, event, true) {
                                assert(model::test_holds(sym, theta, model::lift_test(g, next_tests[tests.len() as int]@), event));
                                assert forall|i: int| 0 <= i < tests.len() implies model::test_holds(sym, theta, model::lift_test(g, tests[i]@), event) by {
                                    assert(next_tests[i] == tests[i]);
                                }
                            }
                            if test_combo(g, sym, theta, tests, event, true) && model::test_holds(sym, theta, model::lift_test(g, t), event) {
                                assert forall|i: int| 0 <= i < next_tests.len() implies model::test_holds(sym, theta, model::lift_test(g, next_tests[i]@), event) by {
                                    if i < tests.len() { assert(next_tests[i] == tests[i]); }
                                    else { assert(next_tests[i]@ == t); }
                                }
                            }
                        } else {
                            regex_exists_prefix(|i: int| model::test_holds(sym, theta, model::lift_test(g, next_tests[i]@), event), tests.len() as int);
                            if test_combo(g, sym, theta, tests, event, false) {
                                let i = choose|i: int| 0 <= i < tests.len() && model::test_holds(sym, theta, model::lift_test(g, tests[i]@), event);
                                assert(next_tests[i] == tests[i]);
                                assert(test_combo(g, sym, theta, next_tests, event, false));
                            }
                        }
                    }
                },
                _ => { regex_combo_push(g, others, id, sym, theta, word, intersect); },
            }
        }
    }

    pub proof fn regex_collect_preserves(g: model::Graph, id: RegexId, before: Seq<RegexId>, after: Seq<RegexId>, mode: RegexModeModel)
        requires model::graph_wf(g), id@ < g.regexes.len(), regex_mode_wf(g, mode), id != mode.absorber,
            model::regex_ids(after) == model::regex_ids(before) + regex_set_piece(g, id@, mode),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            #![trigger regex_combo(g, sym, theta, after, word, mode.intersect)]
            regex_combo(g, sym, theta, after, word, mode.intersect)
                == if mode.intersect { regex_combo(g, sym, theta, before, word, true) && model::regex_lang(g, sym, theta, id@, word) }
                    else { regex_combo(g, sym, theta, before, word, false) || model::regex_lang(g, sym, theta, id@, word) },
    {
        hide(language::lang);
        hide(model::lift_regex);
        regex_ids_shape(before);
        regex_ids_shape(after);
        regex_children_count(g, id@);
        regex_constants(g);
        assert(model::regex_ids(after) == model::regex_ids(before) + regex_set_piece(g, id@, mode));
        assert(model::regex_ids(after).subrange(before.len() as int, after.len() as int) == regex_set_piece(g, id@, mode));
        assert forall|i: int| before.len() <= i < after.len() implies after[i]@ == regex_set_piece(g, id@, mode)[i - before.len()] by {};
        assert(after.len() >= before.len());
        assert forall|i: int| 0 <= i < before.len() implies after[i] == before[i] by {
            assert(model::regex_ids(after)[i] == model::regex_ids(before)[i]);
            assert(after[i]@ == before[i]@);
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            #![trigger regex_combo(g, sym, theta, after, word, mode.intersect)]
            regex_combo(g, sym, theta, after, word, mode.intersect)
                == if mode.intersect { regex_combo(g, sym, theta, before, word, true) && model::regex_lang(g, sym, theta, id@, word) }
                    else { regex_combo(g, sym, theta, before, word, false) || model::regex_lang(g, sym, theta, id@, word) } by {
            regex_node_language(g, id@, sym, theta, word);
            regex_language_unfold(model::gsem(sym, theta), language::Regex::Empty, word);
            regex_language_unfold(model::gsem(sym, theta), language::Regex::All, word);
            let pivot = before.len() as int;
            if mode.intersect {
                if regex_combo(g, sym, theta, after, word, true) {
                    assert forall|i: int| 0 <= i < before.len() implies model::regex_lang(g, sym, theta, before[i]@, word) by {
                        assert(after[i] == before[i]);
                    }
                    if id != mode.identity {
                        if g.regexes[id@ as int].kind is Intersect {
                            let cs = regex_children(g, id@);
                            assert forall|i: int| 0 <= i < cs.len() implies model::regex_lang(g, sym, theta, cs[i], word) by {
                                assert(after[pivot + i]@ == cs[i]);
                            }
                        } else { assert(after[pivot] == id); }
                    }
                }
                if regex_combo(g, sym, theta, before, word, true) && model::regex_lang(g, sym, theta, id@, word) {
                    assert forall|i: int| 0 <= i < after.len() implies model::regex_lang(g, sym, theta, after[i]@, word) by {
                        if i < pivot { assert(after[i] == before[i]); }
                        else if g.regexes[id@ as int].kind is Intersect { assert(after[i]@ == regex_children(g, id@)[i - pivot]); }
                        else { assert(after[i] == id); }
                    }
                }
            } else {
                if regex_combo(g, sym, theta, after, word, false) {
                    let i = choose|i: int| 0 <= i < after.len() && model::regex_lang(g, sym, theta, after[i]@, word);
                    if i < pivot { assert(after[i] == before[i]); }
                    else if g.regexes[id@ as int].kind is Union { assert(after[i]@ == regex_children(g, id@)[i - pivot]); }
                    else { assert(after[i] == id); }
                }
                if regex_combo(g, sym, theta, before, word, false) {
                    let i = choose|i: int| 0 <= i < before.len() && model::regex_lang(g, sym, theta, before[i]@, word);
                    assert(after[i] == before[i]);
                    assert(regex_combo(g, sym, theta, after, word, false));
                }
                if model::regex_lang(g, sym, theta, id@, word) {
                    assert(id != mode.identity);
                    if g.regexes[id@ as int].kind is Union {
                        let cs = regex_children(g, id@);
                        assert(regex_set_piece(g, id@, mode) == cs);
                        let i = choose|i: int| 0 <= i < cs.len() && model::regex_lang(g, sym, theta, cs[i], word);
                        assert(after[pivot + i]@ == cs[i]);
                        assert(regex_combo(g, sym, theta, after, word, false));
                    } else {
                        assert(regex_set_piece(g, id@, mode) == seq![id@]);
                        assert(after[pivot]@ == id@);
                        assert(after[pivot] == id);
                        assert(regex_combo(g, sym, theta, after, word, false));
                    }
                }
            }
        }
    }

    pub proof fn regex_stats_decisions(g: model::Graph, ids: Seq<RegexId>, epsilon: RegexId, stats: RegexStatsModel, intersect: bool)
        requires model::graph_wf(g), regex_ids_valid(g, ids), epsilon@ == g.constants.epsilon,
            regex_stats_prefix(g, ids, ids.len(), epsilon, stats, true),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            (stats.complement ==> regex_combo(g, sym, theta, ids, word, intersect) == !intersect)
            && (intersect && stats.epsilon ==> regex_combo(g, sym, theta, ids, word, true) == (stats.all_nullable && word.len() == 0)),
    {
        assert(ids.subrange(0, ids.len() as int) =~= ids);
        regex_constants(g);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            (stats.complement ==> regex_combo(g, sym, theta, ids, word, intersect) == !intersect)
            && (intersect && stats.epsilon ==> regex_combo(g, sym, theta, ids, word, true) == (stats.all_nullable && word.len() == 0)) by {
            if stats.complement {
                let i = choose|i: int| 0 <= i < ids.len() && regex_has_complement_model(g, ids[i]@, ids);
                let inner = match g.regexes[ids[i]@ as int].kind { model::RegexKindNode::Not(r) => r, _ => 0nat };
                let j = choose|j: int| 0 <= j < ids.len() && ids[j]@ == inner;
                regex_node_language(g, ids[i]@, sym, theta, word);
                if intersect && regex_combo(g, sym, theta, ids, word, true) {
                    assert(model::regex_lang(g, sym, theta, ids[i]@, word));
                    assert(model::regex_lang(g, sym, theta, ids[j]@, word));
                }
                if !intersect {
                    assert(model::regex_lang(g, sym, theta, ids[i]@, word) || model::regex_lang(g, sym, theta, ids[j]@, word));
                }
            }
            if intersect && stats.epsilon {
                let i = choose|i: int| 0 <= i < ids.len() && ids[i] == epsilon;
                if regex_combo(g, sym, theta, ids, word, true) {
                    assert(model::regex_lang(g, sym, theta, ids[i]@, word));
                    assert(word =~= Seq::<Data>::empty());
                    assert forall|j: int| 0 <= j < ids.len() implies language::nullable(model::lift_regex(g, ids[j]@)) by {
                        language::lemma_nullable_iff_nil(model::gsem(sym, theta), model::lift_regex(g, ids[j]@));
                    }
                }
                if stats.all_nullable && word.len() == 0 {
                    assert(word =~= Seq::<Data>::empty());
                    assert forall|j: int| 0 <= j < ids.len() implies model::regex_lang(g, sym, theta, ids[j]@, word) by {
                        language::lemma_nullable_iff_nil(model::gsem(sym, theta), model::lift_regex(g, ids[j]@));
                    }
                }
            }
        }
    }

    pub proof fn regex_combo_extends(a: model::Graph, b: model::Graph, ids: Seq<RegexId>, intersect: bool)
        requires model::graph_wf(a), model::graph_extends(a, b), regex_ids_valid(a, ids),
        ensures regex_ids_valid(b, ids), forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            regex_combo(a, sym, theta, ids, word, intersect) == regex_combo(b, sym, theta, ids, word, intersect),
    {
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
    }

    pub proof fn regex_group_extends(a: model::Graph, b: model::Graph, tests: Seq<TestId>, others: Seq<RegexId>, intersect: bool)
        requires model::graph_wf(a), model::graph_extends(a, b), test_ids_valid(a, tests), regex_ids_valid(a, others),
        ensures test_ids_valid(b, tests), regex_ids_valid(b, others), forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            regex_group_combo(a, sym, theta, tests, others, word, intersect) == regex_group_combo(b, sym, theta, tests, others, word, intersect),
    {
        model::lemma_graph_wf_elim(a);
        model::lemma_lift_stable_under_extends(a, b);
        regex_combo_extends(a, b, others, intersect);
    }

    pub open spec fn regex_split_prefix(g: model::Graph, flat: Seq<RegexId>, tests: Seq<TestId>, others: Seq<RegexId>, count: nat) -> bool {
        count <= flat.len() && forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>, intersect: bool|
            regex_group_combo(g, sym, theta, tests, others, word, intersect)
                == regex_combo(g, sym, theta, flat.subrange(0, count as int), word, intersect)
    }

    pub proof fn regex_combo_prefix(g: model::Graph, ids: Seq<RegexId>, index: int, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>, intersect: bool)
        requires 0 <= index < ids.len(),
        ensures regex_combo(g, sym, theta, ids.subrange(0, index + 1), word, intersect)
            == if intersect { regex_combo(g, sym, theta, ids.subrange(0, index), word, true) && model::regex_lang(g, sym, theta, ids[index]@, word) }
                else { regex_combo(g, sym, theta, ids.subrange(0, index), word, false) || model::regex_lang(g, sym, theta, ids[index]@, word) },
    {
        assert(ids.subrange(0, index + 1) =~= ids.subrange(0, index).push(ids[index]));
        regex_combo_push(g, ids.subrange(0, index), ids[index], sym, theta, word, intersect);
    }

    pub proof fn regex_absorber_member(g: model::Graph, children: Seq<RegexId>, index: int, mode: RegexModeModel)
        requires model::graph_wf(g), regex_ids_valid(g, children), 0 <= index < children.len(),
            regex_mode_wf(g, mode), children[index] == mode.absorber,
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            regex_combo(g, sym, theta, children, word, mode.intersect) == !mode.intersect,
    {
        regex_constants(g);
        assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            regex_combo(g, sym, theta, children, word, mode.intersect) == !mode.intersect by {
            if mode.intersect && regex_combo(g, sym, theta, children, word, true) {
                assert(model::regex_lang(g, sym, theta, children[index]@, word));
            }
            if !mode.intersect { assert(model::regex_lang(g, sym, theta, children[index]@, word)); }
        }
    }

    pub proof fn regex_group_equivalence_extends(g: model::Graph, next: model::Graph, original: Seq<RegexId>, tests: Seq<TestId>, others: Seq<RegexId>, intersect: bool)
        requires model::graph_wf(g), model::graph_extends(g, next), regex_ids_valid(g, original), test_ids_valid(g, tests), regex_ids_valid(g, others),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> regex_group_combo(g, sym, theta, tests, others, word, intersect) == regex_combo(g, sym, theta, original, word, intersect),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            ==> regex_group_combo(next, sym, theta, tests, others, word, intersect) == regex_combo(next, sym, theta, original, word, intersect),
    {
        regex_group_extends(g, next, tests, others, intersect);
        regex_combo_extends(g, next, original, intersect);
    }

    pub proof fn regex_equivalence_extends(g: model::Graph, next: model::Graph, original: Seq<RegexId>, current: Seq<RegexId>, intersect: bool)
        requires model::graph_wf(g), model::graph_extends(g, next), regex_ids_valid(g, original), regex_ids_valid(g, current), regex_equivalent(g, original, current, intersect),
        ensures regex_equivalent(next, original, current, intersect),
    {
        regex_combo_extends(g, next, original, intersect);
        regex_combo_extends(g, next, current, intersect);
    }

    pub proof fn regex_member_ids_valid(g: model::Graph, source: Seq<RegexId>, target: Seq<RegexId>)
        requires regex_ids_valid(g, source), forall|id: RegexId| target.contains(id) ==> source.contains(id),
        ensures regex_ids_valid(g, target),
    {
        assert forall|i: int| 0 <= i < target.len() implies target[i]@ < g.regexes.len() by {
            assert(target.contains(target[i]));
            assert(source.contains(target[i]));
            let j = choose|j: int| 0 <= j < source.len() && source[j] == target[i];
        }
    }

    pub proof fn regex_multiset_members(source: Seq<RegexId>, target: Seq<RegexId>)
        requires source.to_multiset() == target.to_multiset(),
        ensures forall|id: RegexId| source.contains(id) == target.contains(id),
    {
        lemma_multiset_members(source, target);
    }

    pub proof fn regex_remove_strict(ids: Seq<RegexId>, index: int)
        requires 0 <= index < ids.len(), model::strictly_increasing(model::regex_ids(ids)),
        ensures model::strictly_increasing(model::regex_ids(ids.remove(index))),
    {
        assert forall|i: int, j: int| 0 <= i < j < ids.remove(index).len()
            implies model::regex_ids(ids.remove(index))[i] < model::regex_ids(ids.remove(index))[j] by {
            let a = if i < index { i } else { i + 1 };
            let b = if j < index { j } else { j + 1 };
            assert(ids.remove(index)[i] == ids[a]);
            assert(ids.remove(index)[j] == ids[b]);
            assert(model::regex_ids(ids)[a] < model::regex_ids(ids)[b]);
        }
    }

    pub proof fn regex_set_result(g: model::Graph, ids: Seq<RegexId>, original: Seq<RegexId>, intersect: bool)
        requires model::graph_wf(g), regex_ids_valid(g, ids), regex_ids_valid(g, original), regex_equivalent(g, ids, original, intersect),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym) ==>
            (ids.len() == 0 ==> regex_combo(g, sym, theta, original, word, intersect) == intersect)
            && (ids.len() == 1 ==> regex_combo(g, sym, theta, original, word, intersect) == model::regex_lang(g, sym, theta, ids[0]@, word)),
    {
        if ids.len() == 1 { assert(ids =~= seq![ids[0]]); }
    }

    pub proof fn regex_test_ids_push(ids: Seq<TestId>, id: TestId)
        ensures model::test_ids(ids.push(id)) == model::test_ids(ids).push(id@),
    { assert(model::test_ids(ids.push(id)) =~= model::test_ids(ids).push(id@)); }

    pub proof fn regex_test_connective_extends(g: model::Graph, next: model::Graph, tests: Seq<TestId>, id: TestId, intersect: bool)
        requires model::graph_wf(g), model::graph_extends(g, next), test_ids_valid(g, tests), id@ < g.tests.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> model::test_holds(sym, theta, model::lift_test(g, id@), event) == test_combo(g, sym, theta, tests, event, intersect),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            ==> model::test_holds(sym, theta, model::lift_test(next, id@), event) == test_combo(next, sym, theta, tests, event, intersect),
    {
        hide(model::test_holds);
        hide(language::lang);
        model::lemma_lift_test_stable(g, next, id@);
        assert forall|i: int| 0 <= i < tests.len() implies model::lift_test(g, tests[i]@) == model::lift_test(next, tests[i]@) by {
            model::lemma_lift_test_stable(g, next, tests[i]@);
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            implies model::test_holds(sym, theta, model::lift_test(next, id@), event) == test_combo(next, sym, theta, tests, event, intersect) by {
            assert(model::test_holds(sym, theta, model::lift_test(g, id@), event) == test_combo(g, sym, theta, tests, event, intersect));
            assert forall|i: int| 0 <= i < tests.len() implies model::test_holds(sym, theta, model::lift_test(g, tests[i]@), event)
                == model::test_holds(sym, theta, model::lift_test(next, tests[i]@), event) by {};
            assert(test_combo(g, sym, theta, tests, event, intersect) == test_combo(next, sym, theta, tests, event, intersect));
        }
    }

    pub proof fn regex_dedup_strict(sorted: Seq<RegexId>, result: Seq<RegexId>)
        requires result == dedup_spec(sorted),
            forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i]@ <= sorted[j]@,
        ensures model::strictly_increasing(model::regex_ids(result)),
    {
        let key: spec_fn(RegexId) -> nat = |id: RegexId| id@;
        lemma_dedup_strict::<RegexId>(sorted, key);
        regex_ids_shape(result);
        assert forall|i: int, j: int| 0 <= i < j < result.len() implies model::regex_ids(result)[i] < model::regex_ids(result)[j] by {
            assert(key(dedup_spec(sorted)[i]) < key(dedup_spec(sorted)[j]));
        }
    }

    pub proof fn regex_combo_ids(g: model::Graph, ids: Seq<RegexId>, sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>, intersect: bool)
        ensures regex_combo_nats(g, sym, theta, model::regex_ids(ids), word, intersect)
            == regex_combo(g, sym, theta, ids, word, intersect),
    {
        regex_ids_shape(ids);
        if intersect {
            if regex_combo_nats(g, sym, theta, model::regex_ids(ids), word, true) {
                assert forall|i: int| 0 <= i < ids.len() implies model::regex_lang(g, sym, theta, ids[i]@, word) by {
                    assert(model::regex_lang(g, sym, theta, model::regex_ids(ids)[i], word));
                }
            }
            if regex_combo(g, sym, theta, ids, word, true) {
                assert forall|i: int| 0 <= i < model::regex_ids(ids).len() implies model::regex_lang(g, sym, theta, model::regex_ids(ids)[i], word) by {
                    assert(model::regex_lang(g, sym, theta, ids[i]@, word));
                }
            }
        } else {
            if regex_combo_nats(g, sym, theta, model::regex_ids(ids), word, false) {
                let i = choose|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, model::regex_ids(ids)[i], word);
                assert(model::regex_lang(g, sym, theta, ids[i]@, word));
            }
            if regex_combo(g, sym, theta, ids, word, false) {
                let i = choose|i: int| 0 <= i < ids.len() && model::regex_lang(g, sym, theta, ids[i]@, word);
                assert(model::regex_lang(g, sym, theta, model::regex_ids(ids)[i], word));
            }
        }
    }


    pub proof fn test_lemma_not_constant_rows(g: model::Graph)
        requires model::graph_wf(g),
        ensures g.constants.test_true < g.tests.len(), g.constants.test_false < g.tests.len(),
            g.tests[g.constants.test_true as int] == model::TestNode::True,
            g.tests[g.constants.test_false as int] == model::TestNode::False,
    {
        model::lemma_graph_wf_elim(g);
    }

    pub proof fn test_lemma_not_leaf_effect(g: model::Graph, id: TestId,
        tasks: Seq<(TestId, bool)>, prior: Seq<TestId>, values: Seq<TestId>, finish: bool)
        requires id@ < g.tests.len(), values.len() == prior.len() + 1,
            values.drop_last() == prior, values.last()@ < g.tests.len(),
            match g.tests[id@ as int] {
                model::TestNode::True => g.tests[values.last()@ as int] == model::TestNode::False,
                model::TestNode::False => g.tests[values.last()@ as int] == model::TestNode::True,
                model::TestNode::Atom(p, positive) => g.tests[values.last()@ as int] == model::TestNode::Atom(p, !positive),
                _ => false,
            },
        ensures test_not_effect(g, id, finish, tasks, prior, tasks, values),
    {
        reveal(test_negation_row);
        match g.tests[id@ as int] {
            model::TestNode::True => {},
            model::TestNode::False => {},
            model::TestNode::Atom(_, _) => {},
            _ => {},
        }
    }

    pub proof fn test_lemma_not_finish_effect(g: model::Graph, id: TestId,
        tasks: Seq<(TestId, bool)>, prior: Seq<TestId>, values: Seq<TestId>, count: nat, and: bool)
        requires id@ < g.tests.len(), count <= prior.len(),
            g.tests[id@ as int] == if and { model::TestNode::Or(test_children(g, id)) }
                else { model::TestNode::And(test_children(g, id)) },
            test_children(g, id).len() == count,
            values.len() == prior.len() - count + 1,
            values.drop_last() == prior.subrange(0, prior.len() as int - count),
            exists|sorted: Seq<TestId>| sorted.to_multiset()
                == prior.subrange(prior.len() as int - count, prior.len() as int).to_multiset()
                && g.tests[values.last()@ as int] == if and { model::TestNode::And(model::test_ids(sorted)) }
                    else { model::TestNode::Or(model::test_ids(sorted)) },
        ensures test_not_effect(g, id, true, tasks, prior, tasks, values),
    {
        if and {} else {}
    }

    pub proof fn test_lemma_not_step_post(before: model::Graph, after: model::Graph, id: TestId, finish: bool,
        pending: Seq<(TestId, bool)>, prior: Seq<TestId>, tasks: Seq<(TestId, bool)>, values: Seq<TestId>)
        requires model::graph_extends(before, after), model::graph_wf(after), id@ < before.tests.len(),
            forall|i: int| 0 <= i < pending.len() ==> #[trigger] pending[i].0@ < before.tests.len(),
            test_ids_valid(after, values), test_not_effect(after, id, finish, pending, prior, tasks, values),
        ensures test_not_work(after, tasks) < test_not_work(before, pending.push((id, finish))),
            forall|root: TestId| test_not_state(before, pending.push((id, finish)), prior, root)
                ==> test_not_state(after, tasks, values, root),
    {
        assert forall|i: int| 0 <= i < pending.push((id, finish)).len()
            implies pending.push((id, finish))[i].0@ < before.tests.len() by {
            if i < pending.len() { assert(pending.push((id, finish))[i] == pending[i]); }
        }
        test_lemma_not_work_extends(before, after, pending.push((id, finish)));
        test_lemma_not_effect_work(after, id, finish, pending, prior, tasks, values);
        assert forall|root: TestId| test_not_state(before, pending.push((id, finish)), prior, root)
            implies test_not_state(after, tasks, values, root) by {
            test_lemma_not_state_extends(before, after, pending.push((id, finish)), prior, root);
            test_lemma_not_effect_state(after, id, finish, pending, prior, tasks, values, root);
        }
    }


    // Guarded transition continuation semantics.
    #[verifier::reject_recursive_types(C)]
    pub struct GuardedTransition<L, C> {
        pub guard: spec_fn(C, Data) -> bool,
        pub term: language::Transition<L>,
    }

    pub open spec fn guarded_semantics<L, C>(
        sem: spec_fn(C, L, Data) -> bool, ctx: C,
    ) -> spec_fn(L, Data) -> bool {
        |leaf: L, event: Data| sem(ctx, leaf, event)
    }

    pub open spec fn guarded_language<L, C>(
        sem: spec_fn(C, L, Data) -> bool, ctx: C, event: Data,
        value: GuardedTransition<L, C>, word: Seq<Data>,
    ) -> bool {
        let context_sem = guarded_semantics(sem, ctx);
        language::lang(context_sem, language::interp_transition(context_sem, event, value.term), word)
    }

    pub open spec fn guarded_refines<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: GuardedTransition<L, C>, after: GuardedTransition<L, C>,
    ) -> bool {
        forall|ctx: C, event: Data| valid(ctx) && #[trigger] (before.guard)(ctx, event)
            ==> (after.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, before, word)
                    == guarded_language(sem, ctx, event, after, word)
    }

    pub open spec fn guarded_stack_refines<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>,
    ) -> bool {
        before.len() == after.len() && forall|i: int| 0 <= i < before.len()
            ==> guarded_refines(sem, valid, before[i], after[i])
    }

    pub open spec fn guarded_constant<L, C>(term: language::Transition<L>) -> GuardedTransition<L, C> {
        GuardedTransition { guard: |ctx: C, event: Data| true, term }
    }

    pub open spec fn guarded_clean<L, C>(
        sem: spec_fn(C, L, Data) -> bool, path: L, term: language::Transition<L>,
    ) -> GuardedTransition<L, C> {
        GuardedTransition { guard: |ctx: C, event: Data| sem(ctx, path, event), term }
    }

    pub open spec fn guarded_not<L, C>(value: GuardedTransition<L, C>) -> GuardedTransition<L, C> {
        GuardedTransition { guard: value.guard, term: language::Transition::Not(Box::new(value.term)) }
    }

    pub open spec fn guarded_append<L, C>(
        value: GuardedTransition<L, C>, suffix: language::Regex<L>,
    ) -> GuardedTransition<L, C> {
        GuardedTransition {
            guard: value.guard,
            term: language::Transition::Append(Box::new(value.term), seq![suffix]),
        }
    }

    pub open spec fn guarded_set<L, C>(
        values: Seq<GuardedTransition<L, C>>, intersect: bool,
    ) -> GuardedTransition<L, C> {
        GuardedTransition {
            guard: |ctx: C, event: Data| forall|i: int| 0 <= i < values.len() ==> #[trigger] (values[i].guard)(ctx, event),
            term: if intersect {
                language::Transition::Intersect(values.map(|i: int, v: GuardedTransition<L, C>| v.term))
            } else {
                language::Transition::Union(values.map(|i: int, v: GuardedTransition<L, C>| v.term))
            },
        }
    }

    pub open spec fn guarded_if<L, C>(
        sem: spec_fn(C, L, Data) -> bool, test: L,
        yes: GuardedTransition<L, C>, no: GuardedTransition<L, C>,
    ) -> GuardedTransition<L, C> {
        GuardedTransition {
            guard: |ctx: C, event: Data| if sem(ctx, test, event) {
                (yes.guard)(ctx, event)
            } else { (no.guard)(ctx, event) },
            term: language::Transition::If(test, Box::new(yes.term), Box::new(no.term)),
        }
    }

    pub open spec fn guarded_clean_if<L, C>(
        sem: spec_fn(C, L, Data) -> bool, test: L, path: L,
        yes: GuardedTransition<L, C>, no: GuardedTransition<L, C>,
    ) -> GuardedTransition<L, C> {
        let value = guarded_if(sem, test, yes, no);
        GuardedTransition {
            guard: |ctx: C, event: Data| sem(ctx, path, event) && (value.guard)(ctx, event),
            term: value.term,
        }
    }

    pub proof fn guarded_lemma_refines_refl<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        value: GuardedTransition<L, C>,
    )
        ensures guarded_refines(sem, valid, value, value),
    {}

    pub proof fn guarded_lemma_refines_transitive<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        a: GuardedTransition<L, C>, b: GuardedTransition<L, C>, c: GuardedTransition<L, C>,
    )
        requires guarded_refines(sem, valid, a, b), guarded_refines(sem, valid, b, c),
        ensures guarded_refines(sem, valid, a, c),
    {}

    pub proof fn guarded_lemma_stack_transitive<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        a: Seq<GuardedTransition<L, C>>, b: Seq<GuardedTransition<L, C>>, c: Seq<GuardedTransition<L, C>>,
    )
        requires guarded_stack_refines(sem, valid, a, b), guarded_stack_refines(sem, valid, b, c),
        ensures guarded_stack_refines(sem, valid, a, c),
    {
        assert forall|i: int| 0 <= i < a.len() implies guarded_refines(sem, valid, a[i], c[i]) by {
            guarded_lemma_refines_transitive(sem, valid, a[i], b[i], c[i]);
        }
    }

    pub proof fn guarded_lemma_not_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: GuardedTransition<L, C>, after: GuardedTransition<L, C>,
    )
        requires guarded_refines(sem, valid, before, after),
        ensures guarded_refines(sem, valid, guarded_not(before), guarded_not(after)),
    {
        assert forall|ctx: C, event: Data| valid(ctx) && #[trigger] (guarded_not(before).guard)(ctx, event)
            implies (guarded_not(after).guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_not(before), word)
                    == guarded_language(sem, ctx, event, guarded_not(after), word) by {
            assert((before.guard)(ctx, event));
            assert((after.guard)(ctx, event));
            assert forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_not(before), word)
                    == guarded_language(sem, ctx, event, guarded_not(after), word) by {
                assert(guarded_language(sem, ctx, event, before, word)
                    == guarded_language(sem, ctx, event, after, word));
                language::lemma_interp_not(guarded_semantics(sem, ctx), event, before.term);
                language::lemma_interp_not(guarded_semantics(sem, ctx), event, after.term);
            }
        }
    }

    pub proof fn guarded_lemma_if_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, test: L,
        a0: GuardedTransition<L, C>, a1: GuardedTransition<L, C>,
        b0: GuardedTransition<L, C>, b1: GuardedTransition<L, C>,
    )
        requires guarded_refines(sem, valid, a0, a1), guarded_refines(sem, valid, b0, b1),
        ensures guarded_refines(sem, valid, guarded_if(sem, test, a0, b0), guarded_if(sem, test, a1, b1)),
    {
        assert forall|ctx: C, event: Data| valid(ctx) && #[trigger] (guarded_if(sem, test, a0, b0).guard)(ctx, event)
            implies (guarded_if(sem, test, a1, b1).guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_if(sem, test, a0, b0), word)
                    == guarded_language(sem, ctx, event, guarded_if(sem, test, a1, b1), word) by {
            if sem(ctx, test, event) {
                assert((a0.guard)(ctx, event));
                assert((a1.guard)(ctx, event));
            } else {
                assert((b0.guard)(ctx, event));
                assert((b1.guard)(ctx, event));
            }
            assert forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_if(sem, test, a0, b0), word)
                    == guarded_language(sem, ctx, event, guarded_if(sem, test, a1, b1), word) by {
                if sem(ctx, test, event) {
                    assert(guarded_language(sem, ctx, event, a0, word)
                        == guarded_language(sem, ctx, event, a1, word));
                } else {
                    assert(guarded_language(sem, ctx, event, b0, word)
                        == guarded_language(sem, ctx, event, b1, word));
                }
                language::lemma_interp_if(guarded_semantics(sem, ctx), event, test, a0.term, b0.term);
                language::lemma_interp_if(guarded_semantics(sem, ctx), event, test, a1.term, b1.term);
            }
        }
    }

    pub proof fn guarded_lemma_set_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>, intersect: bool,
    )
        requires guarded_stack_refines(sem, valid, before, after),
        ensures guarded_refines(sem, valid, guarded_set(before, intersect), guarded_set(after, intersect)),
    {
        assert forall|ctx: C, event: Data| valid(ctx)
            && #[trigger] (guarded_set(before, intersect).guard)(ctx, event)
            implies (guarded_set(after, intersect).guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_set(before, intersect), word)
                    == guarded_language(sem, ctx, event, guarded_set(after, intersect), word) by {
            assert forall|i: int| 0 <= i < after.len() implies (after[i].guard)(ctx, event) by {
                assert((before[i].guard)(ctx, event));
            }
            let context_sem = guarded_semantics(sem, ctx);
            let left = before.map(|i: int, value: GuardedTransition<L, C>| value.term);
            let right = after.map(|i: int, value: GuardedTransition<L, C>| value.term);
            assert forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_set(before, intersect), word)
                    == guarded_language(sem, ctx, event, guarded_set(after, intersect), word) by {
                assert forall|i: int| 0 <= i < before.len() implies
                    language::lang(context_sem, language::interp_transition(context_sem, event, left[i]), word)
                        == language::lang(context_sem, language::interp_transition(context_sem, event, right[i]), word) by {
                    assert(guarded_refines(sem, valid, before[i], after[i]));
                    assert((before[i].guard)(ctx, event));
                    assert(guarded_language(sem, ctx, event, before[i], word)
                        == guarded_language(sem, ctx, event, after[i], word));
                }
                if intersect {
                    language::lemma_interp_intersect(context_sem, event, left, word);
                    language::lemma_interp_intersect(context_sem, event, right, word);
                } else {
                    language::lemma_interp_union(context_sem, event, left, word);
                    language::lemma_interp_union(context_sem, event, right, word);
                    if exists|i: int| 0 <= i < left.len()
                        && language::lang(context_sem, language::interp_transition(context_sem, event, left[i]), word) {
                        let i = choose|i: int| 0 <= i < left.len()
                            && language::lang(context_sem, language::interp_transition(context_sem, event, left[i]), word);
                        assert(language::lang(context_sem, language::interp_transition(context_sem, event, right[i]), word));
                    }
                    if exists|i: int| 0 <= i < right.len()
                        && language::lang(context_sem, language::interp_transition(context_sem, event, right[i]), word) {
                        let i = choose|i: int| 0 <= i < right.len()
                            && language::lang(context_sem, language::interp_transition(context_sem, event, right[i]), word);
                        assert(language::lang(context_sem, language::interp_transition(context_sem, event, left[i]), word));
                    }
                }
            }
        }
    }

    pub proof fn guarded_lemma_append_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: GuardedTransition<L, C>, after: GuardedTransition<L, C>, suffix: language::Regex<L>,
    )
        requires guarded_refines(sem, valid, before, after),
        ensures guarded_refines(sem, valid, guarded_append(before, suffix), guarded_append(after, suffix)),
    {
        assert forall|ctx: C, event: Data| valid(ctx)
            && #[trigger] (guarded_append(before, suffix).guard)(ctx, event)
            implies (guarded_append(after, suffix).guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_append(before, suffix), word)
                    == guarded_language(sem, ctx, event, guarded_append(after, suffix), word) by {
            assert((before.guard)(ctx, event));
            assert((after.guard)(ctx, event));
            let context_sem = guarded_semantics(sem, ctx);
            let left = seq![language::interp_transition(context_sem, event, before.term), suffix];
            let right = seq![language::interp_transition(context_sem, event, after.term), suffix];
            assert forall|i: int, word: Seq<Data>| 0 <= i < left.len() implies
                language::lang(context_sem, left[i], word) == language::lang(context_sem, right[i], word) by {
                if i == 0 {
                    assert(guarded_language(sem, ctx, event, before, word)
                        == guarded_language(sem, ctx, event, after, word));
                } else { assert(i == 1); }
            }
            regex_concat_congruent(context_sem, left, right);
            language::lemma_interp_append(context_sem, event, before.term, seq![suffix]);
            language::lemma_interp_append(context_sem, event, after.term, seq![suffix]);
            assert(seq![language::interp_transition(context_sem, event, before.term)] + seq![suffix] =~= left);
            assert(seq![language::interp_transition(context_sem, event, after.term)] + seq![suffix] =~= right);
        }
    }

    pub enum GuardedAction<L> {
        Clean(language::Transition<L>, L),
        Not(language::Transition<L>),
        Append(language::Transition<L>, language::Regex<L>),
        Pair(language::Transition<L>, language::Transition<L>),
        Union(nat),
        Intersect(nat),
        If(L),
        CleanIf(L, L),
        Fold(Seq<language::Transition<L>>, nat),
        NotResult,
        AppendResult(language::Regex<L>),
        SwapThen,
    }

    pub open spec fn guarded_apply<L, C>(
        sem: spec_fn(C, L, Data) -> bool, action: GuardedAction<L>,
        values: Seq<GuardedTransition<L, C>>,
    ) -> Option<Seq<GuardedTransition<L, C>>> {
        match action {
            GuardedAction::Clean(term, path) => Some(values.push(guarded_clean(sem, path, term))),
            GuardedAction::Not(term) => Some(values.push(guarded_constant(language::Transition::Not(Box::new(term))))),
            GuardedAction::Append(term, suffix) => Some(values.push(guarded_constant(
                language::Transition::Append(Box::new(term), seq![suffix])))),
            GuardedAction::Pair(left, right) => Some(values.push(guarded_constant(
                language::Transition::Intersect(seq![left, right])))),
            GuardedAction::Union(count) => if count <= values.len() {
                let start = values.len() as int - count as int;
                Some(values.take(start).push(guarded_set(values.subrange(start, values.len() as int), false)))
            } else { None },
            GuardedAction::Intersect(count) => if count <= values.len() {
                let start = values.len() as int - count as int;
                Some(values.take(start).push(guarded_set(values.subrange(start, values.len() as int), true)))
            } else { None },
            GuardedAction::If(test) => if values.len() >= 2 {
                Some(values.take(values.len() as int - 2).push(guarded_if(sem, test,
                    values[values.len() as int - 2], values.last())))
            } else { None },
            GuardedAction::CleanIf(test, path) => if values.len() >= 2 {
                Some(values.take(values.len() as int - 2).push(guarded_clean_if(sem, test, path,
                    values[values.len() as int - 2], values.last())))
            } else { None },
            GuardedAction::Fold(terms, index) => if index == 0 {
                Some(values.push(guarded_constant(language::Transition::Intersect(terms))))
            } else if index < terms.len() {
                if values.len() > 0 {
                    let remaining = terms.subrange(index as int, terms.len() as int)
                        .map(|i: int, term: language::Transition<L>| guarded_constant(term));
                    Some(values.drop_last().push(guarded_set(seq![values.last()] + remaining, true)))
                } else { None }
            } else { Some(values) },
            GuardedAction::NotResult => if values.len() > 0 {
                Some(values.drop_last().push(guarded_not(values.last())))
            } else { None },
            GuardedAction::AppendResult(suffix) => if values.len() > 0 {
                Some(values.drop_last().push(guarded_append(values.last(), suffix)))
            } else { None },
            GuardedAction::SwapThen => if values.len() >= 2 {
                Some(values.take(values.len() as int - 2).push(values.last()).push(values[values.len() as int - 2]))
            } else { None },
        }
    }

    pub open spec fn guarded_run<L, C>(
        sem: spec_fn(C, L, Data) -> bool, tasks: Seq<GuardedAction<L>>,
        values: Seq<GuardedTransition<L, C>>,
    ) -> Option<Seq<GuardedTransition<L, C>>>
        decreases tasks.len(),
    {
        if tasks.len() == 0 { Some(values) }
        else {
            match guarded_apply(sem, tasks.last(), values) {
                Some(next) => guarded_run(sem, tasks.drop_last(), next),
                None => None,
            }
        }
    }

    pub open spec fn guarded_program_refines<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: Option<Seq<GuardedTransition<L, C>>>, after: Option<Seq<GuardedTransition<L, C>>>,
    ) -> bool {
        match before {
            None => true,
            Some(left) => match after {
                Some(right) => guarded_stack_refines(sem, valid, left, right),
                None => false,
            },
        }
    }

    pub proof fn guarded_lemma_program_transitive<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        a: Option<Seq<GuardedTransition<L, C>>>, b: Option<Seq<GuardedTransition<L, C>>>,
        c: Option<Seq<GuardedTransition<L, C>>>,
    )
        requires guarded_program_refines(sem, valid, a, b), guarded_program_refines(sem, valid, b, c),
        ensures guarded_program_refines(sem, valid, a, c),
    {
        match a {
            None => {},
            Some(left) => match (b, c) {
                (Some(middle), Some(right)) => guarded_lemma_stack_transitive(sem, valid, left, middle, right),
                _ => {},
            },
        }
    }

    pub proof fn guarded_lemma_stack_slice<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>, start: int, end: int,
    )
        requires guarded_stack_refines(sem, valid, before, after), 0 <= start <= end <= before.len(),
        ensures guarded_stack_refines(sem, valid, before.subrange(start, end), after.subrange(start, end)),
    {
        assert forall|i: int| 0 <= i < before.subrange(start, end).len() implies
            guarded_refines(sem, valid, before.subrange(start, end)[i], after.subrange(start, end)[i]) by {
            assert(before.subrange(start, end)[i] == before[start + i]);
            assert(after.subrange(start, end)[i] == after[start + i]);
        }
    }

    pub proof fn guarded_lemma_stack_push<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>,
        left: GuardedTransition<L, C>, right: GuardedTransition<L, C>,
    )
        requires guarded_stack_refines(sem, valid, before, after), guarded_refines(sem, valid, left, right),
        ensures guarded_stack_refines(sem, valid, before.push(left), after.push(right)),
    {
        assert forall|i: int| 0 <= i < before.push(left).len() implies
            guarded_refines(sem, valid, before.push(left)[i], after.push(right)[i]) by {
            if i < before.len() {
                assert(before.push(left)[i] == before[i]);
                assert(after.push(right)[i] == after[i]);
            } else { assert(i == before.len()); }
        }
    }

    pub proof fn guarded_lemma_run_prefix<L, C>(
        sem: spec_fn(C, L, Data) -> bool, prefix: Seq<GuardedAction<L>>, suffix: Seq<GuardedAction<L>>,
        values: Seq<GuardedTransition<L, C>>,
    )
        ensures guarded_run(sem, prefix + suffix, values) == match guarded_run(sem, suffix, values) {
            Some(next) => guarded_run(sem, prefix, next),
            None => None,
        },
        decreases suffix.len(),
    {
        if suffix.len() > 0 {
            assert((prefix + suffix).last() == suffix.last());
            assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
            match guarded_apply(sem, suffix.last(), values) {
                Some(next) => guarded_lemma_run_prefix(sem, prefix, suffix.drop_last(), next),
                None => {},
            }
        } else { assert(prefix + suffix =~= prefix); }
    }

    pub proof fn guarded_lemma_clean_if_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, test: L, path: L,
        a0: GuardedTransition<L, C>, a1: GuardedTransition<L, C>,
        b0: GuardedTransition<L, C>, b1: GuardedTransition<L, C>,
    )
        requires guarded_refines(sem, valid, a0, a1), guarded_refines(sem, valid, b0, b1),
        ensures guarded_refines(sem, valid,
            guarded_clean_if(sem, test, path, a0, b0), guarded_clean_if(sem, test, path, a1, b1)),
    {
        guarded_lemma_if_congruent(sem, valid, test, a0, a1, b0, b1);
        assert forall|ctx: C, event: Data| valid(ctx)
            && #[trigger] (guarded_clean_if(sem, test, path, a0, b0).guard)(ctx, event)
            implies (guarded_clean_if(sem, test, path, a1, b1).guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_clean_if(sem, test, path, a0, b0), word)
                    == guarded_language(sem, ctx, event, guarded_clean_if(sem, test, path, a1, b1), word) by {
            assert((guarded_if(sem, test, a0, b0).guard)(ctx, event));
            assert((guarded_if(sem, test, a1, b1).guard)(ctx, event));
            assert forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, guarded_clean_if(sem, test, path, a0, b0), word)
                    == guarded_language(sem, ctx, event, guarded_clean_if(sem, test, path, a1, b1), word) by {
                assert(guarded_language(sem, ctx, event, guarded_if(sem, test, a0, b0), word)
                    == guarded_language(sem, ctx, event, guarded_if(sem, test, a1, b1), word));
            }
        }
    }

    pub proof fn guarded_lemma_stack_refl<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, values: Seq<GuardedTransition<L, C>>,
    )
        ensures guarded_stack_refines(sem, valid, values, values),
    {
        assert forall|i: int| 0 <= i < values.len() implies guarded_refines(sem, valid, values[i], values[i]) by {
            guarded_lemma_refines_refl(sem, valid, values[i]);
        }
    }

    pub proof fn guarded_lemma_stack_concat<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        a0: Seq<GuardedTransition<L, C>>, a1: Seq<GuardedTransition<L, C>>,
        b0: Seq<GuardedTransition<L, C>>, b1: Seq<GuardedTransition<L, C>>,
    )
        requires guarded_stack_refines(sem, valid, a0, a1), guarded_stack_refines(sem, valid, b0, b1),
        ensures guarded_stack_refines(sem, valid, a0 + b0, a1 + b1),
    {
        assert forall|i: int| 0 <= i < (a0 + b0).len() implies
            guarded_refines(sem, valid, (a0 + b0)[i], (a1 + b1)[i]) by {
            if i < a0.len() {
                assert((a0 + b0)[i] == a0[i]);
                assert((a1 + b1)[i] == a1[i]);
            } else {
                assert((a0 + b0)[i] == b0[i - a0.len() as int]);
                assert((a1 + b1)[i] == b1[i - a1.len() as int]);
            }
        }
    }

    pub proof fn guarded_lemma_reduce_set_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>, count: nat, intersect: bool,
    )
        requires guarded_stack_refines(sem, valid, before, after), count <= before.len(),
        ensures guarded_stack_refines(sem, valid,
            before.take(before.len() as int - count as int).push(guarded_set(
                before.subrange(before.len() as int - count as int, before.len() as int), intersect)),
            after.take(after.len() as int - count as int).push(guarded_set(
                after.subrange(after.len() as int - count as int, after.len() as int), intersect))),
    {
        let start = before.len() as int - count as int;
        guarded_lemma_stack_slice(sem, valid, before, after, 0, start);
        guarded_lemma_stack_slice(sem, valid, before, after, start, before.len() as int);
        guarded_lemma_set_congruent(sem, valid,
            before.subrange(start, before.len() as int), after.subrange(start, after.len() as int), intersect);
        guarded_lemma_stack_push(sem, valid, before.take(start), after.take(start),
            guarded_set(before.subrange(start, before.len() as int), intersect),
            guarded_set(after.subrange(start, after.len() as int), intersect));
    }

    pub proof fn guarded_lemma_apply_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, action: GuardedAction<L>,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>,
    )
        requires guarded_stack_refines(sem, valid, before, after),
        ensures guarded_program_refines(sem, valid,
            guarded_apply(sem, action, before), guarded_apply(sem, action, after)),
    {
        match action {
            GuardedAction::Clean(term, path) => {
                let value = guarded_clean(sem, path, term);
                guarded_lemma_refines_refl(sem, valid, value);
                guarded_lemma_stack_push(sem, valid, before, after, value, value);
            },
            GuardedAction::Not(term) => {
                let value = guarded_constant(language::Transition::Not(Box::new(term)));
                guarded_lemma_refines_refl(sem, valid, value);
                guarded_lemma_stack_push(sem, valid, before, after, value, value);
            },
            GuardedAction::Append(term, suffix) => {
                let value = guarded_constant(language::Transition::Append(Box::new(term), seq![suffix]));
                guarded_lemma_refines_refl(sem, valid, value);
                guarded_lemma_stack_push(sem, valid, before, after, value, value);
            },
            GuardedAction::Pair(left, right) => {
                let value = guarded_constant(language::Transition::Intersect(seq![left, right]));
                guarded_lemma_refines_refl(sem, valid, value);
                guarded_lemma_stack_push(sem, valid, before, after, value, value);
            },
            GuardedAction::Union(count) => {
                if count <= before.len() { guarded_lemma_reduce_set_congruent(sem, valid, before, after, count, false); }
            },
            GuardedAction::Intersect(count) => {
                if count <= before.len() { guarded_lemma_reduce_set_congruent(sem, valid, before, after, count, true); }
            },
            GuardedAction::If(test) => {
                if before.len() >= 2 {
                    let start = before.len() as int - 2;
                    guarded_lemma_stack_slice(sem, valid, before, after, 0, start);
                    guarded_lemma_if_congruent(sem, valid, test,
                        before[start], after[start], before.last(), after.last());
                    guarded_lemma_stack_push(sem, valid, before.take(start), after.take(start),
                        guarded_if(sem, test, before[start], before.last()),
                        guarded_if(sem, test, after[start], after.last()));
                }
            },
            GuardedAction::CleanIf(test, path) => {
                if before.len() >= 2 {
                    let start = before.len() as int - 2;
                    guarded_lemma_stack_slice(sem, valid, before, after, 0, start);
                    guarded_lemma_clean_if_congruent(sem, valid, test, path,
                        before[start], after[start], before.last(), after.last());
                    guarded_lemma_stack_push(sem, valid, before.take(start), after.take(start),
                        guarded_clean_if(sem, test, path, before[start], before.last()),
                        guarded_clean_if(sem, test, path, after[start], after.last()));
                }
            },
            GuardedAction::Fold(terms, index) => {
                if index == 0 {
                    let value = guarded_constant(language::Transition::Intersect(terms));
                    guarded_lemma_refines_refl(sem, valid, value);
                    guarded_lemma_stack_push(sem, valid, before, after, value, value);
                } else if index < terms.len() && before.len() > 0 {
                    let start = before.len() as int - 1;
                    guarded_lemma_stack_slice(sem, valid, before, after, 0, start);
                    let remaining: Seq<GuardedTransition<L, C>> = terms.subrange(index as int, terms.len() as int)
                        .map(|i: int, term: language::Transition<L>| guarded_constant(term));
                    guarded_lemma_stack_refl(sem, valid, remaining);
                    guarded_lemma_stack_push(sem, valid, Seq::empty(), Seq::empty(), before.last(), after.last());
                    guarded_lemma_stack_concat(sem, valid, seq![before.last()], seq![after.last()], remaining, remaining);
                    guarded_lemma_set_congruent(sem, valid, seq![before.last()] + remaining, seq![after.last()] + remaining, true);
                    guarded_lemma_stack_push(sem, valid, before.drop_last(), after.drop_last(),
                        guarded_set(seq![before.last()] + remaining, true),
                        guarded_set(seq![after.last()] + remaining, true));
                }
            },
            GuardedAction::NotResult => {
                if before.len() > 0 {
                    guarded_lemma_stack_slice(sem, valid, before, after, 0, before.len() as int - 1);
                    guarded_lemma_not_congruent(sem, valid, before.last(), after.last());
                    guarded_lemma_stack_push(sem, valid, before.drop_last(), after.drop_last(),
                        guarded_not(before.last()), guarded_not(after.last()));
                }
            },
            GuardedAction::AppendResult(suffix) => {
                if before.len() > 0 {
                    guarded_lemma_stack_slice(sem, valid, before, after, 0, before.len() as int - 1);
                    guarded_lemma_append_congruent(sem, valid, before.last(), after.last(), suffix);
                    guarded_lemma_stack_push(sem, valid, before.drop_last(), after.drop_last(),
                        guarded_append(before.last(), suffix), guarded_append(after.last(), suffix));
                }
            },
            GuardedAction::SwapThen => {
                if before.len() >= 2 {
                    let start = before.len() as int - 2;
                    guarded_lemma_stack_slice(sem, valid, before, after, 0, start);
                    guarded_lemma_stack_push(sem, valid, before.take(start), after.take(start), before.last(), after.last());
                    guarded_lemma_stack_push(sem, valid, before.take(start).push(before.last()),
                        after.take(start).push(after.last()), before[start], after[start]);
                }
            },
        }
    }

    pub proof fn guarded_lemma_run_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, tasks: Seq<GuardedAction<L>>,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>,
    )
        requires guarded_stack_refines(sem, valid, before, after),
        ensures guarded_program_refines(sem, valid, guarded_run(sem, tasks, before), guarded_run(sem, tasks, after)),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            guarded_lemma_apply_congruent(sem, valid, tasks.last(), before, after);
            match (guarded_apply(sem, tasks.last(), before), guarded_apply(sem, tasks.last(), after)) {
                (Some(left), Some(right)) => guarded_lemma_run_congruent(sem, valid, tasks.drop_last(), left, right),
                _ => {},
            }
        }
    }

    // Native transition work-stack representation.
    pub struct TransitionContext {
        pub symbols: model::Symbols,
        pub bindings: Seq<Data>,
    }

    pub type TransitionMeaning = GuardedTransition<model::Test, TransitionContext>;
    pub type TransitionAction = GuardedAction<model::Test>;

    pub open spec fn transition_context_sem() -> spec_fn(TransitionContext, model::Test, Data) -> bool {
        |ctx: TransitionContext, test: model::Test, event: Data|
            model::test_holds(ctx.symbols, ctx.bindings, test, event)
    }

    pub open spec fn transition_context_valid() -> spec_fn(TransitionContext) -> bool {
        |ctx: TransitionContext| model::symbols_wf(ctx.symbols)
    }

    pub enum ActionShape {
        Clean(nat, nat), Not(nat), Append(nat, nat), Pair(nat, nat),
        Union(nat), Intersect(nat), If(nat), CleanIf(nat, nat),
        Fold(Seq<nat>, nat), NotResult, AppendResult(nat), SwapThen,
    }

    pub enum ChildShape { Clean(nat), Not, Append(nat), PairLeft(nat), PairRight(nat) }

    impl View for Action {
        type V = ActionShape;
        open(super) spec fn view(&self) -> ActionShape {
            match self {
                Action::Clean(id, path) => ActionShape::Clean(id@, path@),
                Action::Not(id) => ActionShape::Not(id@),
                Action::Append(id, suffix) => ActionShape::Append(id@, suffix@),
                Action::Pair(a, b) => ActionShape::Pair(a@, b@),
                Action::Union(count) => ActionShape::Union(*count as nat),
                Action::Intersect(count) => ActionShape::Intersect(*count as nat),
                Action::If(test) => ActionShape::If(test@),
                Action::CleanIf(test, path) => ActionShape::CleanIf(test@, path@),
                Action::Fold(ids, index) => ActionShape::Fold(model::transition_ids(ids.view()), *index as nat),
                Action::NotResult => ActionShape::NotResult,
                Action::AppendResult(suffix) => ActionShape::AppendResult(suffix@),
                Action::SwapThen => ActionShape::SwapThen,
            }
        }
    }

    impl View for ChildAction {
        type V = ChildShape;
        open(super) spec fn view(&self) -> ChildShape {
            match self {
                ChildAction::Clean(path) => ChildShape::Clean(path@),
                ChildAction::Not => ChildShape::Not,
                ChildAction::Append(suffix) => ChildShape::Append(suffix@),
                ChildAction::PairLeft(other) => ChildShape::PairLeft(other@),
                ChildAction::PairRight(other) => ChildShape::PairRight(other@),
            }
        }
    }

    pub open spec fn transition_action_views<T: View<V = ActionShape>>(tasks: Seq<T>) -> Seq<ActionShape> {
        tasks.map(|i: int, task: T| task@)
    }

    pub open spec fn transition_action_valid(g: model::Graph, task: ActionShape) -> bool {
        match task {
            ActionShape::Clean(id, path) => id < g.transitions.len() && path < g.tests.len(),
            ActionShape::Not(id) => id < g.transitions.len(),
            ActionShape::Append(id, suffix) => id < g.transitions.len() && suffix < g.regexes.len(),
            ActionShape::Pair(a, b) => a < g.transitions.len() && b < g.transitions.len(),
            ActionShape::If(test) => test < g.tests.len(),
            ActionShape::CleanIf(test, path) => test < g.tests.len() && path < g.tests.len(),
            ActionShape::Fold(ids, index) => model::bounded(ids, g.transitions.len()),
            ActionShape::AppendResult(suffix) => suffix < g.regexes.len(),
            _ => true,
        }
    }

    pub open spec fn transition_tasks_valid(g: model::Graph, tasks: Seq<ActionShape>) -> bool {
        forall|i: int| 0 <= i < tasks.len() ==> transition_action_valid(g, tasks[i])
    }

    pub open spec fn transition_freeze_action(g: model::Graph, task: ActionShape) -> TransitionAction {
        match task {
            ActionShape::Clean(id, path) => GuardedAction::Clean(model::lift_transition(g, id), model::lift_test(g, path)),
            ActionShape::Not(id) => GuardedAction::Not(model::lift_transition(g, id)),
            ActionShape::Append(id, suffix) => GuardedAction::Append(model::lift_transition(g, id), model::lift_regex(g, suffix)),
            ActionShape::Pair(a, b) => GuardedAction::Pair(model::lift_transition(g, a), model::lift_transition(g, b)),
            ActionShape::Union(count) => GuardedAction::Union(count),
            ActionShape::Intersect(count) => GuardedAction::Intersect(count),
            ActionShape::If(test) => GuardedAction::If(model::lift_test(g, test)),
            ActionShape::CleanIf(test, path) => GuardedAction::CleanIf(model::lift_test(g, test), model::lift_test(g, path)),
            ActionShape::Fold(ids, index) => GuardedAction::Fold(ids.map(|i: int, id: nat| model::lift_transition(g, id)), index),
            ActionShape::NotResult => GuardedAction::NotResult,
            ActionShape::AppendResult(suffix) => GuardedAction::AppendResult(model::lift_regex(g, suffix)),
            ActionShape::SwapThen => GuardedAction::SwapThen,
        }
    }

    pub open spec fn transition_freeze_tasks(g: model::Graph, tasks: Seq<ActionShape>) -> Seq<TransitionAction> {
        tasks.map(|i: int, task: ActionShape| transition_freeze_action(g, task))
    }

    pub open spec fn transition_known(g: model::Graph, id: TransitionId) -> TransitionMeaning {
        guarded_constant(model::lift_transition(g, id@))
    }

    pub open spec fn transition_known_values(g: model::Graph, values: Seq<TransitionId>) -> Seq<TransitionMeaning> {
        values.map(|i: int, id: TransitionId| transition_known(g, id))
    }

    pub open spec fn transition_program(
        g: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>,
    ) -> Option<Seq<TransitionMeaning>> {
        guarded_run(transition_context_sem(), transition_freeze_tasks(g, tasks), transition_known_values(g, values))
    }

    pub open spec fn transition_program_refines(
        before: Option<Seq<TransitionMeaning>>, after: Option<Seq<TransitionMeaning>>,
    ) -> bool {
        guarded_program_refines(transition_context_sem(), transition_context_valid(), before, after)
    }

    pub open spec fn transition_if_combo(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, test: TestId,
        yes: TransitionId, no: TransitionId, event: Data, word: Seq<Data>,
    ) -> bool {
        if model::test_holds(sym, theta, model::lift_test(g, test@), event) {
            transition_lang(g, sym, theta, yes, event, word)
        } else { transition_lang(g, sym, theta, no, event, word) }
    }

    #[verifier::opaque]
    pub open spec fn transition_children(g: model::Graph, id: nat) -> Seq<nat> {
        match g.transitions[id as int] {
            model::TransitionNode::Union(ids) => ids,
            model::TransitionNode::Intersect(ids) => ids,
            _ => Seq::empty(),
        }
    }

    pub open spec fn transition_child_count(g: model::Graph, id: nat, count: nat) -> bool {
        id < g.transitions.len() && match g.transitions[id as int] {
            model::TransitionNode::Union(ids) => ids.len() == count,
            model::TransitionNode::Intersect(ids) => ids.len() == count,
            _ => false,
        }
    }

    pub proof fn transition_lemma_context_sem(ctx: TransitionContext)
        ensures guarded_semantics(transition_context_sem(), ctx) == model::gsem(ctx.symbols, ctx.bindings),
    {
        assert(guarded_semantics(transition_context_sem(), ctx) =~= model::gsem(ctx.symbols, ctx.bindings));
    }

    pub proof fn transition_lemma_known_language(
        g: model::Graph, id: TransitionId, ctx: TransitionContext, event: Data, word: Seq<Data>,
    )
        ensures guarded_language(transition_context_sem(), ctx, event, transition_known(g, id), word)
            == transition_lang(g, ctx.symbols, ctx.bindings, id, event, word),
    {
        transition_lemma_context_sem(ctx);
    }

    pub proof fn transition_lemma_action_stable(before: model::Graph, after: model::Graph, task: ActionShape)
        requires model::graph_wf(before), model::graph_extends(before, after), transition_action_valid(before, task),
        ensures transition_action_valid(after, task),
            transition_freeze_action(before, task) == transition_freeze_action(after, task),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_stable_under_extends(before, after);
        match task {
            ActionShape::Fold(ids, index) => {
                assert(ids.map(|i: int, id: nat| model::lift_transition(before, id))
                    =~= ids.map(|i: int, id: nat| model::lift_transition(after, id)));
            },
            _ => {},
        }
    }

    pub proof fn transition_lemma_program_stable(
        before: model::Graph, after: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>,
    )
        requires model::graph_wf(before), model::graph_extends(before, after),
            transition_tasks_valid(before, tasks), transition_ids_valid(before, values),
        ensures transition_tasks_valid(after, tasks), transition_ids_valid(after, values),
            transition_program(before, tasks, values) == transition_program(after, tasks, values),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_stable_under_extends(before, after);
        assert forall|i: int| 0 <= i < tasks.len() implies
            transition_action_valid(after, tasks[i])
                && transition_freeze_action(before, tasks[i]) == transition_freeze_action(after, tasks[i]) by {
            transition_lemma_action_stable(before, after, tasks[i]);
        }
        assert(transition_freeze_tasks(before, tasks) =~= transition_freeze_tasks(after, tasks));
        assert(transition_known_values(before, values) =~= transition_known_values(after, values));
    }

    pub struct TransitionModeModel {
        pub intersect: bool,
        pub identity: TransitionId,
        pub absorber: TransitionId,
    }

    impl View for TransitionMode {
        type V = TransitionModeModel;
        open(super) spec fn view(&self) -> TransitionModeModel {
            TransitionModeModel { intersect: self.intersect, identity: self.identity, absorber: self.absorber }
        }
    }

    pub open spec fn transition_mode_valid(g: model::Graph, mode: TransitionModeModel) -> bool {
        mode.identity@ == (if mode.intersect { g.constants.transition_all } else { g.constants.transition_empty })
        && mode.absorber@ == (if mode.intersect { g.constants.transition_empty } else { g.constants.transition_all })
    }

    pub proof fn transition_unfold(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.transitions.len(),
        ensures match g.transitions[id as int] {
            model::TransitionNode::Const(regex) => model::lift_transition(g, id)
                == language::Transition::Const(model::lift_regex(g, regex)),
            model::TransitionNode::If(test, yes, no) => model::lift_transition(g, id)
                == language::Transition::If(model::lift_test(g, test),
                    Box::new(model::lift_transition(g, yes)), Box::new(model::lift_transition(g, no))),
            model::TransitionNode::Union(ids) => model::lift_transition(g, id)
                == language::Transition::Union(ids.map(|i: int, child: nat| model::lift_transition(g, child))),
            model::TransitionNode::Intersect(ids) => model::lift_transition(g, id)
                == language::Transition::Intersect(ids.map(|i: int, child: nat| model::lift_transition(g, child))),
            model::TransitionNode::Not(inner) => model::lift_transition(g, id)
                == language::Transition::Not(Box::new(model::lift_transition(g, inner))),
            model::TransitionNode::Append(inner, suffix) => model::lift_transition(g, id)
                == language::Transition::Append(Box::new(model::lift_transition(g, inner)), model::lift_regexes(g, suffix)),
        },
    {
        model::lemma_graph_transition_wf(g, id);
        match g.transitions[id as int] {
            model::TransitionNode::Union(ids) => {
                assert(model::lift_transitions(g, ids, id)
                    =~= ids.map(|i: int, child: nat| model::lift_transition(g, child)));
            },
            model::TransitionNode::Intersect(ids) => {
                assert(model::lift_transitions(g, ids, id)
                    =~= ids.map(|i: int, child: nat| model::lift_transition(g, child)));
            },
            _ => {},
        }
    }

    pub open spec fn transition_unbounded_node(g: model::Graph, node: model::TransitionNode) -> language::Transition<model::Test> {
        match node {
            model::TransitionNode::Const(regex) => language::Transition::Const(model::lift_regex(g, regex)),
            model::TransitionNode::If(test, yes, no) => language::Transition::If(model::lift_test(g, test),
                Box::new(model::lift_transition(g, yes)), Box::new(model::lift_transition(g, no))),
            model::TransitionNode::Union(ids) => language::Transition::Union(
                ids.map(|i: int, child: nat| model::lift_transition(g, child))),
            model::TransitionNode::Intersect(ids) => language::Transition::Intersect(
                ids.map(|i: int, child: nat| model::lift_transition(g, child))),
            model::TransitionNode::Not(inner) => language::Transition::Not(Box::new(model::lift_transition(g, inner))),
            model::TransitionNode::Append(inner, suffix) => language::Transition::Append(
                Box::new(model::lift_transition(g, inner)), model::lift_regexes(g, suffix)),
        }
    }



    pub proof fn guarded_lemma_run_result_congruent<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, tasks: Seq<GuardedAction<L>>,
        before: Option<Seq<GuardedTransition<L, C>>>, after: Option<Seq<GuardedTransition<L, C>>>,
    )
        requires guarded_program_refines(sem, valid, before, after),
        ensures guarded_program_refines(sem, valid,
            match before { Some(values) => guarded_run(sem, tasks, values), None => None },
            match after { Some(values) => guarded_run(sem, tasks, values), None => None }),
    {
        match (before, after) {
            (Some(left), Some(right)) => guarded_lemma_run_congruent(sem, valid, tasks, left, right),
            _ => {},
        }
    }

    pub proof fn guarded_lemma_frame_effect<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        prefix: Seq<GuardedAction<L>>, expansion: Seq<GuardedAction<L>>, action: GuardedAction<L>,
        before: Seq<GuardedTransition<L, C>>, after: Seq<GuardedTransition<L, C>>,
    )
        requires guarded_program_refines(sem, valid,
            guarded_apply(sem, action, before), guarded_run(sem, expansion, after)),
        ensures guarded_program_refines(sem, valid,
            guarded_run(sem, prefix.push(action), before), guarded_run(sem, prefix + expansion, after)),
    {
        guarded_lemma_run_prefix(sem, prefix, seq![action], before);
        guarded_lemma_run_prefix(sem, prefix, expansion, after);
        assert(prefix.push(action) =~= prefix + seq![action]);
        guarded_lemma_run_singleton(sem, action, before);
        assert(guarded_run(sem, seq![action], before) == guarded_apply(sem, action, before));
        guarded_lemma_run_result_congruent(sem, valid, prefix,
            guarded_apply(sem, action, before), guarded_run(sem, expansion, after));
    }


    pub open spec fn transition_effect(
        g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
        tasks: Seq<ActionShape>, values: Seq<TransitionId>,
    ) -> bool {
        pending.is_prefix_of(tasks) && guarded_program_refines(transition_context_sem(), transition_context_valid(),
            guarded_apply(transition_context_sem(), transition_freeze_action(g, task), transition_known_values(g, prior)),
            guarded_run(transition_context_sem(), transition_freeze_tasks(g,
                tasks.subrange(pending.len() as int, tasks.len() as int)), transition_known_values(g, values)))
    }

    pub proof fn transition_lemma_effect_frame(
        g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
        tasks: Seq<ActionShape>, values: Seq<TransitionId>,
    )
        requires transition_effect(g, task, pending, prior, tasks, values),
        ensures transition_program_refines(
            transition_program(g, pending.push(task), prior), transition_program(g, tasks, values)),
    {
        let prefix = transition_freeze_tasks(g, pending);
        let expansion = transition_freeze_tasks(g, tasks.subrange(pending.len() as int, tasks.len() as int));
        assert(transition_freeze_tasks(g, pending.push(task)) =~= prefix.push(transition_freeze_action(g, task)));
        assert(transition_freeze_tasks(g, tasks) =~= prefix + expansion);
        guarded_lemma_frame_effect(transition_context_sem(), transition_context_valid(), prefix, expansion,
            transition_freeze_action(g, task), transition_known_values(g, prior), transition_known_values(g, values));
    }

    pub open spec fn transition_initial_value(g: model::Graph, task: ActionShape) -> Option<TransitionMeaning> {
        match guarded_apply(transition_context_sem(), transition_freeze_action(g, task), Seq::empty()) {
            Some(values) => if values.len() == 1 { Some(values[0]) } else { None },
            None => None,
        }
    }

    pub proof fn transition_lemma_children(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.transitions.len(),
        ensures model::bounded(transition_children(g, id), g.transitions.len()),
            match g.transitions[id as int] {
                model::TransitionNode::Union(ids) => transition_children(g, id) == ids,
                model::TransitionNode::Intersect(ids) => transition_children(g, id) == ids,
                _ => transition_children(g, id).len() == 0,
            },
    {
        reveal(transition_children);
        model::lemma_graph_transition_wf(g, id);
        match g.transitions[id as int] {
            model::TransitionNode::Union(ids) => {},
            model::TransitionNode::Intersect(ids) => {},
            _ => {},
        }
    }

    pub proof fn transition_lemma_child(g: model::Graph, id: nat, index: nat, child: nat)
        requires model::graph_wf(g), id < g.transitions.len(),
            model::transition_node_child(g.transitions[id as int], index) == Some(child),
        ensures index < transition_children(g, id).len(), transition_children(g, id)[index as int] == child,
            child < g.transitions.len(),
    {
        transition_lemma_children(g, id);
        reveal(transition_children);
        match g.transitions[id as int] {
            model::TransitionNode::Union(ids) => {},
            model::TransitionNode::Intersect(ids) => {},
            _ => {},
        }
    }

    #[verifier::opaque]
    pub open spec fn transition_suffix(g: model::Graph, id: nat) -> Seq<nat> {
        match g.transitions[id as int] {
            model::TransitionNode::Append(inner, suffix) => suffix,
            _ => Seq::empty(),
        }
    }

    pub open spec fn transition_suffix_count(g: model::Graph, id: nat, count: nat) -> bool {
        id < g.transitions.len() && match g.transitions[id as int] {
            model::TransitionNode::Append(inner, suffix) => suffix.len() == count,
            _ => false,
        }
    }

    pub proof fn transition_lemma_suffix(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.transitions.len(),
        ensures model::bounded(transition_suffix(g, id), g.regexes.len()),
            match g.transitions[id as int] {
                model::TransitionNode::Append(inner, suffix) => transition_suffix(g, id) == suffix,
                _ => transition_suffix(g, id).len() == 0,
            },
    {
        reveal(transition_suffix);
        model::lemma_graph_transition_wf(g, id);
    }

    pub proof fn transition_lemma_suffix_child(g: model::Graph, id: nat, index: nat, child: nat)
        requires model::graph_wf(g), id < g.transitions.len(),
            model::transition_node_suffix(g.transitions[id as int], index) == Some(child),
        ensures index < transition_suffix(g, id).len(), transition_suffix(g, id)[index as int] == child,
            child < g.regexes.len(),
    {
        transition_lemma_suffix(g, id);
        reveal(transition_suffix);
        match g.transitions[id as int] {
            model::TransitionNode::Append(inner, suffix) => {},
            _ => {},
        }
    }

    pub proof fn transition_ids_push(ids: Seq<TransitionId>, id: TransitionId)
        ensures model::transition_ids(ids.push(id)) == model::transition_ids(ids).push(id@),
    {
        assert(model::transition_ids(ids.push(id)) =~= model::transition_ids(ids).push(id@));
    }


    pub proof fn guarded_lemma_run_singleton<L, C>(
        sem: spec_fn(C, L, Data) -> bool, action: GuardedAction<L>, values: Seq<GuardedTransition<L, C>>,
    )
        ensures guarded_run(sem, seq![action], values) == guarded_apply(sem, action, values),
    {
        reveal_with_fuel(guarded_run, 2);
    }


    pub open spec fn transition_collect_work(g: model::Graph, id: nat, intersect: bool) -> nat
        decreases id, 1nat, 0nat,
    {
        if id >= g.transitions.len() { 1 }
        else {
            match g.transitions[id as int] {
                model::TransitionNode::Union(ids) => if !intersect && model::bounded(ids, id) {
                    1 + transition_collect_work_ids(g, ids, id, intersect)
                } else { 1 },
                model::TransitionNode::Intersect(ids) => if intersect && model::bounded(ids, id) {
                    1 + transition_collect_work_ids(g, ids, id, intersect)
                } else { 1 },
                _ => 1,
            }
        }
    }

    pub open spec fn transition_collect_work_ids(g: model::Graph, ids: Seq<nat>, bound: nat, intersect: bool) -> nat
        decreases bound, 0nat, ids.len(),
        when model::bounded(ids, bound)
    {
        if ids.len() == 0 { 0 }
        else {
            transition_collect_work_ids(g, ids.drop_last(), bound, intersect)
                + transition_collect_work(g, ids.last(), intersect)
        }
    }

    pub open spec fn transition_pending_work(g: model::Graph, ids: Seq<TransitionId>, intersect: bool) -> nat {
        transition_collect_work_ids(g, model::transition_ids(ids), g.transitions.len(), intersect)
    }

    pub proof fn transition_lemma_work_bounds(g: model::Graph, ids: Seq<nat>, a: nat, b: nat, intersect: bool)
        requires model::bounded(ids, a), model::bounded(ids, b),
        ensures transition_collect_work_ids(g, ids, a, intersect) == transition_collect_work_ids(g, ids, b, intersect),
        decreases ids.len(),
    {
        if ids.len() > 0 { transition_lemma_work_bounds(g, ids.drop_last(), a, b, intersect); }
    }

    pub proof fn transition_lemma_work_concat(g: model::Graph, left: Seq<nat>, right: Seq<nat>, bound: nat, intersect: bool)
        requires model::bounded(left, bound), model::bounded(right, bound),
        ensures transition_collect_work_ids(g, left + right, bound, intersect)
            == transition_collect_work_ids(g, left, bound, intersect) + transition_collect_work_ids(g, right, bound, intersect),
        decreases right.len(),
    {
        assert(model::bounded(left + right, bound));
        if right.len() > 0 {
            assert((left + right).drop_last() =~= left + right.drop_last());
            assert((left + right).last() == right.last());
            transition_lemma_work_concat(g, left, right.drop_last(), bound, intersect);
        } else { assert(left + right =~= left); }
    }

    pub proof fn transition_lemma_work_positive(g: model::Graph, id: nat, intersect: bool)
        ensures transition_collect_work(g, id, intersect) >= 1,
    {}

    // ----- termination cost arithmetic (transition_machine) -----
    pub open spec fn n4(d: nat) -> nat
        decreases d,
    {
        if d == 0 { 1 } else { 4 * n4((d - 1) as nat) }
    }

    pub open spec fn log4_floor(d: nat) -> nat
        decreases d,
    {
        if d < 4 { 0 } else { 1 + log4_floor(d / 4) }
    }

    pub open spec fn set_bound(total: nat, n: nat) -> nat {
        if n == 0 { 2 } else if n == 1 { total } else { (total - 1) as nat }
    }

    pub open spec fn if_bound(a: nat, b: nat) -> nat { 1 + if a >= b { a } else { b } }

    pub open spec fn pair_bound(a: nat, b: nat) -> nat { a * b + a + b }

    pub open spec fn sum_plus1(ds: Seq<nat>) -> nat
        decreases ds.len(),
    {
        if ds.len() == 0 { 0 } else { sum_plus1(ds.drop_last()) + ds.last() + 1 }
    }

    pub open spec fn prod_plus1(ds: Seq<nat>) -> nat
        decreases ds.len(),
    {
        if ds.len() == 0 { 1 } else { prod_plus1(ds.drop_last()) * (ds.last() + 1) }
    }

    pub open spec fn union_bound(ds: Seq<nat>) -> nat { set_bound(sum_plus1(ds), ds.len()) }

    pub open spec fn intersect_bound(ds: Seq<nat>) -> nat { set_bound(prod_plus1(ds), ds.len()) }

    proof fn lemma_n4_pos(d: nat)
        ensures n4(d) >= 1, d < n4(d),
        decreases d,
    {
        if d > 0 { lemma_n4_pos((d - 1) as nat); }
    }

    proof fn lemma_log4_le(d: nat)
        requires d >= 1,
        ensures n4(log4_floor(d)) <= d,
        decreases d,
    {
        if d >= 4 { lemma_log4_le(d / 4); }
    }

    #[via_fn]
    proof fn clean_cost_decreases(d: nat) {
        if d > 1 {
            lemma_log4_le(d);
            assert(2 * (((d - 1) as nat) / 2) + 1 <= d);
        }
    }

    #[via_fn]
    proof fn not_cost_decreases(d: nat) {
        if d > 1 {
            lemma_n4_pos((d - 1) as nat);
            assert(n4(d) == 4 * n4((d - 1) as nat));
            lemma_n4_pos(d);
            if d >= 2 {
                lemma_n4_pos((d - 2) as nat);
                assert(n4((d - 1) as nat) == 4 * n4((d - 2) as nat));
            }
        }
    }

    #[via_fn]
    proof fn pair_cost_decreases(x: nat, y: nat) {
        if !(x == 0 || y == 0 || (x <= 1 && y <= 1)) {
            assert(x * (y + 1) < pair_bound(x, y)) by (nonlinear_arith) requires y >= 1;
            assert(y * (x + 1) < pair_bound(x, y)) by (nonlinear_arith) requires x >= 1;
            assert(x * y < pair_bound(x, y)) by (nonlinear_arith) requires x >= 1;
            if x >= 1 { assert(pair_bound((x - 1) as nat, y) < pair_bound(x, y)) by (nonlinear_arith) requires x >= 1; }
            if y >= 1 { assert(pair_bound(x, (y - 1) as nat) < pair_bound(x, y)) by (nonlinear_arith) requires y >= 1; }
            if x >= 1 && y >= 1 {
                assert(pair_bound((x - 1) as nat, (y - 1) as nat) < pair_bound(x, y)) by (nonlinear_arith) requires x >= 1, y >= 1;
            }
        }
    }

    /// Cost of `Clean` on a node of depth bound `d`.
    pub open spec fn clean_cost(d: nat) -> nat
        decreases d, 3nat, 0nat via clean_cost_decreases
    {
        if d <= 1 { 1 } else {
            4 + d + 3 * clean_cost((d - 1) as nat) + pair_cost_upto(d, d)
                + not_cost(log4_floor(d)) + append_cost(((d - 1) as nat) / 2)
        }
    }

    /// Cost of `Not` on a node of depth bound `d`.
    pub open spec fn not_cost(d: nat) -> nat
        decreases n4(d), 2nat, 0nat via not_cost_decreases
    {
        if d <= 1 { 1 } else {
            4 + n4(d) + 2 * not_cost((d - 1) as nat) + clean_cost(1 + n4((d - 1) as nat)) + clean_cost(2)
                + pair_cost_upto((n4(d) - 1) as nat, (n4(d) - 1) as nat)
        }
    }

    /// Cost of `Append` on a node of depth bound `d`.
    pub open spec fn append_cost(d: nat) -> nat
        decreases 2 * d + 1, 2nat, 0nat,
    {
        if d <= 1 { 1 } else { 3 + 3 * append_cost((d - 1) as nat) + clean_cost(2 * d) }
    }

    /// Cost of `Pair` on nodes of depth bounds `x` and `y`.
    pub open spec fn pair_cost(x: nat, y: nat) -> nat
        decreases pair_bound(x, y), 2nat, 0nat via pair_cost_decreases
    {
        if x == 0 || y == 0 || (x <= 1 && y <= 1) { 1 } else {
            6 + (if x >= 2 { 2 * pair_cost((x - 1) as nat, y) + clean_cost(x * (y + 1)) } else { 0 })
                + (if y >= 2 { 2 * pair_cost(x, (y - 1) as nat) + clean_cost(y * (x + 1)) } else { 0 })
                + (if x >= 2 && y >= 2 { pair_cost((x - 1) as nat, (y - 1) as nat) + clean_cost(x * y) } else { 0 })
        }
    }

    /// Sum of `pair_cost(x, y')` over `1 <= y' <= y` with `pair_bound(x, y') <= e`.
    pub open spec fn pair_cost_row(x: nat, y: nat, e: nat) -> nat
        decreases e, 2nat, y + 1,
    {
        if y == 0 { 0 } else {
            (if pair_bound(x, y) <= e { pair_cost(x, y) } else { 0 }) + pair_cost_row(x, (y - 1) as nat, e)
        }
    }

    /// Sum of `pair_cost_row(x', e, e)` over `1 <= x' <= x`.
    pub open spec fn pair_cost_upto(x: nat, e: nat) -> nat
        decreases e, 2nat, e + x + 2,
    {
        if x == 0 { 0 } else { pair_cost_row(x, e, e) + pair_cost_upto((x - 1) as nat, e) }
    }

    pub open spec fn pair_cost_total(e: nat) -> nat { pair_cost_upto(e, e) }

    pub open spec fn sum_map(f: spec_fn(nat) -> nat, ds: Seq<nat>) -> nat decreases ds.len() { if ds.len() == 0 { 0 } else { sum_map(f, ds.drop_last()) + f(ds.last()) } }
    pub open spec fn all_pos(ds: Seq<nat>) -> bool { forall|i: int| 0 <= i < ds.len() ==> #[trigger] ds[i] >= 1 }
    pub open spec fn le_pointwise(a: Seq<nat>, b: Seq<nat>) -> bool { a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= b[i] }
    pub open spec fn n4s(ds: Seq<nat>) -> Seq<nat> { Seq::new(ds.len(), |i: int| n4(ds[i])) }
    pub open spec fn appends(ds: Seq<nat>) -> Seq<nat> { Seq::new(ds.len(), |i: int| 2 * ds[i] + 1) }
    pub open spec fn pairs_left(ds: Seq<nat>, y: nat) -> Seq<nat> { Seq::new(ds.len(), |i: int| pair_bound(ds[i], y)) }
    pub open spec fn pairs_right(x: nat, ds: Seq<nat>) -> Seq<nat> { Seq::new(ds.len(), |i: int| pair_bound(x, ds[i])) }
    pub open spec fn clean_cost_fn() -> spec_fn(nat) -> nat { |d: nat| clean_cost(d) }
    pub open spec fn not_cost_fn() -> spec_fn(nat) -> nat { |d: nat| not_cost(d) }
    pub open spec fn append_cost_fn() -> spec_fn(nat) -> nat { |d: nat| append_cost(d) }
    pub open spec fn pair_cost_left_fn(y: nat) -> spec_fn(nat) -> nat { |d: nat| pair_cost(d, y) }
    pub open spec fn pair_cost_right_fn(x: nat) -> spec_fn(nat) -> nat { |d: nat| pair_cost(x, d) }
    /// Abstract cost of the intersect fold from index k with accumulator bound acc.
    pub open spec fn fold_cost(ds: Seq<nat>, k: nat, acc: nat) -> nat decreases ds.len() - k when k <= ds.len() {
        if k >= ds.len() { 1 } else { 1 + pair_cost(acc, ds[k as int]) + fold_cost(ds, k + 1, pair_bound(acc, ds[k as int])) } }
    pub open spec fn fold_bound(ds: Seq<nat>, k: nat, acc: nat) -> nat decreases ds.len() - k when k <= ds.len() {
        if k >= ds.len() { acc } else { fold_bound(ds, k + 1, pair_bound(acc, ds[k as int])) } }

    // ---------------------------------------------------------------- n4

    pub proof fn lemma_n4_mono(a: nat, b: nat)
        requires a <= b,
        ensures n4(a) <= n4(b), a < b ==> n4(a) < n4(b),
        decreases b,
    {
        if a < b {
            lemma_n4_mono(a, (b - 1) as nat);
            lemma_n4_pos((b - 1) as nat);
        }
    }

    pub proof fn lemma_n4_add(a: nat, b: nat)
        ensures n4(a + b) == n4(a) * n4(b),
        decreases b,
    {
        if b > 0 {
            lemma_n4_add(a, (b - 1) as nat);
            let p = n4(a);
            let q = n4((b - 1) as nat);
            assert(n4(a + b) == 4 * n4((a + (b - 1)) as nat));
            assert(4 * (p * q) == p * (4 * q)) by (nonlinear_arith);
        } else {
            assert(n4(a) * 1 == n4(a)) by (nonlinear_arith);
        }
    }

    proof fn lemma_singleton(ds: Seq<nat>)
        requires ds.len() == 1,
        ensures sum_plus1(ds) == ds[0] + 1, prod_plus1(ds) == ds[0] + 1, ds.last() == ds[0],
    {
        let p = prod_plus1(ds.drop_last());
        assert(sum_plus1(ds.drop_last()) == 0);
        assert(p == 1);
        assert(p * (ds[0] + 1) == ds[0] + 1) by (nonlinear_arith) requires p == 1;
    }

    pub proof fn lemma_log4_n4(k: nat)
        ensures log4_floor(n4(k)) == k,
        decreases k,
    {
        if k > 0 {
            lemma_n4_pos((k - 1) as nat);
            assert(n4(k) == 4 * n4((k - 1) as nat));
            assert(n4(k) / 4 == n4((k - 1) as nat));
            lemma_log4_n4((k - 1) as nat);
        }
    }

    proof fn lemma_n4_small()
        ensures n4(0) == 1, n4(1) == 4, n4(2) == 16,
    {
        assert(n4(0) == 1);
        assert(n4(1) == 4);
        assert(n4(2) == 16);
    }

    // ---------------------------------------------------------------- costs: positivity, steps

    pub proof fn lemma_costs_pos(d: nat)
        ensures clean_cost(d) >= 1, not_cost(d) >= 1, append_cost(d) >= 1,
    {
    }

    proof fn lemma_pair_cost_pos(x: nat, y: nat)
        ensures pair_cost(x, y) >= 1,
    {
    }

    proof fn lemma_clean_step(d: nat)
        ensures clean_cost(d) <= clean_cost(d + 1), d >= 1 ==> 2 * clean_cost(d) <= clean_cost(d + 1),
    {
        lemma_costs_pos(d);
        assert(((d + 1) - 1) as nat == d);
    }

    proof fn lemma_not_step(d: nat)
        ensures not_cost(d) <= not_cost(d + 1), d >= 1 ==> 2 * not_cost(d) <= not_cost(d + 1),
    {
        lemma_costs_pos(d);
        assert(((d + 1) - 1) as nat == d);
    }

    proof fn lemma_append_step(d: nat)
        ensures append_cost(d) <= append_cost(d + 1), d >= 1 ==> 2 * append_cost(d) <= append_cost(d + 1),
    {
        lemma_costs_pos(d);
        assert(((d + 1) - 1) as nat == d);
    }

    proof fn lemma_pair_step_x(x: nat, y: nat)
        ensures
            pair_cost(x, y) <= pair_cost(x + 1, y),
            x >= 1 && y >= 1 ==> 2 * pair_cost(x, y) <= pair_cost(x + 1, y),
    {
        lemma_pair_cost_pos(x, y);
        lemma_pair_cost_pos(x + 1, y);
        assert(((x + 1) - 1) as nat == x);
    }

    proof fn lemma_pair_step_y(x: nat, y: nat)
        ensures
            pair_cost(x, y) <= pair_cost(x, y + 1),
            x >= 1 && y >= 1 ==> 2 * pair_cost(x, y) <= pair_cost(x, y + 1),
    {
        lemma_pair_cost_pos(x, y);
        lemma_pair_cost_pos(x, y + 1);
        assert(((y + 1) - 1) as nat == y);
    }

    // ---------------------------------------------------------------- generic step-function facts

    #[verifier::opaque]
    pub open spec fn steps_ok(f: spec_fn(nat) -> nat) -> bool {
        forall|d: nat| #[trigger] f(d) <= f(d + 1) && (d >= 1 ==> 2 * f(d) <= f(d + 1))
    }

    proof fn lemma_steps_at(f: spec_fn(nat) -> nat, d: nat)
        requires steps_ok(f),
        ensures f(d) <= f(d + 1), d >= 1 ==> 2 * f(d) <= f(d + 1),
    {
        reveal(steps_ok);
    }

    proof fn lemma_f_mono(f: spec_fn(nat) -> nat, a: nat, b: nat)
        requires steps_ok(f), a <= b,
        ensures f(a) <= f(b),
        decreases b - a,
    {
        if a < b {
            lemma_f_mono(f, a, (b - 1) as nat);
            lemma_steps_at(f, (b - 1) as nat);
        }
    }

    proof fn lemma_f_superadd(f: spec_fn(nat) -> nat, a: nat, b: nat)
        requires steps_ok(f), a >= 1, b >= 1,
        ensures f(a) + f(b) <= f(a + b),
    {
        let m: nat = if a >= b { a } else { b };
        lemma_f_mono(f, a, m);
        lemma_f_mono(f, b, m);
        lemma_steps_at(f, m);
        lemma_f_mono(f, m + 1, a + b);
    }

    proof fn lemma_all_pos_drop_last(ds: Seq<nat>)
        requires all_pos(ds), ds.len() >= 1,
        ensures all_pos(ds.drop_last()), ds.last() >= 1,
    {
        assert forall|i: int| 0 <= i < ds.drop_last().len() implies #[trigger] ds.drop_last()[i] >= 1 by {
            assert(ds[i] >= 1);
        }
        assert(ds[ds.len() - 1] >= 1);
    }

    proof fn lemma_f_sum(f: spec_fn(nat) -> nat, ds: Seq<nat>)
        requires steps_ok(f), all_pos(ds), ds.len() >= 1,
        ensures
            sum_plus1(ds) >= 2 * ds.len(),
            sum_map(f, ds) <= f((sum_plus1(ds) - ds.len()) as nat),
        decreases ds.len(),
    {
        lemma_all_pos_drop_last(ds);
        let p = ds.drop_last();
        if ds.len() == 1 {
            assert(sum_map(f, p) == 0);
            assert(sum_plus1(p) == 0);
        } else {
            lemma_f_sum(f, p);
            let s1 = (sum_plus1(p) - p.len()) as nat;
            lemma_f_superadd(f, s1, ds.last());
            assert((sum_plus1(ds) - ds.len()) as nat == s1 + ds.last());
        }
    }

    proof fn lemma_sum_ge(ds: Seq<nat>)
        requires all_pos(ds),
        ensures sum_plus1(ds) >= 2 * ds.len(),
        decreases ds.len(),
    {
        if ds.len() >= 1 {
            lemma_all_pos_drop_last(ds);
            lemma_sum_ge(ds.drop_last());
        }
    }

    proof fn lemma_prod_ge(ds: Seq<nat>)
        requires all_pos(ds),
        ensures
            prod_plus1(ds) >= ds.len() + 1,
            prod_plus1(ds) >= sum_plus1(ds),
        decreases ds.len(),
    {
        if ds.len() >= 1 {
            lemma_all_pos_drop_last(ds);
            let p = ds.drop_last();
            lemma_prod_ge(p);
            let pp = prod_plus1(p);
            let sp = sum_plus1(p);
            let l = ds.last();
            let n = p.len();
            if n == 0 {
                assert(pp == 1);
                assert(sp == 0);
                assert(pp * (l + 1) == l + 1);
            } else {
                assert(pp * (l + 1) >= sp + l + 1 && pp * (l + 1) >= n + 2) by (nonlinear_arith)
                    requires pp >= sp, pp >= n + 1, n >= 1, l >= 1;
            }
        }
    }

    proof fn lemma_prod_pos(ds: Seq<nat>)
        ensures prod_plus1(ds) >= 1,
        decreases ds.len(),
    {
        if ds.len() >= 1 {
            lemma_prod_pos(ds.drop_last());
            let pp = prod_plus1(ds.drop_last());
            let l = ds.last();
            assert(pp * (l + 1) >= 1) by (nonlinear_arith) requires pp >= 1;
        }
    }

    proof fn lemma_f_sum_bounds(f: spec_fn(nat) -> nat, ds: Seq<nat>)
        requires steps_ok(f), all_pos(ds),
        ensures
            sum_map(f, ds) <= f((union_bound(ds) - 1) as nat),
            sum_map(f, ds) <= f((intersect_bound(ds) - 1) as nat),
    {
        if ds.len() == 1 {
            lemma_singleton(ds);
            lemma_f_sum(f, ds);
        } else if ds.len() >= 2 {
            lemma_f_sum(f, ds);
            lemma_prod_ge(ds);
            lemma_f_mono(f, (sum_plus1(ds) - ds.len()) as nat, (union_bound(ds) - 1) as nat);
            lemma_f_mono(f, (sum_plus1(ds) - ds.len()) as nat, (intersect_bound(ds) - 1) as nat);
        }
    }

    // ---------------------------------------------------------------- monotonicity

    proof fn lemma_clean_steps_ok()
        ensures steps_ok(clean_cost_fn()),
    {
        reveal(steps_ok);
        assert forall|d: nat| #[trigger] clean_cost_fn()(d) <= clean_cost_fn()(d + 1)
            && (d >= 1 ==> 2 * clean_cost_fn()(d) <= clean_cost_fn()(d + 1)) by {
            lemma_clean_step(d);
        }
    }

    proof fn lemma_not_steps_ok()
        ensures steps_ok(not_cost_fn()),
    {
        reveal(steps_ok);
        assert forall|d: nat| #[trigger] not_cost_fn()(d) <= not_cost_fn()(d + 1)
            && (d >= 1 ==> 2 * not_cost_fn()(d) <= not_cost_fn()(d + 1)) by {
            lemma_not_step(d);
        }
    }

    proof fn lemma_append_steps_ok()
        ensures steps_ok(append_cost_fn()),
    {
        reveal(steps_ok);
        assert forall|d: nat| #[trigger] append_cost_fn()(d) <= append_cost_fn()(d + 1)
            && (d >= 1 ==> 2 * append_cost_fn()(d) <= append_cost_fn()(d + 1)) by {
            lemma_append_step(d);
        }
    }

    proof fn lemma_pair_left_steps_ok(y: nat)
        requires y >= 1,
        ensures steps_ok(pair_cost_left_fn(y)),
    {
        reveal(steps_ok);
        assert forall|d: nat| #[trigger] pair_cost_left_fn(y)(d) <= pair_cost_left_fn(y)(d + 1)
            && (d >= 1 ==> 2 * pair_cost_left_fn(y)(d) <= pair_cost_left_fn(y)(d + 1)) by {
            lemma_pair_step_x(d, y);
        }
    }

    proof fn lemma_pair_right_steps_ok(x: nat)
        requires x >= 1,
        ensures steps_ok(pair_cost_right_fn(x)),
    {
        reveal(steps_ok);
        assert forall|d: nat| #[trigger] pair_cost_right_fn(x)(d) <= pair_cost_right_fn(x)(d + 1)
            && (d >= 1 ==> 2 * pair_cost_right_fn(x)(d) <= pair_cost_right_fn(x)(d + 1)) by {
            lemma_pair_step_y(x, d);
        }
    }

    pub proof fn lemma_clean_cost_mono(a: nat, b: nat)
        requires a <= b,
        ensures clean_cost(a) <= clean_cost(b),
    {
        lemma_clean_steps_ok();
        lemma_f_mono(clean_cost_fn(), a, b);
    }

    pub proof fn lemma_not_cost_mono(a: nat, b: nat)
        requires a <= b,
        ensures not_cost(a) <= not_cost(b),
    {
        lemma_not_steps_ok();
        lemma_f_mono(not_cost_fn(), a, b);
    }

    pub proof fn lemma_append_cost_mono(a: nat, b: nat)
        requires a <= b,
        ensures append_cost(a) <= append_cost(b),
    {
        lemma_append_steps_ok();
        lemma_f_mono(append_cost_fn(), a, b);
    }

    proof fn lemma_pair_cost_mono_x(x1: nat, x2: nat, y: nat)
        requires x1 <= x2,
        ensures pair_cost(x1, y) <= pair_cost(x2, y),
        decreases x2,
    {
        if x1 < x2 {
            lemma_pair_cost_mono_x(x1, (x2 - 1) as nat, y);
            lemma_pair_step_x((x2 - 1) as nat, y);
        }
    }

    proof fn lemma_pair_cost_mono_y(x: nat, y1: nat, y2: nat)
        requires y1 <= y2,
        ensures pair_cost(x, y1) <= pair_cost(x, y2),
        decreases y2,
    {
        if y1 < y2 {
            lemma_pair_cost_mono_y(x, y1, (y2 - 1) as nat);
            lemma_pair_step_y(x, (y2 - 1) as nat);
        }
    }

    pub proof fn lemma_pair_cost_mono(x1: nat, y1: nat, x2: nat, y2: nat)
        requires x1 <= x2, y1 <= y2,
        ensures 1 <= pair_cost(x1, y1) <= pair_cost(x2, y2),
    {
        lemma_pair_cost_pos(x1, y1);
        lemma_pair_cost_mono_x(x1, x2, y1);
        lemma_pair_cost_mono_y(x2, y1, y2);
    }

    proof fn lemma_row_mono_y(x: nat, y1: nat, y2: nat, e: nat)
        requires y1 <= y2,
        ensures pair_cost_row(x, y1, e) <= pair_cost_row(x, y2, e),
        decreases y2,
    {
        if y1 < y2 {
            lemma_row_mono_y(x, y1, (y2 - 1) as nat, e);
        }
    }

    proof fn lemma_row_mono_e(x: nat, y: nat, e1: nat, e2: nat)
        requires e1 <= e2,
        ensures pair_cost_row(x, y, e1) <= pair_cost_row(x, y, e2),
        decreases y,
    {
        if y > 0 {
            lemma_row_mono_e(x, (y - 1) as nat, e1, e2);
        }
    }

    proof fn lemma_upto_mono_x(x1: nat, x2: nat, e: nat)
        requires x1 <= x2,
        ensures pair_cost_upto(x1, e) <= pair_cost_upto(x2, e),
        decreases x2,
    {
        if x1 < x2 {
            lemma_upto_mono_x(x1, (x2 - 1) as nat, e);
        }
    }

    proof fn lemma_upto_mono_e(x: nat, e1: nat, e2: nat)
        requires e1 <= e2,
        ensures pair_cost_upto(x, e1) <= pair_cost_upto(x, e2),
        decreases x,
    {
        if x > 0 {
            lemma_upto_mono_e((x - 1) as nat, e1, e2);
            lemma_row_mono_e(x, e1, e1, e2);
            lemma_row_mono_y(x, e1, e2, e2);
        }
    }

    pub proof fn lemma_pair_cost_total_mono(a: nat, b: nat)
        requires a <= b,
        ensures pair_cost_total(a) <= pair_cost_total(b),
    {
        lemma_upto_mono_e(a, a, b);
        lemma_upto_mono_x(a, b, b);
    }

    pub proof fn lemma_pair_bound_mono(a1: nat, b1: nat, a2: nat, b2: nat)
        requires a1 <= a2, b1 <= b2,
        ensures pair_bound(a1, b1) <= pair_bound(a2, b2),
    {
        assert(a1 * b1 <= a2 * b2) by (nonlinear_arith) requires a1 <= a2, b1 <= b2;
    }

    pub proof fn lemma_pair_bound_ge(a: nat, b: nat)
        ensures a <= pair_bound(a, b), b <= pair_bound(a, b),
    {
        assert(a * b >= 0) by (nonlinear_arith);
    }

    /// `transition_collect([a, b], true)` stays within `pair_bound`.
    pub proof fn collect_lemma_pair_bound(g: model::Graph, a: TransitionId, b: TransitionId)
        ensures collect_bound(g, seq![a, b], true) == pair_bound(tdepth(g, a@), tdepth(g, b@)),
    {
        let x = tdepth(g, a@);
        let y = tdepth(g, b@);
        let ds = value_depths(g, seq![a, b]);
        assert(ds =~= seq![x, y]);
        assert(ds.drop_last() =~= seq![x]);
        assert(ds.last() == y);
        lemma_singleton(seq![x]);
        assert(prod_plus1(ds) == (x + 1) * (y + 1));
        assert((x + 1) * (y + 1) == x * y + x + y + 1) by (nonlinear_arith);
    }

    pub proof fn lemma_pair_bound_comm(a: nat, b: nat)
        ensures pair_bound(a, b) == pair_bound(b, a),
    {
        assert(a * b == b * a) by (nonlinear_arith);
    }

    // ---------------------------------------------------------------- set bounds

    proof fn lemma_le_pointwise_drop_last(a: Seq<nat>, b: Seq<nat>)
        requires le_pointwise(a, b), a.len() >= 1,
        ensures le_pointwise(a.drop_last(), b.drop_last()), a.last() <= b.last(),
    {
        assert forall|i: int| 0 <= i < a.drop_last().len() implies #[trigger] a.drop_last()[i] <= b.drop_last()[i] by {
            assert(a[i] <= b[i]);
        }
        assert(a[a.len() - 1] <= b[a.len() - 1]);
    }

    proof fn lemma_totals_mono(a: Seq<nat>, b: Seq<nat>)
        requires le_pointwise(a, b),
        ensures sum_plus1(a) <= sum_plus1(b), prod_plus1(a) <= prod_plus1(b),
        decreases a.len(),
    {
        if a.len() >= 1 {
            lemma_le_pointwise_drop_last(a, b);
            lemma_totals_mono(a.drop_last(), b.drop_last());
            let pa = prod_plus1(a.drop_last());
            let pb = prod_plus1(b.drop_last());
            let la = a.last();
            let lb = b.last();
            assert(pa * (la + 1) <= pb * (lb + 1)) by (nonlinear_arith) requires pa <= pb, la <= lb;
        }
    }

    pub proof fn lemma_bounds_mono(a: Seq<nat>, b: Seq<nat>)
        requires le_pointwise(a, b),
        ensures union_bound(a) <= union_bound(b), intersect_bound(a) <= intersect_bound(b),
    {
        lemma_totals_mono(a, b);
        lemma_prod_pos(a);
        lemma_prod_pos(b);
        assert(prod_plus1(a) <= prod_plus1(b));
    }

    pub proof fn lemma_bounds_pos(ds: Seq<nat>)
        requires all_pos(ds),
        ensures
            union_bound(ds) >= 2,
            intersect_bound(ds) >= 2,
            sum_plus1(ds) <= union_bound(ds) + 1,
            prod_plus1(ds) <= intersect_bound(ds) + 1,
            prod_plus1(ds) >= 1,
            ds.len() >= 2 ==> union_bound(ds) + 1 == sum_plus1(ds) && intersect_bound(ds) + 1 == prod_plus1(ds),
    {
        lemma_sum_ge(ds);
        lemma_prod_ge(ds);
    }

    // ---------------------------------------------------------------- sum lemmas

    pub proof fn lemma_clean_sum(ds: Seq<nat>)
        requires all_pos(ds),
        ensures
            sum_map(clean_cost_fn(), ds) <= clean_cost((union_bound(ds) - 1) as nat),
            sum_map(clean_cost_fn(), ds) <= clean_cost((intersect_bound(ds) - 1) as nat),
    {
        lemma_clean_steps_ok();
        lemma_f_sum_bounds(clean_cost_fn(), ds);
    }

    pub proof fn lemma_not_sum(ds: Seq<nat>)
        requires all_pos(ds),
        ensures
            sum_map(not_cost_fn(), ds) <= not_cost((union_bound(ds) - 1) as nat),
            sum_map(not_cost_fn(), ds) <= not_cost((intersect_bound(ds) - 1) as nat),
    {
        lemma_not_steps_ok();
        lemma_f_sum_bounds(not_cost_fn(), ds);
    }

    pub proof fn lemma_append_sum(ds: Seq<nat>)
        requires all_pos(ds),
        ensures
            sum_map(append_cost_fn(), ds) <= append_cost((union_bound(ds) - 1) as nat),
            sum_map(append_cost_fn(), ds) <= append_cost((intersect_bound(ds) - 1) as nat),
    {
        lemma_append_steps_ok();
        lemma_f_sum_bounds(append_cost_fn(), ds);
    }

    pub proof fn lemma_pair_left_sum(ds: Seq<nat>, y: nat)
        requires all_pos(ds), y >= 1,
        ensures sum_map(pair_cost_left_fn(y), ds) <= pair_cost((union_bound(ds) - 1) as nat, y),
    {
        lemma_pair_left_steps_ok(y);
        lemma_f_sum_bounds(pair_cost_left_fn(y), ds);
    }

    pub proof fn lemma_pair_right_sum(x: nat, ds: Seq<nat>)
        requires all_pos(ds), x >= 1,
        ensures sum_map(pair_cost_right_fn(x), ds) <= pair_cost(x, (union_bound(ds) - 1) as nat),
    {
        lemma_pair_right_steps_ok(x);
        lemma_f_sum_bounds(pair_cost_right_fn(x), ds);
    }

    // ---------------------------------------------------------------- Not bounds

    proof fn lemma_n4s_prod(ds: Seq<nat>)
        requires ds.len() >= 1,
        ensures
            sum_plus1(ds) >= 1,
            prod_plus1(n4s(ds)) <= 2 * n4((sum_plus1(ds) - 1) as nat),
            ds.len() >= 2 ==> prod_plus1(n4s(ds)) <= n4((sum_plus1(ds) - 1) as nat),
        decreases ds.len(),
    {
        let p = ds.drop_last();
        let l = ds.last();
        assert(n4s(ds).drop_last() =~= n4s(p));
        assert(n4s(ds).last() == n4(l));
        lemma_n4_pos(l);
        if ds.len() == 1 {
            lemma_singleton(ds);
            lemma_singleton(n4s(ds));
        } else {
            lemma_n4s_prod(p);
            let a = (sum_plus1(p) - 1) as nat;
            let pp = prod_plus1(n4s(p));
            let m = n4(a);
            let q = n4(l);
            lemma_n4_add(a, l + 1);
            assert(n4(l + 1) == 4 * q);
            assert((sum_plus1(ds) - 1) as nat == a + (l + 1));
            assert(pp * (q + 1) <= m * (4 * q)) by (nonlinear_arith) requires pp <= 2 * m, q >= 1;
        }
    }

    proof fn lemma_n4s_sum(ds: Seq<nat>)
        requires ds.len() >= 1, all_pos(ds),
        ensures
            prod_plus1(ds) >= 1,
            sum_plus1(n4s(ds)) <= 2 * n4((prod_plus1(ds) - 1) as nat),
            ds.len() >= 2 ==> sum_plus1(n4s(ds)) <= n4((prod_plus1(ds) - 1) as nat),
        decreases ds.len(),
    {
        let p = ds.drop_last();
        let l = ds.last();
        lemma_all_pos_drop_last(ds);
        assert(n4s(ds).drop_last() =~= n4s(p));
        assert(n4s(ds).last() == n4(l));
        lemma_n4_pos(l);
        lemma_prod_pos(ds);
        if ds.len() == 1 {
            lemma_singleton(ds);
            lemma_singleton(n4s(ds));
        } else {
            lemma_n4s_sum(p);
            lemma_prod_ge(p);
            let pp = prod_plus1(p);
            let a = (pp - 1) as nat;
            let s = sum_plus1(n4s(p));
            let m = n4(a);
            let q = n4(l);
            lemma_n4_pos(a);
            lemma_n4_add(a, l + 1);
            assert(n4(l + 1) == 4 * q);
            assert(pp * (l + 1) - 1 >= a + (l + 1)) by (nonlinear_arith) requires pp == a + 1, a >= 1, l >= 1;
            lemma_n4_mono(a + (l + 1), (prod_plus1(ds) - 1) as nat);
            assert(2 * m + q + 1 <= m * (4 * q)) by (nonlinear_arith) requires m >= 1, q >= 1;
        }
    }

    pub proof fn lemma_not_union(ds: Seq<nat>)
        requires all_pos(ds),
        ensures intersect_bound(n4s(ds)) < n4(union_bound(ds)),
    {
        lemma_n4_small();
        if ds.len() == 1 {
            lemma_singleton(ds);
            lemma_singleton(n4s(ds));
            lemma_n4_pos(ds[0]);
            assert(union_bound(ds) == ds[0] + 1);
            assert(n4(ds[0] + 1) == 4 * n4(ds[0]));
            assert(n4s(ds)[0] == n4(ds[0]));
        } else if ds.len() >= 2 {
            lemma_n4s_prod(ds);
            lemma_n4_pos((sum_plus1(ds) - 1) as nat);
            lemma_prod_pos(n4s(ds));
        }
    }

    pub proof fn lemma_not_intersect(ds: Seq<nat>)
        requires all_pos(ds),
        ensures union_bound(n4s(ds)) <= n4(intersect_bound(ds)),
    {
        lemma_n4_small();
        if ds.len() == 1 {
            lemma_singleton(ds);
            lemma_singleton(n4s(ds));
            lemma_n4_pos(ds[0]);
        } else if ds.len() >= 2 {
            lemma_n4s_sum(ds);
        }
    }

    // ---------------------------------------------------------------- Append / Pair over unions

    proof fn lemma_appends_sum(ds: Seq<nat>)
        ensures sum_plus1(appends(ds)) == 2 * sum_plus1(ds),
        decreases ds.len(),
    {
        if ds.len() >= 1 {
            assert(appends(ds).drop_last() =~= appends(ds.drop_last()));
            lemma_appends_sum(ds.drop_last());
        }
    }

    pub proof fn lemma_append_union(ds: Seq<nat>)
        requires all_pos(ds),
        ensures union_bound(appends(ds)) <= 2 * union_bound(ds) + 1,
    {
        lemma_appends_sum(ds);
        lemma_sum_ge(ds);
    }

    proof fn lemma_pairs_left_sum(ds: Seq<nat>, y: nat)
        ensures sum_plus1(pairs_left(ds, y)) == (y + 1) * sum_plus1(ds),
        decreases ds.len(),
    {
        if ds.len() >= 1 {
            assert(pairs_left(ds, y).drop_last() =~= pairs_left(ds.drop_last(), y));
            lemma_pairs_left_sum(ds.drop_last(), y);
            let s = sum_plus1(ds.drop_last());
            let l = ds.last();
            assert((y + 1) * s + (l * y + l + y) + 1 == (y + 1) * (s + l + 1)) by (nonlinear_arith);
        } else {
            assert((y + 1) * sum_plus1(ds) == 0) by (nonlinear_arith) requires sum_plus1(ds) == 0;
        }
    }

    proof fn lemma_pairs_right_sum(x: nat, ds: Seq<nat>)
        ensures sum_plus1(pairs_right(x, ds)) == (x + 1) * sum_plus1(ds),
        decreases ds.len(),
    {
        if ds.len() >= 1 {
            assert(pairs_right(x, ds).drop_last() =~= pairs_right(x, ds.drop_last()));
            lemma_pairs_right_sum(x, ds.drop_last());
            let s = sum_plus1(ds.drop_last());
            let l = ds.last();
            assert((x + 1) * s + (x * l + x + l) + 1 == (x + 1) * (s + l + 1)) by (nonlinear_arith);
        } else {
            assert((x + 1) * sum_plus1(ds) == 0) by (nonlinear_arith) requires sum_plus1(ds) == 0;
        }
    }

    pub proof fn lemma_pair_union_left(ds: Seq<nat>, y: nat)
        requires all_pos(ds),
        ensures union_bound(pairs_left(ds, y)) <= pair_bound(union_bound(ds), y),
    {
        lemma_pairs_left_sum(ds, y);
        lemma_sum_ge(ds);
        let s = sum_plus1(ds);
        let u = union_bound(ds);
        if ds.len() == 1 {
            lemma_singleton(ds);
            assert((y + 1) * s <= u * y + u + y) by (nonlinear_arith) requires u == s;
        } else if ds.len() >= 2 {
            assert((y + 1) * s <= u * y + u + y + 1) by (nonlinear_arith) requires u + 1 == s;
        }
    }

    pub proof fn lemma_pair_union_right(x: nat, ds: Seq<nat>)
        requires all_pos(ds),
        ensures union_bound(pairs_right(x, ds)) <= pair_bound(x, union_bound(ds)),
    {
        lemma_pairs_right_sum(x, ds);
        lemma_sum_ge(ds);
        let s = sum_plus1(ds);
        let u = union_bound(ds);
        if ds.len() == 1 {
            lemma_singleton(ds);
            assert((x + 1) * s <= x * u + x + u) by (nonlinear_arith) requires u == s;
        } else if ds.len() >= 2 {
            assert((x + 1) * s <= x * u + x + u + 1) by (nonlinear_arith) requires u + 1 == s;
        }
    }

    // ---------------------------------------------------------------- intersect fold

    proof fn lemma_prod_front(ds: Seq<nat>)
        requires ds.len() >= 1,
        ensures prod_plus1(ds) == (ds[0] + 1) * prod_plus1(ds.subrange(1, ds.len() as int)),
        decreases ds.len(),
    {
        let t = ds.subrange(1, ds.len() as int);
        if ds.len() == 1 {
            lemma_singleton(ds);
            assert(prod_plus1(t) == 1);
            assert((ds[0] + 1) * prod_plus1(t) == ds[0] + 1) by (nonlinear_arith) requires prod_plus1(t) == 1;
        } else {
            let p = ds.drop_last();
            lemma_prod_front(p);
            assert(t.drop_last() =~= p.subrange(1, p.len() as int));
            assert(p[0] == ds[0]);
            assert(t.last() == ds.last());
            let a = ds[0] + 1;
            let b = prod_plus1(p.subrange(1, p.len() as int));
            let c = ds.last() + 1;
            assert((a * b) * c == a * (b * c)) by (nonlinear_arith);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_fold_bound_eq(ds: Seq<nat>, k: nat, acc: nat)
        requires k <= ds.len(),
        ensures
            fold_bound(ds, k, acc) + 1 == (acc + 1) * prod_plus1(ds.subrange(k as int, ds.len() as int)),
            fold_bound(ds, k, acc) >= acc,
        decreases ds.len() - k,
    {
        let t = ds.subrange(k as int, ds.len() as int);
        if k >= ds.len() {
            assert(t.len() == 0);
            assert(prod_plus1(t) == 1);
            assert((acc + 1) * 1 == acc + 1) by (nonlinear_arith);
        } else {
            let d = ds[k as int];
            let acc2 = pair_bound(acc, d);
            lemma_fold_bound_eq(ds, k + 1, acc2);
            lemma_prod_front(t);
            assert(t[0] == d);
            assert(t.subrange(1, t.len() as int) =~= ds.subrange(k + 1 as int, ds.len() as int));
            let r = prod_plus1(ds.subrange(k + 1 as int, ds.len() as int));
            assert((acc * d + acc + d + 1) * r == (acc + 1) * ((d + 1) * r)) by (nonlinear_arith);
            assert(acc * d >= 0) by (nonlinear_arith);
        }
    }

    proof fn lemma_row_ge(x: nat, y: nat, ye: nat, e: nat)
        requires 1 <= y <= ye, pair_bound(x, y) <= e,
        ensures pair_cost(x, y) <= pair_cost_row(x, ye, e),
        decreases ye,
    {
        if y < ye {
            lemma_row_ge(x, y, (ye - 1) as nat, e);
        }
    }

    proof fn lemma_fold_cost_bound(ds: Seq<nat>, k: nat, acc: nat, e: nat)
        requires acc >= 1, k <= ds.len(), all_pos(ds), e >= fold_bound(ds, k, acc),
        ensures
            fold_cost(ds, k, acc) + pair_cost_upto((acc - 1) as nat, e)
                <= (ds.len() - k) + 1 + pair_cost_upto((fold_bound(ds, k, acc) - 1) as nat, e),
        decreases ds.len() - k,
    {
        if k < ds.len() {
            let d = ds[k as int];
            assert(d >= 1);
            let acc2 = pair_bound(acc, d);
            assert(acc * d >= 1) by (nonlinear_arith) requires acc >= 1, d >= 1;
            lemma_fold_bound_eq(ds, k + 1, acc2);
            lemma_fold_cost_bound(ds, k + 1, acc2, e);
            lemma_row_ge(acc, d, e, e);
            lemma_upto_mono_x(acc, (acc2 - 1) as nat, e);
            assert(pair_cost_upto(acc, e) == pair_cost_row(acc, e, e) + pair_cost_upto((acc - 1) as nat, e));
        }
    }

    pub proof fn lemma_fold(ds: Seq<nat>)
        requires ds.len() >= 2, all_pos(ds),
        ensures
            fold_bound(ds, 1, ds[0]) == intersect_bound(ds),
            fold_cost(ds, 1, ds[0]) <= intersect_bound(ds) + pair_cost_total(intersect_bound(ds)),
    {
        let e = intersect_bound(ds);
        lemma_fold_bound_eq(ds, 1, ds[0]);
        lemma_prod_front(ds);
        lemma_prod_ge(ds);
        assert(ds[0] >= 1);
        lemma_fold_cost_bound(ds, 1, ds[0], e);
        lemma_upto_mono_x((e - 1) as nat, e, e);
    }

    pub proof fn lemma_fold_mono(ds: Seq<nat>, k: nat, a: nat, b: nat)
        requires a <= b, k <= ds.len(),
        ensures fold_cost(ds, k, a) <= fold_cost(ds, k, b), fold_bound(ds, k, a) <= fold_bound(ds, k, b),
        decreases ds.len() - k,
    {
        if k < ds.len() {
            let d = ds[k as int];
            lemma_pair_bound_mono(a, d, b, d);
            lemma_pair_cost_mono(a, d, b, d);
            lemma_fold_mono(ds, k + 1, pair_bound(a, d), pair_bound(b, d));
        }
    }

    // ===== transition_machine termination: per-node depth bounds and an abstract run of the task stack =====

    /// Depth bound of a transition node: `1 + max` at `If`, additive at `Union`, multiplicative at
    /// `Intersect`, `4^d` at `Not`, `2d + 1` at `Append`.
    pub open spec fn tdepth(g: model::Graph, id: nat) -> nat
        decreases id, 1nat,
    {
        if id >= g.transitions.len() { 1 } else {
            match g.transitions[id as int] {
                model::TransitionNode::Const(_) => 1,
                model::TransitionNode::If(_, a, b) => if_bound(
                    if a < id { tdepth(g, a) } else { 1 }, if b < id { tdepth(g, b) } else { 1 }),
                model::TransitionNode::Union(cs) => union_bound(tdepths_bounded(g, cs, id)),
                model::TransitionNode::Intersect(cs) => intersect_bound(tdepths_bounded(g, cs, id)),
                model::TransitionNode::Not(c) => n4(if c < id { tdepth(g, c) } else { 1 }),
                model::TransitionNode::Append(c, _) => 2 * (if c < id { tdepth(g, c) } else { 1 }) + 1,
            }
        }
    }

    pub open spec fn tdepths_bounded(g: model::Graph, cs: Seq<nat>, bound: nat) -> Seq<nat>
        decreases bound, 0nat,
    {
        Seq::new(cs.len(), |j: int| if 0 <= j < cs.len() && cs[j] < bound { tdepth(g, cs[j]) } else { 1 })
    }

    pub open spec fn tdepths(g: model::Graph, ids: Seq<nat>) -> Seq<nat> {
        Seq::new(ids.len(), |i: int| tdepth(g, ids[i]))
    }

    pub open spec fn value_depths(g: model::Graph, values: Seq<TransitionId>) -> Seq<nat> {
        Seq::new(values.len(), |i: int| tdepth(g, values[i]@))
    }

    pub open spec fn tdepth_node(g: model::Graph, node: model::TransitionNode) -> nat {
        match node {
            model::TransitionNode::Const(_) => 1,
            model::TransitionNode::If(_, a, b) => if_bound(tdepth(g, a), tdepth(g, b)),
            model::TransitionNode::Union(cs) => union_bound(tdepths(g, cs)),
            model::TransitionNode::Intersect(cs) => intersect_bound(tdepths(g, cs)),
            model::TransitionNode::Not(c) => n4(tdepth(g, c)),
            model::TransitionNode::Append(c, _) => 2 * tdepth(g, c) + 1,
        }
    }

    pub proof fn tdepth_lemma_unfold(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.transitions.len(),
        ensures tdepth(g, id) == tdepth_node(g, g.transitions[id as int]),
    {
        model::lemma_graph_transition_wf(g, id);
        match g.transitions[id as int] {
            model::TransitionNode::Union(cs) => { assert(tdepths_bounded(g, cs, id) =~= tdepths(g, cs)); },
            model::TransitionNode::Intersect(cs) => { assert(tdepths_bounded(g, cs, id) =~= tdepths(g, cs)); },
            _ => {},
        }
    }

    pub proof fn tdepth_lemma_pos(g: model::Graph, id: nat)
        ensures tdepth(g, id) >= 1,
        decreases id,
    {
        if id < g.transitions.len() {
            match g.transitions[id as int] {
                model::TransitionNode::Union(cs) => {
                    let ds = tdepths_bounded(g, cs, id);
                    assert forall|j: int| 0 <= j < ds.len() implies #[trigger] ds[j] >= 1 by {
                        if cs[j] < id { tdepth_lemma_pos(g, cs[j]); }
                    }
                    lemma_bounds_pos(ds);
                },
                model::TransitionNode::Intersect(cs) => {
                    let ds = tdepths_bounded(g, cs, id);
                    assert forall|j: int| 0 <= j < ds.len() implies #[trigger] ds[j] >= 1 by {
                        if cs[j] < id { tdepth_lemma_pos(g, cs[j]); }
                    }
                    lemma_bounds_pos(ds);
                },
                model::TransitionNode::Not(c) => { lemma_n4_pos(if c < id { tdepth(g, c) } else { 1 }); },
                _ => {},
            }
        }
    }

    pub proof fn tdepths_lemma_pos(g: model::Graph, ids: Seq<nat>)
        ensures all_pos(tdepths(g, ids)),
    {
        assert forall|i: int| 0 <= i < tdepths(g, ids).len() implies #[trigger] tdepths(g, ids)[i] >= 1 by {
            tdepth_lemma_pos(g, ids[i]);
        }
    }

    pub proof fn value_depths_lemma_pos(g: model::Graph, values: Seq<TransitionId>)
        ensures all_pos(value_depths(g, values)),
    {
        assert forall|i: int| 0 <= i < value_depths(g, values).len() implies #[trigger] value_depths(g, values)[i] >= 1 by {
            tdepth_lemma_pos(g, values[i]@);
        }
    }

    pub proof fn tdepth_lemma_extends(a: model::Graph, b: model::Graph, id: nat)
        requires model::graph_extends(a, b), id < a.transitions.len(),
        ensures tdepth(a, id) == tdepth(b, id),
        decreases id,
    {
        assert(a.transitions[id as int] == b.transitions[id as int]);
        match a.transitions[id as int] {
            model::TransitionNode::If(_, x, y) => {
                if x < id { tdepth_lemma_extends(a, b, x); }
                if y < id { tdepth_lemma_extends(a, b, y); }
            },
            model::TransitionNode::Union(cs) => {
                assert forall|j: int| 0 <= j < cs.len() implies tdepths_bounded(a, cs, id)[j] == tdepths_bounded(b, cs, id)[j] by {
                    if cs[j] < id { tdepth_lemma_extends(a, b, cs[j]); }
                }
                assert(tdepths_bounded(a, cs, id) =~= tdepths_bounded(b, cs, id));
            },
            model::TransitionNode::Intersect(cs) => {
                assert forall|j: int| 0 <= j < cs.len() implies tdepths_bounded(a, cs, id)[j] == tdepths_bounded(b, cs, id)[j] by {
                    if cs[j] < id { tdepth_lemma_extends(a, b, cs[j]); }
                }
                assert(tdepths_bounded(a, cs, id) =~= tdepths_bounded(b, cs, id));
            },
            model::TransitionNode::Not(c) => { if c < id { tdepth_lemma_extends(a, b, c); } },
            model::TransitionNode::Append(c, _) => { if c < id { tdepth_lemma_extends(a, b, c); } },
            _ => {},
        }
    }

    pub proof fn tdepth_lemma_extends_forall(a: model::Graph)
        ensures forall|b: model::Graph, id: nat| model::graph_extends(a, b) && id < a.transitions.len()
            ==> #[trigger] tdepth(b, id) == tdepth(a, id),
    {
        assert forall|b: model::Graph, id: nat| model::graph_extends(a, b) && id < a.transitions.len()
            implies #[trigger] tdepth(b, id) == tdepth(a, id) by { tdepth_lemma_extends(a, b, id); }
    }

    pub proof fn tdepths_lemma_extends(a: model::Graph, b: model::Graph, ids: Seq<nat>)
        requires model::graph_extends(a, b), model::bounded(ids, a.transitions.len()),
        ensures tdepths(a, ids) == tdepths(b, ids),
    {
        assert forall|i: int| 0 <= i < ids.len() implies tdepths(a, ids)[i] == tdepths(b, ids)[i] by {
            tdepth_lemma_extends(a, b, ids[i]);
        }
        assert(tdepths(a, ids) =~= tdepths(b, ids));
    }

    pub proof fn tdepths_lemma_extends_forall(a: model::Graph, values: Seq<TransitionId>)
        requires transition_ids_valid(a, values),
        ensures forall|b: model::Graph| model::graph_extends(a, b)
            ==> #[trigger] tdepths(b, model::transition_ids(values)) == tdepths(a, model::transition_ids(values)),
    {
        let ids = model::transition_ids(values);
        assert(model::bounded(ids, a.transitions.len()));
        assert forall|b: model::Graph| model::graph_extends(a, b)
            implies #[trigger] tdepths(b, ids) == tdepths(a, ids) by { tdepths_lemma_extends(a, b, ids); }
    }

    pub proof fn value_depths_lemma_extends(a: model::Graph, b: model::Graph, values: Seq<TransitionId>)
        requires model::graph_extends(a, b), transition_ids_valid(a, values),
        ensures value_depths(a, values) == value_depths(b, values),
    {
        assert forall|i: int| 0 <= i < values.len() implies value_depths(a, values)[i] == value_depths(b, values)[i] by {
            tdepth_lemma_extends(a, b, values[i]@);
        }
        assert(value_depths(a, values) =~= value_depths(b, values));
    }

    pub proof fn tdepth_lemma_constants(g: model::Graph)
        requires model::graph_wf(g),
        ensures tdepth(g, g.constants.transition_empty) == 1, tdepth(g, g.constants.transition_all) == 1,
            tdepth(g, g.constants.transition_epsilon) == 1,
    {
        model::lemma_graph_wf_elim(g);
    }

    pub proof fn tdepth_lemma_const(g: model::Graph, id: nat)
        requires id < g.transitions.len(), g.transitions[id as int] is Const,
        ensures tdepth(g, id) == 1,
    {}

    // ----- abstract value stack -----

    pub open spec fn abs_at(stack: Seq<nat>, j: int) -> nat { if 0 <= j < stack.len() { stack[j] } else { 1 } }
    pub open spec fn abs_peek(stack: Seq<nat>, from_top: nat) -> nat { abs_at(stack, stack.len() - 1 - from_top) }
    pub open spec fn abs_top(stack: Seq<nat>, k: nat) -> Seq<nat> { Seq::new(k, |i: int| abs_at(stack, stack.len() - k + i)) }
    pub open spec fn abs_pop(stack: Seq<nat>, k: nat) -> Seq<nat> {
        if k <= stack.len() { stack.take(stack.len() - k) } else { Seq::empty() }
    }

    pub open spec fn action_cost(g: model::Graph, task: ActionShape, stack: Seq<nat>) -> nat {
        match task {
            ActionShape::Clean(id, _) => clean_cost(tdepth(g, id)),
            ActionShape::Not(id) => not_cost(tdepth(g, id)),
            ActionShape::Append(id, _) => append_cost(tdepth(g, id)),
            ActionShape::Pair(a, b) => pair_cost(tdepth(g, a), tdepth(g, b)),
            ActionShape::Union(_) => 1,
            ActionShape::If(_) => 1,
            ActionShape::SwapThen => 1,
            ActionShape::Intersect(n) =>
                2 + intersect_bound(abs_top(stack, n)) + pair_cost_total(intersect_bound(abs_top(stack, n))),
            ActionShape::Fold(xs, k) => if k == 0 {
                    1 + intersect_bound(tdepths(g, xs)) + pair_cost_total(intersect_bound(tdepths(g, xs)))
                } else if k >= xs.len() { 1 } else { fold_cost(tdepths(g, xs), k, abs_peek(stack, 0)) },
            ActionShape::CleanIf(_, _) => 1 + clean_cost(if_bound(abs_peek(stack, 1), abs_peek(stack, 0))),
            ActionShape::NotResult => 1 + not_cost(abs_peek(stack, 0)),
            ActionShape::AppendResult(_) => 1 + append_cost(abs_peek(stack, 0)),
        }
    }

    pub open spec fn action_next(g: model::Graph, task: ActionShape, stack: Seq<nat>) -> Seq<nat> {
        match task {
            ActionShape::Clean(id, _) => stack.push(tdepth(g, id)),
            ActionShape::Not(id) => stack.push(n4(tdepth(g, id))),
            ActionShape::Append(id, _) => stack.push(2 * tdepth(g, id) + 1),
            ActionShape::Pair(a, b) => stack.push(pair_bound(tdepth(g, a), tdepth(g, b))),
            ActionShape::Union(n) => abs_pop(stack, n).push(union_bound(abs_top(stack, n))),
            ActionShape::Intersect(n) => abs_pop(stack, n).push(intersect_bound(abs_top(stack, n))),
            ActionShape::Fold(xs, k) => if k == 0 { stack.push(intersect_bound(tdepths(g, xs))) }
                else if k >= xs.len() { stack }
                else { abs_pop(stack, 1).push(fold_bound(tdepths(g, xs), k, abs_peek(stack, 0))) },
            ActionShape::If(_) => abs_pop(stack, 2).push(if_bound(abs_peek(stack, 1), abs_peek(stack, 0))),
            ActionShape::CleanIf(_, _) => abs_pop(stack, 2).push(if_bound(abs_peek(stack, 1), abs_peek(stack, 0))),
            ActionShape::NotResult => abs_pop(stack, 1).push(n4(abs_peek(stack, 0))),
            ActionShape::AppendResult(_) => abs_pop(stack, 1).push(2 * abs_peek(stack, 0) + 1),
            ActionShape::SwapThen => abs_pop(stack, 2).push(abs_peek(stack, 0)).push(abs_peek(stack, 1)),
        }
    }

    /// Runs `tasks` (top = last) over an abstract stack of depth bounds; returns total cost and final stack.
    pub open spec fn machine_run(g: model::Graph, tasks: Seq<ActionShape>, stack: Seq<nat>) -> (nat, Seq<nat>)
        decreases tasks.len(),
    {
        if tasks.len() == 0 { (0, stack) } else {
            let rest = machine_run(g, tasks.drop_last(), action_next(g, tasks.last(), stack));
            (action_cost(g, tasks.last(), stack) + rest.0, rest.1)
        }
    }

    /// Termination measure of `transition_machine`.
    pub open spec fn machine_cost(g: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>) -> nat {
        machine_run(g, tasks, value_depths(g, values)).0
    }

    /// One machine step strictly lowers `machine_cost`: `task` was popped from `tasks0`.
    pub open spec fn machine_progress(
        g0: model::Graph, tasks0: Seq<ActionShape>, task: ActionShape, v0: Seq<TransitionId>,
        g1: model::Graph, tasks1: Seq<ActionShape>, v1: Seq<TransitionId>,
    ) -> bool {
        machine_cost(g1, tasks1, v1) < machine_cost(g0, tasks0.push(task), v0)
    }

    pub proof fn le_pointwise_push(s1: Seq<nat>, s2: Seq<nat>, x: nat, y: nat)
        requires le_pointwise(s1, s2), x <= y,
        ensures le_pointwise(s1.push(x), s2.push(y)),
    {
        assert forall|i: int| 0 <= i < s1.push(x).len() implies #[trigger] s1.push(x)[i] <= s2.push(y)[i] by {
            if i < s1.len() { assert(s1[i] <= s2[i]); }
        }
    }

    pub proof fn le_pointwise_refl(s: Seq<nat>)
        ensures le_pointwise(s, s),
    {}

    pub proof fn machine_lemma_stack_mono(s1: Seq<nat>, s2: Seq<nat>, k: nat)
        requires le_pointwise(s1, s2),
        ensures le_pointwise(abs_top(s1, k), abs_top(s2, k)), le_pointwise(abs_pop(s1, k), abs_pop(s2, k)),
            abs_peek(s1, k) <= abs_peek(s2, k),
    {
        assert forall|i: int| 0 <= i < abs_top(s1, k).len() implies #[trigger] abs_top(s1, k)[i] <= abs_top(s2, k)[i] by {
            let j = s1.len() - k + i;
            if 0 <= j < s1.len() { assert(s1[j] <= s2[j]); }
        }
        assert forall|i: int| 0 <= i < abs_pop(s1, k).len() implies #[trigger] abs_pop(s1, k)[i] <= abs_pop(s2, k)[i] by {
            assert(s1[i] <= s2[i]);
        }
        let j = s1.len() - 1 - k;
        if 0 <= j < s1.len() { assert(s1[j] <= s2[j]); }
    }

    pub proof fn machine_lemma_action_mono(g: model::Graph, task: ActionShape, s1: Seq<nat>, s2: Seq<nat>)
        requires le_pointwise(s1, s2),
        ensures action_cost(g, task, s1) <= action_cost(g, task, s2),
            le_pointwise(action_next(g, task, s1), action_next(g, task, s2)),
    {
        machine_lemma_stack_mono(s1, s2, 0);
        machine_lemma_stack_mono(s1, s2, 1);
        machine_lemma_stack_mono(s1, s2, 2);
        let p0 = abs_peek(s1, 0);
        let q0 = abs_peek(s2, 0);
        let p1 = abs_peek(s1, 1);
        let q1 = abs_peek(s2, 1);
        match task {
            ActionShape::Clean(id, _) => { le_pointwise_push(s1, s2, tdepth(g, id), tdepth(g, id)); },
            ActionShape::Not(id) => { le_pointwise_push(s1, s2, n4(tdepth(g, id)), n4(tdepth(g, id))); },
            ActionShape::Append(id, _) => { le_pointwise_push(s1, s2, 2 * tdepth(g, id) + 1, 2 * tdepth(g, id) + 1); },
            ActionShape::Pair(a, b) => {
                let v = pair_bound(tdepth(g, a), tdepth(g, b));
                le_pointwise_push(s1, s2, v, v);
            },
            ActionShape::Union(n) => {
                machine_lemma_stack_mono(s1, s2, n);
                lemma_bounds_mono(abs_top(s1, n), abs_top(s2, n));
                le_pointwise_push(abs_pop(s1, n), abs_pop(s2, n), union_bound(abs_top(s1, n)), union_bound(abs_top(s2, n)));
            },
            ActionShape::Intersect(n) => {
                machine_lemma_stack_mono(s1, s2, n);
                lemma_bounds_mono(abs_top(s1, n), abs_top(s2, n));
                lemma_pair_cost_total_mono(intersect_bound(abs_top(s1, n)), intersect_bound(abs_top(s2, n)));
                le_pointwise_push(abs_pop(s1, n), abs_pop(s2, n),
                    intersect_bound(abs_top(s1, n)), intersect_bound(abs_top(s2, n)));
            },
            ActionShape::Fold(xs, k) => {
                let ds = tdepths(g, xs);
                if k == 0 {
                    le_pointwise_push(s1, s2, intersect_bound(ds), intersect_bound(ds));
                } else if k < xs.len() {
                    lemma_fold_mono(ds, k, p0, q0);
                    le_pointwise_push(abs_pop(s1, 1), abs_pop(s2, 1), fold_bound(ds, k, p0), fold_bound(ds, k, q0));
                }
            },
            ActionShape::If(_) => {
                le_pointwise_push(abs_pop(s1, 2), abs_pop(s2, 2), if_bound(p1, p0), if_bound(q1, q0));
            },
            ActionShape::CleanIf(_, _) => {
                lemma_clean_cost_mono(if_bound(p1, p0), if_bound(q1, q0));
                le_pointwise_push(abs_pop(s1, 2), abs_pop(s2, 2), if_bound(p1, p0), if_bound(q1, q0));
            },
            ActionShape::NotResult => {
                lemma_not_cost_mono(p0, q0);
                lemma_n4_mono(p0, q0);
                le_pointwise_push(abs_pop(s1, 1), abs_pop(s2, 1), n4(p0), n4(q0));
            },
            ActionShape::AppendResult(_) => {
                lemma_append_cost_mono(p0, q0);
                le_pointwise_push(abs_pop(s1, 1), abs_pop(s2, 1), 2 * p0 + 1, 2 * q0 + 1);
            },
            ActionShape::SwapThen => {
                le_pointwise_push(abs_pop(s1, 2), abs_pop(s2, 2), p0, q0);
                le_pointwise_push(abs_pop(s1, 2).push(p0), abs_pop(s2, 2).push(q0), p1, q1);
            },
        }
    }

    pub proof fn machine_lemma_run_mono(g: model::Graph, tasks: Seq<ActionShape>, s1: Seq<nat>, s2: Seq<nat>)
        requires le_pointwise(s1, s2),
        ensures machine_run(g, tasks, s1).0 <= machine_run(g, tasks, s2).0,
            le_pointwise(machine_run(g, tasks, s1).1, machine_run(g, tasks, s2).1),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            machine_lemma_action_mono(g, tasks.last(), s1, s2);
            machine_lemma_run_mono(g, tasks.drop_last(), action_next(g, tasks.last(), s1), action_next(g, tasks.last(), s2));
        }
    }

    pub proof fn machine_lemma_run_split(g: model::Graph, pre: Seq<ActionShape>, post: Seq<ActionShape>, s: Seq<nat>)
        ensures machine_run(g, pre + post, s).0
                == machine_run(g, post, s).0 + machine_run(g, pre, machine_run(g, post, s).1).0,
            machine_run(g, pre + post, s).1 == machine_run(g, pre, machine_run(g, post, s).1).1,
        decreases post.len(),
    {
        if post.len() == 0 {
            assert(pre + post =~= pre);
        } else {
            assert((pre + post).drop_last() =~= pre + post.drop_last());
            assert((pre + post).last() == post.last());
            machine_lemma_run_split(g, pre, post.drop_last(), action_next(g, post.last(), s));
        }
    }

    pub proof fn machine_lemma_action_extends(g0: model::Graph, g1: model::Graph, task: ActionShape, s: Seq<nat>)
        requires model::graph_extends(g0, g1), transition_action_valid(g0, task),
        ensures action_cost(g0, task, s) == action_cost(g1, task, s), action_next(g0, task, s) == action_next(g1, task, s),
    {
        match task {
            ActionShape::Clean(id, _) => { tdepth_lemma_extends(g0, g1, id); },
            ActionShape::Not(id) => { tdepth_lemma_extends(g0, g1, id); },
            ActionShape::Append(id, _) => { tdepth_lemma_extends(g0, g1, id); },
            ActionShape::Pair(a, b) => { tdepth_lemma_extends(g0, g1, a); tdepth_lemma_extends(g0, g1, b); },
            ActionShape::Fold(xs, _) => { tdepths_lemma_extends(g0, g1, xs); },
            _ => {},
        }
    }

    pub proof fn machine_lemma_run_extends(g0: model::Graph, g1: model::Graph, tasks: Seq<ActionShape>, s: Seq<nat>)
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, tasks),
        ensures machine_run(g0, tasks, s) == machine_run(g1, tasks, s),
        decreases tasks.len(),
    {
        if tasks.len() > 0 {
            let t = tasks.last();
            assert(transition_action_valid(g0, tasks[tasks.len() - 1]));
            machine_lemma_action_extends(g0, g1, t, s);
            assert forall|i: int| 0 <= i < tasks.drop_last().len() implies transition_action_valid(g0, #[trigger] tasks.drop_last()[i]) by {
                assert(tasks.drop_last()[i] == tasks[i]);
            }
            machine_lemma_run_extends(g0, g1, tasks.drop_last(), action_next(g0, t, s));
        }
    }

    /// One machine step: popping `task` and pushing `added` lowers the measure when the local run of
    /// `added` is cheaper than `task` and leaves a pointwise smaller stack.
    pub proof fn machine_lemma_step(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, task: ActionShape,
        added: Seq<ActionShape>, v0: Seq<TransitionId>, v1: Seq<TransitionId>,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            machine_run(g1, added, value_depths(g1, v1)).0 < action_cost(g0, task, value_depths(g0, v0)),
            le_pointwise(machine_run(g1, added, value_depths(g1, v1)).1, action_next(g0, task, value_depths(g0, v0))),
        ensures machine_cost(g1, pending + added, v1) < machine_cost(g0, pending.push(task), v0),
    {
        let s0 = value_depths(g0, v0);
        let r = machine_run(g1, added, value_depths(g1, v1));
        let next = action_next(g0, task, s0);
        assert(pending.push(task).drop_last() =~= pending);
        machine_lemma_run_split(g1, pending, added, value_depths(g1, v1));
        machine_lemma_run_mono(g1, pending, r.1, next);
        machine_lemma_run_extends(g0, g1, pending, next);
    }

    /// A step that only pushes one value bounded by the task's abstract result.
    pub proof fn machine_lemma_push(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, task: ActionShape,
        v0: Seq<TransitionId>, out: TransitionId, bound: nat,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending), transition_ids_valid(g0, v0),
            action_cost(g0, task, value_depths(g0, v0)) >= 1,
            action_next(g0, task, value_depths(g0, v0)) == value_depths(g0, v0).push(bound),
            tdepth(g1, out@) <= bound,
        ensures machine_cost(g1, pending, v0.push(out)) < machine_cost(g0, pending.push(task), v0),
    {
        value_depths_lemma_extends(g0, g1, v0);
        assert(value_depths(g1, v0.push(out)) =~= value_depths(g1, v0).push(tdepth(g1, out@)));
        le_pointwise_push(value_depths(g0, v0), value_depths(g0, v0), tdepth(g1, out@), bound);
        assert(pending + Seq::<ActionShape>::empty() =~= pending);
        machine_lemma_step(g0, g1, pending, task, Seq::empty(), v0, v0.push(out));
    }

    // ----- child task lists -----

    pub open spec fn child_shapes(cs: Seq<nat>, action: ChildShape) -> Seq<ActionShape> {
        cs.reverse().map(|i: int, child: nat| transition_child_shape(action, child))
    }

    pub open spec fn child_cost_fn(g: model::Graph, action: ChildShape) -> spec_fn(nat) -> nat {
        match action {
            ChildShape::Clean(_) => clean_cost_fn(),
            ChildShape::Not => not_cost_fn(),
            ChildShape::Append(_) => append_cost_fn(),
            ChildShape::PairLeft(other) => pair_cost_left_fn(tdepth(g, other)),
            ChildShape::PairRight(other) => pair_cost_right_fn(tdepth(g, other)),
        }
    }

    pub open spec fn child_bound(g: model::Graph, action: ChildShape, d: nat) -> nat {
        match action {
            ChildShape::Clean(_) => d,
            ChildShape::Not => n4(d),
            ChildShape::Append(_) => 2 * d + 1,
            ChildShape::PairLeft(other) => pair_bound(d, tdepth(g, other)),
            ChildShape::PairRight(other) => pair_bound(tdepth(g, other), d),
        }
    }

    pub open spec fn child_bounds(g: model::Graph, action: ChildShape, ds: Seq<nat>) -> Seq<nat> {
        Seq::new(ds.len(), |i: int| child_bound(g, action, ds[i]))
    }

    pub proof fn lemma_sum_map_front(f: spec_fn(nat) -> nat, ds: Seq<nat>)
        requires ds.len() > 0,
        ensures sum_map(f, ds) == f(ds[0]) + sum_map(f, ds.drop_first()),
        decreases ds.len(),
    {
        if ds.len() == 1 {
            assert(ds.drop_last().len() == 0);
            assert(ds.drop_first().len() == 0);
            assert(sum_map(f, ds.drop_last()) == 0);
            assert(sum_map(f, ds.drop_first()) == 0);
            assert(ds.last() == ds[0]);
        } else {
            let init = ds.drop_last();
            lemma_sum_map_front(f, init);
            assert(init[0] == ds[0]);
            assert(init.drop_first() =~= ds.drop_first().drop_last());
            assert(ds.drop_first().last() == ds.last());
            assert(sum_map(f, ds.drop_first())
                == sum_map(f, ds.drop_first().drop_last()) + f(ds.drop_first().last()));
        }
    }

    pub proof fn machine_lemma_children_run(g: model::Graph, cs: Seq<nat>, action: ChildShape, s: Seq<nat>)
        ensures machine_run(g, child_shapes(cs, action), s)
            == (sum_map(child_cost_fn(g, action), tdepths(g, cs)), s + child_bounds(g, action, tdepths(g, cs))),
        decreases cs.len(),
    {
        let shapes = child_shapes(cs, action);
        let ds = tdepths(g, cs);
        let f = child_cost_fn(g, action);
        if cs.len() == 0 {
            assert(s + child_bounds(g, action, ds) =~= s);
        } else {
            let rest = cs.drop_first();
            assert(shapes.last() == transition_child_shape(action, cs[0]));
            assert(shapes.drop_last() =~= child_shapes(rest, action));
            let b0 = child_bound(g, action, ds[0]);
            assert(action_cost(g, shapes.last(), s) == f(ds[0]));
            assert(action_next(g, shapes.last(), s) == s.push(b0));
            machine_lemma_children_run(g, rest, action, s.push(b0));
            assert(tdepths(g, rest) =~= ds.drop_first());
            lemma_sum_map_front(f, ds);
            assert(s.push(b0) + child_bounds(g, action, tdepths(g, rest)) =~= s + child_bounds(g, action, ds));
        }
    }

    /// Running `[Union(n)/Intersect(n)] + children(action)` over `s`.
    pub proof fn machine_lemma_set_run(g: model::Graph, id: nat, action: ChildShape, intersect: bool, s: Seq<nat>)
        requires model::graph_wf(g), id < g.transitions.len(),
        ensures ({
            let cs = transition_children(g, id);
            let ds = tdepths(g, cs);
            let bs = child_bounds(g, action, ds);
            let marker = if intersect { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) };
            let r = machine_run(g, seq![marker] + transition_child_actions(g, id, action), s);
            &&& r.0 == sum_map(child_cost_fn(g, action), ds)
                + (if intersect { 2 + intersect_bound(bs) + pair_cost_total(intersect_bound(bs)) } else { 1 })
            &&& r.1 == s.push(if intersect { intersect_bound(bs) } else { union_bound(bs) })
        }),
    {
        let cs = transition_children(g, id);
        let ds = tdepths(g, cs);
        let bs = child_bounds(g, action, ds);
        let marker = if intersect { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) };
        assert(transition_child_actions(g, id, action) =~= child_shapes(cs, action));
        machine_lemma_children_run(g, cs, action, s);
        machine_lemma_run_split(g, seq![marker], child_shapes(cs, action), s);
        let t = s + bs;
        assert(abs_top(t, cs.len()) =~= bs);
        assert(abs_pop(t, cs.len()) =~= s);
        assert(seq![marker].drop_last() =~= Seq::<ActionShape>::empty());
        assert(seq![marker].last() == marker);
        let next = action_next(g, marker, t);
        assert(machine_run(g, Seq::<ActionShape>::empty(), next) == (0nat, next));
        assert(machine_run(g, seq![marker], t) == (action_cost(g, marker, t), next));
    }

    pub proof fn graph_lemma_extends_refl(g: model::Graph)
        ensures model::graph_extends(g, g),
    {
        assert(g.tests.subrange(0, g.tests.len() as int) =~= g.tests);
        assert(g.regexes.subrange(0, g.regexes.len() as int) =~= g.regexes);
        assert(g.transitions.subrange(0, g.transitions.len() as int) =~= g.transitions);
    }

    pub proof fn machine_lemma_run1(g: model::Graph, t: ActionShape, s: Seq<nat>)
        ensures machine_run(g, seq![t], s) == (action_cost(g, t, s), action_next(g, t, s)),
    {
        assert(seq![t].drop_last() =~= Seq::<ActionShape>::empty());
        assert(seq![t].last() == t);
        assert(machine_run(g, Seq::<ActionShape>::empty(), action_next(g, t, s)) == (0nat, action_next(g, t, s)));
    }

    pub proof fn machine_lemma_run2(g: model::Graph, t1: ActionShape, t2: ActionShape, s: Seq<nat>)
        ensures machine_run(g, seq![t1, t2], s) == (action_cost(g, t2, s) + action_cost(g, t1, action_next(g, t2, s)),
            action_next(g, t1, action_next(g, t2, s))),
    {
        assert(seq![t1, t2].drop_last() =~= seq![t1]);
        assert(seq![t1, t2].last() == t2);
        machine_lemma_run1(g, t1, action_next(g, t2, s));
    }

    pub proof fn machine_lemma_run3(g: model::Graph, t1: ActionShape, t2: ActionShape, t3: ActionShape, s: Seq<nat>)
        ensures ({
            let s1 = action_next(g, t3, s);
            let s2 = action_next(g, t2, s1);
            machine_run(g, seq![t1, t2, t3], s)
                == (action_cost(g, t3, s) + action_cost(g, t2, s1) + action_cost(g, t1, s2), action_next(g, t1, s2))
        }),
    {
        assert(seq![t1, t2, t3].drop_last() =~= seq![t1, t2]);
        assert(seq![t1, t2, t3].last() == t3);
        machine_lemma_run2(g, t1, t2, action_next(g, t3, s));
    }

    pub open spec fn value_bound(g: model::Graph, task: ActionShape) -> nat {
        match task {
            ActionShape::Clean(id, _) => tdepth(g, id),
            ActionShape::Not(id) => n4(tdepth(g, id)),
            ActionShape::Append(id, _) => 2 * tdepth(g, id) + 1,
            ActionShape::Pair(a, b) => pair_bound(tdepth(g, a), tdepth(g, b)),
            _ => 0,
        }
    }

    pub open spec fn value_task(task: ActionShape) -> bool {
        task is Clean || task is Not || task is Append || task is Pair
    }

    /// A value-producing task (`Clean`/`Not`/`Append`/`Pair`) that directly pushes `out`.
    pub proof fn machine_value_result(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, task: ActionShape,
        v0: Seq<TransitionId>, out: TransitionId,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending), transition_ids_valid(g0, v0),
            value_task(task),
            tdepth(g1, out@) <= value_bound(g0, task)
                || (out@ < g1.transitions.len() && g1.transitions[out@ as int] is Const),
        ensures machine_cost(g1, pending, v0.push(out)) < machine_cost(g0, pending.push(task), v0),
    {
        match task {
            ActionShape::Clean(id, _) => { lemma_costs_pos(tdepth(g0, id)); tdepth_lemma_pos(g0, id); },
            ActionShape::Not(id) => { lemma_costs_pos(tdepth(g0, id)); lemma_n4_pos(tdepth(g0, id)); },
            ActionShape::Append(id, _) => { lemma_costs_pos(tdepth(g0, id)); },
            ActionShape::Pair(a, b) => {
                lemma_pair_cost_mono(tdepth(g0, a), tdepth(g0, b), tdepth(g0, a), tdepth(g0, b));
                tdepth_lemma_pos(g0, a);
                assert(tdepth(g0, a) * tdepth(g0, b) >= 0) by (nonlinear_arith);
            },
            _ => {},
        }
        if out@ < g1.transitions.len() && g1.transitions[out@ as int] is Const { tdepth_lemma_const(g1, out@); }
        machine_lemma_push(g0, g1, pending, task, v0, out, value_bound(g0, task));
    }

    // ----- Clean -----

    pub proof fn machine_clean_if(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, path: TestId,
        test: TestId, a: TransitionId, b: TransitionId, yes: TestId, no: TestId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            g0.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
        ensures machine_cost(g1, transition_clean_if_tasks(g1, test, a, b, yes, no, pending), v0)
            < machine_cost(g0, pending.push(ActionShape::Clean(id@, path@)), v0),
    {
        model::lemma_graph_transition_wf(g0, id@);
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_extends(g0, g1, a@);
        tdepth_lemma_extends(g0, g1, b@);
        tdepth_lemma_pos(g0, a@);
        tdepth_lemma_pos(g0, b@);
        let da = tdepth(g0, a@);
        let db = tdepth(g0, b@);
        let d = tdepth(g0, id@);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let task = ActionShape::Clean(id@, path@);
        lemma_clean_cost_mono(da, (d - 1) as nat);
        lemma_clean_cost_mono(db, (d - 1) as nat);
        let tasks = transition_clean_if_tasks(g1, test, a, b, yes, no, pending);
        if yes@ == g1.constants.test_false {
            let added = seq![ActionShape::Clean(b@, no@)];
            assert(tasks =~= pending + added);
            machine_lemma_run1(g1, added[0], s0);
            le_pointwise_push(s0, s0, db, d);
            machine_lemma_step(g0, g1, pending, task, added, v0, v0);
        } else if no@ == g1.constants.test_false {
            let added = seq![ActionShape::Clean(a@, yes@)];
            assert(tasks =~= pending + added);
            machine_lemma_run1(g1, added[0], s0);
            le_pointwise_push(s0, s0, da, d);
            machine_lemma_step(g0, g1, pending, task, added, v0, v0);
        } else {
            let added = seq![ActionShape::If(test@), ActionShape::Clean(b@, no@), ActionShape::Clean(a@, yes@)];
            assert(tasks =~= pending + added);
            machine_lemma_run3(g1, added[0], added[1], added[2], s0);
            let s2 = s0.push(da).push(db);
            assert(abs_pop(s2, 2) =~= s0);
            assert(abs_peek(s2, 1) == da);
            assert(abs_peek(s2, 0) == db);
            le_pointwise_push(s0, s0, d, d);
            machine_lemma_step(g0, g1, pending, task, added, v0, v0);
        }
    }

    pub proof fn machine_clean_children(
        g: model::Graph, pending: Seq<ActionShape>, id: TransitionId, path: TestId, intersect: bool, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g), transition_tasks_valid(g, pending), transition_ids_valid(g, v0),
            id@ < g.transitions.len(),
            match g.transitions[id@ as int] {
                model::TransitionNode::Union(_) => !intersect,
                model::TransitionNode::Intersect(_) => intersect,
                _ => false,
            },
        ensures machine_cost(g, transition_clean_child_tasks(g, id, path, intersect, pending), v0)
            < machine_cost(g, pending.push(ActionShape::Clean(id@, path@)), v0),
    {
        transition_lemma_children(g, id@);
        tdepth_lemma_unfold(g, id@);
        graph_lemma_extends_refl(g);
        let cs = transition_children(g, id@);
        let ds = tdepths(g, cs);
        tdepths_lemma_pos(g, cs);
        let action = ChildShape::Clean(path@);
        let marker = if intersect { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) };
        let added = seq![marker] + transition_child_actions(g, id@, action);
        assert(transition_clean_child_tasks(g, id, path, intersect, pending) =~= pending + added);
        let s0 = value_depths(g, v0);
        machine_lemma_set_run(g, id@, action, intersect, s0);
        assert(child_bounds(g, action, ds) =~= ds);
        lemma_clean_sum(ds);
        lemma_bounds_pos(ds);
        let d = tdepth(g, id@);
        le_pointwise_push(s0, s0, d, d);
        machine_lemma_step(g, g, pending, ActionShape::Clean(id@, path@), added, v0, v0);
    }

    pub proof fn machine_clean_not(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, path: TestId,
        inner: TransitionId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            g0.transitions[id@ as int] == model::TransitionNode::Not(inner@),
        ensures machine_cost(g1, pending.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@)), v0)
            < machine_cost(g0, pending.push(ActionShape::Clean(id@, path@)), v0),
    {
        model::lemma_graph_transition_wf(g0, id@);
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_extends(g0, g1, inner@);
        tdepth_lemma_pos(g0, inner@);
        let dc = tdepth(g0, inner@);
        let d = tdepth(g0, id@);
        lemma_n4_pos(dc);
        lemma_n4_mono(1, dc);
        assert(n4(1) == 4 * n4(0));
        lemma_log4_n4(dc);
        lemma_clean_cost_mono(dc, (d - 1) as nat);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::NotResult, ActionShape::Clean(inner@, path@)];
        assert(pending.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@)) =~= pending + added);
        machine_lemma_run2(g1, added[0], added[1], s0);
        assert(abs_peek(s0.push(dc), 0) == dc);
        assert(abs_pop(s0.push(dc), 1) =~= s0);
        le_pointwise_push(s0, s0, d, d);
        machine_lemma_step(g0, g1, pending, ActionShape::Clean(id@, path@), added, v0, v0);
    }

    pub proof fn machine_clean_append(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, path: TestId,
        inner: TransitionId, r: RegexId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            match g0.transitions[id@ as int] { model::TransitionNode::Append(c, _) => c == inner@, _ => false },
        ensures machine_cost(g1, pending.push(ActionShape::AppendResult(r@)).push(ActionShape::Clean(inner@, path@)), v0)
            < machine_cost(g0, pending.push(ActionShape::Clean(id@, path@)), v0),
    {
        model::lemma_graph_transition_wf(g0, id@);
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_extends(g0, g1, inner@);
        tdepth_lemma_pos(g0, inner@);
        let dc = tdepth(g0, inner@);
        let d = tdepth(g0, id@);
        assert(((d - 1) as nat) / 2 == dc);
        lemma_clean_cost_mono(dc, (d - 1) as nat);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::AppendResult(r@), ActionShape::Clean(inner@, path@)];
        assert(pending.push(ActionShape::AppendResult(r@)).push(ActionShape::Clean(inner@, path@)) =~= pending + added);
        machine_lemma_run2(g1, added[0], added[1], s0);
        assert(abs_peek(s0.push(dc), 0) == dc);
        assert(abs_pop(s0.push(dc), 1) =~= s0);
        le_pointwise_push(s0, s0, d, d);
        machine_lemma_step(g0, g1, pending, ActionShape::Clean(id@, path@), added, v0, v0);
    }

    // ----- Not / Append -----

    pub proof fn machine_not_double(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, inner: TransitionId,
        v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            g0.transitions[id@ as int] == model::TransitionNode::Not(inner@),
        ensures machine_cost(g1, pending, v0.push(inner)) < machine_cost(g0, pending.push(ActionShape::Not(id@)), v0),
    {
        model::lemma_graph_transition_wf(g0, id@);
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_extends(g0, g1, inner@);
        lemma_n4_pos(tdepth(g0, inner@));
        lemma_n4_pos(tdepth(g0, id@));
        machine_value_result(g0, g1, pending, ActionShape::Not(id@), v0, inner);
    }

    /// `out` is a freshly interned `Not(id)` / `Append(id, _)` node.
    pub proof fn machine_wrap_interned(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, task: ActionShape,
        v0: Seq<TransitionId>, out: TransitionId,
    )
        requires model::graph_wf(g1), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), transition_action_valid(g0, task), out@ < g1.transitions.len(),
            match task {
                ActionShape::Not(id) => g1.transitions[out@ as int] == model::TransitionNode::Not(id),
                ActionShape::Append(id, _) => match g1.transitions[out@ as int] {
                    model::TransitionNode::Append(c, _) => c == id,
                    _ => false,
                },
                _ => false,
            },
        ensures machine_cost(g1, pending, v0.push(out)) < machine_cost(g0, pending.push(task), v0),
    {
        tdepth_lemma_unfold(g1, out@);
        match task {
            ActionShape::Not(id) => { tdepth_lemma_extends(g0, g1, id); },
            ActionShape::Append(id, _) => { tdepth_lemma_extends(g0, g1, id); },
            _ => {},
        }
        machine_value_result(g0, g1, pending, task, v0, out);
    }

    pub proof fn machine_not_flip(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, test: TestId,
        a: TransitionId, b: TransitionId, out: TransitionId, path: TestId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            g0.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
            a@ == g0.constants.transition_all, b@ == g0.constants.transition_empty,
            out@ < g1.transitions.len(), tdepth(g1, out@) <= 2,
        ensures machine_cost(g1, pending.push(ActionShape::Clean(out@, path@)), v0)
            < machine_cost(g0, pending.push(ActionShape::Not(id@)), v0),
    {
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_constants(g0);
        let d = tdepth(g0, id@);
        assert(d == 2);
        lemma_n4_pos(2);
        lemma_clean_cost_mono(tdepth(g1, out@), 2);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::Clean(out@, path@)];
        assert(pending.push(ActionShape::Clean(out@, path@)) =~= pending + added);
        machine_lemma_run1(g1, added[0], s0);
        le_pointwise_push(s0, s0, tdepth(g1, out@), n4(d));
        machine_lemma_step(g0, g1, pending, ActionShape::Not(id@), added, v0, v0);
    }

    pub open spec fn unary_task(id: TransitionId, suffix: Option<RegexId>) -> ActionShape {
        match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) }
    }

    pub proof fn machine_unary_if(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, test: TestId,
        a: TransitionId, b: TransitionId, suffix: Option<RegexId>, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            g0.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
        ensures machine_cost(g1, machine_unary_if_tasks(g1, test, a, b, suffix, pending), v0)
            < machine_cost(g0, pending.push(unary_task(id, suffix)), v0),
    {
        model::lemma_graph_transition_wf(g0, id@);
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_extends(g0, g1, a@);
        tdepth_lemma_extends(g0, g1, b@);
        tdepth_lemma_pos(g0, a@);
        tdepth_lemma_pos(g0, b@);
        let da = tdepth(g0, a@);
        let db = tdepth(g0, b@);
        let d = tdepth(g0, id@);
        let m = (d - 1) as nat;
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let task = unary_task(id, suffix);
        let added = seq![
            ActionShape::CleanIf(test@, g1.constants.test_true),
            match suffix { Some(r) => ActionShape::Append(b@, r@), None => ActionShape::Not(b@) },
            match suffix { Some(r) => ActionShape::Append(a@, r@), None => ActionShape::Not(a@) }];
        assert(machine_unary_if_tasks(g1, test, a, b, suffix, pending) =~= pending + added);
        machine_lemma_run3(g1, added[0], added[1], added[2], s0);
        match suffix {
            Some(r) => {
                let s2 = s0.push(2 * da + 1).push(2 * db + 1);
                assert(abs_pop(s2, 2) =~= s0);
                assert(abs_peek(s2, 1) == 2 * da + 1);
                assert(abs_peek(s2, 0) == 2 * db + 1);
                let ib = if_bound(2 * da + 1, 2 * db + 1);
                assert(ib <= 2 * d);
                lemma_append_cost_mono(da, m);
                lemma_append_cost_mono(db, m);
                lemma_clean_cost_mono(ib, 2 * d);
                le_pointwise_push(s0, s0, ib, 2 * d + 1);
            },
            None => {
                let s2 = s0.push(n4(da)).push(n4(db));
                assert(abs_pop(s2, 2) =~= s0);
                assert(abs_peek(s2, 1) == n4(da));
                assert(abs_peek(s2, 0) == n4(db));
                let ib = if_bound(n4(da), n4(db));
                lemma_n4_mono(da, m);
                lemma_n4_mono(db, m);
                lemma_n4_pos(m);
                assert(n4(d) == 4 * n4(m));
                lemma_not_cost_mono(da, m);
                lemma_not_cost_mono(db, m);
                lemma_clean_cost_mono(ib, 1 + n4(m));
                le_pointwise_push(s0, s0, ib, n4(d));
            },
        }
        machine_lemma_step(g0, g1, pending, task, added, v0, v0);
    }

    pub proof fn machine_unary_children(
        g: model::Graph, pending: Seq<ActionShape>, id: TransitionId, suffix: Option<RegexId>, intersect: bool,
        v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g), transition_tasks_valid(g, pending), transition_ids_valid(g, v0),
            id@ < g.transitions.len(),
            match g.transitions[id@ as int] {
                model::TransitionNode::Union(_) => intersect == (suffix is None),
                model::TransitionNode::Intersect(_) => !intersect && suffix is None,
                _ => false,
            },
        ensures machine_cost(g, machine_unary_child_tasks(g, id, suffix, intersect, pending), v0)
            < machine_cost(g, pending.push(unary_task(id, suffix)), v0),
    {
        transition_lemma_children(g, id@);
        tdepth_lemma_unfold(g, id@);
        graph_lemma_extends_refl(g);
        let cs = transition_children(g, id@);
        let ds = tdepths(g, cs);
        tdepths_lemma_pos(g, cs);
        lemma_bounds_pos(ds);
        let d = tdepth(g, id@);
        let action = match suffix { Some(r) => ChildShape::Append(r@), None => ChildShape::Not };
        let marker = if intersect { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) };
        let added = seq![marker] + transition_child_actions(g, id@, action);
        assert(machine_unary_child_tasks(g, id, suffix, intersect, pending) =~= pending + added);
        let s0 = value_depths(g, v0);
        machine_lemma_set_run(g, id@, action, intersect, s0);
        let bs = child_bounds(g, action, ds);
        match suffix {
            Some(r) => {
                assert(bs =~= appends(ds));
                lemma_append_sum(ds);
                lemma_append_union(ds);
                le_pointwise_push(s0, s0, union_bound(bs), 2 * d + 1);
            },
            None => {
                assert(bs =~= n4s(ds));
                lemma_not_sum(ds);
                if intersect {
                    lemma_not_union(ds);
                    lemma_pair_cost_total_mono(intersect_bound(bs), (n4(d) - 1) as nat);
                    le_pointwise_push(s0, s0, intersect_bound(bs), n4(d));
                } else {
                    lemma_not_intersect(ds);
                    le_pointwise_push(s0, s0, union_bound(bs), n4(d));
                }
            },
        }
        machine_lemma_step(g, g, pending, unary_task(id, suffix), added, v0, v0);
    }

    pub proof fn machine_append_nested(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, id: TransitionId, r: RegexId,
        inner: TransitionId, combined: RegexId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), id@ < g0.transitions.len(),
            match g0.transitions[id@ as int] { model::TransitionNode::Append(c, _) => c == inner@, _ => false },
        ensures machine_cost(g1, pending.push(ActionShape::Append(inner@, combined@)), v0)
            < machine_cost(g0, pending.push(ActionShape::Append(id@, r@)), v0),
    {
        model::lemma_graph_transition_wf(g0, id@);
        tdepth_lemma_unfold(g0, id@);
        tdepth_lemma_extends(g0, g1, inner@);
        tdepth_lemma_pos(g0, inner@);
        let dc = tdepth(g0, inner@);
        let d = tdepth(g0, id@);
        lemma_append_cost_mono(dc, (d - 1) as nat);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::Append(inner@, combined@)];
        assert(pending.push(added[0]) =~= pending + added);
        machine_lemma_run1(g1, added[0], s0);
        le_pointwise_push(s0, s0, 2 * dc + 1, 2 * d + 1);
        machine_lemma_step(g0, g1, pending, ActionShape::Append(id@, r@), added, v0, v0);
    }

    // ----- Pair -----

    pub proof fn machine_pair_union(
        g: model::Graph, pending: Seq<ActionShape>, a: TransitionId, b: TransitionId, left: bool, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g), transition_tasks_valid(g, pending), transition_ids_valid(g, v0),
            a@ < g.transitions.len(), b@ < g.transitions.len(),
            g.transitions[if left { a@ as int } else { b@ as int }] is Union,
        ensures ({
            let id = if left { a@ } else { b@ };
            let action = if left { ChildShape::PairLeft(b@) } else { ChildShape::PairRight(a@) };
            machine_cost(g, pending.push(ActionShape::Union(transition_children(g, id).len()))
                + transition_child_actions(g, id, action), v0)
                < machine_cost(g, pending.push(ActionShape::Pair(a@, b@)), v0)
        }),
    {
        let id = if left { a@ } else { b@ };
        let action = if left { ChildShape::PairLeft(b@) } else { ChildShape::PairRight(a@) };
        transition_lemma_children(g, id);
        tdepth_lemma_unfold(g, id);
        graph_lemma_extends_refl(g);
        let cs = transition_children(g, id);
        let ds = tdepths(g, cs);
        tdepths_lemma_pos(g, cs);
        lemma_bounds_pos(ds);
        tdepth_lemma_pos(g, a@);
        tdepth_lemma_pos(g, b@);
        let x = tdepth(g, a@);
        let y = tdepth(g, b@);
        let marker = ActionShape::Union(cs.len());
        let added = seq![marker] + transition_child_actions(g, id, action);
        assert(pending.push(marker) + transition_child_actions(g, id, action) =~= pending + added);
        let s0 = value_depths(g, v0);
        machine_lemma_set_run(g, id, action, false, s0);
        let bs = child_bounds(g, action, ds);
        if left {
            assert(bs =~= pairs_left(ds, y));
            lemma_pair_left_sum(ds, y);
            lemma_pair_union_left(ds, y);
        } else {
            assert(bs =~= pairs_right(x, ds));
            lemma_pair_right_sum(x, ds);
            lemma_pair_union_right(x, ds);
        }
        le_pointwise_push(s0, s0, union_bound(bs), pair_bound(x, y));
        machine_lemma_step(g, g, pending, ActionShape::Pair(a@, b@), added, v0, v0);
    }

    pub proof fn lemma_pair_if_bound(x: nat, y: nat, p: nat, q: nat)
        requires x >= 1, p <= pair_bound((x - 1) as nat, y), q <= pair_bound((x - 1) as nat, y),
        ensures if_bound(p, q) <= x * (y + 1), x * (y + 1) <= pair_bound(x, y),
    {
        assert(pair_bound((x - 1) as nat, y) + 1 == x * (y + 1)) by (nonlinear_arith) requires x >= 1;
        assert(x * (y + 1) <= pair_bound(x, y)) by (nonlinear_arith);
    }

    pub proof fn machine_pair_split(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, a: TransitionId, b: TransitionId,
        test: TestId, t: TransitionId, e: TransitionId, path: TestId, left: bool, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), a@ < g0.transitions.len(), b@ < g0.transitions.len(),
            g0.transitions[if left { a@ as int } else { b@ as int }] == model::TransitionNode::If(test@, t@, e@),
        ensures machine_cost(g1, if left {
                pending.push(ActionShape::CleanIf(test@, path@)).push(ActionShape::Pair(e@, b@)).push(ActionShape::Pair(t@, b@))
            } else {
                pending.push(ActionShape::CleanIf(test@, path@)).push(ActionShape::Pair(a@, e@)).push(ActionShape::Pair(a@, t@))
            }, v0) < machine_cost(g0, pending.push(ActionShape::Pair(a@, b@)), v0),
    {
        if left {
            machine_pair_split_left(g0, g1, pending, a, b, test, t, e, path, v0);
        } else {
            machine_pair_split_right(g0, g1, pending, a, b, test, t, e, path, v0);
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn machine_pair_split_left(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, a: TransitionId, b: TransitionId,
        test: TestId, t: TransitionId, e: TransitionId, path: TestId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), a@ < g0.transitions.len(), b@ < g0.transitions.len(),
            g0.transitions[a@ as int] == model::TransitionNode::If(test@, t@, e@),
        ensures machine_cost(g1, pending.push(ActionShape::CleanIf(test@, path@)).push(ActionShape::Pair(e@, b@))
                .push(ActionShape::Pair(t@, b@)), v0) < machine_cost(g0, pending.push(ActionShape::Pair(a@, b@)), v0),
    {
        model::lemma_graph_transition_wf(g0, a@);
        tdepth_lemma_unfold(g0, a@);
        tdepth_lemma_extends(g0, g1, b@);
        tdepth_lemma_extends(g0, g1, t@);
        tdepth_lemma_extends(g0, g1, e@);
        tdepth_lemma_pos(g0, b@);
        tdepth_lemma_pos(g0, t@);
        tdepth_lemma_pos(g0, e@);
        let x = tdepth(g0, a@);
        let y = tdepth(g0, b@);
        let dt = tdepth(g0, t@);
        let de = tdepth(g0, e@);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::CleanIf(test@, path@), ActionShape::Pair(e@, b@), ActionShape::Pair(t@, b@)];
        assert(pending.push(added[0]).push(added[1]).push(added[2]) =~= pending + added);
        machine_lemma_run3(g1, added[0], added[1], added[2], s0);
        let p = pair_bound(dt, y);
        let q = pair_bound(de, y);
        let s2 = s0.push(p).push(q);
        assert(abs_pop(s2, 2) =~= s0);
        assert(abs_peek(s2, 1) == p);
        assert(abs_peek(s2, 0) == q);
        lemma_pair_bound_mono(dt, y, (x - 1) as nat, y);
        lemma_pair_bound_mono(de, y, (x - 1) as nat, y);
        lemma_pair_if_bound(x, y, p, q);
        lemma_pair_cost_mono(dt, y, (x - 1) as nat, y);
        lemma_pair_cost_mono(de, y, (x - 1) as nat, y);
        lemma_clean_cost_mono(if_bound(p, q), x * (y + 1));
        lemma_pair_split_cost(x, y, pair_cost(dt, y) + pair_cost(de, y) + 1 + clean_cost(if_bound(p, q)));
        le_pointwise_push(s0, s0, if_bound(p, q), pair_bound(x, y));
        machine_lemma_step(g0, g1, pending, ActionShape::Pair(a@, b@), added, v0, v0);
    }

    #[verifier::spinoff_prover]
    pub proof fn machine_pair_split_right(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, a: TransitionId, b: TransitionId,
        test: TestId, t: TransitionId, e: TransitionId, path: TestId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), a@ < g0.transitions.len(), b@ < g0.transitions.len(),
            g0.transitions[b@ as int] == model::TransitionNode::If(test@, t@, e@),
        ensures machine_cost(g1, pending.push(ActionShape::CleanIf(test@, path@)).push(ActionShape::Pair(a@, e@))
                .push(ActionShape::Pair(a@, t@)), v0) < machine_cost(g0, pending.push(ActionShape::Pair(a@, b@)), v0),
    {
        model::lemma_graph_transition_wf(g0, b@);
        tdepth_lemma_unfold(g0, b@);
        tdepth_lemma_extends(g0, g1, a@);
        tdepth_lemma_extends(g0, g1, t@);
        tdepth_lemma_extends(g0, g1, e@);
        tdepth_lemma_pos(g0, a@);
        tdepth_lemma_pos(g0, t@);
        tdepth_lemma_pos(g0, e@);
        let x = tdepth(g0, a@);
        let y = tdepth(g0, b@);
        let dt = tdepth(g0, t@);
        let de = tdepth(g0, e@);
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::CleanIf(test@, path@), ActionShape::Pair(a@, e@), ActionShape::Pair(a@, t@)];
        assert(pending.push(added[0]).push(added[1]).push(added[2]) =~= pending + added);
        machine_lemma_run3(g1, added[0], added[1], added[2], s0);
        let p = pair_bound(x, dt);
        let q = pair_bound(x, de);
        let s2 = s0.push(p).push(q);
        assert(abs_pop(s2, 2) =~= s0);
        assert(abs_peek(s2, 1) == p);
        assert(abs_peek(s2, 0) == q);
        lemma_pair_bound_comm(x, dt);
        lemma_pair_bound_comm(x, de);
        lemma_pair_bound_comm(x, y);
        lemma_pair_bound_mono(dt, x, (y - 1) as nat, x);
        lemma_pair_bound_mono(de, x, (y - 1) as nat, x);
        lemma_pair_if_bound(y, x, p, q);
        lemma_pair_cost_mono(x, dt, x, (y - 1) as nat);
        lemma_pair_cost_mono(x, de, x, (y - 1) as nat);
        lemma_clean_cost_mono(if_bound(p, q), y * (x + 1));
        lemma_pair_split_cost_right(x, y, pair_cost(x, dt) + pair_cost(x, de) + 1 + clean_cost(if_bound(p, q)));
        le_pointwise_push(s0, s0, if_bound(p, q), pair_bound(x, y));
        machine_lemma_step(g0, g1, pending, ActionShape::Pair(a@, b@), added, v0, v0);
    }

    pub proof fn lemma_pair_split_cost(x: nat, y: nat, c: nat)
        requires x >= 2, y >= 1, c <= 2 * pair_cost((x - 1) as nat, y) + 1 + clean_cost(x * (y + 1)),
        ensures c < pair_cost(x, y),
    {}

    pub proof fn lemma_pair_split_cost_right(x: nat, y: nat, c: nat)
        requires x >= 1, y >= 2, c <= 2 * pair_cost(x, (y - 1) as nat) + 1 + clean_cost(y * (x + 1)),
        ensures c < pair_cost(x, y),
    {}

    pub proof fn machine_pair_both(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, a: TransitionId, b: TransitionId,
        x: TestId, xt: TransitionId, xe: TransitionId, y: TestId, yt: TransitionId, ye: TransitionId,
        path: TestId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), a@ < g0.transitions.len(), b@ < g0.transitions.len(),
            g0.transitions[a@ as int] == model::TransitionNode::If(x@, xt@, xe@),
            g0.transitions[b@ as int] == model::TransitionNode::If(y@, yt@, ye@),
        ensures machine_cost(g1, pending.push(ActionShape::CleanIf(x@, path@))
                .push(ActionShape::Pair(xe@, ye@)).push(ActionShape::Pair(xt@, yt@)), v0)
            < machine_cost(g0, pending.push(ActionShape::Pair(a@, b@)), v0),
    {
        model::lemma_graph_transition_wf(g0, a@);
        model::lemma_graph_transition_wf(g0, b@);
        tdepth_lemma_unfold(g0, a@);
        tdepth_lemma_unfold(g0, b@);
        tdepth_lemma_extends(g0, g1, xt@);
        tdepth_lemma_extends(g0, g1, xe@);
        tdepth_lemma_extends(g0, g1, yt@);
        tdepth_lemma_extends(g0, g1, ye@);
        tdepth_lemma_pos(g0, xt@);
        tdepth_lemma_pos(g0, xe@);
        tdepth_lemma_pos(g0, yt@);
        tdepth_lemma_pos(g0, ye@);
        let dx = tdepth(g0, a@);
        let dy = tdepth(g0, b@);
        let mx = (dx - 1) as nat;
        let my = (dy - 1) as nat;
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let added = seq![ActionShape::CleanIf(x@, path@), ActionShape::Pair(xe@, ye@), ActionShape::Pair(xt@, yt@)];
        assert(pending.push(added[0]).push(added[1]).push(added[2]) =~= pending + added);
        machine_lemma_run3(g1, added[0], added[1], added[2], s0);
        let p = pair_bound(tdepth(g0, xt@), tdepth(g0, yt@));
        let q = pair_bound(tdepth(g0, xe@), tdepth(g0, ye@));
        let s2 = s0.push(p).push(q);
        assert(abs_pop(s2, 2) =~= s0);
        assert(abs_peek(s2, 1) == p);
        assert(abs_peek(s2, 0) == q);
        lemma_pair_bound_mono(tdepth(g0, xt@), tdepth(g0, yt@), mx, dy);
        lemma_pair_bound_mono(tdepth(g0, xe@), tdepth(g0, ye@), mx, dy);
        lemma_pair_if_bound(dx, dy, p, q);
        lemma_pair_cost_mono(tdepth(g0, xt@), tdepth(g0, yt@), mx, dy);
        lemma_pair_cost_mono(tdepth(g0, xe@), tdepth(g0, ye@), mx, dy);
        lemma_clean_cost_mono(if_bound(p, q), dx * (dy + 1));
        le_pointwise_push(s0, s0, if_bound(p, q), pair_bound(dx, dy));
        machine_lemma_step(g0, g1, pending, ActionShape::Pair(a@, b@), added, v0, v0);
    }

    pub proof fn machine_pair_empty(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, a: TransitionId, b: TransitionId,
        x: TestId, xt: TransitionId, xe: TransitionId, y: TestId, yt: TransitionId, ye: TransitionId,
        guard: TestId, path: TestId, empty: TransitionId, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g0), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), a@ < g0.transitions.len(), b@ < g0.transitions.len(),
            g0.transitions[a@ as int] == model::TransitionNode::If(x@, xt@, xe@),
            g0.transitions[b@ as int] == model::TransitionNode::If(y@, yt@, ye@),
            tdepth(g1, empty@) == 1,
        ensures machine_cost(g1, pending.push(ActionShape::CleanIf(guard@, path@))
                .push(ActionShape::SwapThen).push(ActionShape::Pair(xt@, yt@)), v0.push(empty))
            < machine_cost(g0, pending.push(ActionShape::Pair(a@, b@)), v0),
    {
        model::lemma_graph_transition_wf(g0, a@);
        model::lemma_graph_transition_wf(g0, b@);
        tdepth_lemma_unfold(g0, a@);
        tdepth_lemma_unfold(g0, b@);
        tdepth_lemma_extends(g0, g1, xt@);
        tdepth_lemma_extends(g0, g1, yt@);
        tdepth_lemma_pos(g0, xt@);
        tdepth_lemma_pos(g0, yt@);
        tdepth_lemma_pos(g0, xe@);
        tdepth_lemma_pos(g0, ye@);
        let dx = tdepth(g0, a@);
        let dy = tdepth(g0, b@);
        let mx = (dx - 1) as nat;
        let my = (dy - 1) as nat;
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let v1 = v0.push(empty);
        assert(value_depths(g1, v1) =~= s0.push(1));
        let added = seq![ActionShape::CleanIf(guard@, path@), ActionShape::SwapThen, ActionShape::Pair(xt@, yt@)];
        assert(pending.push(added[0]).push(added[1]).push(added[2]) =~= pending + added);
        machine_lemma_run3(g1, added[0], added[1], added[2], s0.push(1));
        let p = pair_bound(tdepth(g0, xt@), tdepth(g0, yt@));
        let s1 = s0.push(1nat).push(p);
        assert(abs_pop(s1, 2) =~= s0);
        assert(abs_peek(s1, 0) == p);
        assert(abs_peek(s1, 1) == 1);
        let s2 = s0.push(p).push(1nat);
        assert(action_next(g1, ActionShape::SwapThen, s1) =~= s2);
        assert(abs_pop(s2, 2) =~= s0);
        assert(abs_peek(s2, 1) == p);
        assert(abs_peek(s2, 0) == 1);
        lemma_pair_bound_mono(tdepth(g0, xt@), tdepth(g0, yt@), mx, my);
        assert(pair_bound(mx, my) + 1 == dx * dy) by (nonlinear_arith) requires dx >= 1, dy >= 1, mx == dx - 1, my == dy - 1;
        assert(dx * dy <= pair_bound(dx, dy)) by (nonlinear_arith);
        assert(tdepth(g0, xt@) * tdepth(g0, yt@) >= 0) by (nonlinear_arith);
        lemma_pair_cost_mono(tdepth(g0, xt@), tdepth(g0, yt@), mx, my);
        lemma_clean_cost_mono(if_bound(p, 1), dx * dy);
        le_pointwise_push(s0, s0, if_bound(p, 1), pair_bound(dx, dy));
        machine_lemma_step(g0, g1, pending, ActionShape::Pair(a@, b@), added, v0, v1);
    }

    // ----- Fold -----

    pub proof fn machine_fold_flat(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, xs: Seq<nat>, v0: Seq<TransitionId>, out: TransitionId,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending), transition_ids_valid(g0, v0),
            tdepth(g1, out@) <= intersect_bound(tdepths(g0, xs)),
        ensures machine_cost(g1, pending, v0.push(out)) < machine_cost(g0, pending.push(ActionShape::Fold(xs, 0)), v0),
    {
        machine_lemma_push(g0, g1, pending, ActionShape::Fold(xs, 0), v0, out, intersect_bound(tdepths(g0, xs)));
    }

    pub proof fn machine_fold_start(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, xs: Seq<nat>, flat: TransitionId,
        cs: Seq<TransitionId>, v0: Seq<TransitionId>,
    )
        requires model::graph_wf(g1), model::graph_extends(g0, g1), transition_tasks_valid(g0, pending),
            transition_ids_valid(g0, v0), flat@ < g1.transitions.len(), cs.len() >= 1,
            g1.transitions[flat@ as int] == model::TransitionNode::Intersect(model::transition_ids(cs)),
            tdepth(g1, flat@) <= intersect_bound(tdepths(g0, xs)),
        ensures machine_cost(g1, pending.push(ActionShape::Fold(model::transition_ids(cs), 1)), v0.push(cs[0]))
            < machine_cost(g0, pending.push(ActionShape::Fold(xs, 0)), v0),
    {
        tdepth_lemma_unfold(g1, flat@);
        let ids = model::transition_ids(cs);
        let ds = tdepths(g1, ids);
        tdepths_lemma_pos(g1, ids);
        let e = intersect_bound(tdepths(g0, xs));
        let e1 = intersect_bound(ds);
        let d0 = ds[0];
        assert(d0 == tdepth(g1, cs[0]@));
        let s0 = value_depths(g0, v0);
        value_depths_lemma_extends(g0, g1, v0);
        let v1 = v0.push(cs[0]);
        assert(value_depths(g1, v1) =~= s0.push(d0));
        let task = ActionShape::Fold(ids, 1);
        let added = seq![task];
        assert(pending.push(task) =~= pending + added);
        machine_lemma_run1(g1, task, s0.push(d0));
        assert(abs_peek(s0.push(d0), 0) == d0);
        assert(abs_pop(s0.push(d0), 1) =~= s0);
        lemma_costs_pos(0);
        if ids.len() >= 2 {
            lemma_fold(ds);
            lemma_pair_cost_total_mono(e1, e);
            le_pointwise_push(s0, s0, e1, e);
        } else {
            lemma_singleton(ds);
            le_pointwise_push(s0, s0, d0, e);
        }
        machine_lemma_step(g0, g1, pending, ActionShape::Fold(xs, 0), added, v0, v1);
    }

    pub proof fn machine_fold_next(g: model::Graph, pending: Seq<ActionShape>, xs: Seq<nat>, k: nat, v0: Seq<TransitionId>)
        requires transition_tasks_valid(g, pending), 1 <= k < xs.len(), v0.len() >= 1,
        ensures machine_cost(g, pending.push(ActionShape::Fold(xs, k + 1)).push(ActionShape::Pair(v0.last()@, xs[k as int])),
                v0.drop_last())
            < machine_cost(g, pending.push(ActionShape::Fold(xs, k)), v0),
    {
        graph_lemma_extends_refl(g);
        let s0 = value_depths(g, v0);
        let s1 = value_depths(g, v0.drop_last());
        assert(s1 =~= abs_pop(s0, 1));
        let da = tdepth(g, v0.last()@);
        assert(abs_peek(s0, 0) == da);
        let ds = tdepths(g, xs);
        let p = pair_bound(da, ds[k as int]);
        let added = seq![ActionShape::Fold(xs, k + 1), ActionShape::Pair(v0.last()@, xs[k as int])];
        assert(pending.push(added[0]).push(added[1]) =~= pending + added);
        machine_lemma_run2(g, added[0], added[1], s1);
        assert(abs_peek(s1.push(p), 0) == p);
        assert(abs_pop(s1.push(p), 1) =~= s1);
        assert(fold_cost(ds, k, da) == 1 + pair_cost(da, ds[k as int]) + fold_cost(ds, k + 1, p));
        assert(fold_bound(ds, k, da) == fold_bound(ds, k + 1, p));
        if k + 1 >= xs.len() {
            assert(fold_cost(ds, k + 1, p) == 1);
            assert(fold_bound(ds, k + 1, p) == p);
        }
        le_pointwise_refl(action_next(g, ActionShape::Fold(xs, k), s0));
        machine_lemma_step(g, g, pending, ActionShape::Fold(xs, k), added, v0, v0.drop_last());
    }

    pub proof fn machine_fold_noop(g: model::Graph, pending: Seq<ActionShape>, xs: Seq<nat>, k: nat, v0: Seq<TransitionId>)
        requires transition_tasks_valid(g, pending), 1 <= k, xs.len() <= k,
        ensures machine_cost(g, pending, v0) < machine_cost(g, pending.push(ActionShape::Fold(xs, k)), v0),
    {
        graph_lemma_extends_refl(g);
        let s0 = value_depths(g, v0);
        assert(pending + Seq::<ActionShape>::empty() =~= pending);
        le_pointwise_refl(s0);
        machine_lemma_step(g, g, pending, ActionShape::Fold(xs, k), Seq::empty(), v0, v0);
    }

    // ----- driver actions -----

    pub proof fn machine_driver_union(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, n: nat, v0: Seq<TransitionId>, out: TransitionId,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending), transition_ids_valid(g0, v0),
            n <= v0.len(),
            tdepth(g1, out@) <= union_bound(value_depths(g0, v0.subrange(v0.len() - n, v0.len() as int))),
        ensures machine_cost(g1, pending, v0.take(v0.len() - n).push(out))
            < machine_cost(g0, pending.push(ActionShape::Union(n)), v0),
    {
        let s0 = value_depths(g0, v0);
        let rest = v0.take(v0.len() - n);
        assert(abs_top(s0, n) =~= value_depths(g0, v0.subrange(v0.len() - n, v0.len() as int)));
        assert(abs_pop(s0, n) =~= value_depths(g0, rest));
        assert(transition_ids_valid(g0, rest));
        value_depths_lemma_extends(g0, g1, rest);
        let v1 = rest.push(out);
        let b = union_bound(abs_top(s0, n));
        assert(value_depths(g1, v1) =~= value_depths(g0, rest).push(tdepth(g1, out@)));
        le_pointwise_push(value_depths(g0, rest), value_depths(g0, rest), tdepth(g1, out@), b);
        assert(pending + Seq::<ActionShape>::empty() =~= pending);
        machine_lemma_step(g0, g1, pending, ActionShape::Union(n), Seq::empty(), v0, v1);
    }

    pub proof fn machine_driver_intersect(g: model::Graph, pending: Seq<ActionShape>, n: nat, v0: Seq<TransitionId>)
        requires transition_tasks_valid(g, pending), n <= v0.len(),
        ensures machine_cost(g, pending.push(ActionShape::Fold(
                model::transition_ids(v0.subrange(v0.len() - n, v0.len() as int)), 0)), v0.take(v0.len() - n))
            < machine_cost(g, pending.push(ActionShape::Intersect(n)), v0),
    {
        graph_lemma_extends_refl(g);
        let s0 = value_depths(g, v0);
        let rest = v0.take(v0.len() - n);
        let xs = model::transition_ids(v0.subrange(v0.len() - n, v0.len() as int));
        assert(abs_top(s0, n) =~= tdepths(g, xs));
        assert(abs_pop(s0, n) =~= value_depths(g, rest));
        let task = ActionShape::Fold(xs, 0);
        let added = seq![task];
        assert(pending.push(task) =~= pending + added);
        machine_lemma_run1(g, task, value_depths(g, rest));
        le_pointwise_refl(action_next(g, ActionShape::Intersect(n), s0));
        machine_lemma_step(g, g, pending, ActionShape::Intersect(n), added, v0, rest);
    }

    pub proof fn machine_driver_if(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, task: ActionShape, v0: Seq<TransitionId>,
        out: TransitionId,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending), transition_ids_valid(g0, v0),
            task is If, v0.len() >= 2,
            tdepth(g1, out@) <= if_bound(tdepth(g0, v0[v0.len() - 2]@), tdepth(g0, v0[v0.len() - 1]@)),
        ensures machine_cost(g1, pending, v0.take(v0.len() - 2).push(out)) < machine_cost(g0, pending.push(task), v0),
    {
        let s0 = value_depths(g0, v0);
        let rest = v0.take(v0.len() - 2);
        assert(abs_pop(s0, 2) =~= value_depths(g0, rest));
        assert(transition_ids_valid(g0, rest));
        value_depths_lemma_extends(g0, g1, rest);
        let v1 = rest.push(out);
        let b = if_bound(abs_peek(s0, 1), abs_peek(s0, 0));
        assert(value_depths(g1, v1) =~= value_depths(g0, rest).push(tdepth(g1, out@)));
        le_pointwise_push(value_depths(g0, rest), value_depths(g0, rest), tdepth(g1, out@), b);
        assert(pending + Seq::<ActionShape>::empty() =~= pending);
        machine_lemma_step(g0, g1, pending, task, Seq::empty(), v0, v1);
    }

    pub proof fn machine_driver_clean_if(
        g0: model::Graph, g1: model::Graph, pending: Seq<ActionShape>, test: TestId, path: TestId,
        v0: Seq<TransitionId>, out: TransitionId,
    )
        requires model::graph_extends(g0, g1), transition_tasks_valid(g0, pending), transition_ids_valid(g0, v0),
            v0.len() >= 2,
            tdepth(g1, out@) <= if_bound(tdepth(g0, v0[v0.len() - 2]@), tdepth(g0, v0[v0.len() - 1]@)),
        ensures machine_cost(g1, pending.push(ActionShape::Clean(out@, path@)), v0.take(v0.len() - 2))
            < machine_cost(g0, pending.push(ActionShape::CleanIf(test@, path@)), v0),
    {
        let s0 = value_depths(g0, v0);
        let rest = v0.take(v0.len() - 2);
        assert(abs_pop(s0, 2) =~= value_depths(g0, rest));
        assert(transition_ids_valid(g0, rest));
        value_depths_lemma_extends(g0, g1, rest);
        let b = if_bound(abs_peek(s0, 1), abs_peek(s0, 0));
        let task = ActionShape::Clean(out@, path@);
        let added = seq![task];
        assert(pending.push(task) =~= pending + added);
        machine_lemma_run1(g1, task, value_depths(g0, rest));
        lemma_clean_cost_mono(tdepth(g1, out@), b);
        le_pointwise_push(value_depths(g0, rest), value_depths(g0, rest), tdepth(g1, out@), b);
        machine_lemma_step(g0, g1, pending, ActionShape::CleanIf(test@, path@), added, v0, rest);
    }

    pub proof fn machine_driver_result(
        g: model::Graph, pending: Seq<ActionShape>, suffix: Option<nat>, v0: Seq<TransitionId>,
    )
        requires transition_tasks_valid(g, pending), v0.len() >= 1,
        ensures machine_cost(g, pending.push(match suffix {
                Some(r) => ActionShape::Append(v0.last()@, r), None => ActionShape::Not(v0.last()@) }), v0.drop_last())
            < machine_cost(g, pending.push(match suffix {
                Some(r) => ActionShape::AppendResult(r), None => ActionShape::NotResult }), v0),
    {
        graph_lemma_extends_refl(g);
        let s0 = value_depths(g, v0);
        let rest = value_depths(g, v0.drop_last());
        assert(abs_pop(s0, 1) =~= rest);
        assert(abs_peek(s0, 0) == tdepth(g, v0.last()@));
        let task = match suffix { Some(r) => ActionShape::Append(v0.last()@, r), None => ActionShape::Not(v0.last()@) };
        let added = seq![task];
        assert(pending.push(task) =~= pending + added);
        machine_lemma_run1(g, task, rest);
        let old_task = match suffix { Some(r) => ActionShape::AppendResult(r), None => ActionShape::NotResult };
        le_pointwise_refl(action_next(g, old_task, s0));
        machine_lemma_step(g, g, pending, old_task, added, v0, v0.drop_last());
    }

    pub proof fn machine_driver_swap(g: model::Graph, pending: Seq<ActionShape>, v0: Seq<TransitionId>)
        requires transition_tasks_valid(g, pending), v0.len() >= 2,
        ensures machine_cost(g, pending, v0.take(v0.len() - 2).push(v0[v0.len() - 1]).push(v0[v0.len() - 2]))
            < machine_cost(g, pending.push(ActionShape::SwapThen), v0),
    {
        graph_lemma_extends_refl(g);
        let s0 = value_depths(g, v0);
        let v1 = v0.take(v0.len() - 2).push(v0[v0.len() - 1]).push(v0[v0.len() - 2]);
        assert(value_depths(g, v1) =~= action_next(g, ActionShape::SwapThen, s0));
        le_pointwise_refl(value_depths(g, v1));
        assert(pending + Seq::<ActionShape>::empty() =~= pending);
        machine_lemma_step(g, g, pending, ActionShape::SwapThen, Seq::empty(), v0, v1);
    }

    // ----- set collection: depth conservation -----

    pub open spec fn collect_bound(g: model::Graph, ids: Seq<TransitionId>, intersect: bool) -> nat {
        if intersect { intersect_bound(value_depths(g, ids)) } else { union_bound(value_depths(g, ids)) }
    }

    pub open spec fn collect_weight(g: model::Graph, ids: Seq<TransitionId>, intersect: bool) -> nat {
        if intersect { prod_plus1(value_depths(g, ids)) } else { sum_plus1(value_depths(g, ids)) }
    }

    pub open spec fn pow2(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
    }

    /// Conserved quantity of `transition_collect_nodes`: pending, flattened, and constant children.
    pub open spec fn collect_total(
        g: model::Graph, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, intersect: bool,
    ) -> nat {
        if intersect {
            collect_weight(g, pending, true) * collect_weight(g, flat, true) * pow2(constants.len())
        } else {
            collect_weight(g, pending, false) + collect_weight(g, flat, false) + 2 * constants.len()
        }
    }

    pub proof fn lemma_pow2_pos(n: nat)
        ensures pow2(n) >= 1,
        decreases n,
    {
        if n > 0 { lemma_pow2_pos((n - 1) as nat); }
    }

    pub proof fn collect_lemma_push(g: model::Graph, ids: Seq<TransitionId>, id: TransitionId, intersect: bool)
        ensures collect_weight(g, ids.push(id), intersect) == if intersect {
                collect_weight(g, ids, true) * (tdepth(g, id@) + 1)
            } else { collect_weight(g, ids, false) + tdepth(g, id@) + 1 },
    {
        let s = value_depths(g, ids);
        assert(value_depths(g, ids.push(id)) =~= s.push(tdepth(g, id@)));
        assert(s.push(tdepth(g, id@)).drop_last() =~= s);
    }

    pub proof fn collect_lemma_concat(g: model::Graph, a: Seq<TransitionId>, b: Seq<TransitionId>, intersect: bool)
        ensures collect_weight(g, a + b, intersect) == if intersect {
                collect_weight(g, a, true) * collect_weight(g, b, true)
            } else { collect_weight(g, a, false) + collect_weight(g, b, false) },
        decreases b.len(),
    {
        if b.len() == 0 {
            assert(a + b =~= a);
            assert(value_depths(g, b).len() == 0);
            let wa = collect_weight(g, a, true);
            assert(wa * 1 == wa) by (nonlinear_arith);
        } else {
            let b0 = b.drop_last();
            let x = b.last();
            collect_lemma_concat(g, a, b0, intersect);
            assert(a + b =~= (a + b0).push(x));
            assert(b =~= b0.push(x));
            collect_lemma_push(g, a + b0, x, intersect);
            collect_lemma_push(g, b0, x, intersect);
            let wa = collect_weight(g, a, true);
            let wb = collect_weight(g, b0, true);
            let d = tdepth(g, x@);
            assert(wa * wb * (d + 1) == wa * (wb * (d + 1))) by (nonlinear_arith);
        }
    }

    pub proof fn collect_lemma_remove(g: model::Graph, s: Seq<TransitionId>, i: int, intersect: bool)
        requires 0 <= i < s.len(),
        ensures collect_weight(g, s, intersect) == if intersect {
                collect_weight(g, s.remove(i), true) * (tdepth(g, s[i]@) + 1)
            } else { collect_weight(g, s.remove(i), false) + tdepth(g, s[i]@) + 1 },
    {
        let a = s.take(i);
        let c = s.skip(i + 1);
        assert(s =~= a.push(s[i]) + c);
        assert(s.remove(i) =~= a + c);
        collect_lemma_concat(g, a.push(s[i]), c, intersect);
        collect_lemma_push(g, a, s[i], intersect);
        collect_lemma_concat(g, a, c, intersect);
        let wa = collect_weight(g, a, true);
        let wc = collect_weight(g, c, true);
        let d = tdepth(g, s[i]@);
        assert(wa * (d + 1) * wc == wa * wc * (d + 1)) by (nonlinear_arith);
    }

    pub proof fn collect_lemma_subset(g: model::Graph, sub: Seq<TransitionId>, sup: Seq<TransitionId>, intersect: bool)
        requires sub.no_duplicates(), forall|x: TransitionId| sub.contains(x) ==> sup.contains(x),
        ensures collect_weight(g, sub, intersect) <= collect_weight(g, sup, intersect),
        decreases sub.len(),
    {
        if sub.len() == 0 {
            assert(value_depths(g, sub).len() == 0);
            lemma_prod_pos(value_depths(g, sup));
        } else {
            let x = sub.last();
            let rest = sub.drop_last();
            assert(sub[sub.len() - 1] == x);
            assert(sub.contains(x));
            let i = choose|i: int| 0 <= i < sup.len() && sup[i] == x;
            let sup2 = sup.remove(i);
            assert forall|y: TransitionId| rest.contains(y) implies sup2.contains(y) by {
                let j = choose|j: int| 0 <= j < rest.len() && rest[j] == y;
                assert(sub[j] == y);
                assert(sub.contains(y));
                let k = choose|k: int| 0 <= k < sup.len() && sup[k] == y;
                assert(k != i);
                if k < i { assert(sup2[k] == y); } else { assert(sup2[k - 1] == y); }
            }
            assert(rest.no_duplicates()) by {
                assert forall|p: int, q: int| 0 <= p < rest.len() && 0 <= q < rest.len() && p != q implies rest[p] != rest[q] by {
                    assert(sub[p] == rest[p] && sub[q] == rest[q]);
                }
            }
            collect_lemma_subset(g, rest, sup2, intersect);
            assert(sub =~= rest.push(x));
            collect_lemma_push(g, rest, x, intersect);
            collect_lemma_remove(g, sup, i, intersect);
            let wr = collect_weight(g, rest, true);
            let ws = collect_weight(g, sup2, true);
            let d = tdepth(g, x@);
            if intersect {
                assert(wr * (d + 1) <= ws * (d + 1)) by (nonlinear_arith) requires wr <= ws;
            }
        }
    }

    pub proof fn collect_lemma_drop(
        g: model::Graph, prefix: Seq<TransitionId>, id: TransitionId, flat: Seq<TransitionId>, rs: Seq<RegexId>, intersect: bool,
    )
        ensures collect_total(g, prefix, flat, rs, intersect) <= collect_total(g, prefix.push(id), flat, rs, intersect),
    {
        collect_lemma_push(g, prefix, id, intersect);
        let wp = collect_weight(g, prefix, true);
        let wf = collect_weight(g, flat, true);
        let p = pow2(rs.len());
        let d = tdepth(g, id@);
        assert(wp * wf * p <= wp * (d + 1) * wf * p) by (nonlinear_arith);
    }

    pub proof fn collect_lemma_leaf(
        g: model::Graph, prefix: Seq<TransitionId>, id: TransitionId, flat: Seq<TransitionId>, rs: Seq<RegexId>, intersect: bool,
    )
        ensures collect_total(g, prefix, flat.push(id), rs, intersect) <= collect_total(g, prefix.push(id), flat, rs, intersect),
    {
        collect_lemma_push(g, prefix, id, intersect);
        collect_lemma_push(g, flat, id, intersect);
        let wp = collect_weight(g, prefix, true);
        let wf = collect_weight(g, flat, true);
        let p = pow2(rs.len());
        let d = tdepth(g, id@);
        assert(wp * (wf * (d + 1)) * p == wp * (d + 1) * wf * p) by (nonlinear_arith);
    }

    pub proof fn collect_lemma_constant(
        g: model::Graph, prefix: Seq<TransitionId>, id: TransitionId, flat: Seq<TransitionId>, rs: Seq<RegexId>,
        r: RegexId, intersect: bool,
    )
        requires id@ < g.transitions.len(), g.transitions[id@ as int] is Const,
        ensures collect_total(g, prefix, flat, rs.push(r), intersect) <= collect_total(g, prefix.push(id), flat, rs, intersect),
    {
        collect_lemma_push(g, prefix, id, intersect);
        tdepth_lemma_const(g, id@);
        assert(pow2(rs.push(r).len()) == 2 * pow2(rs.len()));
        let wp = collect_weight(g, prefix, true);
        let wf = collect_weight(g, flat, true);
        let p = pow2(rs.len());
        assert(wp * wf * (2 * p) == wp * 2 * wf * p) by (nonlinear_arith);
    }

    pub proof fn collect_lemma_expand(
        g: model::Graph, prefix: Seq<TransitionId>, id: TransitionId, children: Seq<TransitionId>,
        flat: Seq<TransitionId>, rs: Seq<RegexId>, intersect: bool,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            model::transition_ids(children) == transition_children(g, id@),
            match g.transitions[id@ as int] {
                model::TransitionNode::Union(_) => !intersect,
                model::TransitionNode::Intersect(_) => intersect,
                _ => false,
            },
        ensures collect_total(g, prefix + children, flat, rs, intersect)
            <= collect_total(g, prefix.push(id), flat, rs, intersect),
    {
        transition_lemma_children(g, id@);
        tdepth_lemma_unfold(g, id@);
        let cs = transition_children(g, id@);
        assert(value_depths(g, children) =~= tdepths(g, cs));
        tdepths_lemma_pos(g, cs);
        lemma_bounds_pos(tdepths(g, cs));
        collect_lemma_concat(g, prefix, children, intersect);
        collect_lemma_push(g, prefix, id, intersect);
        let wp = collect_weight(g, prefix, true);
        let wc = collect_weight(g, children, true);
        let wf = collect_weight(g, flat, true);
        let p = pow2(rs.len());
        let d = tdepth(g, id@);
        if intersect {
            assert(wp * wc * wf * p <= wp * (d + 1) * wf * p) by (nonlinear_arith) requires wc <= d + 1;
        }
    }

    /// After `transition_collect_nodes`: the flattened children and constants fit in the original weight.
    pub proof fn collect_lemma_flat(
        g: model::Graph, original: Seq<TransitionId>, pending: Seq<TransitionId>, flat: Seq<TransitionId>,
        rs: Seq<RegexId>, intersect: bool,
    )
        requires pending.len() == 0,
            collect_total(g, pending, flat, rs, intersect)
                <= collect_total(g, original, Seq::empty(), Seq::empty(), intersect),
        ensures collect_weight(g, flat, intersect) <= collect_weight(g, original, intersect),
            rs.len() >= 1 ==> if intersect { collect_weight(g, flat, true) * 2 <= collect_weight(g, original, true) }
                else { collect_weight(g, flat, false) + 2 <= collect_weight(g, original, false) },
    {
        assert(value_depths(g, pending).len() == 0);
        assert(value_depths(g, Seq::<TransitionId>::empty()).len() == 0);
        let wf = collect_weight(g, flat, true);
        let wo = collect_weight(g, original, true);
        let p = pow2(rs.len());
        lemma_pow2_pos(rs.len());
        if rs.len() >= 1 { lemma_pow2_pos((rs.len() - 1) as nat); }
        if intersect {
            assert(1 * wf * p == wf * p) by (nonlinear_arith);
            assert(wo * 1 * 1 == wo) by (nonlinear_arith);
            assert(wf <= wf * p) by (nonlinear_arith) requires p >= 1;
            if rs.len() >= 1 { assert(wf * 2 <= wf * p) by (nonlinear_arith) requires p >= 2; }
        }
    }

    pub proof fn collect_lemma_extends(a: model::Graph, b: model::Graph, ids: Seq<TransitionId>, intersect: bool)
        requires model::graph_extends(a, b), transition_ids_valid(a, ids),
        ensures collect_weight(a, ids, intersect) == collect_weight(b, ids, intersect),
    {
        value_depths_lemma_extends(a, b, ids);
    }

    /// `t` is the constant transition built from the collected constants.
    pub proof fn collect_lemma_const_result(
        a: model::Graph, b: model::Graph, original: Seq<TransitionId>, flat: Seq<TransitionId>, t: TransitionId,
        pushed: bool, intersect: bool,
    )
        requires model::graph_extends(a, b), transition_ids_valid(a, original), transition_ids_valid(a, flat),
            t@ < b.transitions.len(), b.transitions[t@ as int] is Const,
            if intersect { collect_weight(a, flat, true) * 2 <= collect_weight(a, original, true) }
                else { collect_weight(a, flat, false) + 2 <= collect_weight(a, original, false) },
        ensures collect_weight(b, if pushed { flat.push(t) } else { flat }, intersect) <= collect_weight(b, original, intersect),
    {
        collect_lemma_extends(a, b, original, intersect);
        collect_lemma_extends(a, b, flat, intersect);
        collect_lemma_push(b, flat, t, intersect);
        tdepth_lemma_const(b, t@);
        let wf = collect_weight(b, flat, true);
        assert(wf <= wf * 2) by (nonlinear_arith);
    }

    pub proof fn collect_lemma_bound(g: model::Graph, ids: Seq<TransitionId>, intersect: bool)
        ensures collect_bound(g, ids, intersect) >= 2,
    {
        value_depths_lemma_pos(g, ids);
        lemma_bounds_pos(value_depths(g, ids));
    }

    /// Depth of the three possible results of `transition_collect`.
    pub proof fn collect_lemma_final(
        entry: model::Graph, g: model::Graph, original: Seq<TransitionId>, flat: Seq<TransitionId>, intersect: bool,
    )
        requires model::graph_wf(g), model::graph_extends(entry, g), transition_ids_valid(entry, original),
            transition_ids_valid(g, flat),
            collect_weight(g, flat, intersect) <= collect_weight(g, original, intersect),
        ensures collect_bound(entry, original, intersect) >= 2,
            tdepth(g, g.constants.transition_empty) == 1, tdepth(g, g.constants.transition_all) == 1,
            flat.len() == 1 ==> tdepth(g, flat[0]@) <= collect_bound(entry, original, intersect),
            flat.len() >= 2 ==> tdepth_node(g, if intersect {
                    model::TransitionNode::Intersect(model::transition_ids(flat))
                } else { model::TransitionNode::Union(model::transition_ids(flat)) })
                <= collect_bound(entry, original, intersect),
    {
        tdepth_lemma_constants(g);
        value_depths_lemma_extends(entry, g, original);
        let ds = value_depths(entry, original);
        value_depths_lemma_pos(entry, original);
        lemma_bounds_pos(ds);
        lemma_sum_ge(ds);
        lemma_prod_ge(ds);
        let fs = value_depths(g, flat);
        value_depths_lemma_pos(g, flat);
        lemma_sum_ge(fs);
        lemma_prod_ge(fs);
        assert(tdepths(g, model::transition_ids(flat)) =~= fs);
        if flat.len() == 1 {
            lemma_singleton(fs);
            assert(fs[0] == tdepth(g, flat[0]@));
        }
    }

    pub open spec fn transition_collect_combo(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, pending: Seq<TransitionId>,
        flat: Seq<TransitionId>, constants: Seq<RegexId>, event: Data, word: Seq<Data>, intersect: bool,
    ) -> bool {
        if intersect {
            transition_combo(g, sym, theta, pending, event, word, true)
                && transition_combo(g, sym, theta, flat, event, word, true)
                && regex_combo(g, sym, theta, constants, word, true)
        } else {
            transition_combo(g, sym, theta, pending, event, word, false)
                || transition_combo(g, sym, theta, flat, event, word, false)
                || regex_combo(g, sym, theta, constants, word, false)
        }
    }



    pub proof fn transition_lemma_ids_bounded(g: model::Graph, ids: Seq<TransitionId>)
        requires transition_ids_valid(g, ids),
        ensures model::bounded(model::transition_ids(ids), g.transitions.len()),
    {}

    pub proof fn transition_lemma_pending_work_concat(
        g: model::Graph, left: Seq<TransitionId>, right: Seq<TransitionId>, intersect: bool,
    )
        requires transition_ids_valid(g, left), transition_ids_valid(g, right),
        ensures transition_pending_work(g, left + right, intersect)
            == transition_pending_work(g, left, intersect) + transition_pending_work(g, right, intersect),
    {
        transition_lemma_ids_bounded(g, left);
        transition_lemma_ids_bounded(g, right);
        assert(model::transition_ids(left + right) =~= model::transition_ids(left) + model::transition_ids(right));
        transition_lemma_work_concat(g, model::transition_ids(left), model::transition_ids(right), g.transitions.len(), intersect);
    }

    pub proof fn transition_lemma_pending_work_push(g: model::Graph, ids: Seq<TransitionId>, id: TransitionId, intersect: bool)
        requires transition_ids_valid(g, ids), id@ < g.transitions.len(),
        ensures transition_pending_work(g, ids.push(id), intersect)
            == transition_pending_work(g, ids, intersect) + transition_collect_work(g, id@, intersect),
    {
        transition_lemma_pending_work_concat(g, ids, seq![id], intersect);
        assert(ids.push(id) =~= ids + seq![id]);
        assert(model::transition_ids(seq![id]) =~= seq![id@]);
        transition_lemma_work_singleton(g, id, intersect);
    }

    pub proof fn transition_lemma_flat_work(g: model::Graph, id: TransitionId, intersect: bool)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            match g.transitions[id@ as int] {
                model::TransitionNode::Union(ids) => !intersect,
                model::TransitionNode::Intersect(ids) => intersect,
                _ => false,
            },
        ensures transition_collect_work(g, id@, intersect)
            == 1 + transition_collect_work_ids(g, transition_children(g, id@), g.transitions.len(), intersect),
    {
        transition_lemma_children(g, id@);
        model::lemma_graph_transition_wf(g, id@);
        transition_lemma_work_bounds(g, transition_children(g, id@), id@, g.transitions.len(), intersect);
    }

    pub proof fn transition_lemma_combo_concat(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, left: Seq<TransitionId>, right: Seq<TransitionId>,
        event: Data, word: Seq<Data>, intersect: bool,
    )
        ensures transition_combo(g, sym, theta, left + right, event, word, intersect)
            == if intersect {
                transition_combo(g, sym, theta, left, event, word, true)
                    && transition_combo(g, sym, theta, right, event, word, true)
            } else {
                transition_combo(g, sym, theta, left, event, word, false)
                    || transition_combo(g, sym, theta, right, event, word, false)
            },
    {
        if intersect {
            if transition_combo(g, sym, theta, left + right, event, word, true) {
                assert forall|i: int| 0 <= i < left.len() implies transition_lang(g, sym, theta, left[i], event, word) by {
                    assert((left + right)[i] == left[i]);
                    assert(transition_lang(g, sym, theta, (left + right)[i], event, word));
                }
                assert forall|i: int| 0 <= i < right.len() implies transition_lang(g, sym, theta, right[i], event, word) by {
                    assert((left + right)[left.len() as int + i] == right[i]);
                    assert(transition_lang(g, sym, theta, (left + right)[left.len() as int + i], event, word));
                }
            }
            if transition_combo(g, sym, theta, left, event, word, true)
                && transition_combo(g, sym, theta, right, event, word, true) {
                assert forall|i: int| 0 <= i < (left + right).len() implies
                    transition_lang(g, sym, theta, (left + right)[i], event, word) by {
                    if i < left.len() { assert((left + right)[i] == left[i]); }
                    else { assert((left + right)[i] == right[i - left.len() as int]); }
                }
            }
        } else {
            if transition_combo(g, sym, theta, left + right, event, word, false) {
                let i = choose|i: int| 0 <= i < (left + right).len()
                    && transition_lang(g, sym, theta, (left + right)[i], event, word);
                if i < left.len() {
                    assert((left + right)[i] == left[i]);
                    assert(transition_combo(g, sym, theta, left, event, word, false));
                } else {
                    assert((left + right)[i] == right[i - left.len() as int]);
                    assert(transition_combo(g, sym, theta, right, event, word, false));
                }
            }
            if transition_combo(g, sym, theta, left, event, word, false) {
                let i = choose|i: int| 0 <= i < left.len() && transition_lang(g, sym, theta, left[i], event, word);
                assert(transition_lang(g, sym, theta, (left + right)[i], event, word));
                assert(transition_combo(g, sym, theta, left + right, event, word, false));
            }
            if transition_combo(g, sym, theta, right, event, word, false) {
                let i = choose|i: int| 0 <= i < right.len() && transition_lang(g, sym, theta, right[i], event, word);
                assert(transition_lang(g, sym, theta, (left + right)[left.len() as int + i], event, word));
                assert(transition_combo(g, sym, theta, left + right, event, word, false));
            }
        }
    }

    pub proof fn transition_lemma_constant(g: model::Graph, id: TransitionId, regex: RegexId)
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::Const(regex@),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, id, event, word) == model::regex_lang(g, sym, theta, regex@, word),
    {
        transition_unfold(g, id@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, id, event, word) == model::regex_lang(g, sym, theta, regex@, word) by {
            language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(g, regex@));
        }
    }

    pub proof fn transition_lemma_children_language(
        g: model::Graph, id: TransitionId, children: Seq<TransitionId>, intersect: bool,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == if intersect {
                model::TransitionNode::Intersect(model::transition_ids(children))
            } else { model::TransitionNode::Union(model::transition_ids(children)) },
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, id, event, word)
                == transition_combo(g, sym, theta, children, event, word, intersect),
    {
        transition_unfold(g, id@);
        let terms = model::transition_ids(children).map(|i: int, child: nat| model::lift_transition(g, child));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, id, event, word)
                == transition_combo(g, sym, theta, children, event, word, intersect) by {
            let sem = model::gsem(sym, theta);
            assert forall|i: int| 0 <= i < children.len() implies
                transition_lang(g, sym, theta, children[i], event, word)
                    == language::lang(sem, language::interp_transition(sem, event, terms[i]), word) by {
                assert(terms[i] == model::lift_transition(g, children[i]@));
            }
            if intersect {
                language::lemma_interp_intersect(sem, event, terms, word);
            } else {
                language::lemma_interp_union(sem, event, terms, word);
                if transition_lang(g, sym, theta, id, event, word) {
                    let i = choose|i: int| 0 <= i < terms.len()
                        && language::lang(sem, language::interp_transition(sem, event, terms[i]), word);
                    assert(transition_lang(g, sym, theta, children[i], event, word));
                }
                if transition_combo(g, sym, theta, children, event, word, false) {
                    let i = choose|i: int| 0 <= i < children.len()
                        && transition_lang(g, sym, theta, children[i], event, word);
                    assert(language::lang(sem, language::interp_transition(sem, event, terms[i]), word));
                }
            }
        }
    }

    pub proof fn transition_lemma_identities(g: model::Graph, mode: TransitionModeModel)
        requires model::graph_wf(g), transition_mode_valid(g, mode),
        ensures mode.identity@ < g.transitions.len(), mode.absorber@ < g.transitions.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                transition_lang(g, sym, theta, mode.identity, event, word) == mode.intersect,
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                transition_lang(g, sym, theta, mode.absorber, event, word) == !mode.intersect,
    {
        model::lemma_graph_wf_elim(g);
        transition_unfold(g, mode.identity@);
        transition_unfold(g, mode.absorber@);
        regex_unfold(g, g.constants.empty);
        regex_unfold(g, g.constants.all);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, mode.identity, event, word) == mode.intersect by {
            if mode.intersect {
                language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(g, g.constants.all));
            } else {
                language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(g, g.constants.empty));
            }
        }
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, mode.absorber, event, word) == !mode.intersect by {
            if mode.intersect {
                language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(g, g.constants.empty));
            } else {
                language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(g, g.constants.all));
            }
        }
    }

    pub open spec fn transition_collect_effect(
        g: model::Graph, mode: TransitionModeModel, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>,
        next_pending: Seq<TransitionId>, next_flat: Seq<TransitionId>, next_constants: Seq<RegexId>, collapsed: bool,
    ) -> bool {
        (forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect)
                == if collapsed { !mode.intersect } else {
                    transition_collect_combo(g, sym, theta, next_pending, next_flat, next_constants, event, word, mode.intersect)
                })
        && (!collapsed && pending.len() > 0 ==> transition_pending_work(g, next_pending, mode.intersect)
            < transition_pending_work(g, pending, mode.intersect))
    }

    pub proof fn transition_lemma_pending_work_pop(g: model::Graph, pending: Seq<TransitionId>, intersect: bool)
        requires transition_ids_valid(g, pending), pending.len() > 0,
        ensures transition_pending_work(g, pending.drop_last(), intersect) < transition_pending_work(g, pending, intersect),
    {
        transition_lemma_pending_work_push(g, pending.drop_last(), pending.last(), intersect);
        transition_lemma_work_positive(g, pending.last()@, intersect);
        assert(pending.drop_last().push(pending.last()) =~= pending);
    }

    pub proof fn transition_lemma_collect_identity(
        g: model::Graph, mode: TransitionModeModel, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>,
    )
        requires model::graph_wf(g), transition_mode_valid(g, mode),
            transition_ids_valid(g, pending), pending.len() > 0, pending.last() == mode.identity,
        ensures transition_collect_effect(g, mode, pending, flat, constants, pending.drop_last(), flat, constants, false),
    {
        transition_lemma_identities(g, mode);
        transition_lemma_pending_work_pop(g, pending, mode.intersect);
        assert(pending.drop_last() + seq![pending.last()] =~= pending);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect)
                == transition_collect_combo(g, sym, theta, pending.drop_last(), flat, constants, event, word, mode.intersect) by {
            transition_lemma_combo_concat(g, sym, theta, pending.drop_last(), seq![pending.last()], event, word, mode.intersect);
        }
    }

    pub proof fn transition_lemma_collect_absorber(
        g: model::Graph, mode: TransitionModeModel, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>,
    )
        requires model::graph_wf(g), transition_mode_valid(g, mode),
            pending.len() > 0, pending.last() == mode.absorber,
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect) == !mode.intersect,
    {
        transition_lemma_identities(g, mode);
        assert(pending.drop_last() + seq![pending.last()] =~= pending);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect) == !mode.intersect by {
            transition_lemma_combo_concat(g, sym, theta, pending.drop_last(), seq![pending.last()], event, word, mode.intersect);
        }
    }

    pub proof fn transition_lemma_collect_leaf(
        g: model::Graph, mode: TransitionModeModel, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>,
    )
        requires transition_ids_valid(g, pending), pending.len() > 0,
        ensures transition_collect_effect(g, mode, pending, flat, constants,
            pending.drop_last(), flat.push(pending.last()), constants, false),
    {
        transition_lemma_pending_work_pop(g, pending, mode.intersect);
        assert(pending.drop_last() + seq![pending.last()] =~= pending);
        assert(flat + seq![pending.last()] =~= flat.push(pending.last()));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect)
                == transition_collect_combo(g, sym, theta, pending.drop_last(), flat.push(pending.last()), constants, event, word, mode.intersect) by {
            transition_lemma_combo_concat(g, sym, theta, pending.drop_last(), seq![pending.last()], event, word, mode.intersect);
            transition_lemma_combo_concat(g, sym, theta, flat, seq![pending.last()], event, word, mode.intersect);
        }
    }

    pub proof fn transition_lemma_collect_constant(
        g: model::Graph, mode: TransitionModeModel, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, regex: RegexId,
    )
        requires model::graph_wf(g), transition_ids_valid(g, pending), pending.len() > 0,
            g.transitions[pending.last()@ as int] == model::TransitionNode::Const(regex@),
        ensures transition_collect_effect(g, mode, pending, flat, constants,
            pending.drop_last(), flat, constants.push(regex), false),
    {
        transition_lemma_constant(g, pending.last(), regex);
        transition_lemma_pending_work_pop(g, pending, mode.intersect);
        assert(pending.drop_last() + seq![pending.last()] =~= pending);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect)
                == transition_collect_combo(g, sym, theta, pending.drop_last(), flat, constants.push(regex), event, word, mode.intersect) by {
            transition_lemma_combo_concat(g, sym, theta, pending.drop_last(), seq![pending.last()], event, word, mode.intersect);
            transition_lemma_regex_combo_push(g, sym, theta, constants, regex, word, mode.intersect);
            assert(regex_combo(g, sym, theta, constants.push(regex), word, mode.intersect)
                == if mode.intersect {
                    regex_combo(g, sym, theta, constants, word, true) && model::regex_lang(g, sym, theta, regex@, word)
                } else {
                    regex_combo(g, sym, theta, constants, word, false) || model::regex_lang(g, sym, theta, regex@, word)
                });
        }
    }

    pub proof fn transition_lemma_collect_expand(
        g: model::Graph, mode: TransitionModeModel, pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, children: Seq<TransitionId>,
    )
        requires model::graph_wf(g), transition_ids_valid(g, pending), pending.len() > 0,
            transition_ids_valid(g, children),
            g.transitions[pending.last()@ as int] == if mode.intersect {
                model::TransitionNode::Intersect(model::transition_ids(children))
            } else { model::TransitionNode::Union(model::transition_ids(children)) },
        ensures transition_collect_effect(g, mode, pending, flat, constants,
            pending.drop_last() + children, flat, constants, false),
    {
        let prefix = pending.drop_last();
        let id = pending.last();
        transition_lemma_pending_work_push(g, prefix, id, mode.intersect);
        transition_lemma_pending_work_concat(g, prefix, children, mode.intersect);
        transition_lemma_ids_bounded(g, children);
        transition_lemma_flat_work(g, id, mode.intersect);
        transition_lemma_children(g, id@);
        assert(transition_children(g, id@) == model::transition_ids(children));
        assert(prefix.push(id) =~= pending);
        transition_lemma_children_language(g, id, children, mode.intersect);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect)
                == transition_collect_combo(g, sym, theta, prefix + children, flat, constants, event, word, mode.intersect) by {
            transition_lemma_combo_concat(g, sym, theta, prefix, seq![id], event, word, mode.intersect);
            transition_lemma_combo_concat(g, sym, theta, prefix, children, event, word, mode.intersect);
        }
    }


    pub proof fn transition_lemma_work_singleton(g: model::Graph, id: TransitionId, intersect: bool)
        requires id@ < g.transitions.len(),
        ensures transition_pending_work(g, seq![id], intersect) == transition_collect_work(g, id@, intersect),
    {
        transition_lemma_ids_bounded(g, seq![id]);
        assert(model::transition_ids(seq![id]) =~= seq![id@]);
        reveal_with_fuel(transition_collect_work_ids, 2);
    }

    pub proof fn transition_lemma_image_suffix(prefix: Seq<TransitionId>, whole: Seq<TransitionId>, suffix: Seq<nat>)
        requires prefix.is_prefix_of(whole),
            model::transition_ids(whole) == model::transition_ids(prefix) + suffix,
        ensures model::transition_ids(whole.subrange(prefix.len() as int, whole.len() as int)) == suffix,
    {
        let tail = whole.subrange(prefix.len() as int, whole.len() as int);
        assert(model::transition_ids(whole).len() == whole.len());
        assert(model::transition_ids(prefix).len() == prefix.len());
        assert((model::transition_ids(prefix) + suffix).len() == prefix.len() + suffix.len());
        assert(tail.len() == suffix.len());
        assert forall|i: int| 0 <= i < suffix.len() implies model::transition_ids(tail)[i] == suffix[i] by {
            assert(tail[i] == whole[prefix.len() as int + i]);
            assert(model::transition_ids(whole)[prefix.len() as int + i] == suffix[i]);
        }
        assert(model::transition_ids(tail) =~= suffix);
    }

    pub proof fn transition_lemma_regex_combo_push(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, values: Seq<RegexId>, value: RegexId, word: Seq<Data>, intersect: bool,
    )
        ensures regex_combo(g, sym, theta, values.push(value), word, intersect)
            == if intersect {
                regex_combo(g, sym, theta, values, word, true) && model::regex_lang(g, sym, theta, value@, word)
            } else {
                regex_combo(g, sym, theta, values, word, false) || model::regex_lang(g, sym, theta, value@, word)
            },
    {
        if intersect {
            if regex_combo(g, sym, theta, values.push(value), word, true) {
                assert(model::regex_lang(g, sym, theta, values.push(value)[values.len() as int]@, word));
                assert forall|i: int| 0 <= i < values.len() implies model::regex_lang(g, sym, theta, values[i]@, word) by {
                    assert(values.push(value)[i] == values[i]);
                }
            }
            if regex_combo(g, sym, theta, values, word, true) && model::regex_lang(g, sym, theta, value@, word) {
                assert forall|i: int| 0 <= i < values.push(value).len() implies
                    model::regex_lang(g, sym, theta, values.push(value)[i]@, word) by {
                    if i < values.len() { assert(values.push(value)[i] == values[i]); }
                    else { assert(i == values.len()); }
                }
            }
        } else {
            if regex_combo(g, sym, theta, values.push(value), word, false) {
                let i = choose|i: int| 0 <= i < values.push(value).len()
                    && model::regex_lang(g, sym, theta, values.push(value)[i]@, word);
                if i < values.len() {
                    assert(values.push(value)[i] == values[i]);
                    assert(regex_combo(g, sym, theta, values, word, false));
                } else { assert(i == values.len()); }
            }
            if regex_combo(g, sym, theta, values, word, false) {
                let i = choose|i: int| 0 <= i < values.len() && model::regex_lang(g, sym, theta, values[i]@, word);
                assert(model::regex_lang(g, sym, theta, values.push(value)[i]@, word));
                assert(regex_combo(g, sym, theta, values.push(value), word, false));
            }
            if model::regex_lang(g, sym, theta, value@, word) {
                assert(model::regex_lang(g, sym, theta, values.push(value)[values.len() as int]@, word));
                assert(regex_combo(g, sym, theta, values.push(value), word, false));
            }
        }
    }

    #[verifier::opaque]
    pub open spec fn test_schedule_extension(g: model::Graph, id: TestId,
        base: Seq<(TestId, bool)>, tasks: Seq<(TestId, bool)>) -> bool {
        base.is_prefix_of(tasks)
            && test_not_schedule(g, id, tasks.subrange(base.len() as int, tasks.len() as int))
    }

    pub proof fn test_lemma_schedule_extension_intro(g: model::Graph, id: TestId, count: nat,
        base: Seq<(TestId, bool)>, tasks: Seq<(TestId, bool)>)
        requires test_child_count(g, id, count), base.is_prefix_of(tasks), tasks.len() == base.len() + count,
            forall|j: int| #![trigger tasks[j]] base.len() <= j < tasks.len() ==> !tasks[j].1,
            forall|j: int| 0 <= j < count
                ==> #[trigger] tasks[base.len() + j].0@ == test_children(g, id)[count as int - 1 - j],
        ensures test_schedule_extension(g, id, base, tasks),
    {
        reveal(test_schedule_extension);
        let suffix = tasks.subrange(base.len() as int, tasks.len() as int);
        assert(test_children(g, id).len() == count);
        assert forall|i: int| 0 <= i < suffix.len()
            implies #[trigger] suffix[i].0@ == test_children(g, id)[suffix.len() as int - 1 - i] && !suffix[i].1 by {
            assert(suffix[i] == tasks[base.len() + i]);
            assert(tasks[base.len() + i].0@ == test_children(g, id)[count as int - 1 - i]);
            assert(!tasks[base.len() + i].1);
        }
    }

    pub proof fn test_lemma_not_scheduled_extension(g: model::Graph, id: TestId,
        pending: Seq<(TestId, bool)>, base: Seq<(TestId, bool)>, tasks: Seq<(TestId, bool)>, values: Seq<TestId>)
        requires base == pending.push((id, true)), test_schedule_extension(g, id, base, tasks),
        ensures test_not_effect(g, id, false, pending, values, tasks, values),
    {
        reveal(test_schedule_extension);
        assert(base.len() == pending.len() + 1);
        assert(tasks.subrange(base.len() as int, tasks.len() as int)
            == tasks.subrange(pending.len() as int + 1, tasks.len() as int));
        match g.tests[id@ as int] {
            model::TestNode::And(_) => {},
            model::TestNode::Or(_) => {},
            _ => {},
        }
    }


    pub open spec fn transition_equivalent(g: model::Graph, left: Seq<TransitionId>, right: Seq<TransitionId>, intersect: bool) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> transition_combo(g, sym, theta, left, event, word, intersect)
                == transition_combo(g, sym, theta, right, event, word, intersect)
    }

    pub proof fn transition_combo_extends(before: model::Graph, after: model::Graph, ids: Seq<TransitionId>, intersect: bool)
        requires model::graph_wf(before), model::graph_extends(before, after), transition_ids_valid(before, ids),
        ensures transition_ids_valid(after, ids),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                transition_combo(before, sym, theta, ids, event, word, intersect)
                    == transition_combo(after, sym, theta, ids, event, word, intersect),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_stable_under_extends(before, after);
    }

    pub proof fn transition_member_ids_valid(g: model::Graph, source: Seq<TransitionId>, target: Seq<TransitionId>)
        requires transition_ids_valid(g, source), forall|id: TransitionId| target.contains(id) ==> source.contains(id),
        ensures transition_ids_valid(g, target),
    {
        assert forall|i: int| 0 <= i < target.len() implies target[i]@ < g.transitions.len() by {
            assert(target.contains(target[i]));
            assert(source.contains(target[i]));
            let j = choose|j: int| 0 <= j < source.len() && source[j] == target[i];
        }
    }

    pub proof fn transition_multiset_members(source: Seq<TransitionId>, target: Seq<TransitionId>)
        requires source.to_multiset() == target.to_multiset(),
        ensures forall|id: TransitionId| source.contains(id) == target.contains(id),
    {
        lemma_multiset_members(source, target);
    }

    pub proof fn transition_dedup_strict(sorted: Seq<TransitionId>, result: Seq<TransitionId>)
        requires result == dedup_spec(sorted),
            forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i]@ <= sorted[j]@,
        ensures model::strictly_increasing(model::transition_ids(result)),
    {
        let key: spec_fn(TransitionId) -> nat = |id: TransitionId| id@;
        lemma_dedup_strict::<TransitionId>(sorted, key);
        assert forall|i: int, j: int| 0 <= i < j < result.len() implies
            model::transition_ids(result)[i] < model::transition_ids(result)[j] by {
            assert(key(dedup_spec(sorted)[i])
                < key(dedup_spec(sorted)[j]));
        }
    }

    pub proof fn transition_combo_members(g: model::Graph, left: Seq<TransitionId>, right: Seq<TransitionId>, intersect: bool)
        requires forall|id: TransitionId| left.contains(id) == right.contains(id),
        ensures transition_equivalent(g, left, right, intersect),
    {
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_combo(g, sym, theta, left, event, word, intersect)
                == transition_combo(g, sym, theta, right, event, word, intersect) by {
            if intersect {
                if transition_combo(g, sym, theta, left, event, word, true) {
                    assert forall|i: int| 0 <= i < right.len() implies transition_lang(g, sym, theta, right[i], event, word) by {
                        assert(right.contains(right[i])); assert(left.contains(right[i]));
                        let j = choose|j: int| 0 <= j < left.len() && left[j] == right[i];
                        assert(transition_lang(g, sym, theta, left[j], event, word));
                    }
                }
                if transition_combo(g, sym, theta, right, event, word, true) {
                    assert forall|i: int| 0 <= i < left.len() implies transition_lang(g, sym, theta, left[i], event, word) by {
                        assert(left.contains(left[i])); assert(right.contains(left[i]));
                        let j = choose|j: int| 0 <= j < right.len() && right[j] == left[i];
                        assert(transition_lang(g, sym, theta, right[j], event, word));
                    }
                }
            } else {
                if transition_combo(g, sym, theta, left, event, word, false) {
                    let i = choose|i: int| 0 <= i < left.len() && transition_lang(g, sym, theta, left[i], event, word);
                    assert(left.contains(left[i])); assert(right.contains(left[i]));
                    let j = choose|j: int| 0 <= j < right.len() && right[j] == left[i];
                    assert(transition_lang(g, sym, theta, right[j], event, word));
                }
                if transition_combo(g, sym, theta, right, event, word, false) {
                    let i = choose|i: int| 0 <= i < right.len() && transition_lang(g, sym, theta, right[i], event, word);
                    assert(right.contains(right[i])); assert(left.contains(right[i]));
                    let j = choose|j: int| 0 <= j < left.len() && left[j] == right[i];
                    assert(transition_lang(g, sym, theta, left[j], event, word));
                }
            }
        }
    }

    pub open spec fn transition_collected(
        g: model::Graph, original: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, intersect: bool,
    ) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> transition_combo(g, sym, theta, original, event, word, intersect)
                == transition_collect_combo(g, sym, theta, Seq::empty(), flat, constants, event, word, intersect)
    }

    pub proof fn transition_lemma_extends_transitive(a: model::Graph, b: model::Graph, c: model::Graph)
        requires model::graph_extends(a, b), model::graph_extends(b, c),
        ensures model::graph_extends(a, c),
    {}

    pub proof fn transition_collected_extends(
        before: model::Graph, after: model::Graph, original: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, intersect: bool,
    )
        requires model::graph_wf(before), model::graph_extends(before, after),
            transition_ids_valid(before, original), transition_ids_valid(before, flat), regex_ids_valid(before, constants),
            transition_collected(before, original, flat, constants, intersect),
        ensures transition_ids_valid(after, original), transition_ids_valid(after, flat), regex_ids_valid(after, constants),
            transition_collected(after, original, flat, constants, intersect),
    {
        transition_combo_extends(before, after, original, intersect);
        transition_combo_extends(before, after, flat, intersect);
        regex_combo_extends(before, after, constants, intersect);
    }

    pub proof fn transition_lemma_group_result(
        g: model::Graph, original: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, mode: TransitionModeModel, grouped: TransitionId,
    )
        requires model::graph_wf(g), transition_mode_valid(g, mode),
            transition_collected(g, original, flat, constants, mode.intersect),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(g, sym, theta, grouped, event, word) == regex_combo(g, sym, theta, constants, word, mode.intersect),
        ensures
            transition_equivalent(g, original, flat.push(grouped), mode.intersect),
            grouped == mode.identity ==> transition_equivalent(g, original, flat, mode.intersect),
            grouped == mode.absorber ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_combo(g, sym, theta, original, event, word, mode.intersect)
                    == transition_lang(g, sym, theta, mode.absorber, event, word),
    {
        hide(transition_lang);
        hide(transition_combo);
        hide(regex_combo);
        transition_lemma_identities(g, mode);
        assert(flat + seq![grouped] =~= flat.push(grouped));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_combo(g, sym, theta, original, event, word, mode.intersect)
                == transition_combo(g, sym, theta, flat.push(grouped), event, word, mode.intersect) by {
            transition_lemma_combo_concat(g, sym, theta, flat, seq![grouped], event, word, mode.intersect);
            transition_lemma_singleton_combo(g, grouped, sym, theta, event, word, mode.intersect);
            transition_lemma_empty_combos(g, sym, theta, event, word, mode.intersect);
            assert(transition_combo(g, sym, theta, original, event, word, mode.intersect)
                == transition_collect_combo(g, sym, theta, Seq::empty(), flat, constants, event, word, mode.intersect));
            assert(transition_lang(g, sym, theta, grouped, event, word)
                == regex_combo(g, sym, theta, constants, word, mode.intersect));
        }
        if grouped == mode.identity {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                implies transition_combo(g, sym, theta, original, event, word, mode.intersect)
                    == transition_combo(g, sym, theta, flat, event, word, mode.intersect) by {
                transition_lemma_combo_concat(g, sym, theta, flat, seq![grouped], event, word, mode.intersect);
                transition_lemma_singleton_combo(g, grouped, sym, theta, event, word, mode.intersect);
                assert(transition_combo(g, sym, theta, original, event, word, mode.intersect)
                    == transition_combo(g, sym, theta, flat.push(grouped), event, word, mode.intersect));
                assert(transition_lang(g, sym, theta, grouped, event, word) == mode.intersect);
            }
        }
    }

    pub proof fn transition_lemma_set_result(g: model::Graph, ids: Seq<TransitionId>, original: Seq<TransitionId>, intersect: bool)
        requires transition_equivalent(g, ids, original, intersect),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> (ids.len() == 0 ==> transition_combo(g, sym, theta, original, event, word, intersect) == intersect)
                && (ids.len() == 1 ==> transition_combo(g, sym, theta, original, event, word, intersect)
                    == transition_lang(g, sym, theta, ids[0], event, word)),
    {
        if ids.len() == 1 { assert(ids =~= seq![ids[0]]); }
    }

    pub proof fn transition_equivalence_extends(
        before: model::Graph, after: model::Graph, original: Seq<TransitionId>, current: Seq<TransitionId>, intersect: bool,
    )
        requires model::graph_wf(before), model::graph_extends(before, after),
            transition_ids_valid(before, original), transition_ids_valid(before, current),
            transition_equivalent(before, original, current, intersect),
        ensures transition_equivalent(after, original, current, intersect),
    {
        transition_combo_extends(before, after, original, intersect);
        transition_combo_extends(before, after, current, intersect);
    }

    pub proof fn transition_equivalence_future(
        g: model::Graph, original: Seq<TransitionId>, current: Seq<TransitionId>, intersect: bool,
    )
        requires model::graph_wf(g), transition_ids_valid(g, original), transition_ids_valid(g, current),
            transition_equivalent(g, original, current, intersect),
        ensures forall|next: model::Graph| model::graph_extends(g, next)
            ==> transition_equivalent(next, original, current, intersect),
    {
        assert forall|next: model::Graph| model::graph_extends(g, next)
            implies transition_equivalent(next, original, current, intersect) by {
            transition_equivalence_extends(g, next, original, current, intersect);
        }
    }

    pub proof fn transition_set_law(ids: Seq<TransitionId>, intersect: bool)
        ensures forall|g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            language::lang(model::gsem(sym, theta), language::interp_transition(model::gsem(sym, theta), event,
                transition_unbounded_node(g, if intersect { model::TransitionNode::Intersect(model::transition_ids(ids)) }
                    else { model::TransitionNode::Union(model::transition_ids(ids)) })), word)
                == transition_combo(g, sym, theta, ids, event, word, intersect),
    {
        assert forall|g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            language::lang(model::gsem(sym, theta), language::interp_transition(model::gsem(sym, theta), event,
                transition_unbounded_node(g, if intersect { model::TransitionNode::Intersect(model::transition_ids(ids)) }
                    else { model::TransitionNode::Union(model::transition_ids(ids)) })), word)
                == transition_combo(g, sym, theta, ids, event, word, intersect) by {
            let sem = model::gsem(sym, theta);
            let terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
            assert forall|i: int| 0 <= i < ids.len() implies
                language::lang(sem, language::interp_transition(sem, event, terms[i]), word)
                    == transition_lang(g, sym, theta, ids[i], event, word) by {
                assert(terms[i] == model::lift_transition(g, ids[i]@));
            }
            if intersect {
                language::lemma_interp_intersect(sem, event, terms, word);
            } else {
                language::lemma_interp_union(sem, event, terms, word);
                if exists|i: int| 0 <= i < terms.len()
                    && language::lang(sem, language::interp_transition(sem, event, terms[i]), word) {
                    let i = choose|i: int| 0 <= i < terms.len()
                        && language::lang(sem, language::interp_transition(sem, event, terms[i]), word);
                    assert(transition_lang(g, sym, theta, ids[i], event, word));
                }
                if transition_combo(g, sym, theta, ids, event, word, false) {
                    let i = choose|i: int| 0 <= i < ids.len() && transition_lang(g, sym, theta, ids[i], event, word);
                    assert(language::lang(sem, language::interp_transition(sem, event, terms[i]), word));
                }
            }
        }
    }


    pub open spec fn transition_child_action_valid(g: model::Graph, action: ChildShape) -> bool {
        match action {
            ChildShape::Clean(path) => path < g.tests.len(),
            ChildShape::Not => true,
            ChildShape::Append(suffix) => suffix < g.regexes.len(),
            ChildShape::PairLeft(other) => other < g.transitions.len(),
            ChildShape::PairRight(other) => other < g.transitions.len(),
        }
    }

    pub open spec fn transition_child_shape(action: ChildShape, child: nat) -> ActionShape {
        match action {
            ChildShape::Clean(path) => ActionShape::Clean(child, path),
            ChildShape::Not => ActionShape::Not(child),
            ChildShape::Append(suffix) => ActionShape::Append(child, suffix),
            ChildShape::PairLeft(other) => ActionShape::Pair(child, other),
            ChildShape::PairRight(other) => ActionShape::Pair(other, child),
        }
    }

    pub open spec fn transition_child_actions(g: model::Graph, id: nat, action: ChildShape) -> Seq<ActionShape> {
        transition_children(g, id).reverse().map(|i: int, child: nat| transition_child_shape(action, child))
    }

    pub proof fn transition_lemma_child_action_valid(g: model::Graph, action: ChildShape, child: nat)
        requires transition_child_action_valid(g, action), child < g.transitions.len(),
        ensures transition_action_valid(g, transition_child_shape(action, child)),
    {}

    pub proof fn transition_lemma_empty_combos(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>, intersect: bool,
    )
        ensures transition_combo(g, sym, theta, Seq::empty(), event, word, intersect) == intersect,
            regex_combo(g, sym, theta, Seq::empty(), word, intersect) == intersect,
    {}


    pub proof fn transition_lemma_singleton_combo(
        g: model::Graph, id: TransitionId, sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>, intersect: bool,
    )
        ensures transition_combo(g, sym, theta, seq![id], event, word, intersect)
            == transition_lang(g, sym, theta, id, event, word),
    {
        hide(transition_lang);
        if intersect {
            if transition_combo(g, sym, theta, seq![id], event, word, true) {
                assert(transition_lang(g, sym, theta, seq![id][0], event, word));
            }
            if transition_lang(g, sym, theta, id, event, word) {
                assert forall|i: int| 0 <= i < 1 implies transition_lang(g, sym, theta, seq![id][i], event, word) by { assert(i == 0); }
            }
        } else {
            if transition_combo(g, sym, theta, seq![id], event, word, false) {
                let i = choose|i: int| 0 <= i < 1 && transition_lang(g, sym, theta, seq![id][i], event, word);
                assert(i == 0);
            }
            if transition_lang(g, sym, theta, id, event, word) {
                assert(transition_lang(g, sym, theta, seq![id][0], event, word));
            }
        }
    }

    pub proof fn transition_lemma_initial_collection(
        g: model::Graph, mode: TransitionModeModel, original: Seq<TransitionId>,
        pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>, collapsed: bool,
    )
        requires model::graph_wf(g), transition_mode_valid(g, mode),
            transition_collect_effect(g, mode, original, Seq::empty(), Seq::empty(), pending, flat, constants, collapsed),
            !collapsed ==> pending.len() == 0,
        ensures
            !collapsed ==> transition_collected(g, original, flat, constants, mode.intersect),
            collapsed ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_combo(g, sym, theta, original, event, word, mode.intersect)
                    == transition_lang(g, sym, theta, mode.absorber, event, word),
    {
        hide(transition_lang);
        hide(transition_combo);
        hide(regex_combo);
        transition_lemma_identities(g, mode);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_combo(g, sym, theta, original, event, word, mode.intersect)
                == if collapsed { transition_lang(g, sym, theta, mode.absorber, event, word) }
                    else { transition_collect_combo(g, sym, theta, Seq::empty(), flat, constants, event, word, mode.intersect) } by {
            transition_lemma_empty_combos(g, sym, theta, event, word, mode.intersect);
            assert(transition_collect_combo(g, sym, theta, original, Seq::empty(), Seq::empty(), event, word, mode.intersect)
                == if collapsed { !mode.intersect } else {
                    transition_collect_combo(g, sym, theta, pending, flat, constants, event, word, mode.intersect)
                });
            if !collapsed { assert(pending =~= Seq::<TransitionId>::empty()); }
        }
    }


    pub proof fn transition_action_views_push<T: View<V = ActionShape>>(tasks: Seq<T>, task: T)
        ensures transition_action_views(tasks.push(task)) == transition_action_views(tasks).push(task@),
    {
        assert(transition_action_views(tasks.push(task)) =~= transition_action_views(tasks).push(task@));
    }

    pub proof fn transition_lemma_child_actions_valid(g: model::Graph, id: nat, action: ChildShape)
        requires model::graph_wf(g), id < g.transitions.len(), transition_child_action_valid(g, action),
        ensures transition_tasks_valid(g, transition_child_actions(g, id, action)),
    {
        transition_lemma_children(g, id);
        assert forall|i: int| 0 <= i < transition_child_actions(g, id, action).len() implies
            transition_action_valid(g, transition_child_actions(g, id, action)[i]) by {
            let child = transition_children(g, id).reverse()[i];
            assert(child < g.transitions.len());
            transition_lemma_child_action_valid(g, action, child);
        }
    }


    pub open spec fn guarded_action_pushes<L>(action: GuardedAction<L>) -> bool {
        match action {
            GuardedAction::Clean(_, _) | GuardedAction::Not(_) | GuardedAction::Append(_, _) | GuardedAction::Pair(_, _) => true,
            GuardedAction::Fold(_, index) => index == 0,
            _ => false,
        }
    }

    pub open spec fn guarded_atomic_value<L, C>(
        sem: spec_fn(C, L, Data) -> bool, action: GuardedAction<L>,
    ) -> Option<GuardedTransition<L, C>> {
        match guarded_apply(sem, action, Seq::empty()) {
            Some(values) => if values.len() == 1 { Some(values[0]) } else { None },
            None => None,
        }
    }

    pub open spec fn guarded_atomic_values<L, C>(
        sem: spec_fn(C, L, Data) -> bool, actions: Seq<GuardedAction<L>>,
    ) -> Seq<GuardedTransition<L, C>> {
        actions.map(|i: int, action: GuardedAction<L>| guarded_atomic_value(sem, action).unwrap())
    }

    pub proof fn guarded_lemma_apply_push<L, C>(
        sem: spec_fn(C, L, Data) -> bool, action: GuardedAction<L>, values: Seq<GuardedTransition<L, C>>,
    )
        requires guarded_action_pushes(action),
        ensures guarded_atomic_value(sem, action) is Some,
            guarded_apply(sem, action, values) == Some(values.push(guarded_atomic_value(sem, action).unwrap())),
    {
        match action {
            GuardedAction::Clean(_, _) => {},
            GuardedAction::Not(_) => {},
            GuardedAction::Append(_, _) => {},
            GuardedAction::Pair(_, _) => {},
            GuardedAction::Fold(_, index) => {},
            _ => {},
        }
    }

    pub proof fn guarded_lemma_push_sequence<L, C>(
        sem: spec_fn(C, L, Data) -> bool, actions: Seq<GuardedAction<L>>, values: Seq<GuardedTransition<L, C>>,
    )
        requires forall|i: int| 0 <= i < actions.len() ==> guarded_action_pushes(actions[i]),
        ensures guarded_run(sem, actions.reverse(), values) == Some(values + guarded_atomic_values(sem, actions)),
        decreases actions.len(),
    {
        if actions.len() > 0 {
            let first = actions[0];
            let rest = actions.skip(1);
            guarded_lemma_apply_push(sem, first, values);
            let value = guarded_atomic_value(sem, first).unwrap();
            assert(actions.reverse().last() == first);
            assert(actions.reverse().drop_last() =~= rest.reverse());
            guarded_lemma_push_sequence(sem, rest, values.push(value));
            assert(guarded_atomic_values(sem, actions) =~= seq![value] + guarded_atomic_values(sem, rest));
            assert(values.push(value) + guarded_atomic_values(sem, rest) =~= values + guarded_atomic_values(sem, actions));
        } else {
            assert(actions.reverse() =~= Seq::<GuardedAction<L>>::empty());
            assert(guarded_atomic_values(sem, actions) =~= Seq::<GuardedTransition<L, C>>::empty());
        }
    }

    pub proof fn guarded_lemma_same_term<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        before: GuardedTransition<L, C>, after: GuardedTransition<L, C>,
    )
        requires before.term == after.term,
            forall|ctx: C, event: Data| valid(ctx) && #[trigger] (before.guard)(ctx, event) ==> (after.guard)(ctx, event),
        ensures guarded_refines(sem, valid, before, after),
    {}

    pub proof fn guarded_lemma_clean_set<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        terms: Seq<language::Transition<L>>, path: L, intersect: bool,
    )
        ensures guarded_refines(sem, valid,
            guarded_clean(sem, path, if intersect { language::Transition::Intersect(terms) } else { language::Transition::Union(terms) }),
            guarded_set(guarded_atomic_values(sem, terms.map(|i: int, term: language::Transition<L>| GuardedAction::Clean(term, path))), intersect)),
    {
        let actions = terms.map(|i: int, term: language::Transition<L>| GuardedAction::Clean(term, path));
        let values = guarded_atomic_values(sem, actions);
        assert(values.map(|i: int, value: GuardedTransition<L, C>| value.term) =~= terms);
        let before = guarded_clean(sem, path,
            if intersect { language::Transition::Intersect(terms) } else { language::Transition::Union(terms) });
        let after = guarded_set(values, intersect);
        assert forall|ctx: C, event: Data| valid(ctx) && #[trigger] (before.guard)(ctx, event)
            implies (after.guard)(ctx, event) by {
            assert forall|i: int| 0 <= i < values.len() implies (values[i].guard)(ctx, event) by {
                assert(values[i] == guarded_clean(sem, path, terms[i]));
            }
        }
        guarded_lemma_same_term(sem, valid, before, after);
    }

    pub proof fn guarded_lemma_apply_set_suffix<L, C>(
        sem: spec_fn(C, L, Data) -> bool, prefix: Seq<GuardedTransition<L, C>>, values: Seq<GuardedTransition<L, C>>, intersect: bool,
    )
        ensures guarded_apply(sem, if intersect { GuardedAction::Intersect(values.len()) } else { GuardedAction::Union(values.len()) },
            prefix + values) == Some(prefix.push(guarded_set(values, intersect))),
    {
        assert((prefix + values).take(prefix.len() as int) =~= prefix);
        assert((prefix + values).subrange(prefix.len() as int, (prefix + values).len() as int) =~= values);
    }


    pub open spec fn transition_action_pushes(task: ActionShape) -> bool {
        match task {
            ActionShape::Clean(_, _) | ActionShape::Not(_) | ActionShape::Append(_, _) | ActionShape::Pair(_, _) => true,
            ActionShape::Fold(_, index) => index == 0,
            _ => false,
        }
    }

    pub open spec fn transition_result(g: model::Graph, task: ActionShape, id: TransitionId) -> bool {
        match transition_initial_value(g, task) {
            Some(expected) => forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                model::symbols_wf(sym) && (expected.guard)(TransitionContext { symbols: sym, bindings: theta }, event)
                    ==> guarded_language(transition_context_sem(), TransitionContext { symbols: sym, bindings: theta }, event, expected, word)
                        == transition_lang(g, sym, theta, id, event, word),
            None => false,
        }
    }

    pub proof fn transition_lemma_known_push(g: model::Graph, values: Seq<TransitionId>, id: TransitionId)
        ensures transition_known_values(g, values.push(id)) == transition_known_values(g, values).push(transition_known(g, id)),
    {
        assert(transition_known_values(g, values.push(id)) =~= transition_known_values(g, values).push(transition_known(g, id)));
    }

    pub proof fn transition_lemma_result_refines(g: model::Graph, task: ActionShape, id: TransitionId)
        requires transition_result(g, task, id),
        ensures transition_initial_value(g, task) matches Some(expected)
            && guarded_refines(transition_context_sem(), transition_context_valid(), expected, transition_known(g, id)),
    {
        let expected = transition_initial_value(g, task).unwrap();
        assert forall|ctx: TransitionContext, event: Data| transition_context_valid()(ctx)
            && #[trigger] (expected.guard)(ctx, event)
            implies (transition_known(g, id).guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(transition_context_sem(), ctx, event, expected, word)
                    == guarded_language(transition_context_sem(), ctx, event, transition_known(g, id), word) by {
            assert(ctx == (TransitionContext { symbols: ctx.symbols, bindings: ctx.bindings }));
            assert forall|word: Seq<Data>| guarded_language(transition_context_sem(), ctx, event, expected, word)
                == guarded_language(transition_context_sem(), ctx, event, transition_known(g, id), word) by {
                transition_lemma_known_language(g, id, ctx, event, word);
                assert(guarded_language(transition_context_sem(), ctx, event, expected, word)
                    == transition_lang(g, ctx.symbols, ctx.bindings, id, event, word));
            }
        }
    }

    pub proof fn transition_lemma_push_result(
        g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>, id: TransitionId,
    )
        requires transition_action_pushes(task), transition_result(g, task, id),
        ensures transition_effect(g, task, pending, prior, pending, prior.push(id)),
    {
        transition_lemma_result_refines(g, task, id);
        let expected = transition_initial_value(g, task).unwrap();
        let known = transition_known_values(g, prior);
        guarded_lemma_stack_refl(transition_context_sem(), transition_context_valid(), known);
        guarded_lemma_stack_push(transition_context_sem(), transition_context_valid(), known, known, expected, transition_known(g, id));
        transition_lemma_known_push(g, prior, id);
        match task {
            ActionShape::Clean(_, _) => {},
            ActionShape::Not(_) => {},
            ActionShape::Append(_, _) => {},
            ActionShape::Pair(_, _) => {},
            ActionShape::Fold(_, index) => {},
            _ => {},
        }
    }

    pub proof fn transition_lemma_clean_children_effect(
        g: model::Graph, id: TransitionId, path: TestId, intersect: bool, base: Seq<ActionShape>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(), path@ < g.tests.len(),
            match g.transitions[id@ as int] {
                model::TransitionNode::Union(ids) => !intersect,
                model::TransitionNode::Intersect(ids) => intersect,
                _ => false,
            },
        ensures forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            transition_clean_child_tasks(g, id, path, intersect, base), prior),
    {
        transition_unfold(g, id@);
        transition_lemma_children(g, id@);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let children = transition_children(g, id@);
        let terms = children.map(|i: int, child: nat| model::lift_transition(g, child));
        let path_term = model::lift_test(g, path@);
        let actions = terms.map(|i: int, term: language::Transition<model::Test>| GuardedAction::Clean(term, path_term));
        let count = children.len();
        let set_shape = if intersect { ActionShape::Intersect(count) } else { ActionShape::Union(count) };
        let set_action = if intersect { GuardedAction::Intersect(count) } else { GuardedAction::Union(count) };
        let suffix = transition_child_actions(g, id@, ChildShape::Clean(path@));
        assert(transition_freeze_tasks(g, suffix) =~= actions.reverse());
        let values = guarded_atomic_values(sem, actions);
        guarded_lemma_clean_set(sem, valid, terms, path_term, intersect);
        assert forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            transition_clean_child_tasks(g, id, path, intersect, base), prior) by {
            let known = transition_known_values(g, prior);
            guarded_lemma_push_sequence(sem, actions, known);
            guarded_lemma_run_prefix(sem, seq![set_action], actions.reverse(), known);
            guarded_lemma_run_singleton(sem, set_action, known + values);
            guarded_lemma_apply_set_suffix(sem, known, values, intersect);
            let expected = guarded_clean(sem, path_term, model::lift_transition(g, id@));
            let result = guarded_set(values, intersect);
            guarded_lemma_stack_refl(sem, valid, known);
            guarded_lemma_stack_push(sem, valid, known, known, expected, result);
            let tasks = base.push(set_shape) + suffix;
            assert(tasks.subrange(base.len() as int, tasks.len() as int) =~= seq![set_shape] + suffix);
            assert(transition_freeze_tasks(g, seq![set_shape] + suffix) =~= seq![set_action] + actions.reverse());
        }
    }


    pub open spec fn transition_clean_child_tasks(
        g: model::Graph, id: TransitionId, path: TestId, intersect: bool, base: Seq<ActionShape>,
    ) -> Seq<ActionShape> {
        base.push(if intersect { ActionShape::Intersect(transition_children(g, id@).len()) }
            else { ActionShape::Union(transition_children(g, id@).len()) })
            + transition_child_actions(g, id@, ChildShape::Clean(path@))
    }


    pub open spec fn transition_configuration_valid(g: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>) -> bool {
        transition_tasks_valid(g, tasks) && transition_ids_valid(g, values)
    }


    pub proof fn transition_lemma_refines_result(g: model::Graph, task: ActionShape, id: TransitionId)
        requires transition_initial_value(g, task) matches Some(expected)
            && guarded_refines(transition_context_sem(), transition_context_valid(), expected, transition_known(g, id)),
        ensures transition_result(g, task, id),
    {
        let expected = transition_initial_value(g, task).unwrap();
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            model::symbols_wf(sym) && (expected.guard)(TransitionContext { symbols: sym, bindings: theta }, event)
            implies #[trigger] guarded_language(transition_context_sem(), TransitionContext { symbols: sym, bindings: theta }, event, expected, word)
                == transition_lang(g, sym, theta, id, event, word) by {
            let ctx = TransitionContext { symbols: sym, bindings: theta };
            transition_lemma_known_language(g, id, ctx, event, word);
            assert(guarded_language(transition_context_sem(), ctx, event, expected, word)
                == guarded_language(transition_context_sem(), ctx, event, transition_known(g, id), word));
        }
    }

    pub proof fn transition_lemma_result_same_term(g: model::Graph, task: ActionShape, id: TransitionId)
        requires transition_initial_value(g, task) matches Some(expected)
            && expected.term == model::lift_transition(g, id@),
        ensures transition_result(g, task, id),
    {
        let expected = transition_initial_value(g, task).unwrap();
        guarded_lemma_same_term(transition_context_sem(), transition_context_valid(), expected, transition_known(g, id));
        transition_lemma_refines_result(g, task, id);
    }

    pub proof fn transition_lemma_clean_identity(g: model::Graph, id: TransitionId, path: TestId)
        ensures transition_result(g, ActionShape::Clean(id@, path@), id),
    {
        transition_lemma_result_same_term(g, ActionShape::Clean(id@, path@), id);
    }

    pub proof fn transition_lemma_constants(g: model::Graph)
        requires model::graph_wf(g),
        ensures model::constants_wf(g),
    {
        model::lemma_graph_wf_elim(g);
    }


    pub open spec fn guarded_clean_branch<L, C>(
        sem: spec_fn(C, L, Data) -> bool, test: L, path: L, yes: L, no: L,
        left: language::Transition<L>, right: language::Transition<L>, yes_false: bool, no_false: bool,
    ) -> GuardedTransition<L, C> {
        if yes_false { guarded_clean(sem, no, right) }
        else if no_false { guarded_clean(sem, yes, left) }
        else { guarded_if(sem, test, guarded_clean(sem, yes, left), guarded_clean(sem, no, right)) }
    }

    pub proof fn guarded_lemma_clean_branches<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool, test: L, path: L, yes: L, no: L,
        left: language::Transition<L>, right: language::Transition<L>, yes_false: bool, no_false: bool,
    )
        requires
            forall|ctx: C, event: Data| valid(ctx) ==> #[trigger] sem(ctx, yes, event) == (sem(ctx, path, event) && sem(ctx, test, event)),
            forall|ctx: C, event: Data| valid(ctx) ==> #[trigger] sem(ctx, no, event) == (sem(ctx, path, event) && !sem(ctx, test, event)),
            yes_false ==> forall|ctx: C, event: Data| valid(ctx) ==> #[trigger] sem(ctx, yes, event) == false,
            no_false ==> forall|ctx: C, event: Data| valid(ctx) ==> #[trigger] sem(ctx, no, event) == false,
        ensures guarded_refines(sem, valid,
            guarded_clean(sem, path, language::Transition::If(test, Box::new(left), Box::new(right))),
            guarded_clean_branch(sem, test, path, yes, no, left, right, yes_false, no_false)),
    {
        let before = guarded_clean(sem, path, language::Transition::If(test, Box::new(left), Box::new(right)));
        let after = guarded_clean_branch(sem, test, path, yes, no, left, right, yes_false, no_false);
        assert forall|ctx: C, event: Data| valid(ctx) && #[trigger] (before.guard)(ctx, event)
            implies (after.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, before, word) == guarded_language(sem, ctx, event, after, word) by {
            assert(sem(ctx, path, event));
            assert(sem(ctx, yes, event) == sem(ctx, test, event));
            assert(sem(ctx, no, event) == !sem(ctx, test, event));
            if yes_false { assert(!sem(ctx, test, event)); }
            else if no_false { assert(sem(ctx, test, event)); }
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, before, word)
                == guarded_language(sem, ctx, event, after, word) by {
                let context_sem = guarded_semantics(sem, ctx);
                language::lemma_interp_if(context_sem, event, test, left, right);
                if !yes_false && !no_false {
                    language::lemma_interp_if(context_sem, event, test, left, right);
                }
            }
        }
    }

    pub open spec fn guarded_clean_branch_tasks<L>(
        test: L, yes: L, no: L, left: language::Transition<L>, right: language::Transition<L>, yes_false: bool, no_false: bool,
    ) -> Seq<GuardedAction<L>> {
        if yes_false { seq![GuardedAction::Clean(right, no)] }
        else if no_false { seq![GuardedAction::Clean(left, yes)] }
        else { seq![GuardedAction::If(test), GuardedAction::Clean(right, no), GuardedAction::Clean(left, yes)] }
    }

    pub proof fn guarded_lemma_clean_branch_run<L, C>(
        sem: spec_fn(C, L, Data) -> bool, test: L, path: L, yes: L, no: L,
        left: language::Transition<L>, right: language::Transition<L>, yes_false: bool, no_false: bool,
        prefix: Seq<GuardedTransition<L, C>>,
    )
        ensures guarded_run(sem, guarded_clean_branch_tasks(test, yes, no, left, right, yes_false, no_false), prefix)
            == Some(prefix.push(guarded_clean_branch(sem, test, path, yes, no, left, right, yes_false, no_false))),
    {
        reveal_with_fuel(guarded_run, 5);
        if !yes_false && !no_false {
            let a = guarded_clean(sem, yes, left);
            let b = guarded_clean(sem, no, right);
            assert(prefix.push(a).push(b).take(prefix.len() as int) =~= prefix);
        }
    }


    pub proof fn transition_test_not_extends(before: model::Graph, after: model::Graph, root: TestId, negated: TestId)
        requires model::graph_wf(before), model::graph_extends(before, after), root@ < before.tests.len(), negated@ < before.tests.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> model::test_holds(sym, theta, model::lift_test(before, negated@), event)
                    == !model::test_holds(sym, theta, model::lift_test(before, root@), event),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
            ==> model::test_holds(sym, theta, model::lift_test(after, negated@), event)
                == !model::test_holds(sym, theta, model::lift_test(after, root@), event),
    {
        hide(model::test_holds);
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_stable_under_extends(before, after);
    }

    pub proof fn transition_lemma_test_pair(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, left: TestId, right: TestId, event: Data,
    )
        ensures test_combo(g, sym, theta, seq![left, right], event, true)
            == (model::test_holds(sym, theta, model::lift_test(g, left@), event)
                && model::test_holds(sym, theta, model::lift_test(g, right@), event)),
    {
        hide(model::test_holds);
        if test_combo(g, sym, theta, seq![left, right], event, true) {
            assert(model::test_holds(sym, theta, model::lift_test(g, seq![left, right][0]@), event));
            assert(model::test_holds(sym, theta, model::lift_test(g, seq![left, right][1]@), event));
        }
        if model::test_holds(sym, theta, model::lift_test(g, left@), event)
            && model::test_holds(sym, theta, model::lift_test(g, right@), event) {
            assert forall|i: int| 0 <= i < 2 implies
                model::test_holds(sym, theta, model::lift_test(g, seq![left, right][i]@), event) by {
                if i == 0 {} else { assert(i == 1); }
            }
        }
    }

    pub proof fn transition_lemma_test_constants(g: model::Graph)
        requires model::graph_wf(g),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data|
            model::test_holds(sym, theta, model::lift_test(g, g.constants.test_true), event)
                && !model::test_holds(sym, theta, model::lift_test(g, g.constants.test_false), event),
    {
        transition_lemma_constants(g);
        assert(model::lift_test(g, g.constants.test_true) == model::Test::True);
        assert(model::lift_test(g, g.constants.test_false) == model::Test::False);
    }

    pub open spec fn transition_path_tests(g: model::Graph, path: TestId, test: TestId, yes: TestId, no: TestId) -> bool {
        forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym) ==>
            (model::test_holds(sym, theta, model::lift_test(g, yes@), event)
                == (model::test_holds(sym, theta, model::lift_test(g, path@), event)
                    && model::test_holds(sym, theta, model::lift_test(g, test@), event)))
            && (model::test_holds(sym, theta, model::lift_test(g, no@), event)
                == (model::test_holds(sym, theta, model::lift_test(g, path@), event)
                    && !model::test_holds(sym, theta, model::lift_test(g, test@), event)))
    }

    pub open spec fn transition_clean_if_tasks(
        g: model::Graph, test: TestId, left: TransitionId, right: TransitionId, yes: TestId, no: TestId, base: Seq<ActionShape>,
    ) -> Seq<ActionShape> {
        if yes@ == g.constants.test_false { base.push(ActionShape::Clean(right@, no@)) }
        else if no@ == g.constants.test_false { base.push(ActionShape::Clean(left@, yes@)) }
        else { base.push(ActionShape::If(test@)).push(ActionShape::Clean(right@, no@)).push(ActionShape::Clean(left@, yes@)) }
    }

    pub proof fn transition_lemma_clean_if_effect(
        g: model::Graph, id: TransitionId, path: TestId, test: TestId,
        left: TransitionId, right: TransitionId, yes: TestId, no: TestId, base: Seq<ActionShape>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::If(test@, left@, right@),
            transition_path_tests(g, path, test, yes, no),
        ensures forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            transition_clean_if_tasks(g, test, left, right, yes, no, base), prior),
    {
        transition_unfold(g, id@);
        transition_lemma_test_constants(g);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let condition = model::lift_test(g, test@);
        let path_term = model::lift_test(g, path@);
        let yes_term = model::lift_test(g, yes@);
        let no_term = model::lift_test(g, no@);
        let a = model::lift_transition(g, left@);
        let b = model::lift_transition(g, right@);
        let yes_false = yes@ == g.constants.test_false;
        let no_false = no@ == g.constants.test_false;
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) implies
            #[trigger] sem(ctx, yes_term, event) == (sem(ctx, path_term, event) && sem(ctx, condition, event)) by {
            assert(model::test_holds(ctx.symbols, ctx.bindings, yes_term, event)
                == (model::test_holds(ctx.symbols, ctx.bindings, path_term, event)
                    && model::test_holds(ctx.symbols, ctx.bindings, condition, event)));
        }
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) implies
            #[trigger] sem(ctx, no_term, event) == (sem(ctx, path_term, event) && !sem(ctx, condition, event)) by {
            assert(model::test_holds(ctx.symbols, ctx.bindings, no_term, event)
                == (model::test_holds(ctx.symbols, ctx.bindings, path_term, event)
                    && !model::test_holds(ctx.symbols, ctx.bindings, condition, event)));
        }
        guarded_lemma_clean_branches(sem, valid, condition, path_term, yes_term, no_term, a, b, yes_false, no_false);
        let expansion = guarded_clean_branch_tasks(condition, yes_term, no_term, a, b, yes_false, no_false);
        let next_tasks = transition_clean_if_tasks(g, test, left, right, yes, no, base);
        assert(transition_freeze_tasks(g, next_tasks.subrange(base.len() as int, next_tasks.len() as int)) =~= expansion);
        assert forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            next_tasks, prior) by {
            let known = transition_known_values(g, prior);
            guarded_lemma_clean_branch_run(sem, condition, path_term, yes_term, no_term, a, b, yes_false, no_false, known);
            guarded_lemma_stack_refl(sem, valid, known);
            guarded_lemma_stack_push(sem, valid, known, known,
                guarded_clean(sem, path_term, model::lift_transition(g, id@)),
                guarded_clean_branch(sem, condition, path_term, yes_term, no_term, a, b, yes_false, no_false));
        }
    }

    pub proof fn transition_configuration_extends(
        before: model::Graph, after: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>,
    )
        requires model::graph_wf(before), model::graph_extends(before, after), transition_configuration_valid(before, tasks, values),
        ensures transition_configuration_valid(after, tasks, values),
    {
        assert forall|i: int| 0 <= i < tasks.len() implies transition_action_valid(after, tasks[i]) by {
            transition_lemma_action_stable(before, after, tasks[i]);
        }
    }

    pub proof fn transition_configuration_future(g: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>)
        requires model::graph_wf(g), transition_configuration_valid(g, tasks, values),
        ensures forall|next: model::Graph| model::graph_extends(g, next) ==> transition_configuration_valid(next, tasks, values),
    {
        assert forall|next: model::Graph| model::graph_extends(g, next) implies transition_configuration_valid(next, tasks, values) by {
            transition_configuration_extends(g, next, tasks, values);
        }
    }


    pub proof fn machine_pair_binary_language<L>(
        sem: spec_fn(L, Data) -> bool, event: Data,
        a: language::Transition<L>, b: language::Transition<L>, word: Seq<Data>,
    )
        ensures language::lang(sem, language::interp_transition(sem, event,
            language::Transition::Intersect(seq![a, b])), word)
            == (language::lang(sem, language::interp_transition(sem, event, a), word)
                && language::lang(sem, language::interp_transition(sem, event, b), word)),
    {
        language::lemma_interp_intersect(sem, event, seq![a, b], word);
        assert((forall|i: int| 0 <= i < 2 ==> language::lang(sem,
            language::interp_transition(sem, event, seq![a, b][i]), word))
            == (language::lang(sem, language::interp_transition(sem, event, a), word)
                && language::lang(sem, language::interp_transition(sem, event, b), word))) by {
            assert forall|i: int| 0 <= i < 2 implies language::lang(sem,
                language::interp_transition(sem, event, seq![a, b][i]), word)
                    == if i == 0 { language::lang(sem, language::interp_transition(sem, event, a), word) }
                    else { language::lang(sem, language::interp_transition(sem, event, b), word) } by {}
        }
    }

    pub proof fn machine_pair_effect_intro(
        g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
        expansion: Seq<ActionShape>, values: Seq<TransitionId>, result: TransitionMeaning,
    )
        requires transition_action_pushes(task),
            guarded_run(transition_context_sem(), transition_freeze_tasks(g, expansion), transition_known_values(g, values))
                == Some(transition_known_values(g, prior).push(result)),
            guarded_refines(transition_context_sem(), transition_context_valid(),
                transition_initial_value(g, task).unwrap(), result),
        ensures transition_effect(g, task, pending, prior, pending + expansion, values),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let known = transition_known_values(g, prior);
        guarded_lemma_apply_push(sem, transition_freeze_action(g, task), known);
        assert(guarded_atomic_value(sem, transition_freeze_action(g, task)) == transition_initial_value(g, task));
        guarded_lemma_stack_refl(sem, valid, known);
        guarded_lemma_stack_push(sem, valid, known, known, transition_initial_value(g, task).unwrap(), result);
        assert((pending + expansion).subrange(pending.len() as int, (pending + expansion).len() as int) =~= expansion);
    }

    pub proof fn machine_pair_set_result(
        g: model::Graph, ids: Seq<TransitionId>, task: ActionShape, out: TransitionId,
    )
        requires task == ActionShape::Fold(model::transition_ids(ids), 0)
                || (ids.len() == 2 && task == ActionShape::Pair(ids[0]@, ids[1]@)),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(g, sym, theta, out, event, word)
                    == transition_combo(g, sym, theta, ids, event, word, true),
        ensures transition_result(g, task, out),
    {
        let terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
        let expected = transition_initial_value(g, task).unwrap();
        if ids.len() == 2 && task == ActionShape::Pair(ids[0]@, ids[1]@) {
            assert(terms =~= seq![model::lift_transition(g, ids[0]@), model::lift_transition(g, ids[1]@)]);
        }
        assert(expected.term == language::Transition::Intersect(terms));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            model::symbols_wf(sym) && (expected.guard)(TransitionContext { symbols: sym, bindings: theta }, event)
            implies guarded_language(transition_context_sem(), TransitionContext { symbols: sym, bindings: theta }, event, expected, word)
                == transition_lang(g, sym, theta, out, event, word) by {
            let ctx = TransitionContext { symbols: sym, bindings: theta };
            transition_lemma_context_sem(ctx);
            language::lemma_interp_intersect(model::gsem(sym, theta), event, terms, word);
            assert forall|i: int| 0 <= i < ids.len() implies
                language::lang(model::gsem(sym, theta), language::interp_transition(model::gsem(sym, theta), event, terms[i]), word)
                    == transition_lang(g, sym, theta, ids[i], event, word) by {
                assert(terms[i] == model::lift_transition(g, ids[i]@));
            }
            assert(transition_lang(g, sym, theta, out, event, word)
                == transition_combo(g, sym, theta, ids, event, word, true));
        }
    }

    pub proof fn machine_pair_identity_result(
        g: model::Graph, a: TransitionId, b: TransitionId, out: TransitionId, all: TransitionId, empty: TransitionId,
    )
        requires model::graph_wf(g), all@ == g.constants.transition_all, empty@ == g.constants.transition_empty,
            (a == b && out == a)
            || (b@ == g.constants.transition_all && out == a)
            || (a@ == g.constants.transition_all && out == b)
            || ((a@ == g.constants.transition_empty || b@ == g.constants.transition_empty)
                && out@ == g.constants.transition_empty),
        ensures transition_result(g, ActionShape::Pair(a@, b@), out),
    {
        transition_lemma_constants(g);
        transition_lemma_identities(g, TransitionModeModel { intersect: true, identity: all, absorber: empty });
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(g, sym, theta, out, event, word)
                == transition_combo(g, sym, theta, seq![a, b], event, word, true) by {
            assert(transition_lang(g, sym, theta, all, event, word));
            assert(!transition_lang(g, sym, theta, empty, event, word));
        }
        machine_pair_set_result(g, seq![a, b], ActionShape::Pair(a@, b@), out);
    }

    pub proof fn machine_pair_if_run<L, C>(
        sem: spec_fn(C, L, Data) -> bool, test: L, path: L,
        at: language::Transition<L>, bt: language::Transition<L>,
        ae: language::Transition<L>, be: language::Transition<L>, prefix: Seq<GuardedTransition<L, C>>,
    )
        ensures guarded_run(sem, seq![GuardedAction::CleanIf(test, path), GuardedAction::Pair(ae, be), GuardedAction::Pair(at, bt)], prefix)
            == Some(prefix.push(guarded_clean_if(sem, test, path,
                guarded_constant(language::Transition::Intersect(seq![at, bt])),
                guarded_constant(language::Transition::Intersect(seq![ae, be]))))),
    {
        reveal_with_fuel(guarded_run, 5);
        let yes = guarded_constant(language::Transition::Intersect(seq![at, bt]));
        let no = guarded_constant(language::Transition::Intersect(seq![ae, be]));
        assert(prefix.push(yes).push(no).take(prefix.len() as int) =~= prefix);
    }

    pub proof fn machine_pair_if_refines(
        g: model::Graph, a: TransitionId, b: TransitionId, test: TestId,
        at: TransitionId, bt: TransitionId, ae: TransitionId, be: TransitionId,
    )
        requires model::graph_wf(g),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> (transition_lang(g, sym, theta, a, event, word) && transition_lang(g, sym, theta, b, event, word))
                    == if model::test_holds(sym, theta, model::lift_test(g, test@), event) {
                        transition_lang(g, sym, theta, at, event, word) && transition_lang(g, sym, theta, bt, event, word)
                    } else { transition_lang(g, sym, theta, ae, event, word) && transition_lang(g, sym, theta, be, event, word) },
        ensures guarded_refines(transition_context_sem(), transition_context_valid(),
            transition_initial_value(g, ActionShape::Pair(a@, b@)).unwrap(),
            guarded_clean_if(transition_context_sem(), model::lift_test(g, test@), model::lift_test(g, g.constants.test_true),
                guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, at@), model::lift_transition(g, bt@)])),
                guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, ae@), model::lift_transition(g, be@)])))),
    {
        transition_lemma_constants(g);
        let before = transition_initial_value(g, ActionShape::Pair(a@, b@)).unwrap();
        let yes = guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, at@), model::lift_transition(g, bt@)]));
        let no = guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, ae@), model::lift_transition(g, be@)]));
        let after = guarded_clean_if(transition_context_sem(), model::lift_test(g, test@), model::lift_test(g, g.constants.test_true), yes, no);
        assert forall|ctx: TransitionContext, event: Data| transition_context_valid()(ctx) && #[trigger] (before.guard)(ctx, event)
            implies (after.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(transition_context_sem(), ctx, event, before, word)
                    == guarded_language(transition_context_sem(), ctx, event, after, word) by {
            transition_lemma_context_sem(ctx);
            assert forall|word: Seq<Data>| guarded_language(transition_context_sem(), ctx, event, before, word)
                == guarded_language(transition_context_sem(), ctx, event, after, word) by {
                let sem = model::gsem(ctx.symbols, ctx.bindings);
                machine_pair_binary_language(sem, event, model::lift_transition(g, a@), model::lift_transition(g, b@), word);
                machine_pair_binary_language(sem, event, model::lift_transition(g, at@), model::lift_transition(g, bt@), word);
                machine_pair_binary_language(sem, event, model::lift_transition(g, ae@), model::lift_transition(g, be@), word);
                language::lemma_interp_if(sem, event, model::lift_test(g, test@), yes.term, no.term);
                assert((transition_lang(g, ctx.symbols, ctx.bindings, a, event, word)
                    && transition_lang(g, ctx.symbols, ctx.bindings, b, event, word))
                    == if model::test_holds(ctx.symbols, ctx.bindings, model::lift_test(g, test@), event) {
                        transition_lang(g, ctx.symbols, ctx.bindings, at, event, word) && transition_lang(g, ctx.symbols, ctx.bindings, bt, event, word)
                    } else { transition_lang(g, ctx.symbols, ctx.bindings, ae, event, word) && transition_lang(g, ctx.symbols, ctx.bindings, be, event, word) });
            }
        }
    }

    pub proof fn machine_pair_if_effect(
        g: model::Graph, a: TransitionId, b: TransitionId, test: TestId,
        at: TransitionId, bt: TransitionId, ae: TransitionId, be: TransitionId,
        pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> (transition_lang(g, sym, theta, a, event, word) && transition_lang(g, sym, theta, b, event, word))
                    == if model::test_holds(sym, theta, model::lift_test(g, test@), event) {
                        transition_lang(g, sym, theta, at, event, word) && transition_lang(g, sym, theta, bt, event, word)
                    } else { transition_lang(g, sym, theta, ae, event, word) && transition_lang(g, sym, theta, be, event, word) },
        ensures transition_effect(g, ActionShape::Pair(a@, b@), pending, prior,
            pending.push(ActionShape::CleanIf(test@, g.constants.test_true))
                .push(ActionShape::Pair(ae@, be@)).push(ActionShape::Pair(at@, bt@)), prior),
    {
        let expansion = seq![ActionShape::CleanIf(test@, g.constants.test_true), ActionShape::Pair(ae@, be@), ActionShape::Pair(at@, bt@)];
        machine_pair_if_run(transition_context_sem(), model::lift_test(g, test@), model::lift_test(g, g.constants.test_true),
            model::lift_transition(g, at@), model::lift_transition(g, bt@), model::lift_transition(g, ae@), model::lift_transition(g, be@), transition_known_values(g, prior));
        assert(transition_freeze_tasks(g, expansion) =~= seq![GuardedAction::CleanIf(model::lift_test(g, test@), model::lift_test(g, g.constants.test_true)),
            GuardedAction::Pair(model::lift_transition(g, ae@), model::lift_transition(g, be@)),
            GuardedAction::Pair(model::lift_transition(g, at@), model::lift_transition(g, bt@))]);
        machine_pair_if_refines(g, a, b, test, at, bt, ae, be);
        let result = guarded_clean_if(transition_context_sem(), model::lift_test(g, test@), model::lift_test(g, g.constants.test_true),
            guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, at@), model::lift_transition(g, bt@)])),
            guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, ae@), model::lift_transition(g, be@)])));
        machine_pair_effect_intro(g, ActionShape::Pair(a@, b@), pending, prior, expansion, prior, result);
        assert(pending + expansion =~= pending.push(expansion[0]).push(expansion[1]).push(expansion[2]));
    }

    pub proof fn machine_pair_if_language(
        g: model::Graph, id: TransitionId, test: TestId, yes: TransitionId, no: TransitionId,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::If(test@, yes@, no@),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, id, event, word)
                == if model::test_holds(sym, theta, model::lift_test(g, test@), event) {
                    transition_lang(g, sym, theta, yes, event, word)
                } else { transition_lang(g, sym, theta, no, event, word) },
    {
        transition_unfold(g, id@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
            transition_lang(g, sym, theta, id, event, word)
                == if model::test_holds(sym, theta, model::lift_test(g, test@), event) {
                    transition_lang(g, sym, theta, yes, event, word)
                } else { transition_lang(g, sym, theta, no, event, word) } by {
            language::lemma_interp_if(model::gsem(sym, theta), event, model::lift_test(g, test@),
                model::lift_transition(g, yes@), model::lift_transition(g, no@));
        }
    }

    pub proof fn machine_pair_empty_run<L, C>(
        sem: spec_fn(C, L, Data) -> bool, test: L, path: L,
        a: language::Transition<L>, b: language::Transition<L>, empty: GuardedTransition<L, C>,
        prefix: Seq<GuardedTransition<L, C>>,
    )
        ensures guarded_run(sem, seq![GuardedAction::CleanIf(test, path), GuardedAction::SwapThen, GuardedAction::Pair(a, b)], prefix.push(empty))
            == Some(prefix.push(guarded_clean_if(sem, test, path,
                guarded_constant(language::Transition::Intersect(seq![a, b])), empty))),
    {
        reveal_with_fuel(guarded_run, 5);
        let pair = guarded_constant(language::Transition::Intersect(seq![a, b]));
        assert(prefix.push(empty).push(pair).take(prefix.len() as int) =~= prefix);
        assert(prefix.push(pair).push(empty).take(prefix.len() as int) =~= prefix);
    }

    pub proof fn machine_pair_empty_effect(
        g: model::Graph, a: TransitionId, b: TransitionId, xt: TransitionId, yt: TransitionId,
        guard: TestId, empty: TransitionId, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), empty@ == g.constants.transition_empty,
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> (transition_lang(g, sym, theta, a, event, word) && transition_lang(g, sym, theta, b, event, word))
                    == (model::test_holds(sym, theta, model::lift_test(g, guard@), event)
                        && transition_lang(g, sym, theta, xt, event, word) && transition_lang(g, sym, theta, yt, event, word)),
        ensures transition_effect(g, ActionShape::Pair(a@, b@), pending, prior,
            pending.push(ActionShape::CleanIf(guard@, g.constants.test_true)).push(ActionShape::SwapThen)
                .push(ActionShape::Pair(xt@, yt@)), prior.push(empty)),
    {
        transition_lemma_constants(g);
        transition_unfold(g, empty@);
        regex_unfold(g, g.constants.empty);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let yes = guarded_constant(language::Transition::Intersect(seq![model::lift_transition(g, xt@), model::lift_transition(g, yt@)]));
        let no = transition_known(g, empty);
        let result = guarded_clean_if(sem, model::lift_test(g, guard@), model::lift_test(g, g.constants.test_true), yes, no);
        let expected = transition_initial_value(g, ActionShape::Pair(a@, b@)).unwrap();
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, expected, word) == guarded_language(sem, ctx, event, result, word) by {
            transition_lemma_context_sem(ctx);
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
                let context_sem = model::gsem(ctx.symbols, ctx.bindings);
                machine_pair_binary_language(context_sem, event, model::lift_transition(g, a@), model::lift_transition(g, b@), word);
                machine_pair_binary_language(context_sem, event, model::lift_transition(g, xt@), model::lift_transition(g, yt@), word);
                language::lemma_interp_if(context_sem, event, model::lift_test(g, guard@), yes.term, no.term);
                language::lemma_interp_const(context_sem, event, language::Regex::Empty);
                assert((transition_lang(g, ctx.symbols, ctx.bindings, a, event, word)
                    && transition_lang(g, ctx.symbols, ctx.bindings, b, event, word))
                    == (model::test_holds(ctx.symbols, ctx.bindings, model::lift_test(g, guard@), event)
                        && transition_lang(g, ctx.symbols, ctx.bindings, xt, event, word)
                        && transition_lang(g, ctx.symbols, ctx.bindings, yt, event, word)));
            }
        }
        let expansion = seq![ActionShape::CleanIf(guard@, g.constants.test_true), ActionShape::SwapThen, ActionShape::Pair(xt@, yt@)];
        assert(transition_freeze_tasks(g, expansion) =~= seq![GuardedAction::CleanIf(model::lift_test(g, guard@), model::lift_test(g, g.constants.test_true)),
            GuardedAction::SwapThen, GuardedAction::Pair(model::lift_transition(g, xt@), model::lift_transition(g, yt@))]);
        transition_lemma_known_push(g, prior, empty);
        machine_pair_empty_run(sem, model::lift_test(g, guard@), model::lift_test(g, g.constants.test_true),
            model::lift_transition(g, xt@), model::lift_transition(g, yt@), no, transition_known_values(g, prior));
        machine_pair_effect_intro(g, ActionShape::Pair(a@, b@), pending, prior, expansion, prior.push(empty), result);
        assert(pending + expansion =~= pending.push(expansion[0]).push(expansion[1]).push(expansion[2]));
    }

    pub proof fn machine_pair_fold_noop(
        g: model::Graph, ids: Seq<TransitionId>, index: nat, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires index > 0, index >= ids.len(),
        ensures transition_effect(g, ActionShape::Fold(model::transition_ids(ids), index), pending, prior, pending, prior),
    {
        guarded_lemma_stack_refl(transition_context_sem(), transition_context_valid(), transition_known_values(g, prior));
        assert(pending.subrange(pending.len() as int, pending.len() as int) =~= Seq::<ActionShape>::empty());
        assert(transition_freeze_tasks(g, Seq::empty()) =~= Seq::<TransitionAction>::empty());
    }

    #[verifier::spinoff_prover]
    pub proof fn machine_pair_union_effect(
        g: model::Graph, a: TransitionId, b: TransitionId, left: bool,
        pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), a@ < g.transitions.len(), b@ < g.transitions.len(),
            match g.transitions[(if left { a@ } else { b@ }) as int] { model::TransitionNode::Union(_) => true, _ => false },
        ensures transition_effect(g, ActionShape::Pair(a@, b@), pending, prior,
            pending.push(ActionShape::Union(transition_children(g, if left { a@ } else { b@ }).len()))
                + transition_child_actions(g, if left { a@ } else { b@ },
                    if left { ChildShape::PairLeft(b@) } else { ChildShape::PairRight(a@) }), prior),
    {
        hide(model::symbols_wf);
        hide(model::test_holds);
        hide(model::lift_regex);
        hide(model::lift_transition);
        hide(language::lang);
        hide(language::interp_transition);
        let root = if left { a } else { b };
        transition_unfold(g, root@);
        transition_lemma_children(g, root@);
        let children = transition_children(g, root@);
        let terms = children.map(|i: int, child: nat| model::lift_transition(g, child));
        let actions = children.map(|i: int, child: nat| if left {
            GuardedAction::Pair(model::lift_transition(g, child), model::lift_transition(g, b@))
        } else { GuardedAction::Pair(model::lift_transition(g, a@), model::lift_transition(g, child)) });
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let values = guarded_atomic_values(sem, actions);
        let expected = transition_initial_value(g, ActionShape::Pair(a@, b@)).unwrap();
        let result = guarded_set(values, false);
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, expected, word) == guarded_language(sem, ctx, event, result, word) by {
            assert forall|i: int| 0 <= i < values.len() implies (values[i].guard)(ctx, event) by {
                assert(actions[i] == if left {
                    GuardedAction::Pair(terms[i], model::lift_transition(g, b@))
                } else { GuardedAction::Pair(model::lift_transition(g, a@), terms[i]) });
            }
            transition_lemma_context_sem(ctx);
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
                let context_sem = model::gsem(ctx.symbols, ctx.bindings);
                let outputs = values.map(|i: int, value: TransitionMeaning| value.term);
                machine_pair_binary_language(context_sem, event, model::lift_transition(g, a@), model::lift_transition(g, b@), word);
                language::lemma_interp_union(context_sem, event, terms, word);
                language::lemma_interp_union(context_sem, event, outputs, word);
                assert forall|i: int| 0 <= i < children.len() implies
                    language::lang(context_sem, language::interp_transition(context_sem, event, outputs[i]), word)
                        == if left {
                            language::lang(context_sem, language::interp_transition(context_sem, event, terms[i]), word)
                                && transition_lang(g, ctx.symbols, ctx.bindings, b, event, word)
                        } else { transition_lang(g, ctx.symbols, ctx.bindings, a, event, word)
                            && language::lang(context_sem, language::interp_transition(context_sem, event, terms[i]), word) } by {
                    if left { machine_pair_binary_language(context_sem, event, terms[i], model::lift_transition(g, b@), word); }
                    else { machine_pair_binary_language(context_sem, event, model::lift_transition(g, a@), terms[i], word); }
                }
                if guarded_language(sem, ctx, event, expected, word) {
                    let i = choose|i: int| 0 <= i < terms.len()
                        && language::lang(context_sem, language::interp_transition(context_sem, event, terms[i]), word);
                    assert(language::lang(context_sem, language::interp_transition(context_sem, event, outputs[i]), word));
                }
                if guarded_language(sem, ctx, event, result, word) {
                    let i = choose|i: int| 0 <= i < outputs.len()
                        && language::lang(context_sem, language::interp_transition(context_sem, event, outputs[i]), word);
                    assert(language::lang(context_sem, language::interp_transition(context_sem, event, terms[i]), word));
                    assert(language::lang(context_sem, language::interp_transition(context_sem, event, language::Transition::Union(terms)), word));
                }
            }
        }
        let suffix = transition_child_actions(g, root@, if left { ChildShape::PairLeft(b@) } else { ChildShape::PairRight(a@) });
        assert(transition_freeze_tasks(g, suffix) =~= actions.reverse());
        guarded_lemma_push_sequence(sem, actions, transition_known_values(g, prior));
        guarded_lemma_run_prefix(sem, seq![GuardedAction::Union(children.len())], actions.reverse(), transition_known_values(g, prior));
        guarded_lemma_run_singleton(sem, GuardedAction::Union(children.len()), transition_known_values(g, prior) + values);
        guarded_lemma_apply_set_suffix(sem, transition_known_values(g, prior), values, false);
        let expansion = seq![ActionShape::Union(children.len())] + suffix;
        assert(transition_freeze_tasks(g, expansion) =~= seq![GuardedAction::Union(children.len())] + actions.reverse());
        machine_pair_effect_intro(g, ActionShape::Pair(a@, b@), pending, prior, expansion, prior, result);
        assert(pending + expansion =~= pending.push(ActionShape::Union(children.len())) + suffix);
    }

    pub proof fn machine_pair_fold_schedule<L, C>(
        sem: spec_fn(C, L, Data) -> bool, valid: spec_fn(C) -> bool,
        terms: Seq<language::Transition<L>>, index: nat, head: language::Transition<L>, prefix: Seq<GuardedTransition<L, C>>,
    )
        requires 0 < index < terms.len(),
        ensures guarded_program_refines(sem, valid,
            guarded_apply(sem, GuardedAction::Fold(terms, index), prefix.push(guarded_constant(head))),
            guarded_run(sem, seq![GuardedAction::Fold(terms, index + 1), GuardedAction::Pair(head, terms[index as int])], prefix)),
    {
        reveal_with_fuel(guarded_run, 4);
        let remaining = terms.subrange(index as int, terms.len() as int).map(|i: int, term: language::Transition<L>| guarded_constant(term));
        let later = terms.subrange(index as int + 1, terms.len() as int).map(|i: int, term: language::Transition<L>| guarded_constant(term));
        let pair = guarded_constant(language::Transition::Intersect(seq![head, terms[index as int]]));
        let before = guarded_set(seq![guarded_constant(head)] + remaining, true);
        let after = if index + 1 < terms.len() { guarded_set(seq![pair] + later, true) } else { pair };
        assert(prefix.push(guarded_constant(head)).drop_last() =~= prefix);
        assert(prefix.push(pair).drop_last() =~= prefix);
        assert forall|ctx: C, event: Data| valid(ctx) && #[trigger] (before.guard)(ctx, event)
            implies (after.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, before, word) == guarded_language(sem, ctx, event, after, word) by {
            assert forall|i: int| 0 <= i < later.len() implies (later[i].guard)(ctx, event) by {};
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, before, word)
                == guarded_language(sem, ctx, event, after, word) by {
                let context_sem = guarded_semantics(sem, ctx);
                let bs = (seq![guarded_constant(head)] + remaining).map(|i: int, value: GuardedTransition<L, C>| value.term);
                let ats = (seq![pair] + later).map(|i: int, value: GuardedTransition<L, C>| value.term);
                language::lemma_interp_intersect(context_sem, event, bs, word);
                if index + 1 < terms.len() { language::lemma_interp_intersect(context_sem, event, ats, word); }
                machine_pair_binary_language(context_sem, event, head, terms[index as int], word);
                if guarded_language(sem, ctx, event, before, word) {
                    assert(language::lang(context_sem, language::interp_transition(context_sem, event, bs[0]), word));
                    assert(language::lang(context_sem, language::interp_transition(context_sem, event, bs[1]), word));
                    assert forall|i: int| 0 <= i < ats.len() implies
                        language::lang(context_sem, language::interp_transition(context_sem, event, ats[i]), word) by {
                        if i > 0 {
                            assert(ats[i] == bs[i + 1]);
                            assert(language::lang(context_sem, language::interp_transition(context_sem, event, bs[i + 1]), word));
                        }
                    }
                }
                if guarded_language(sem, ctx, event, after, word) {
                    if index + 1 < terms.len() {
                        assert(after.term == language::Transition::Intersect(ats));
                        assert(language::lang(context_sem, language::interp_transition(context_sem, event, ats[0]), word));
                        assert(ats[0] == pair.term);
                    }
                    assert(language::lang(context_sem, language::interp_transition(context_sem, event, pair.term), word));
                    assert forall|i: int| 0 <= i < bs.len() implies
                        language::lang(context_sem, language::interp_transition(context_sem, event, bs[i]), word) by {
                        if i > 1 {
                            assert(index + 1 < terms.len());
                            assert(bs[i] == ats[i - 1]);
                            assert(language::lang(context_sem, language::interp_transition(context_sem, event, ats[i - 1]), word));
                        }
                    }
                }
            }
        }
        guarded_lemma_stack_refl(sem, valid, prefix);
        guarded_lemma_stack_push(sem, valid, prefix, prefix, before, after);
    }

    pub proof fn machine_pair_fold_next_effect(
        g: model::Graph, ids: Seq<TransitionId>, index: nat, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires 0 < index < ids.len(), prior.len() > 0,
        ensures transition_effect(g, ActionShape::Fold(model::transition_ids(ids), index), pending, prior,
            pending.push(ActionShape::Fold(model::transition_ids(ids), index + 1))
                .push(ActionShape::Pair(prior.last()@, ids[index as int]@)), prior.drop_last()),
    {
        let terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
        let expansion = seq![ActionShape::Fold(model::transition_ids(ids), index + 1), ActionShape::Pair(prior.last()@, ids[index as int]@)];
        let prefix = transition_known_values(g, prior.drop_last());
        assert(transition_known_values(g, prior) =~= prefix.push(transition_known(g, prior.last())));
        assert(transition_freeze_tasks(g, expansion) =~= seq![GuardedAction::Fold(terms, index + 1),
            GuardedAction::Pair(model::lift_transition(g, prior.last()@), terms[index as int])]);
        machine_pair_fold_schedule(transition_context_sem(), transition_context_valid(), terms, index,
            model::lift_transition(g, prior.last()@), prefix);
        assert(pending.push(expansion[0]).push(expansion[1]) =~= pending + expansion);
        assert((pending + expansion).subrange(pending.len() as int, (pending + expansion).len() as int) =~= expansion);
    }

    pub proof fn machine_pair_fold_first_run<L, C>(
        sem: spec_fn(C, L, Data) -> bool, terms: Seq<language::Transition<L>>, prefix: Seq<GuardedTransition<L, C>>,
    )
        requires terms.len() > 0,
        ensures guarded_run(sem, seq![GuardedAction::Fold(terms, 1)], prefix.push(guarded_constant(terms[0])))
            == Some(prefix.push(if terms.len() == 1 { guarded_constant(terms[0]) } else {
                guarded_set(terms.map(|i: int, term: language::Transition<L>| guarded_constant(term)), true) })),
    {
        guarded_lemma_run_singleton(sem, GuardedAction::Fold(terms, 1), prefix.push(guarded_constant(terms[0])));
        if terms.len() > 1 {
            assert(seq![guarded_constant::<L, C>(terms[0])] + terms.subrange(1, terms.len() as int)
                .map(|i: int, term: language::Transition<L>| guarded_constant::<L, C>(term))
                =~= terms.map(|i: int, term: language::Transition<L>| guarded_constant::<L, C>(term)));
            assert(prefix.push(guarded_constant(terms[0])).drop_last() =~= prefix);
        }
    }

    pub proof fn machine_pair_fold_first_effect(
        g: model::Graph, ids: Seq<TransitionId>, children: Seq<TransitionId>, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires children.len() > 0,
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_combo(g, sym, theta, ids, event, word, true)
                    == transition_combo(g, sym, theta, children, event, word, true),
        ensures transition_effect(g, ActionShape::Fold(model::transition_ids(ids), 0), pending, prior,
            pending.push(ActionShape::Fold(model::transition_ids(children), 1)), prior.push(children[0])),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let terms = model::transition_ids(children).map(|i: int, id: nat| model::lift_transition(g, id));
        let expected = transition_initial_value(g, ActionShape::Fold(model::transition_ids(ids), 0)).unwrap();
        let result = if terms.len() == 1 { guarded_constant(terms[0]) } else {
            guarded_set(terms.map(|i: int, term: language::Transition<model::Test>| guarded_constant(term)), true) };
        let input_terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, expected, word) == guarded_language(sem, ctx, event, result, word) by {
            transition_lemma_context_sem(ctx);
            assert forall|i: int| 0 <= i < terms.len() implies
                (guarded_constant::<model::Test, TransitionContext>(terms[i]).guard)(ctx, event) by {};
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
                let context_sem = model::gsem(ctx.symbols, ctx.bindings);
                language::lemma_interp_intersect(context_sem, event, input_terms, word);
                if terms.len() != 1 {
                    assert(terms.map(|i: int, term: language::Transition<model::Test>| guarded_constant::<model::Test, TransitionContext>(term))
                        .map(|i: int, value: TransitionMeaning| value.term) =~= terms);
                    assert(result.term == language::Transition::Intersect(terms));
                    language::lemma_interp_intersect(context_sem, event, terms, word);
                }
                assert forall|i: int| 0 <= i < ids.len() implies
                    language::lang(context_sem, language::interp_transition(context_sem, event, input_terms[i]), word)
                        == transition_lang(g, ctx.symbols, ctx.bindings, ids[i], event, word) by {};
                assert forall|i: int| 0 <= i < children.len() implies
                    language::lang(context_sem, language::interp_transition(context_sem, event, terms[i]), word)
                        == transition_lang(g, ctx.symbols, ctx.bindings, children[i], event, word) by {};
                assert(transition_combo(g, ctx.symbols, ctx.bindings, ids, event, word, true)
                    == transition_combo(g, ctx.symbols, ctx.bindings, children, event, word, true));
            }
        }
        let expansion = seq![ActionShape::Fold(model::transition_ids(children), 1)];
        assert(transition_freeze_tasks(g, expansion) =~= seq![GuardedAction::Fold(terms, 1)]);
        transition_lemma_known_push(g, prior, children[0]);
        machine_pair_fold_first_run(sem, terms, transition_known_values(g, prior));
        machine_pair_effect_intro(g, ActionShape::Fold(model::transition_ids(ids), 0), pending, prior,
            expansion, prior.push(children[0]), result);
        assert(pending + expansion =~= pending.push(expansion[0]));
    }

    pub proof fn machine_pair_empty_branches(
        g: model::Graph, a: TransitionId, b: TransitionId, x: TestId, xt: TransitionId,
        y: TestId, yt: TransitionId, empty: TransitionId, guard: TestId,
    )
        requires model::graph_wf(g), a@ < g.transitions.len(), b@ < g.transitions.len(),
            empty@ == g.constants.transition_empty,
            g.transitions[a@ as int] == model::TransitionNode::If(x@, xt@, empty@),
            g.transitions[b@ as int] == model::TransitionNode::If(y@, yt@, empty@),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> model::test_holds(sym, theta, model::lift_test(g, guard@), event)
                    == test_combo(g, sym, theta, seq![x, y], event, true),
        ensures
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> (transition_lang(g, sym, theta, a, event, word) && transition_lang(g, sym, theta, b, event, word))
                    == (model::test_holds(sym, theta, model::lift_test(g, guard@), event)
                        && transition_lang(g, sym, theta, xt, event, word) && transition_lang(g, sym, theta, yt, event, word)),
            guard@ == g.constants.test_false ==> transition_result(g, ActionShape::Pair(a@, b@), empty),
    {
        machine_pair_if_language(g, a, x, xt, empty);
        machine_pair_if_language(g, b, y, yt, empty);
        transition_lemma_constants(g);
        transition_unfold(g, empty@);
        regex_unfold(g, g.constants.empty);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies (transition_lang(g, sym, theta, a, event, word) && transition_lang(g, sym, theta, b, event, word))
                == (model::test_holds(sym, theta, model::lift_test(g, guard@), event)
                    && transition_lang(g, sym, theta, xt, event, word) && transition_lang(g, sym, theta, yt, event, word)) by {
            language::lemma_interp_const(model::gsem(sym, theta), event, language::Regex::Empty);
            assert(model::test_holds(sym, theta, model::lift_test(g, guard@), event)
                == test_combo(g, sym, theta, seq![x, y], event, true));
        }
        if guard@ == g.constants.test_false {
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                implies transition_lang(g, sym, theta, empty, event, word)
                    == transition_combo(g, sym, theta, seq![a, b], event, word, true) by {
                assert((transition_lang(g, sym, theta, a, event, word) && transition_lang(g, sym, theta, b, event, word))
                    == (model::test_holds(sym, theta, model::lift_test(g, guard@), event)
                        && transition_lang(g, sym, theta, xt, event, word) && transition_lang(g, sym, theta, yt, event, word)));
            }
            machine_pair_set_result(g, seq![a, b], ActionShape::Pair(a@, b@), empty);
        }
    }


    pub proof fn transition_lemma_clean_not_effect(
        g: model::Graph, id: TransitionId, path: TestId, inner: TransitionId, base: Seq<ActionShape>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::Not(inner@),
        ensures forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            base.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@)), prior),
    {
        transition_unfold(g, id@);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let before = guarded_clean(sem, model::lift_test(g, path@), model::lift_transition(g, id@));
        let after = guarded_not(guarded_clean(sem, model::lift_test(g, path@), model::lift_transition(g, inner@)));
        guarded_lemma_same_term(sem, valid, before, after);
        assert forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            base.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@)), prior) by {
            let known = transition_known_values(g, prior);
            guarded_lemma_stack_refl(sem, valid, known);
            guarded_lemma_stack_push(sem, valid, known, known, before, after);
            let tasks = base.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@));
            assert(transition_freeze_tasks(g, tasks.subrange(base.len() as int, tasks.len() as int))
                =~= seq![GuardedAction::NotResult, GuardedAction::Clean(model::lift_transition(g, inner@), model::lift_test(g, path@))]);
            reveal_with_fuel(guarded_run, 3);
        }
    }

    pub proof fn transition_lemma_clean_append_effect(
        g: model::Graph, id: TransitionId, path: TestId, inner: TransitionId,
        suffix: Seq<RegexId>, combined: RegexId, base: Seq<ActionShape>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::Append(inner@, model::regex_ids(suffix)),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(g, sym, theta, combined@, word) == concat_combo(g, sym, theta, suffix, word),
        ensures forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            base.push(ActionShape::AppendResult(combined@)).push(ActionShape::Clean(inner@, path@)), prior),
    {
        transition_unfold(g, id@);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let path_term = model::lift_test(g, path@);
        let term = model::lift_transition(g, inner@);
        let combined_term = model::lift_regex(g, combined@);
        let before = guarded_clean(sem, path_term, model::lift_transition(g, id@));
        let after = guarded_append(guarded_clean(sem, path_term, term), combined_term);
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (before.guard)(ctx, event)
            implies (after.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, before, word) == guarded_language(sem, ctx, event, after, word) by {
            transition_lemma_context_sem(ctx);
            let context_sem = model::gsem(ctx.symbols, ctx.bindings);
            let suffix_terms = model::lift_regexes(g, model::regex_ids(suffix));
            language::lemma_interp_append(context_sem, event, term, suffix_terms);
            language::lemma_interp_append(context_sem, event, term, seq![combined_term]);
            assert forall|word: Seq<Data>| language::lang(context_sem, language::Regex::Concat(suffix_terms), word)
                == language::lang(context_sem, combined_term, word) by {
                assert(model::regex_lang(g, ctx.symbols, ctx.bindings, combined@, word)
                    == concat_combo(g, ctx.symbols, ctx.bindings, suffix, word));
            }
            regex_concat_replace(context_sem, seq![language::interp_transition(context_sem, event, term)], suffix_terms, combined_term);
        }
        assert forall|prior: Seq<TransitionId>| #[trigger] transition_effect(g, ActionShape::Clean(id@, path@), base, prior,
            base.push(ActionShape::AppendResult(combined@)).push(ActionShape::Clean(inner@, path@)), prior) by {
            let known = transition_known_values(g, prior);
            guarded_lemma_stack_refl(sem, valid, known);
            guarded_lemma_stack_push(sem, valid, known, known, before, after);
            let tasks = base.push(ActionShape::AppendResult(combined@)).push(ActionShape::Clean(inner@, path@));
            assert(transition_freeze_tasks(g, tasks.subrange(base.len() as int, tasks.len() as int))
                =~= seq![GuardedAction::AppendResult(combined_term), GuardedAction::Clean(term, path_term)]);
            reveal_with_fuel(guarded_run, 3);
        }
    }

    pub proof fn machine_unary_not_result(g: model::Graph, id: TransitionId, out: TransitionId)
        requires forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> transition_lang(g, sym, theta, out, event, word) == !transition_lang(g, sym, theta, id, event, word),
        ensures transition_result(g, ActionShape::Not(id@), out),
    {
        let expected = transition_initial_value(g, ActionShape::Not(id@)).unwrap();
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            && (expected.guard)(TransitionContext { symbols: sym, bindings: theta }, event)
            implies guarded_language(transition_context_sem(), TransitionContext { symbols: sym, bindings: theta }, event, expected, word)
                == transition_lang(g, sym, theta, out, event, word) by {
            transition_lemma_context_sem(TransitionContext { symbols: sym, bindings: theta });
            language::lemma_interp_not(model::gsem(sym, theta), event, model::lift_transition(g, id@));
        }
    }

    pub open spec fn machine_unary_append_language(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, id: TransitionId, suffix: RegexId,
        event: Data, word: Seq<Data>,
    ) -> bool {
        language::lang(model::gsem(sym, theta), language::Regex::Concat(seq![
            language::interp_transition(model::gsem(sym, theta), event, model::lift_transition(g, id@)),
            model::lift_regex(g, suffix@),
        ]), word)
    }

    pub proof fn machine_unary_append_result(g: model::Graph, id: TransitionId, suffix: RegexId, out: TransitionId)
        requires forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            ==> transition_lang(g, sym, theta, out, event, word)
                == machine_unary_append_language(g, sym, theta, id, suffix, event, word),
        ensures transition_result(g, ActionShape::Append(id@, suffix@), out),
    {
        let expected = transition_initial_value(g, ActionShape::Append(id@, suffix@)).unwrap();
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            && (expected.guard)(TransitionContext { symbols: sym, bindings: theta }, event)
            implies guarded_language(transition_context_sem(), TransitionContext { symbols: sym, bindings: theta }, event, expected, word)
                == transition_lang(g, sym, theta, out, event, word) by {
            transition_lemma_context_sem(TransitionContext { symbols: sym, bindings: theta });
            language::lemma_interp_append(model::gsem(sym, theta), event, model::lift_transition(g, id@), seq![model::lift_regex(g, suffix@)]);
            assert(seq![language::interp_transition(model::gsem(sym, theta), event, model::lift_transition(g, id@))]
                + seq![model::lift_regex(g, suffix@)] =~= seq![
                    language::interp_transition(model::gsem(sym, theta), event, model::lift_transition(g, id@)), model::lift_regex(g, suffix@)]);
        }
    }

    pub proof fn machine_unary_append_identity<L>(sem: spec_fn(L, Data) -> bool, head: language::Regex<L>, word: Seq<Data>)
        ensures language::lang(sem, language::Regex::Concat(seq![head, language::Regex::Epsilon]), word) == language::lang(sem, head, word),
            !language::lang(sem, language::Regex::Concat(seq![head, language::Regex::Empty]), word),
    {
        language::lemma_concat_pair(sem, head, language::Regex::Epsilon, word);
        language::lemma_concat_pair(sem, head, language::Regex::Empty, word);
        if language::lang(sem, head, word) {
            let empty = Seq::<Data>::empty();
            assert(word == word + empty);
            assert(language::lang(sem, language::Regex::Epsilon, empty));
        }
    }

    pub proof fn machine_unary_append_reassociate<L>(
        sem: spec_fn(L, Data) -> bool, head: language::Regex<L>, suffix: Seq<language::Regex<L>>, last: language::Regex<L>,
    )
        ensures forall|word: Seq<Data>| language::lang(sem,
            language::Regex::Concat(seq![language::Regex::Concat(seq![head] + suffix), last]), word)
            == language::lang(sem, language::Regex::Concat(seq![head, language::Regex::Concat(suffix.push(last))]), word),
    {
        let flat = seq![head] + suffix;
        assert forall|word: Seq<Data>| language::lang(sem, language::Regex::Concat(seq![language::Regex::Concat(flat)]), word)
            == language::lang(sem, language::Regex::Concat(flat), word) by {
            language::lemma_concat_singleton(sem, language::Regex::Concat(flat), word);
        }
        regex_concat_append_congruent(sem, seq![language::Regex::Concat(flat)], flat, seq![last]);
        let tail = suffix.push(last);
        regex_concat_replace(sem, seq![head], tail, language::Regex::Concat(tail));
        assert(flat + seq![last] =~= seq![head] + tail);
        assert(seq![language::Regex::Concat(flat)] + seq![last] =~= seq![language::Regex::Concat(flat), last]);
        assert(seq![head].push(language::Regex::Concat(tail)) =~= seq![head, language::Regex::Concat(tail)]);
        assert forall|word: Seq<Data>| language::lang(sem,
            language::Regex::Concat(seq![language::Regex::Concat(flat), last]), word)
            == language::lang(sem, language::Regex::Concat(seq![head, language::Regex::Concat(tail)]), word) by {
            assert(language::lang(sem, language::Regex::Concat(seq![language::Regex::Concat(flat)] + seq![last]), word)
                == language::lang(sem, language::Regex::Concat(flat + seq![last]), word));
            assert(language::lang(sem, language::Regex::Concat(seq![head] + tail), word)
                == language::lang(sem, language::Regex::Concat(seq![head].push(language::Regex::Concat(tail))), word));
        }
    }

    pub proof fn machine_unary_demorgan<L>(
        sem: spec_fn(L, Data) -> bool, event: Data, terms: Seq<language::Transition<L>>, intersect: bool, word: Seq<Data>,
    )
        ensures language::lang(sem, language::interp_transition(sem, event, language::Transition::Not(Box::new(
            if intersect { language::Transition::Intersect(terms) } else { language::Transition::Union(terms) }))), word)
            == language::lang(sem, language::interp_transition(sem, event,
                if intersect { language::Transition::Union(terms.map(|i: int, term: language::Transition<L>| language::Transition::Not(Box::new(term)))) }
                else { language::Transition::Intersect(terms.map(|i: int, term: language::Transition<L>| language::Transition::Not(Box::new(term)))) }), word),
    {
        let negated = terms.map(|i: int, term: language::Transition<L>| language::Transition::Not(Box::new(term)));
        assert forall|i: int| 0 <= i < terms.len() implies
            language::lang(sem, language::interp_transition(sem, event, negated[i]), word)
                == !language::lang(sem, language::interp_transition(sem, event, terms[i]), word) by {
            language::lemma_interp_not(sem, event, terms[i]);
        }
        if intersect {
            language::lemma_interp_not(sem, event, language::Transition::Intersect(terms));
            language::lemma_interp_intersect(sem, event, terms, word);
            language::lemma_interp_union(sem, event, negated, word);
            if !(forall|i: int| 0 <= i < terms.len() ==> language::lang(sem, language::interp_transition(sem, event, terms[i]), word)) {
                let i = choose|i: int| 0 <= i < terms.len() && !language::lang(sem, language::interp_transition(sem, event, terms[i]), word);
                assert(language::lang(sem, language::interp_transition(sem, event, negated[i]), word));
            }
        } else {
            language::lemma_interp_not(sem, event, language::Transition::Union(terms));
            language::lemma_interp_union(sem, event, terms, word);
            language::lemma_interp_intersect(sem, event, negated, word);
            if !(exists|i: int| 0 <= i < terms.len() && language::lang(sem, language::interp_transition(sem, event, terms[i]), word)) {
                assert forall|i: int| 0 <= i < terms.len() implies language::lang(sem, language::interp_transition(sem, event, negated[i]), word) by {}
            }
        }
    }

    pub proof fn machine_unary_append_union<L>(
        sem: spec_fn(L, Data) -> bool, event: Data, terms: Seq<language::Transition<L>>, suffix: language::Regex<L>, word: Seq<Data>,
    )
        ensures language::lang(sem, language::interp_transition(sem, event,
            language::Transition::Append(Box::new(language::Transition::Union(terms)), seq![suffix])), word)
            == language::lang(sem, language::interp_transition(sem, event, language::Transition::Union(
                terms.map(|i: int, term: language::Transition<L>| language::Transition::Append(Box::new(term), seq![suffix])))), word),
    {
        let head = language::interp_transition(sem, event, language::Transition::Union(terms));
        let appended = terms.map(|i: int, term: language::Transition<L>| language::Transition::Append(Box::new(term), seq![suffix]));
        language::lemma_interp_append(sem, event, language::Transition::Union(terms), seq![suffix]);
        assert(seq![head] + seq![suffix] =~= seq![head, suffix]);
        language::lemma_concat_pair(sem, head, suffix, word);
        language::lemma_interp_union(sem, event, appended, word);
        assert forall|i: int| 0 <= i < terms.len() implies
            language::lang(sem, language::interp_transition(sem, event, appended[i]), word)
                == (exists|u: Seq<Data>, v: Seq<Data>| word == u + v
                    && language::lang(sem, language::interp_transition(sem, event, terms[i]), u) && language::lang(sem, suffix, v)) by {
            language::lemma_interp_append(sem, event, terms[i], seq![suffix]);
            let r = language::interp_transition(sem, event, terms[i]);
            assert(seq![r] + seq![suffix] =~= seq![r, suffix]);
            language::lemma_concat_pair(sem, r, suffix, word);
        }
        if language::lang(sem, language::Regex::Concat(seq![head, suffix]), word) {
            let (u, v) = choose|u: Seq<Data>, v: Seq<Data>| word == u + v && language::lang(sem, head, u) && language::lang(sem, suffix, v);
            language::lemma_interp_union(sem, event, terms, u);
            let i = choose|i: int| 0 <= i < terms.len() && language::lang(sem, language::interp_transition(sem, event, terms[i]), u);
            assert(language::lang(sem, language::interp_transition(sem, event, appended[i]), word));
        }
        if language::lang(sem, language::interp_transition(sem, event, language::Transition::Union(appended)), word) {
            let i = choose|i: int| 0 <= i < appended.len() && language::lang(sem, language::interp_transition(sem, event, appended[i]), word);
            let (u, v) = choose|u: Seq<Data>, v: Seq<Data>| word == u + v
                && language::lang(sem, language::interp_transition(sem, event, terms[i]), u) && language::lang(sem, suffix, v);
            language::lemma_interp_union(sem, event, terms, u);
            assert(language::lang(sem, head, u));
            assert(language::lang(sem, language::Regex::Concat(seq![head, suffix]), word));
        }
    }

    pub open spec fn machine_unary_child_tasks(
        g: model::Graph, id: TransitionId, suffix: Option<RegexId>, intersect: bool, base: Seq<ActionShape>,
    ) -> Seq<ActionShape> {
        base.push(if intersect { ActionShape::Intersect(transition_children(g, id@).len()) }
            else { ActionShape::Union(transition_children(g, id@).len()) })
            + transition_child_actions(g, id@, match suffix { Some(r) => ChildShape::Append(r@), None => ChildShape::Not })
    }

    pub proof fn machine_unary_children_effect(
        g: model::Graph, id: TransitionId, suffix: Option<RegexId>, intersect: bool, base: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            match suffix {
                Some(r) => r@ < g.regexes.len() && !intersect && g.transitions[id@ as int] matches model::TransitionNode::Union(_),
                None => match g.transitions[id@ as int] {
                    model::TransitionNode::Union(_) => intersect,
                    model::TransitionNode::Intersect(_) => !intersect,
                    _ => false,
                },
            },
        ensures transition_effect(g, match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) },
            base, prior, machine_unary_child_tasks(g, id, suffix, intersect, base), prior),
    {
        transition_unfold(g, id@);
        transition_lemma_children(g, id@);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let children = transition_children(g, id@);
        let terms = children.map(|i: int, child: nat| model::lift_transition(g, child));
        let actions = terms.map(|i: int, term: language::Transition<model::Test>| match suffix {
            Some(r) => GuardedAction::Append(term, model::lift_regex(g, r@)), None => GuardedAction::Not(term),
        });
        let count = children.len();
        let set_shape = if intersect { ActionShape::Intersect(count) } else { ActionShape::Union(count) };
        let set_action = if intersect { GuardedAction::Intersect(count) } else { GuardedAction::Union(count) };
        let child_shape = match suffix { Some(r) => ChildShape::Append(r@), None => ChildShape::Not };
        let expansion = transition_child_actions(g, id@, child_shape);
        assert(transition_freeze_tasks(g, expansion) =~= actions.reverse());
        let mapped = guarded_atomic_values(sem, actions);
        let task = match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) };
        let expected = transition_initial_value(g, task).unwrap();
        let result = guarded_set(mapped, intersect);
        assert(result.term == if intersect { language::Transition::Intersect(mapped.map(|i: int, value: TransitionMeaning| value.term)) }
            else { language::Transition::Union(mapped.map(|i: int, value: TransitionMeaning| value.term)) });
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
            assert forall|i: int| 0 <= i < mapped.len() implies (mapped[i].guard)(ctx, event) by {
                match suffix { Some(r) => {}, None => {} }
            }
            let context_sem = guarded_semantics(sem, ctx);
            match suffix {
                Some(r) => {
                    assert(mapped.map(|i: int, value: TransitionMeaning| value.term) =~= terms.map(|i: int, term: language::Transition<model::Test>|
                        language::Transition::Append(Box::new(term), seq![model::lift_regex(g, r@)])));
                    assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                        == guarded_language(sem, ctx, event, result, word) by {
                        machine_unary_append_union(context_sem, event, terms, model::lift_regex(g, r@), word);
                    }
                },
                None => {
                    assert(mapped.map(|i: int, value: TransitionMeaning| value.term) =~= terms.map(|i: int, term: language::Transition<model::Test>|
                        language::Transition::Not(Box::new(term))));
                    assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                        == guarded_language(sem, ctx, event, result, word) by {
                        machine_unary_demorgan(context_sem, event, terms, !intersect, word);
                    }
                },
            }
        }
        let known = transition_known_values(g, prior);
        guarded_lemma_push_sequence(sem, actions, known);
        guarded_lemma_run_prefix(sem, seq![set_action], actions.reverse(), known);
        guarded_lemma_run_singleton(sem, set_action, known + mapped);
        guarded_lemma_apply_set_suffix(sem, known, mapped, intersect);
        guarded_lemma_stack_refl(sem, valid, known);
        guarded_lemma_stack_push(sem, valid, known, known, expected, result);
        let tasks = machine_unary_child_tasks(g, id, suffix, intersect, base);
        assert(tasks.subrange(base.len() as int, tasks.len() as int) =~= seq![set_shape] + expansion);
        assert(transition_freeze_tasks(g, seq![set_shape] + expansion) =~= seq![set_action] + actions.reverse());
    }

    pub proof fn machine_unary_replace_effect(
        g: model::Graph, task: ActionShape, next: ActionShape, base: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires transition_action_pushes(task), transition_action_pushes(next),
            guarded_refines(transition_context_sem(), transition_context_valid(),
                transition_initial_value(g, task).unwrap(), transition_initial_value(g, next).unwrap()),
        ensures transition_effect(g, task, base, prior, base.push(next), prior),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let known = transition_known_values(g, prior);
        guarded_lemma_apply_push(sem, transition_freeze_action(g, task), known);
        guarded_lemma_apply_push(sem, transition_freeze_action(g, next), known);
        guarded_lemma_run_singleton(sem, transition_freeze_action(g, next), known);
        guarded_lemma_stack_refl(sem, valid, known);
        guarded_lemma_stack_push(sem, valid, known, known,
            transition_initial_value(g, task).unwrap(), transition_initial_value(g, next).unwrap());
        assert(base.push(next).subrange(base.len() as int, base.len() as int + 1) =~= seq![next]);
        assert(transition_freeze_tasks(g, seq![next]) =~= seq![transition_freeze_action(g, next)]);
    }

    pub proof fn machine_unary_clean_result_effect(
        g: model::Graph, task: ActionShape, out: TransitionId, base: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), transition_action_pushes(task), transition_result(g, task, out),
        ensures transition_effect(g, task, base, prior, base.push(ActionShape::Clean(out@, g.constants.test_true)), prior),
    {
        transition_lemma_constants(g);
        transition_lemma_result_refines(g, task, out);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let clean = transition_initial_value(g, ActionShape::Clean(out@, g.constants.test_true)).unwrap();
        let known = transition_known(g, out);
        assert(model::lift_test(g, g.constants.test_true) == model::Test::True);
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (known.guard)(ctx, event)
            implies (clean.guard)(ctx, event) by {}
        guarded_lemma_same_term(sem, valid, known, clean);
        guarded_lemma_refines_transitive(sem, valid, transition_initial_value(g, task).unwrap(), known, clean);
        machine_unary_replace_effect(g, task, ActionShape::Clean(out@, g.constants.test_true), base, prior);
    }

    pub open spec fn machine_unary_if_tasks(
        g: model::Graph, test: TestId, yes: TransitionId, no: TransitionId, suffix: Option<RegexId>, base: Seq<ActionShape>,
    ) -> Seq<ActionShape> {
        base.push(ActionShape::CleanIf(test@, g.constants.test_true))
            .push(match suffix { Some(r) => ActionShape::Append(no@, r@), None => ActionShape::Not(no@) })
            .push(match suffix { Some(r) => ActionShape::Append(yes@, r@), None => ActionShape::Not(yes@) })
    }

    pub proof fn machine_unary_if_effect(
        g: model::Graph, id: TransitionId, test: TestId, yes: TransitionId, no: TransitionId,
        suffix: Option<RegexId>, base: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::If(test@, yes@, no@),
        ensures transition_effect(g, match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) },
            base, prior, machine_unary_if_tasks(g, test, yes, no, suffix, base), prior),
    {
        transition_unfold(g, id@);
        transition_lemma_constants(g);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let task = match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) };
        let a = match suffix { Some(r) => ActionShape::Append(yes@, r@), None => ActionShape::Not(yes@) };
        let b = match suffix { Some(r) => ActionShape::Append(no@, r@), None => ActionShape::Not(no@) };
        let av = transition_initial_value(g, a).unwrap();
        let bv = transition_initial_value(g, b).unwrap();
        let expected = transition_initial_value(g, task).unwrap();
        let result = guarded_clean_if(sem, model::lift_test(g, test@), model::lift_test(g, g.constants.test_true), av, bv);
        assert(model::lift_test(g, g.constants.test_true) == model::Test::True);
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
            let context_sem = guarded_semantics(sem, ctx);
            let test_term = model::lift_test(g, test@);
            language::lemma_interp_if(context_sem, event, test_term, av.term, bv.term);
            language::lemma_interp_if(context_sem, event, test_term, model::lift_transition(g, yes@), model::lift_transition(g, no@));
            match suffix {
                Some(r) => {
                    language::lemma_interp_append(context_sem, event, model::lift_transition(g, id@), seq![model::lift_regex(g, r@)]);
                    language::lemma_interp_append(context_sem, event, model::lift_transition(g, yes@), seq![model::lift_regex(g, r@)]);
                    language::lemma_interp_append(context_sem, event, model::lift_transition(g, no@), seq![model::lift_regex(g, r@)]);
                },
                None => {
                    language::lemma_interp_not(context_sem, event, model::lift_transition(g, id@));
                    language::lemma_interp_not(context_sem, event, model::lift_transition(g, yes@));
                    language::lemma_interp_not(context_sem, event, model::lift_transition(g, no@));
                },
            }
        }
        let known = transition_known_values(g, prior);
        let expansion = seq![ActionShape::CleanIf(test@, g.constants.test_true), b, a];
        let frozen = transition_freeze_tasks(g, expansion);
        assert(frozen =~= seq![GuardedAction::CleanIf(model::lift_test(g, test@), model::lift_test(g, g.constants.test_true)),
            transition_freeze_action(g, b), transition_freeze_action(g, a)]);
        reveal_with_fuel(guarded_run, 4);
        assert(guarded_run(sem, frozen, known) == Some(known.push(result)));
        guarded_lemma_stack_refl(sem, valid, known);
        guarded_lemma_stack_push(sem, valid, known, known, expected, result);
        let tasks = machine_unary_if_tasks(g, test, yes, no, suffix, base);
        assert(tasks.subrange(base.len() as int, tasks.len() as int) =~= expansion);
    }

    pub proof fn machine_unary_not_const_result(
        before: model::Graph, after: model::Graph, id: TransitionId, head: RegexId, negated: RegexId, out: TransitionId,
    )
        requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
            id@ < before.transitions.len(), before.transitions[id@ as int] == model::TransitionNode::Const(head@),
            negated@ < before.regexes.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(before, sym, theta, negated@, word) == !model::regex_lang(before, sym, theta, head@, word),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == model::regex_lang(after, sym, theta, negated@, word),
        ensures transition_result(after, ActionShape::Not(id@), out),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_graph_transition_wf(before, id@);
        model::lemma_lift_stable_under_extends(before, after);
        transition_unfold(after, id@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(after, sym, theta, out, event, word) == !transition_lang(after, sym, theta, id, event, word) by {
            language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(after, head@));
            assert(model::regex_lang(before, sym, theta, negated@, word) == !model::regex_lang(before, sym, theta, head@, word));
        }
        machine_unary_not_result(after, id, out);
    }

    pub proof fn machine_unary_double_not_result(g: model::Graph, id: TransitionId, inner: TransitionId)
        requires model::graph_wf(g), id@ < g.transitions.len(), g.transitions[id@ as int] == model::TransitionNode::Not(inner@),
        ensures transition_result(g, ActionShape::Not(id@), inner),
    {
        transition_unfold(g, id@);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(g, sym, theta, inner, event, word) == !transition_lang(g, sym, theta, id, event, word) by {
            language::lemma_interp_not(model::gsem(sym, theta), event, model::lift_transition(g, inner@));
        }
        machine_unary_not_result(g, id, inner);
    }

    pub proof fn machine_unary_append_identity_result(g: model::Graph, id: TransitionId, suffix: RegexId, out: TransitionId)
        requires model::graph_wf(g),
            (suffix@ == g.constants.epsilon && out == id)
                || (suffix@ == g.constants.empty && out@ == g.constants.transition_empty),
        ensures transition_result(g, ActionShape::Append(id@, suffix@), out),
    {
        transition_lemma_constants(g);
        transition_unfold(g, g.constants.transition_empty);
        regex_unfold(g, g.constants.empty);
        regex_unfold(g, g.constants.epsilon);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(g, sym, theta, out, event, word)
                == machine_unary_append_language(g, sym, theta, id, suffix, event, word) by {
            machine_unary_append_identity(model::gsem(sym, theta),
                language::interp_transition(model::gsem(sym, theta), event, model::lift_transition(g, id@)), word);
            language::lemma_interp_const(model::gsem(sym, theta), event, language::Regex::Empty);
        }
        machine_unary_append_result(g, id, suffix, out);
    }

    #[verifier::spinoff_prover]
    pub proof fn machine_unary_append_const_result(
        before: model::Graph, after: model::Graph, id: TransitionId, head: RegexId, suffix: RegexId, combined: RegexId, out: TransitionId,
    )
        requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
            id@ < before.transitions.len(), before.transitions[id@ as int] == model::TransitionNode::Const(head@),
            suffix@ < before.regexes.len(), combined@ < before.regexes.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(before, sym, theta, combined@, word) == concat_combo(before, sym, theta, seq![head, suffix], word),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == model::regex_lang(after, sym, theta, combined@, word),
        ensures transition_result(after, ActionShape::Append(id@, suffix@), out),
    {
        hide(model::test_holds);
        hide(language::lang);
        hide(model::symbols_wf);
        hide(model::lift_regex);
        hide(model::lift_transition);
        hide(language::interp_transition);
        hide(transition_result);
        model::lemma_graph_wf_elim(before);
        model::lemma_graph_transition_wf(before, id@);
        model::lemma_lift_regex_stable(before, after, head@);
        model::lemma_lift_regex_stable(before, after, suffix@);
        model::lemma_lift_regex_stable(before, after, combined@);
        transition_unfold(after, id@);
        assert(model::lift_regexes(before, model::regex_ids(seq![head, suffix]))
            =~= seq![model::lift_regex(before, head@), model::lift_regex(before, suffix@)]);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(after, sym, theta, out, event, word)
                == machine_unary_append_language(after, sym, theta, id, suffix, event, word) by {
            language::lemma_interp_const(model::gsem(sym, theta), event, model::lift_regex(after, head@));
            assert(model::regex_lang(before, sym, theta, combined@, word) == concat_combo(before, sym, theta, seq![head, suffix], word));
        }
        machine_unary_append_result(after, id, suffix, out);
    }

    pub proof fn machine_unary_flip_result(
        before: model::Graph, after: model::Graph, id: TransitionId, test: TestId,
        yes: TransitionId, no: TransitionId, negated: TestId, out: TransitionId,
    )
        requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
            id@ < before.transitions.len(), before.transitions[id@ as int] == model::TransitionNode::If(test@, yes@, no@),
            yes@ == before.constants.transition_all, no@ == before.constants.transition_empty, negated@ < before.tests.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data| model::symbols_wf(sym)
                ==> model::test_holds(sym, theta, model::lift_test(before, negated@), event)
                    == !model::test_holds(sym, theta, model::lift_test(before, test@), event),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == transition_if_combo(after, sym, theta, negated, yes, no, event, word),
        ensures transition_result(after, ActionShape::Not(id@), out),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_graph_transition_wf(before, id@);
        model::lemma_lift_stable_under_extends(before, after);
        transition_lemma_constants(after);
        transition_unfold(after, id@);
        transition_unfold(after, yes@);
        transition_unfold(after, no@);
        regex_unfold(after, after.constants.empty);
        regex_unfold(after, after.constants.all);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(after, sym, theta, out, event, word) == !transition_lang(after, sym, theta, id, event, word) by {
            let sem = model::gsem(sym, theta);
            language::lemma_interp_if(sem, event, model::lift_test(after, test@), model::lift_transition(after, yes@), model::lift_transition(after, no@));
            language::lemma_interp_const(sem, event, language::Regex::Empty);
            language::lemma_interp_const(sem, event, language::Regex::All);
            assert(model::test_holds(sym, theta, model::lift_test(before, negated@), event)
                == !model::test_holds(sym, theta, model::lift_test(before, test@), event));
        }
        machine_unary_not_result(after, id, out);
    }

    pub proof fn machine_unary_append_nested_effect(
        g: model::Graph, id: TransitionId, inner: TransitionId, suffix: RegexId, combined: RegexId,
        children: Seq<RegexId>, base: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), id@ < g.transitions.len(),
            g.transitions[id@ as int] == model::TransitionNode::Append(inner@, model::regex_ids(children)),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(g, sym, theta, combined@, word) == concat_combo(g, sym, theta, children.push(suffix), word),
        ensures transition_effect(g, ActionShape::Append(id@, suffix@), base, prior,
            base.push(ActionShape::Append(inner@, combined@)), prior),
    {
        transition_unfold(g, id@);
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let task = ActionShape::Append(id@, suffix@);
        let next = ActionShape::Append(inner@, combined@);
        let expected = transition_initial_value(g, task).unwrap();
        let result = transition_initial_value(g, next).unwrap();
        let tail = model::lift_regexes(g, model::regex_ids(children));
        assert(model::lift_regexes(g, model::regex_ids(children.push(suffix))) =~= tail.push(model::lift_regex(g, suffix@)));
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
            transition_lemma_context_sem(ctx);
            let context_sem = model::gsem(ctx.symbols, ctx.bindings);
            let head = language::interp_transition(context_sem, event, model::lift_transition(g, inner@));
            let last = model::lift_regex(g, suffix@);
            let combined_term = model::lift_regex(g, combined@);
            language::lemma_interp_append(context_sem, event, model::lift_transition(g, inner@), tail);
            language::lemma_interp_append(context_sem, event, model::lift_transition(g, id@), seq![last]);
            language::lemma_interp_append(context_sem, event, model::lift_transition(g, inner@), seq![combined_term]);
            machine_unary_append_reassociate(context_sem, head, tail, last);
            assert forall|word: Seq<Data>| language::lang(context_sem, language::Regex::Concat(tail.push(last)), word)
                == language::lang(context_sem, combined_term, word) by {
                assert(model::regex_lang(g, ctx.symbols, ctx.bindings, combined@, word)
                    == concat_combo(g, ctx.symbols, ctx.bindings, children.push(suffix), word));
            }
            regex_concat_replace(context_sem, seq![head], tail.push(last), combined_term);
            regex_concat_replace(context_sem, seq![head], tail.push(last), language::Regex::Concat(tail.push(last)));
            assert(seq![head].push(language::Regex::Concat(tail.push(last))) =~= seq![head, language::Regex::Concat(tail.push(last))]);
            assert(seq![head] + tail.push(last) =~= (seq![head] + tail).push(last));
            assert(seq![head].push(combined_term) =~= seq![head, combined_term]);
            assert(seq![language::Regex::Concat(seq![head] + tail)] + seq![last] =~= seq![language::Regex::Concat(seq![head] + tail), last]);
            assert(seq![head] + seq![combined_term] =~= seq![head, combined_term]);
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
                assert(language::lang(context_sem, language::Regex::Concat(seq![language::Regex::Concat(seq![head] + tail), last]), word)
                    == language::lang(context_sem, language::Regex::Concat(seq![head, language::Regex::Concat(tail.push(last))]), word));
                assert(language::lang(context_sem, language::Regex::Concat(seq![head] + tail.push(last)), word)
                    == language::lang(context_sem, language::Regex::Concat(seq![head, language::Regex::Concat(tail.push(last))]), word));
                assert(language::lang(context_sem, language::Regex::Concat(seq![head] + tail.push(last)), word)
                    == language::lang(context_sem, language::Regex::Concat(seq![head, combined_term]), word));
            }
        }
        machine_unary_replace_effect(g, task, next, base, prior);
    }

    pub proof fn machine_unary_suffix_language(g: model::Graph, suffix: RegexId, children: Seq<RegexId>)
        requires model::graph_wf(g), suffix@ < g.regexes.len(),
            children == seq![suffix] || g.regexes[suffix@ as int].kind == model::RegexKindNode::Concat(model::regex_ids(children)),
        ensures forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
            model::regex_lang(g, sym, theta, suffix@, word) == concat_combo(g, sym, theta, children, word),
    {
        if children == seq![suffix] {
            assert(model::lift_regexes(g, model::regex_ids(children)) =~= seq![model::lift_regex(g, suffix@)]);
            assert forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
                model::regex_lang(g, sym, theta, suffix@, word) == concat_combo(g, sym, theta, children, word) by {
                language::lemma_concat_singleton(model::gsem(sym, theta), model::lift_regex(g, suffix@), word);
            }
        } else { regex_unfold(g, suffix@); }
    }

    #[verifier::spinoff_prover]
    pub proof fn machine_unary_append_raw_result(
        before: model::Graph, after: model::Graph, id: TransitionId, suffix: RegexId, children: Seq<RegexId>, out: TransitionId,
    )
        requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
            id@ < before.transitions.len(), suffix@ < before.regexes.len(), regex_ids_valid(before, children),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>|
                model::regex_lang(before, sym, theta, suffix@, word) == concat_combo(before, sym, theta, children, word),
            model::lift_transition(after, out@) == transition_unbounded_node(after,
                model::TransitionNode::Append(id@, model::regex_ids(children))),
        ensures transition_result(after, ActionShape::Append(id@, suffix@), out),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_stable_under_extends(before, after);
        assert(model::lift_regexes(before, model::regex_ids(children)) =~= model::lift_regexes(after, model::regex_ids(children)));
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(after, sym, theta, out, event, word)
                == machine_unary_append_language(after, sym, theta, id, suffix, event, word) by {
            let sem = model::gsem(sym, theta);
            let head = language::interp_transition(sem, event, model::lift_transition(after, id@));
            let tail = model::lift_regexes(after, model::regex_ids(children));
            let last = model::lift_regex(after, suffix@);
            language::lemma_interp_append(sem, event, model::lift_transition(after, id@), tail);
            assert forall|w: Seq<Data>| language::lang(sem, language::Regex::Concat(tail), w) == language::lang(sem, last, w) by {
                assert(model::regex_lang(before, sym, theta, suffix@, w) == concat_combo(before, sym, theta, children, w));
            }
            regex_concat_replace(sem, seq![head], tail, last);
            assert(seq![head].push(last) =~= seq![head, last]);
        }
        machine_unary_append_result(after, id, suffix, out);
    }


    pub proof fn machine_pair_constant_result(
        before: model::Graph, after: model::Graph, a: TransitionId, b: TransitionId,
        x: RegexId, y: RegexId, regex: RegexId, out: TransitionId,
    )
        requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
            a@ < after.transitions.len(), b@ < after.transitions.len(),
            x@ < before.regexes.len(), y@ < before.regexes.len(), regex@ < before.regexes.len(),
            after.transitions[a@ as int] == model::TransitionNode::Const(x@),
            after.transitions[b@ as int] == model::TransitionNode::Const(y@),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(before, sym, theta, regex@, word) == regex_combo(before, sym, theta, seq![x, y], word, true),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == model::regex_lang(after, sym, theta, regex@, word),
        ensures transition_result(after, ActionShape::Pair(a@, b@), out),
    {
        regex_combo_extends(before, after, seq![regex], true);
        regex_combo_extends(before, after, seq![x, y], true);
        transition_lemma_constant(after, a, x);
        transition_lemma_constant(after, b, y);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_lang(after, sym, theta, out, event, word)
                == transition_combo(after, sym, theta, seq![a, b], event, word, true) by {
            assert(model::regex_lang(before, sym, theta, regex@, word)
                == regex_combo(before, sym, theta, seq![x, y], word, true));
            regex_combo_push(before, Seq::empty(), regex, sym, theta, word, true);
            regex_combo_push(after, Seq::empty(), regex, sym, theta, word, true);
            assert(Seq::<RegexId>::empty().push(regex) =~= seq![regex]);
            assert(regex_combo(before, sym, theta, seq![regex], word, true)
                == model::regex_lang(before, sym, theta, regex@, word));
            assert(regex_combo(after, sym, theta, seq![regex], word, true)
                == model::regex_lang(after, sym, theta, regex@, word));
            assert(transition_lang(after, sym, theta, out, event, word)
                == model::regex_lang(after, sym, theta, regex@, word));
        }
        machine_pair_set_result(after, seq![a, b], ActionShape::Pair(a@, b@), out);
    }

    pub proof fn machine_pair_fold_collection_effect(
        g: model::Graph, ids: Seq<TransitionId>, flat: TransitionId, children: Seq<TransitionId>,
        pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires model::graph_wf(g), flat@ < g.transitions.len(), children.len() > 0,
            g.transitions[flat@ as int] == model::TransitionNode::Intersect(model::transition_ids(children)),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(g, sym, theta, flat, event, word) == transition_combo(g, sym, theta, ids, event, word, true),
        ensures transition_effect(g, ActionShape::Fold(model::transition_ids(ids), 0), pending, prior,
            pending.push(ActionShape::Fold(model::transition_ids(children), 1)), prior.push(children[0])),
    {
        transition_lemma_children_language(g, flat, children, true);
        assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
            implies transition_combo(g, sym, theta, ids, event, word, true)
                == transition_combo(g, sym, theta, children, event, word, true) by {
            assert(transition_lang(g, sym, theta, flat, event, word)
                == transition_combo(g, sym, theta, ids, event, word, true));
            assert(transition_lang(g, sym, theta, flat, event, word)
                == transition_combo(g, sym, theta, children, event, word, true));
        }
        machine_pair_fold_first_effect(g, ids, children, pending, prior);
    }

    pub proof fn machine_driver_union_effect(
        g: model::Graph, count: nat, pending: Seq<ActionShape>, prior: Seq<TransitionId>, out: TransitionId,
    )
        requires count <= prior.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(g, sym, theta, out, event, word)
                    == transition_combo(g, sym, theta, prior.subrange(prior.len() as int - count as int, prior.len() as int), event, word, false),
        ensures transition_effect(g, ActionShape::Union(count), pending, prior, pending,
            prior.take(prior.len() as int - count as int).push(out)),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let start = prior.len() as int - count as int;
        let ids = prior.subrange(start, prior.len() as int);
        let prefix = transition_known_values(g, prior.take(start));
        let children = transition_known_values(g, ids);
        assert(transition_known_values(g, prior) =~= prefix + children);
        let expected = guarded_set(children, false);
        let result = transition_known(g, out);
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, expected, word) == guarded_language(sem, ctx, event, result, word) by {
            transition_lemma_context_sem(ctx);
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
                let terms = children.map(|i: int, value: TransitionMeaning| value.term);
                language::lemma_interp_union(model::gsem(ctx.symbols, ctx.bindings), event, terms, word);
                assert forall|i: int| 0 <= i < ids.len() implies language::lang(model::gsem(ctx.symbols, ctx.bindings),
                    language::interp_transition(model::gsem(ctx.symbols, ctx.bindings), event, terms[i]), word)
                        == transition_lang(g, ctx.symbols, ctx.bindings, ids[i], event, word) by {}
                if guarded_language(sem, ctx, event, expected, word) {
                    let i = choose|i: int| 0 <= i < terms.len() && language::lang(model::gsem(ctx.symbols, ctx.bindings),
                        language::interp_transition(model::gsem(ctx.symbols, ctx.bindings), event, terms[i]), word);
                    assert(transition_combo(g, ctx.symbols, ctx.bindings, ids, event, word, false));
                }
                if transition_combo(g, ctx.symbols, ctx.bindings, ids, event, word, false) {
                    let i = choose|i: int| 0 <= i < ids.len() && transition_lang(g, ctx.symbols, ctx.bindings, ids[i], event, word);
                    assert(language::lang(model::gsem(ctx.symbols, ctx.bindings),
                        language::interp_transition(model::gsem(ctx.symbols, ctx.bindings), event, terms[i]), word));
                }
                transition_lemma_known_language(g, out, ctx, event, word);
                assert(transition_lang(g, ctx.symbols, ctx.bindings, out, event, word)
                    == transition_combo(g, ctx.symbols, ctx.bindings, ids, event, word, false));
            }
        }
        guarded_lemma_apply_set_suffix(sem, prefix, children, false);
        guarded_lemma_stack_refl(sem, valid, prefix);
        guarded_lemma_stack_push(sem, valid, prefix, prefix, expected, result);
        transition_lemma_known_push(g, prior.take(start), out);
        assert(pending.subrange(pending.len() as int, pending.len() as int) =~= Seq::<ActionShape>::empty());
    }

    pub proof fn machine_driver_intersect_effect(
        g: model::Graph, count: nat, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    )
        requires count <= prior.len(),
        ensures transition_effect(g, ActionShape::Intersect(count), pending, prior,
            pending.push(ActionShape::Fold(model::transition_ids(prior.subrange(prior.len() as int - count as int, prior.len() as int)), 0)),
            prior.take(prior.len() as int - count as int)),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let start = prior.len() as int - count as int;
        let ids = prior.subrange(start, prior.len() as int);
        let prefix = transition_known_values(g, prior.take(start));
        let children = transition_known_values(g, ids);
        let expected = guarded_set(children, true);
        let terms = model::transition_ids(ids).map(|i: int, id: nat| model::lift_transition(g, id));
        let result = guarded_constant(language::Transition::Intersect(terms));
        assert(expected.term == result.term) by {
            assert(children.map(|i: int, value: TransitionMeaning| value.term) =~= terms);
        }
        guarded_lemma_same_term(sem, valid, expected, result);
        assert(transition_known_values(g, prior) =~= prefix + children);
        guarded_lemma_apply_set_suffix(sem, prefix, children, true);
        guarded_lemma_stack_refl(sem, valid, prefix);
        guarded_lemma_stack_push(sem, valid, prefix, prefix, expected, result);
        let task = ActionShape::Fold(model::transition_ids(ids), 0);
        assert(pending.push(task).subrange(pending.len() as int, pending.len() as int + 1) =~= seq![task]);
        assert(transition_freeze_tasks(g, seq![task]) =~= seq![GuardedAction::Fold(terms, 0)]);
        guarded_lemma_run_singleton(sem, GuardedAction::Fold(terms, 0), prefix);
    }

    pub proof fn machine_driver_if_effect(
        g: model::Graph, test: TestId, path: Option<TestId>, pending: Seq<ActionShape>, prior: Seq<TransitionId>, out: TransitionId,
    )
        requires prior.len() >= 2,
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(g, sym, theta, out, event, word)
                    == transition_if_combo(g, sym, theta, test, prior[prior.len() as int - 2], prior.last(), event, word),
        ensures match path {
            None => transition_effect(g, ActionShape::If(test@), pending, prior, pending,
                prior.take(prior.len() as int - 2).push(out)),
            Some(path) => transition_effect(g, ActionShape::CleanIf(test@, path@), pending, prior,
                pending.push(ActionShape::Clean(out@, path@)), prior.take(prior.len() as int - 2)),
        },
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let start = prior.len() as int - 2;
        let prefix_ids = prior.take(start);
        let prefix = transition_known_values(g, prefix_ids);
        let a = prior[start];
        let b = prior.last();
        let yes = transition_known(g, a);
        let no = transition_known(g, b);
        assert(transition_known_values(g, prior) =~= prefix.push(yes).push(no));
        let expected = match path {
            None => guarded_if(sem, model::lift_test(g, test@), yes, no),
            Some(path) => guarded_clean_if(sem, model::lift_test(g, test@), model::lift_test(g, path@), yes, no),
        };
        let result = match path {
            None => transition_known(g, out),
            Some(path) => guarded_clean(sem, model::lift_test(g, path@), model::lift_transition(g, out@)),
        };
        assert forall|ctx: TransitionContext, event: Data| valid(ctx) && #[trigger] (expected.guard)(ctx, event)
            implies (result.guard)(ctx, event) && forall|word: Seq<Data>|
                guarded_language(sem, ctx, event, expected, word) == guarded_language(sem, ctx, event, result, word) by {
            transition_lemma_context_sem(ctx);
            language::lemma_interp_if(model::gsem(ctx.symbols, ctx.bindings), event, model::lift_test(g, test@), yes.term, no.term);
            assert forall|word: Seq<Data>| guarded_language(sem, ctx, event, expected, word)
                == guarded_language(sem, ctx, event, result, word) by {
                assert(transition_lang(g, ctx.symbols, ctx.bindings, out, event, word)
                    == transition_if_combo(g, ctx.symbols, ctx.bindings, test, a, b, event, word));
            }
        }
        guarded_lemma_stack_refl(sem, valid, prefix);
        guarded_lemma_stack_push(sem, valid, prefix, prefix, expected, result);
        assert(prefix.push(yes).push(no).take(start) =~= prefix);
        match path {
            None => {
                transition_lemma_known_push(g, prefix_ids, out);
                assert(pending.subrange(pending.len() as int, pending.len() as int) =~= Seq::<ActionShape>::empty());
            },
            Some(path) => {
                let task = ActionShape::Clean(out@, path@);
                assert(pending.push(task).subrange(pending.len() as int, pending.len() as int + 1) =~= seq![task]);
                assert(transition_freeze_tasks(g, seq![task]) =~= seq![GuardedAction::Clean(model::lift_transition(g, out@), model::lift_test(g, path@))]);
                guarded_lemma_run_singleton(sem, transition_freeze_action(g, task), prefix);
            },
        }
    }

    pub open spec fn machine_driver_result_action(task: ActionShape, id: TransitionId) -> ActionShape {
        match task {
            ActionShape::NotResult => ActionShape::Not(id@),
            ActionShape::AppendResult(suffix) => ActionShape::Append(id@, suffix),
            _ => task,
        }
    }

    pub proof fn machine_driver_result_effect(g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>)
        requires prior.len() > 0, task is NotResult || task is AppendResult,
        ensures transition_effect(g, task, pending, prior, pending.push(machine_driver_result_action(task, prior.last())), prior.drop_last()),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        let next = machine_driver_result_action(task, prior.last());
        let prefix = transition_known_values(g, prior.drop_last());
        let last = transition_known(g, prior.last());
        assert(transition_known_values(g, prior) =~= prefix.push(last));
        let before = guarded_apply(sem, transition_freeze_action(g, task), transition_known_values(g, prior));
        let after = guarded_apply(sem, transition_freeze_action(g, next), prefix);
        assert(before == after) by {
            assert(prefix.push(last).drop_last() =~= prefix);
            match task { ActionShape::NotResult => {}, ActionShape::AppendResult(suffix) => {}, _ => {} }
        }
        guarded_lemma_stack_refl(sem, valid, after.unwrap());
        guarded_lemma_run_singleton(sem, transition_freeze_action(g, next), prefix);
        assert(pending.push(next).subrange(pending.len() as int, pending.len() as int + 1) =~= seq![next]);
        assert(transition_freeze_tasks(g, seq![next]) =~= seq![transition_freeze_action(g, next)]);
    }

    pub proof fn machine_driver_swap_effect(g: model::Graph, pending: Seq<ActionShape>, prior: Seq<TransitionId>)
        requires prior.len() >= 2,
        ensures transition_effect(g, ActionShape::SwapThen, pending, prior, pending,
            prior.take(prior.len() as int - 2).push(prior.last()).push(prior[prior.len() as int - 2])),
    {
        let next = prior.take(prior.len() as int - 2).push(prior.last()).push(prior[prior.len() as int - 2]);
        let known = transition_known_values(g, prior);
        assert(transition_known_values(g, next) =~= known.take(known.len() as int - 2).push(known.last()).push(known[known.len() as int - 2]));
        guarded_lemma_stack_refl(transition_context_sem(), transition_context_valid(), transition_known_values(g, next));
        assert(pending.subrange(pending.len() as int, pending.len() as int) =~= Seq::<ActionShape>::empty());
    }

    pub proof fn machine_driver_complete(g: model::Graph, task: ActionShape, values: Seq<TransitionId>)
        requires transition_action_pushes(task),
            transition_program_refines(transition_program(g, seq![task], Seq::empty()), Some(transition_known_values(g, values))),
        ensures values.len() == 1, transition_result(g, task, values.last()),
    {
        let sem = transition_context_sem();
        let valid = transition_context_valid();
        assert(transition_freeze_tasks(g, seq![task]) =~= seq![transition_freeze_action(g, task)]);
        assert(transition_known_values(g, Seq::empty()) =~= Seq::<TransitionMeaning>::empty());
        guarded_lemma_run_singleton(sem, transition_freeze_action(g, task), Seq::<TransitionMeaning>::empty());
        let expected = transition_initial_value(g, task).unwrap();
        assert(guarded_apply(sem, transition_freeze_action(g, task), Seq::<TransitionMeaning>::empty()) == Some(seq![expected]));
        assert(transition_program(g, seq![task], Seq::empty()) == Some(seq![expected]));
        assert(values.len() == 1);
        assert(guarded_refines(sem, valid, expected, transition_known(g, values.last())));
        transition_lemma_refines_result(g, task, values.last());
    }


    pub open spec fn transition_append_combo(
        g: model::Graph, sym: model::Symbols, theta: Seq<Data>, root: TransitionId, suffix: Seq<RegexId>, event: Data, word: Seq<Data>,
    ) -> bool {
        let sem = model::gsem(sym, theta);
        language::lang(sem, language::Regex::Concat(seq![language::interp_transition(sem, event, model::lift_transition(g, root@))]
            + model::lift_regexes(g, model::regex_ids(suffix))), word)
    }

    pub proof fn machine_driver_extension_future(before: model::Graph, middle: model::Graph)
        requires model::graph_extends(before, middle),
        ensures forall|after: model::Graph| model::graph_extends(middle, after) ==> model::graph_extends(before, after),
    {
        assert forall|after: model::Graph| model::graph_extends(middle, after) implies model::graph_extends(before, after) by {
            transition_lemma_extends_transitive(before, middle, after);
        }
    }

    pub proof fn machine_driver_if_future(
        before: model::Graph, test: TestId, yes: TransitionId, no: TransitionId, local: TransitionId,
    )
        requires model::graph_wf(before), test@ < before.tests.len(),
            yes@ < before.transitions.len(), no@ < before.transitions.len(), local@ < before.transitions.len(),
            forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(before, sym, theta, local, event, word) == transition_if_combo(before, sym, theta, test, yes, no, event, word),
        ensures forall|after: model::Graph, out: TransitionId| model::graph_extends(before, after) && model::graph_wf(after)
            && #[trigger] transition_result(after, ActionShape::Clean(local@, before.constants.test_true), out)
            ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == transition_if_combo(after, sym, theta, test, yes, no, event, word),
    {
        model::lemma_graph_wf_elim(before);
        assert forall|after: model::Graph, out: TransitionId| model::graph_extends(before, after) && model::graph_wf(after)
            && #[trigger] transition_result(after, ActionShape::Clean(local@, before.constants.test_true), out)
            implies forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == transition_if_combo(after, sym, theta, test, yes, no, event, word) by {
            model::lemma_lift_test_stable(before, after, test@);
            model::lemma_lift_transition_stable(before, after, yes@);
            model::lemma_lift_transition_stable(before, after, no@);
            model::lemma_lift_transition_stable(before, after, local@);
            transition_lemma_test_constants(after);
            let expected = transition_initial_value(after, ActionShape::Clean(local@, before.constants.test_true)).unwrap();
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                implies transition_lang(after, sym, theta, out, event, word) == transition_if_combo(after, sym, theta, test, yes, no, event, word) by {
                let ctx = TransitionContext { symbols: sym, bindings: theta };
                transition_lemma_context_sem(ctx);
                assert((expected.guard)(ctx, event));
                assert(guarded_language(transition_context_sem(), ctx, event, expected, word)
                    == transition_lang(after, sym, theta, out, event, word));
                assert(transition_lang(before, sym, theta, local, event, word)
                    == transition_if_combo(before, sym, theta, test, yes, no, event, word));
            }
        }
    }

    pub proof fn machine_driver_append_future(
        before: model::Graph, root: TransitionId, suffix: Seq<RegexId>, combined: RegexId,
    )
        requires model::graph_wf(before), combined@ < before.regexes.len(), regex_ids_valid(before, suffix),
            forall|sym: model::Symbols, theta: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                ==> model::regex_lang(before, sym, theta, combined@, word) == concat_combo(before, sym, theta, suffix, word),
        ensures forall|after: model::Graph, out: TransitionId| model::graph_extends(before, after) && model::graph_wf(after)
            && #[trigger] transition_result(after, ActionShape::Append(root@, combined@), out)
            ==> forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == transition_append_combo(after, sym, theta, root, suffix, event, word),
    {
        model::lemma_graph_wf_elim(before);
        assert forall|after: model::Graph, out: TransitionId| model::graph_extends(before, after) && model::graph_wf(after)
            && #[trigger] transition_result(after, ActionShape::Append(root@, combined@), out)
            implies forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                ==> transition_lang(after, sym, theta, out, event, word) == transition_append_combo(after, sym, theta, root, suffix, event, word) by {
            model::lemma_lift_regex_stable(before, after, combined@);
            regex_concat_extends(before, after, suffix);
            let expected = transition_initial_value(after, ActionShape::Append(root@, combined@)).unwrap();
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>| model::symbols_wf(sym)
                implies transition_lang(after, sym, theta, out, event, word) == transition_append_combo(after, sym, theta, root, suffix, event, word) by {
                let ctx = TransitionContext { symbols: sym, bindings: theta };
                transition_lemma_context_sem(ctx);
                let sem = model::gsem(sym, theta);
                let head = language::interp_transition(sem, event, model::lift_transition(after, root@));
                let tail = model::lift_regexes(after, model::regex_ids(suffix));
                let combined_term = model::lift_regex(after, combined@);
                language::lemma_interp_append(sem, event, model::lift_transition(after, root@), seq![combined_term]);
                assert forall|w: Seq<Data>| language::lang(sem, language::Regex::Concat(tail), w) == language::lang(sem, combined_term, w) by {
                    assert(model::regex_lang(before, sym, theta, combined@, w) == concat_combo(before, sym, theta, suffix, w));
                    assert(concat_combo(before, sym, theta, suffix, w) == concat_combo(after, sym, theta, suffix, w));
                }
                regex_concat_replace(sem, seq![head], tail, combined_term);
                assert((expected.guard)(ctx, event));
                assert(guarded_language(transition_context_sem(), ctx, event, expected, word)
                    == transition_lang(after, sym, theta, out, event, word));
                assert(seq![head] + seq![combined_term] =~= seq![head].push(combined_term));
            }
        }
    }

        }
}

// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use super::error::HistoryError;
use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::*;
#[cfg(verus_keep_ghost)]
use verify::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

pub(crate) type KernelResult<T> = core::result::Result<T, HistoryError>;
#[verus_verify]
pub(crate) const MAX_GRAPH_BYTES: usize = 100 * 1024;

// Keep a loop-body error in a local, stop the loop, and propagate it after the loop.
macro_rules! loop_try {
    ($expression:expr, $failure:ident) => {{
        let outcome = $expression;
        match outcome {
            Ok(value) => value,
            Err(error) => {
                $failure = Some(error);
                break;
            }
        }
    }};
}
pub(crate) use loop_try;

// A checked iteration is one function call. No partially reborrowed store is
// carried by an early loop exit; success and failure meet at the loop condition.
macro_rules! scan {
    ($state:ident,$index:ident,$count:expr,$condition:expr,$value:ident=>$step:expr) => {{
        let mut $index = 0;
        while $index < $count && $condition {
            $state = match $state {
                Ok($value) => $step,
                Err(error) => Err(error),
            };
            $index = $index.saturating_add(1);
        }
    }};
    ($state:ident,$index:ident,$count:expr,$condition:expr,$value:ident=>$step:expr; $($spec:tt)*) => {{
        let mut $index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec($($spec)*))]
        while $index < $count && $condition {
            $state = match $state {
                Ok($value) => $step,
                Err(error) => Err(error),
            };
            $index = $index.saturating_add(1);
        }
    }};
}
pub(crate) use scan;

macro_rules! id {
    ($name:ident) => {
        #[verus_verify]
        #[verus_verify(external_derive)]
        #[cfg_attr(verus_keep_ghost, derive(Structural))]
        #[derive(Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub(crate) struct $name(pub(crate) u32);
        #[verus_verify]
        impl Clone for $name {
            #[verus_spec(result => ensures result == *self)]
            fn clone(&self) -> Self {
                *self
            }
        }
        #[verus_verify]
        impl $name {
            #[verus_spec(result => ensures
                                                match result {
                                                    Ok(index) => index as nat == self.0 as nat,
                                                    Err(error) => self.0 as nat > usize::MAX as nat && error is Invariant,
                                                },
                                            )]
            pub(crate) fn index(self) -> KernelResult<usize> {
                match usize::try_from(self.0) {
                    Ok(index) => Ok(index),
                    Err(_) => Err(super::error::graph_id_overflow()),
                }
            }
            #[verus_spec(result => ensures
                                                match result {
                                                    Ok(id) => id.0 as nat == index as nat,
                                                    Err(error) => index as nat > u32::MAX as nat && error is GraphLimit,
                                                },
                                            )]
            pub(crate) fn from_index(index: usize) -> KernelResult<Self> {
                match u32::try_from(index) {
                    Ok(value) => Ok(Self(value)),
                    Err(_) => Err(super::error::graph_index_overflow()),
                }
            }
        }
    };
}
id!(TestId);
id!(RegexId);
id!(TransitionId);
id!(ConstId);
id!(PathId);
id!(VariableId);

// `eq` is proved equal to structural equality on the view, so derived `Hash` agrees with it.
#[allow(clippy::derived_hash_with_manual_eq)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialOrd, Ord, Hash)]
pub(crate) enum Term {
    Constant(ConstId),
    Variable(VariableId),
}
#[allow(clippy::derived_hash_with_manual_eq)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialOrd, Ord, Hash)]
pub(crate) enum Primitive {
    HasValue(PathId),
    EqCore(PathId, Term),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, Hash)]
pub(crate) enum TestView<'a> {
    True,
    False,
    Atom {
        primitive: Primitive,
        positive: bool,
    },
    And(&'a [TestId]),
    Or(&'a [TestId]),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, Hash)]
pub(crate) enum RegexKindView<'a> {
    Empty,
    All,
    Epsilon,
    Test(TestId),
    Union(&'a [RegexId]),
    Concat(&'a [RegexId]),
    Star(RegexId),
    Intersect(&'a [RegexId]),
    Not(RegexId),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, Eq, Hash)]
pub(crate) struct RegexView<'a> {
    pub(crate) kind: RegexKindView<'a>,
    pub(crate) nullable: bool,
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, Hash)]
pub(crate) enum TransitionView<'a> {
    Const(RegexId),
    If {
        test: TestId,
        then_transition: TransitionId,
        else_transition: TransitionId,
    },
    Union(&'a [TransitionId]),
    Intersect(&'a [TransitionId]),
    Not(TransitionId),
    Append {
        transition: TransitionId,
        suffix: &'a [RegexId],
    },
}

// Copy the drop-free operands before comparing. Deriving these enum comparisons
// delegates borrowed child fields to a reference-of-reference Eq implementation
// which the pinned extractor cannot interpret.
#[verus_verify]
#[verus_spec(result =>
    requires T::obeys_eq_spec(),
        forall|a: T, b: T| a.eq_spec(&b) == (a == b),
    ensures result == (left@ == right@),
)]
pub(super) fn id_slice_eq<T: Copy + Eq>(left: &[T], right: &[T]) -> bool {
    let mut equal = left.len() == right.len();
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            T::obeys_eq_spec(),
            forall|a: T, b: T| a.eq_spec(&b) == (a == b),
            index <= left.len(),
            equal ==> left.len() == right.len(),
            equal ==> forall|i: int| 0 <= i < index ==> left@[i] == right@[i],
            !equal ==> left@ != right@,
        decreases left.len() - index,
    ))]
    while equal && index < left.len() {
        equal = match (left.get(index).copied(), right.get(index).copied()) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        };
        proof! {
            if equal {
                assert forall|i: int| 0 <= i <= index implies left@[i] == right@[i] by {}
            } else {
                assert(left@[index as int] != right@[index as int]);
                assert(left@ != right@);
            }
        }
        index = index.saturating_add(1);
    }
    proof! { if equal { assert(left@ =~= right@); } }
    equal
}
#[verus_verify]
impl PartialEq for Term {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Constant(a), Self::Constant(b)) => a == b,
            (Self::Variable(a), Self::Variable(b)) => a == b,
            _ => false,
        }
    }
}
impl Eq for Term {}
#[verus_verify]
impl PartialEq for Primitive {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::HasValue(a), Self::HasValue(b)) => a == b,
            (Self::EqCore(p, t), Self::EqCore(q, u)) => p == q && t == u,
            _ => false,
        }
    }
}
impl Eq for Primitive {}
#[verus_verify]
impl PartialEq for TestView<'_> {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::True, Self::True) | (Self::False, Self::False) => true,
            (
                Self::Atom {
                    primitive: p,
                    positive: x,
                },
                Self::Atom {
                    primitive: q,
                    positive: y,
                },
            ) => p == q && x == y,
            (Self::And(a), Self::And(b)) | (Self::Or(a), Self::Or(b)) => {
                proof! { lemma_test_ids_eq(a@, b@); }
                id_slice_eq(a, b)
            }
            _ => false,
        }
    }
}
impl Eq for TestView<'_> {}
#[verus_verify]
impl PartialEq for RegexKindView<'_> {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Empty, Self::Empty)
            | (Self::All, Self::All)
            | (Self::Epsilon, Self::Epsilon) => true,
            (Self::Test(a), Self::Test(b)) => a == b,
            (Self::Star(a), Self::Star(b)) | (Self::Not(a), Self::Not(b)) => a == b,
            (Self::Union(a), Self::Union(b))
            | (Self::Concat(a), Self::Concat(b))
            | (Self::Intersect(a), Self::Intersect(b)) => {
                proof! { lemma_regex_ids_eq(a@, b@); }
                id_slice_eq(a, b)
            }
            _ => false,
        }
    }
}
impl Eq for RegexKindView<'_> {}
#[verus_verify]
impl PartialEq for RegexView<'_> {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.nullable == other.nullable
    }
}
#[verus_verify]
impl PartialEq for TransitionView<'_> {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Const(a), Self::Const(b)) => a == b,
            (
                Self::If {
                    test: a,
                    then_transition: b,
                    else_transition: c,
                },
                Self::If {
                    test: x,
                    then_transition: y,
                    else_transition: z,
                },
            ) => a == x && b == y && c == z,
            (Self::Union(a), Self::Union(b)) | (Self::Intersect(a), Self::Intersect(b)) => {
                proof! { lemma_transition_ids_eq(a@, b@); }
                id_slice_eq(a, b)
            }
            (Self::Not(a), Self::Not(b)) => a == b,
            (
                Self::Append {
                    transition: a,
                    suffix: x,
                },
                Self::Append {
                    transition: b,
                    suffix: y,
                },
            ) => {
                proof! { lemma_regex_ids_eq(x@, y@); }
                a == b && id_slice_eq(x, y)
            }
            _ => false,
        }
    }
}
impl Eq for TransitionView<'_> {}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Constants {
    pub(crate) test_true: TestId,
    pub(crate) test_false: TestId,
    pub(crate) empty: RegexId,
    pub(crate) all: RegexId,
    pub(crate) epsilon: RegexId,
    pub(crate) transition_empty: TransitionId,
    pub(crate) transition_all: TransitionId,
    pub(crate) transition_epsilon: TransitionId,
}
pub(crate) trait KernelStore {
    fn checkpoint(&mut self) -> KernelResult<()>;
    fn charge_aux(&mut self, bytes: usize) -> KernelResult<()>;
    fn reserve_derivatives(
        &mut self,
        values: &mut Vec<Option<TransitionId>>,
        additional: usize,
    ) -> KernelResult<()>;
    fn reserve_atoms(&mut self, values: &mut Vec<TestId>, additional: usize) -> KernelResult<()>;
    fn constants(&self) -> Constants;
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>>;
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>>;
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>>;
    fn intern_test(&mut self, node: TestView<'_>) -> KernelResult<TestId>;
    fn intern_regex(&mut self, kind: RegexKindView<'_>, nullable: bool) -> KernelResult<RegexId>;
    fn intern_transition(&mut self, node: TransitionView<'_>) -> KernelResult<TransitionId>;
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct AtomSet {
    ids: Vec<TestId>,
}
#[verus_verify]
impl AtomSet {
    #[verus_spec(result => ensures result@ == self@)]
    pub(crate) const fn ids(&self) -> &[TestId] {
        self.ids.as_slice()
    }
}
#[verus_verify]
#[verus_spec(result => ensures
    final(store).graph() == old(store).graph(),
    final(store).valid_store() == old(store).valid_store(),
    final(store).restoration() == old(store).restoration(),
    match result {
        Ok(Some(id)) => index < ids@.len() && id == ids@[index as int]
            && id@ < final(store).graph().tests.len()
            && (final(store).graph().tests[id@ as int] matches TestNode::Atom(_, true))
            && match previous { Some(prev) => prev@ < id@, None => true },
        _ => result is Err,
    },
)]
fn atom_set_step<G: KernelStore>(
    store: &mut G,
    ids: &[TestId],
    index: usize,
    previous: Option<TestId>,
) -> KernelResult<Option<TestId>> {
    store.checkpoint()?;
    let id = match ids.get(index) {
        Some(v) => *v,
        None => return Err(super::error::invalid_atom_set()),
    };
    let valid = matches!(test_head(store, id), Ok(TestHead::Atom(_, true)));
    let unordered = match previous {
        Some(prev) => prev >= id,
        None => false,
    };
    if !valid || unordered {
        Err(super::error::invalid_atom_set())
    } else {
        Ok(Some(id))
    }
}
#[verus_verify]
#[verus_spec(result => ensures
    final(store).graph() == old(store).graph(),
    final(store).valid_store() == old(store).valid_store(),
    final(store).restoration() == old(store).restoration(),
    match result { Ok(atoms) => atoms@ == ids@ && atom_ids_wf(final(store).graph(), atoms@), Err(_) => true },
)]
pub(crate) fn atom_set<G: KernelStore>(store: &mut G, ids: Vec<TestId>) -> KernelResult<AtomSet> {
    let mut state = Ok(None);
    scan!(state,index,ids.len(),state.is_ok(),previous=>atom_set_step(store,&ids,index,previous);
        invariant
            store.graph() == old(store).graph(),
            store.valid_store() == old(store).valid_store(),
            store.restoration() == old(store).restoration(),
            index <= ids.len(),
            match state {
                Ok(previous) => atom_prefix_wf(store.graph(), ids@, index as nat)
                    && previous == if index == 0 { None } else { Some(ids@[index as int - 1]) },
                Err(_) => true,
            },
        decreases ids.len() - index,
    );
    state?;
    Ok(AtomSet { ids })
}

// Drop-free heads end store-backed slice borrows before any mutable operation.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) enum TestHead {
    True,
    False,
    Atom(Primitive, bool),
    And(usize),
    Or(usize),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy)]
pub(crate) enum RegexHead {
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
pub(crate) enum TransitionHead {
    Const(RegexId),
    If(TestId, TransitionId, TransitionId),
    Union(usize),
    Intersect(usize),
    Not(TransitionId),
    Append(TransitionId, usize),
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(head) => id@ < store.graph().tests.len() && head@ == test_node_head(store.graph().tests[id@ as int]),
    Err(_) => true,
})]
pub(crate) fn test_head<G: KernelStore>(store: &G, id: TestId) -> KernelResult<TestHead> {
    Ok(match store.test(id)? {
        TestView::True => TestHead::True,
        TestView::False => TestHead::False,
        TestView::Atom {
            primitive,
            positive,
        } => TestHead::Atom(primitive, positive),
        TestView::And(xs) => TestHead::And(xs.len()),
        TestView::Or(xs) => TestHead::Or(xs.len()),
    })
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(head) => id@ < store.graph().regexes.len() && head@ == regex_node_head(store.graph().regexes[id@ as int].kind),
    Err(_) => true,
})]
pub(crate) fn regex_head<G: KernelStore>(store: &G, id: RegexId) -> KernelResult<RegexHead> {
    Ok(match store.regex(id)?.kind {
        RegexKindView::Empty => RegexHead::Empty,
        RegexKindView::All => RegexHead::All,
        RegexKindView::Epsilon => RegexHead::Epsilon,
        RegexKindView::Test(t) => RegexHead::Test(t),
        RegexKindView::Union(xs) => RegexHead::Union(xs.len()),
        RegexKindView::Concat(xs) => RegexHead::Concat(xs.len()),
        RegexKindView::Star(inner) => RegexHead::Star(inner),
        RegexKindView::Intersect(xs) => RegexHead::Intersect(xs.len()),
        RegexKindView::Not(inner) => RegexHead::Not(inner),
    })
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(head) => id@ < store.graph().transitions.len() && head@ == transition_node_head(store.graph().transitions[id@ as int]),
    Err(_) => true,
})]
pub(crate) fn transition_head<G: KernelStore>(
    store: &G,
    id: TransitionId,
) -> KernelResult<TransitionHead> {
    Ok(match store.transition(id)? {
        TransitionView::Const(r) => TransitionHead::Const(r),
        TransitionView::If {
            test,
            then_transition,
            else_transition,
        } => TransitionHead::If(test, then_transition, else_transition),
        TransitionView::Union(xs) => TransitionHead::Union(xs.len()),
        TransitionView::Intersect(xs) => TransitionHead::Intersect(xs.len()),
        TransitionView::Not(inner) => TransitionHead::Not(inner),
        TransitionView::Append { transition, suffix } => {
            TransitionHead::Append(transition, suffix.len())
        }
    })
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(child) => id@ < store.graph().tests.len() && test_node_child(store.graph().tests[id@ as int], index as nat) == Some(child@),
    Err(_) => true,
})]
pub(crate) fn test_child<G: KernelStore>(
    store: &G,
    id: TestId,
    index: usize,
) -> KernelResult<TestId> {
    match store.test(id)? {
        TestView::And(xs) | TestView::Or(xs) => match xs.get(index) {
            Some(value) => Ok(*value),
            None => Err(super::error::normalization_invariant()),
        },
        _ => Err(super::error::normalization_invariant()),
    }
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(child) => id@ < store.graph().regexes.len() && regex_node_child(store.graph().regexes[id@ as int].kind, index as nat) == Some(child@),
    Err(_) => true,
})]
pub(crate) fn regex_child<G: KernelStore>(
    store: &G,
    id: RegexId,
    index: usize,
) -> KernelResult<RegexId> {
    match store.regex(id)?.kind {
        RegexKindView::Union(xs) | RegexKindView::Concat(xs) | RegexKindView::Intersect(xs) => {
            match xs.get(index) {
                Some(value) => Ok(*value),
                None => Err(super::error::normalization_invariant()),
            }
        }
        _ => Err(super::error::normalization_invariant()),
    }
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(child) => id@ < store.graph().transitions.len() && transition_node_child(store.graph().transitions[id@ as int], index as nat) == Some(child@),
    Err(_) => true,
})]
pub(crate) fn transition_child<G: KernelStore>(
    store: &G,
    id: TransitionId,
    index: usize,
) -> KernelResult<TransitionId> {
    match store.transition(id)? {
        TransitionView::Union(xs) | TransitionView::Intersect(xs) => match xs.get(index) {
            Some(value) => Ok(*value),
            None => Err(super::error::normalization_invariant()),
        },
        _ => Err(super::error::normalization_invariant()),
    }
}
#[verus_verify]
#[verus_spec(result => ensures match result {
    Ok(child) => id@ < store.graph().transitions.len() && transition_node_suffix(store.graph().transitions[id@ as int], index as nat) == Some(child@),
    Err(_) => true,
})]
pub(crate) fn suffix_child<G: KernelStore>(
    store: &G,
    id: TransitionId,
    index: usize,
) -> KernelResult<RegexId> {
    match store.transition(id)? {
        TransitionView::Append { suffix, .. } => match suffix.get(index) {
            Some(value) => Ok(*value),
            None => Err(super::error::normalization_invariant()),
        },
        _ => Err(super::error::normalization_invariant()),
    }
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    use crate::verify::history_specs::{self as language, Regex, Transition};
    use crate::verify::value_specs::Data;
    use alloc::boxed::Box;
    use vstd::std_specs::cmp::{OrdSpecImpl, PartialEqSpecImpl, PartialOrdSpecImpl};

    macro_rules! id_model {
        ($id:ident) => { verus! {
            impl View for $id {
                type V = nat;
                open(crate) spec fn view(&self) -> nat { self.0 as nat }
            }
            impl PartialEqSpecImpl for $id {
                open spec fn obeys_eq_spec() -> bool { true }
                open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self.0 == other.0 }
            }
            impl OrdSpecImpl for $id {
                open spec fn obeys_cmp_spec() -> bool { true }
                open(crate) spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering {
                    vstd::std_specs::cmp::OrdSpec::cmp_spec(&self.0, &other.0)
                }
            }
            impl PartialOrdSpecImpl for $id {
                open spec fn obeys_partial_cmp_spec() -> bool { true }
                open(crate) spec fn partial_cmp_spec(&self, other: &Self) -> Option<core::cmp::Ordering> {
                    Some(vstd::std_specs::cmp::OrdSpec::cmp_spec(&self.0, &other.0))
                }
            }
        }};
    }
    id_model!(TestId);
    id_model!(RegexId);
    id_model!(TransitionId);
    id_model!(ConstId);
    id_model!(PathId);
    id_model!(VariableId);

    verus! {

    pub enum GTerm { Constant(nat), Variable(nat) }
    pub enum Primitive { HasValue(nat), EqCore(nat, GTerm) }
    pub enum TestNode { True, False, Atom(Primitive, bool), And(Seq<nat>), Or(Seq<nat>) }
    pub enum Test { True, False, Atom(Primitive, bool), And(Seq<Test>), Or(Seq<Test>) }
    pub enum RegexKindNode {
        Empty, All, Epsilon, Test(nat), Union(Seq<nat>), Concat(Seq<nat>),
        Star(nat), Intersect(Seq<nat>), Not(nat),
    }
    pub struct RegexNode { pub kind: RegexKindNode, pub nullable: bool }
    pub enum TransitionNode {
        Const(nat), If(nat, nat, nat), Union(Seq<nat>), Intersect(Seq<nat>),
        Not(nat), Append(nat, Seq<nat>),
    }
    pub struct ConstantsModel {
        pub test_true: nat, pub test_false: nat,
        pub empty: nat, pub all: nat, pub epsilon: nat,
        pub transition_empty: nat, pub transition_all: nat, pub transition_epsilon: nat,
    }
    pub struct Graph {
        pub tests: Seq<TestNode>, pub regexes: Seq<RegexNode>,
        pub transitions: Seq<TransitionNode>, pub constants: ConstantsModel,
    }
    pub struct Symbols {
        pub constants: Seq<Data>, pub paths: Seq<Seq<Data>>, pub variables: Seq<Seq<char>>,
    }
    pub enum TestHeadNode { True, False, Atom(Primitive, bool), And(nat), Or(nat) }
    pub enum RegexHeadNode {
        Empty, All, Epsilon, Test(nat), Union(nat), Concat(nat), Star(nat), Intersect(nat), Not(nat),
    }
    pub enum TransitionHeadNode { Const(nat), If(nat, nat, nat), Union(nat), Intersect(nat), Not(nat), Append(nat, nat) }

    impl PartialEqSpecImpl for super::Term {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }
    impl PartialEqSpecImpl for super::Primitive {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }
    impl PartialEqSpecImpl for TestView<'_> {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }
    impl PartialEqSpecImpl for RegexKindView<'_> {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }
    impl PartialEqSpecImpl for RegexView<'_> {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }
    impl PartialEqSpecImpl for TransitionView<'_> {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }

    impl View for super::Term {
        type V = GTerm;
        open(crate) spec fn view(&self) -> GTerm {
            match self { super::Term::Constant(c) => GTerm::Constant(c@), super::Term::Variable(v) => GTerm::Variable(v@) }
        }
    }
    impl View for super::Primitive {
        type V = Primitive;
        open(crate) spec fn view(&self) -> Primitive {
            match self { super::Primitive::HasValue(p) => Primitive::HasValue(p@), super::Primitive::EqCore(p, t) => Primitive::EqCore(p@, t@) }
        }
    }
    pub open spec fn test_ids(ids: Seq<TestId>) -> Seq<nat> { Seq::new(ids.len(), |i: int| ids[i]@) }
    pub open spec fn regex_ids(ids: Seq<RegexId>) -> Seq<nat> { Seq::new(ids.len(), |i: int| ids[i]@) }
    pub open spec fn transition_ids(ids: Seq<TransitionId>) -> Seq<nat> { Seq::new(ids.len(), |i: int| ids[i]@) }
    pub proof fn lemma_test_ids_eq(a: Seq<TestId>, b: Seq<TestId>)
        ensures (test_ids(a) == test_ids(b)) == (a == b),
    {
        if test_ids(a) == test_ids(b) {
            assert(test_ids(a).len() == a.len());
            assert(test_ids(b).len() == b.len());
            assert(a.len() == b.len());
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                assert(test_ids(a)[i] == a[i]@);
                assert(test_ids(b)[i] == b[i]@);
            }
            assert(a =~= b);
        }
    }
    pub proof fn lemma_regex_ids_eq(a: Seq<RegexId>, b: Seq<RegexId>)
        ensures (regex_ids(a) == regex_ids(b)) == (a == b),
    {
        if regex_ids(a) == regex_ids(b) {
            assert(regex_ids(a).len() == a.len());
            assert(regex_ids(b).len() == b.len());
            assert(a.len() == b.len());
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                assert(regex_ids(a)[i] == a[i]@);
                assert(regex_ids(b)[i] == b[i]@);
            }
            assert(a =~= b);
        }
    }
    pub proof fn lemma_transition_ids_eq(a: Seq<TransitionId>, b: Seq<TransitionId>)
        ensures (transition_ids(a) == transition_ids(b)) == (a == b),
    {
        if transition_ids(a) == transition_ids(b) {
            assert(transition_ids(a).len() == a.len());
            assert(transition_ids(b).len() == b.len());
            assert(a.len() == b.len());
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                assert(transition_ids(a)[i] == a[i]@);
                assert(transition_ids(b)[i] == b[i]@);
            }
            assert(a =~= b);
        }
    }
    impl View for TestView<'_> {
        type V = TestNode;
        open(crate) spec fn view(&self) -> TestNode {
            match self {
                TestView::True => TestNode::True, TestView::False => TestNode::False,
                TestView::Atom { primitive, positive } => TestNode::Atom(primitive@, *positive),
                TestView::And(ids) => TestNode::And(test_ids(ids@)), TestView::Or(ids) => TestNode::Or(test_ids(ids@)),
            }
        }
    }
    impl View for RegexKindView<'_> {
        type V = RegexKindNode;
        open(crate) spec fn view(&self) -> RegexKindNode {
            match self {
                RegexKindView::Empty => RegexKindNode::Empty, RegexKindView::All => RegexKindNode::All,
                RegexKindView::Epsilon => RegexKindNode::Epsilon, RegexKindView::Test(t) => RegexKindNode::Test(t@),
                RegexKindView::Union(ids) => RegexKindNode::Union(regex_ids(ids@)),
                RegexKindView::Concat(ids) => RegexKindNode::Concat(regex_ids(ids@)),
                RegexKindView::Star(r) => RegexKindNode::Star(r@),
                RegexKindView::Intersect(ids) => RegexKindNode::Intersect(regex_ids(ids@)),
                RegexKindView::Not(r) => RegexKindNode::Not(r@),
            }
        }
    }
    impl View for RegexView<'_> {
        type V = RegexNode;
        open(crate) spec fn view(&self) -> RegexNode { RegexNode { kind: self.kind@, nullable: self.nullable } }
    }
    impl View for TransitionView<'_> {
        type V = TransitionNode;
        open(crate) spec fn view(&self) -> TransitionNode {
            match self {
                TransitionView::Const(r) => TransitionNode::Const(r@),
                TransitionView::If { test, then_transition, else_transition } => TransitionNode::If(test@, then_transition@, else_transition@),
                TransitionView::Union(ids) => TransitionNode::Union(transition_ids(ids@)),
                TransitionView::Intersect(ids) => TransitionNode::Intersect(transition_ids(ids@)),
                TransitionView::Not(t) => TransitionNode::Not(t@),
                TransitionView::Append { transition, suffix } => TransitionNode::Append(transition@, regex_ids(suffix@)),
            }
        }
    }
    impl View for Constants {
        type V = ConstantsModel;
        open(crate) spec fn view(&self) -> ConstantsModel {
            ConstantsModel { test_true: self.test_true@, test_false: self.test_false@,
                empty: self.empty@, all: self.all@, epsilon: self.epsilon@,
                transition_empty: self.transition_empty@, transition_all: self.transition_all@,
                transition_epsilon: self.transition_epsilon@ }
        }
    }
    impl View for AtomSet {
        type V = Seq<TestId>;
        open(super) spec fn view(&self) -> Seq<TestId> { self.ids@ }
    }
    impl View for TestHead {
        type V = TestHeadNode;
        open(crate) spec fn view(&self) -> TestHeadNode {
            match self {
                TestHead::True => TestHeadNode::True, TestHead::False => TestHeadNode::False,
                TestHead::Atom(p, b) => TestHeadNode::Atom(p@, *b),
                TestHead::And(n) => TestHeadNode::And(*n as nat), TestHead::Or(n) => TestHeadNode::Or(*n as nat),
            }
        }
    }
    impl View for RegexHead {
        type V = RegexHeadNode;
        open(crate) spec fn view(&self) -> RegexHeadNode {
            match self {
                RegexHead::Empty => RegexHeadNode::Empty, RegexHead::All => RegexHeadNode::All,
                RegexHead::Epsilon => RegexHeadNode::Epsilon, RegexHead::Test(t) => RegexHeadNode::Test(t@),
                RegexHead::Union(n) => RegexHeadNode::Union(*n as nat), RegexHead::Concat(n) => RegexHeadNode::Concat(*n as nat),
                RegexHead::Star(r) => RegexHeadNode::Star(r@), RegexHead::Intersect(n) => RegexHeadNode::Intersect(*n as nat),
                RegexHead::Not(r) => RegexHeadNode::Not(r@),
            }
        }
    }
    impl View for TransitionHead {
        type V = TransitionHeadNode;
        open(crate) spec fn view(&self) -> TransitionHeadNode {
            match self {
                TransitionHead::Const(r) => TransitionHeadNode::Const(r@),
                TransitionHead::If(t, a, b) => TransitionHeadNode::If(t@, a@, b@),
                TransitionHead::Union(n) => TransitionHeadNode::Union(*n as nat),
                TransitionHead::Intersect(n) => TransitionHeadNode::Intersect(*n as nat),
                TransitionHead::Not(t) => TransitionHeadNode::Not(t@),
                TransitionHead::Append(t, n) => TransitionHeadNode::Append(t@, *n as nat),
            }
        }
    }

    pub open spec fn test_node_head(node: TestNode) -> TestHeadNode {
        match node {
            TestNode::True => TestHeadNode::True, TestNode::False => TestHeadNode::False,
            TestNode::Atom(p, b) => TestHeadNode::Atom(p, b), TestNode::And(cs) => TestHeadNode::And(cs.len()), TestNode::Or(cs) => TestHeadNode::Or(cs.len()),
        }
    }
    pub open spec fn regex_node_head(node: RegexKindNode) -> RegexHeadNode {
        match node {
            RegexKindNode::Empty => RegexHeadNode::Empty, RegexKindNode::All => RegexHeadNode::All,
            RegexKindNode::Epsilon => RegexHeadNode::Epsilon, RegexKindNode::Test(t) => RegexHeadNode::Test(t),
            RegexKindNode::Union(cs) => RegexHeadNode::Union(cs.len()), RegexKindNode::Concat(cs) => RegexHeadNode::Concat(cs.len()),
            RegexKindNode::Star(r) => RegexHeadNode::Star(r), RegexKindNode::Intersect(cs) => RegexHeadNode::Intersect(cs.len()),
            RegexKindNode::Not(r) => RegexHeadNode::Not(r),
        }
    }
    pub open spec fn transition_node_head(node: TransitionNode) -> TransitionHeadNode {
        match node {
            TransitionNode::Const(r) => TransitionHeadNode::Const(r), TransitionNode::If(t, a, b) => TransitionHeadNode::If(t, a, b),
            TransitionNode::Union(cs) => TransitionHeadNode::Union(cs.len()), TransitionNode::Intersect(cs) => TransitionHeadNode::Intersect(cs.len()),
            TransitionNode::Not(t) => TransitionHeadNode::Not(t), TransitionNode::Append(t, rs) => TransitionHeadNode::Append(t, rs.len()),
        }
    }
    pub open spec fn test_node_child(node: TestNode, i: nat) -> Option<nat> {
        match node { TestNode::And(cs) | TestNode::Or(cs) => if i < cs.len() { Some(cs[i as int]) } else { None }, _ => None }
    }
    pub open spec fn regex_node_child(node: RegexKindNode, i: nat) -> Option<nat> {
        match node { RegexKindNode::Union(cs) | RegexKindNode::Concat(cs) | RegexKindNode::Intersect(cs) => if i < cs.len() { Some(cs[i as int]) } else { None }, _ => None }
    }
    pub open spec fn transition_node_child(node: TransitionNode, i: nat) -> Option<nat> {
        match node { TransitionNode::Union(cs) | TransitionNode::Intersect(cs) => if i < cs.len() { Some(cs[i as int]) } else { None }, _ => None }
    }
    pub open spec fn transition_node_suffix(node: TransitionNode, i: nat) -> Option<nat> {
        match node { TransitionNode::Append(_, cs) => if i < cs.len() { Some(cs[i as int]) } else { None }, _ => None }
    }

    pub open spec fn bounded(cs: Seq<nat>, bound: nat) -> bool {
        forall|i: int| 0 <= i < cs.len() ==> #[trigger] cs[i] < bound
    }
    pub open spec fn strictly_increasing(cs: Seq<nat>) -> bool {
        forall|i: int, j: int| 0 <= i < j < cs.len() ==> #[trigger] cs[i] < #[trigger] cs[j]
    }
    pub open spec fn nondecreasing(cs: Seq<nat>) -> bool {
        forall|i: int, j: int| 0 <= i < j < cs.len() ==> #[trigger] cs[i] <= #[trigger] cs[j]
    }
    pub open spec fn test_node_wf_at(g: Graph, node: TestNode, bound: nat) -> bool {
        match node {
            TestNode::And(cs) | TestNode::Or(cs) => bounded(cs, bound) && strictly_increasing(cs),
            _ => true,
        }
    }
    pub open spec fn test_node_wf(g: Graph, node: TestNode) -> bool { test_node_wf_at(g, node, g.tests.len()) }
    pub open spec fn regex_kind_wf_at(g: Graph, node: RegexKindNode, bound: nat) -> bool {
        match node {
            RegexKindNode::Test(t) => t < g.tests.len(),
            RegexKindNode::Union(cs) | RegexKindNode::Intersect(cs) => bounded(cs, bound) && strictly_increasing(cs),
            RegexKindNode::Concat(cs) => bounded(cs, bound),
            RegexKindNode::Star(r) | RegexKindNode::Not(r) => r < bound,
            _ => true,
        }
    }
    pub open spec fn transition_node_wf_at(g: Graph, node: TransitionNode, bound: nat) -> bool {
        match node {
            TransitionNode::Const(r) => r < g.regexes.len(),
            TransitionNode::If(t, a, b) => t < g.tests.len() && a < bound && b < bound,
            TransitionNode::Union(cs) | TransitionNode::Intersect(cs) => bounded(cs, bound) && strictly_increasing(cs),
            TransitionNode::Not(t) => t < bound,
            TransitionNode::Append(t, rs) => t < bound && bounded(rs, g.regexes.len()),
        }
    }
    pub open spec fn transition_node_wf(g: Graph, node: TransitionNode) -> bool { transition_node_wf_at(g, node, g.transitions.len()) }

    pub open spec fn lift_test(g: Graph, i: nat) -> Test
        decreases i, 1nat,
    {
        if i >= g.tests.len() { Test::False } else {
            match g.tests[i as int] {
                TestNode::True => Test::True, TestNode::False => Test::False, TestNode::Atom(p, b) => Test::Atom(p, b),
                TestNode::And(cs) => Test::And(lift_tests(g, cs, i)), TestNode::Or(cs) => Test::Or(lift_tests(g, cs, i)),
            }
        }
    }
    pub open spec fn lift_tests(g: Graph, cs: Seq<nat>, bound: nat) -> Seq<Test>
        decreases bound, 0nat,
    {
        Seq::new(cs.len(), |j: int| if 0 <= j < cs.len() && cs[j] < bound { lift_test(g, cs[j]) } else { Test::False })
    }
    pub open spec fn lift_regex(g: Graph, i: nat) -> Regex<Test>
        decreases i, 2nat,
    {
        if i >= g.regexes.len() { Regex::Empty } else { lift_regex_kind_bounded(g, g.regexes[i as int].kind, i) }
    }
    pub open spec fn lift_regex_kind_bounded(g: Graph, node: RegexKindNode, bound: nat) -> Regex<Test>
        decreases bound, 1nat,
    {
        match node {
            RegexKindNode::Empty => Regex::Empty, RegexKindNode::All => Regex::All, RegexKindNode::Epsilon => Regex::Epsilon,
            RegexKindNode::Test(t) => Regex::Test(lift_test(g, t)),
            RegexKindNode::Union(cs) => Regex::Union(lift_regexes_bounded(g, cs, bound)),
            RegexKindNode::Concat(cs) => Regex::Concat(lift_regexes_bounded(g, cs, bound)),
            RegexKindNode::Intersect(cs) => Regex::Intersect(lift_regexes_bounded(g, cs, bound)),
            RegexKindNode::Star(r) => Regex::Star(Box::new(if r < bound { lift_regex(g, r) } else { Regex::Empty })),
            RegexKindNode::Not(r) => Regex::Not(Box::new(if r < bound { lift_regex(g, r) } else { Regex::Empty })),
        }
    }
    pub open spec fn lift_regexes_bounded(g: Graph, cs: Seq<nat>, bound: nat) -> Seq<Regex<Test>>
        decreases bound, 0nat,
    {
        Seq::new(cs.len(), |j: int| if 0 <= j < cs.len() && cs[j] < bound { lift_regex(g, cs[j]) } else { Regex::Empty })
    }
    pub open spec fn lift_regex_kind(g: Graph, node: RegexKindNode) -> Regex<Test> { lift_regex_kind_bounded(g, node, g.regexes.len()) }
    pub open spec fn lift_regexes(g: Graph, cs: Seq<nat>) -> Seq<Regex<Test>> {
        Seq::new(cs.len(), |j: int| lift_regex(g, cs[j]))
    }
    pub open spec fn lift_transition(g: Graph, i: nat) -> Transition<Test>
        decreases i, 1nat,
    {
        if i >= g.transitions.len() { Transition::Const(Regex::Empty) } else {
            match g.transitions[i as int] {
                TransitionNode::Const(r) => Transition::Const(lift_regex(g, r)),
                TransitionNode::If(t, a, b) => Transition::If(lift_test(g, t),
                    Box::new(if a < i { lift_transition(g, a) } else { Transition::Const(Regex::Empty) }),
                    Box::new(if b < i { lift_transition(g, b) } else { Transition::Const(Regex::Empty) })),
                TransitionNode::Union(cs) => Transition::Union(lift_transitions(g, cs, i)),
                TransitionNode::Intersect(cs) => Transition::Intersect(lift_transitions(g, cs, i)),
                TransitionNode::Not(t) => Transition::Not(Box::new(if t < i { lift_transition(g, t) } else { Transition::Const(Regex::Empty) })),
                TransitionNode::Append(t, rs) => Transition::Append(
                    Box::new(if t < i { lift_transition(g, t) } else { Transition::Const(Regex::Empty) }), lift_regexes(g, rs)),
            }
        }
    }
    pub open spec fn lift_transitions(g: Graph, cs: Seq<nat>, bound: nat) -> Seq<Transition<Test>>
        decreases bound, 0nat,
    {
        Seq::new(cs.len(), |j: int| if 0 <= j < cs.len() && cs[j] < bound { lift_transition(g, cs[j]) } else { Transition::Const(Regex::Empty) })
    }

    pub open spec fn regex_node_wf_at(g: Graph, node: RegexNode, bound: nat) -> bool {
        regex_kind_wf_at(g, node.kind, bound)
            && node.nullable == language::nullable(lift_regex_kind_bounded(g, node.kind, bound))
    }
    pub open spec fn regex_node_wf(g: Graph, node: RegexNode) -> bool { regex_node_wf_at(g, node, g.regexes.len()) }
    pub open spec fn tables_wf(g: Graph) -> bool {
        (forall|i: int| 0 <= i < g.tests.len() ==> test_node_wf_at(g, #[trigger] g.tests[i], i as nat))
        && (forall|i: int| 0 <= i < g.regexes.len() ==> regex_node_wf_at(g, #[trigger] g.regexes[i], i as nat))
        && (forall|i: int| 0 <= i < g.transitions.len() ==> transition_node_wf_at(g, #[trigger] g.transitions[i], i as nat))
    }
    pub open spec fn constants_wf(g: Graph) -> bool {
        let c = g.constants;
        c.test_true < g.tests.len() && g.tests[c.test_true as int] == TestNode::True
        && c.test_false < g.tests.len() && g.tests[c.test_false as int] == TestNode::False
        && c.empty < g.regexes.len() && g.regexes[c.empty as int] == (RegexNode { kind: RegexKindNode::Empty, nullable: false })
        && c.all < g.regexes.len() && g.regexes[c.all as int] == (RegexNode { kind: RegexKindNode::All, nullable: true })
        && c.epsilon < g.regexes.len() && g.regexes[c.epsilon as int] == (RegexNode { kind: RegexKindNode::Epsilon, nullable: true })
        && c.transition_empty < g.transitions.len() && g.transitions[c.transition_empty as int] == TransitionNode::Const(c.empty)
        && c.transition_all < g.transitions.len() && g.transitions[c.transition_all as int] == TransitionNode::Const(c.all)
        && c.transition_epsilon < g.transitions.len() && g.transitions[c.transition_epsilon as int] == TransitionNode::Const(c.epsilon)
    }
    pub open spec fn unique_nodes(g: Graph) -> bool {
        g.tests.no_duplicates() && g.regexes.no_duplicates() && g.transitions.no_duplicates()
    }
    #[verifier::opaque]
    pub open spec fn graph_wf(g: Graph) -> bool { tables_wf(g) && constants_wf(g) && unique_nodes(g) }

    pub proof fn lemma_graph_wf_elim(g: Graph)
        requires graph_wf(g),
        ensures tables_wf(g), constants_wf(g), unique_nodes(g),
    { reveal(graph_wf); }

    pub proof fn lemma_graph_wf_intro(g: Graph)
        requires tables_wf(g), constants_wf(g), unique_nodes(g),
        ensures graph_wf(g),
    { reveal(graph_wf); }

    pub proof fn lemma_graph_test_wf(g: Graph, id: nat)
        requires graph_wf(g), id < g.tests.len(),
        ensures test_node_wf_at(g, g.tests[id as int], id),
    { reveal(graph_wf); }

    pub proof fn lemma_graph_regex_wf(g: Graph, id: nat)
        requires graph_wf(g), id < g.regexes.len(),
        ensures regex_node_wf_at(g, g.regexes[id as int], id),
            g.regexes[id as int].nullable == language::nullable(lift_regex(g, id)),
    { reveal(graph_wf); }

    pub proof fn lemma_graph_transition_wf(g: Graph, id: nat)
        requires graph_wf(g), id < g.transitions.len(),
        ensures transition_node_wf_at(g, g.transitions[id as int], id),
    { reveal(graph_wf); }

    pub open spec fn tables_extend(old: Graph, new: Graph) -> bool {
        old.tests.is_prefix_of(new.tests) && old.regexes.is_prefix_of(new.regexes) && old.transitions.is_prefix_of(new.transitions)
    }
    pub open spec fn graph_extends(old: Graph, new: Graph) -> bool { tables_extend(old, new) && old.constants == new.constants }
    pub open spec fn symbols_wf(s: Symbols) -> bool {
        s.constants.no_duplicates() && s.paths.no_duplicates() && s.variables.no_duplicates()
        && forall|i: int| 0 <= i < s.variables.len() ==> #[trigger] s.variables[i].len() > 0
    }
    pub open spec fn primitive_holds(s: Symbols, theta: Seq<Data>, p: Primitive, e: Data) -> bool {
        match p {
            Primitive::HasValue(path) => path < s.paths.len() && language::select(e, s.paths[path as int]) is Some,
            Primitive::EqCore(path, term) => path < s.paths.len() && match term {
                GTerm::Constant(c) => c < s.constants.len() && language::select(e, s.paths[path as int]) == Some(s.constants[c as int]),
                GTerm::Variable(v) => v < theta.len() && language::select(e, s.paths[path as int]) == Some(theta[v as int]),
            },
        }
    }
    pub open spec fn test_holds(s: Symbols, theta: Seq<Data>, t: Test, e: Data) -> bool
        decreases t,
    {
        match t {
            Test::True => true, Test::False => false, Test::Atom(p, positive) => primitive_holds(s, theta, p, e) == positive,
            Test::And(cs) => forall|i: int| 0 <= i < cs.len() ==> test_holds(s, theta, cs[i], e),
            Test::Or(cs) => exists|i: int| 0 <= i < cs.len() && test_holds(s, theta, cs[i], e),
        }
    }
    pub open spec fn gsem(s: Symbols, theta: Seq<Data>) -> spec_fn(Test, Data) -> bool { |t: Test, e: Data| test_holds(s, theta, t, e) }
    pub open spec fn regex_lang(g: Graph, s: Symbols, theta: Seq<Data>, i: nat, word: Seq<Data>) -> bool {
        language::lang(gsem(s, theta), lift_regex(g, i), word)
    }
    pub open spec fn atom_ids_wf(g: Graph, ids: Seq<TestId>) -> bool {
        strictly_increasing(test_ids(ids))
        && forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.tests.len()
            && #[trigger] g.tests[ids[i]@ as int] matches TestNode::Atom(_, true)
    }

    pub open spec fn atom_prefix_wf(g: Graph, ids: Seq<TestId>, n: nat) -> bool {
        n <= ids.len()
        && (forall|i: int| 0 <= i < n ==> ids[i]@ < g.tests.len()
            && #[trigger] g.tests[ids[i]@ as int] matches TestNode::Atom(_, true))
        && (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] ids[i]@ < #[trigger] ids[j]@)
    }

    pub proof fn lemma_constant_atoms_disjoint(s: Symbols, theta: Seq<Data>, path: nat, a: nat, b: nat, event: Data)
        requires symbols_wf(s), a != b,
        ensures !(primitive_holds(s, theta, Primitive::EqCore(path, GTerm::Constant(a)), event)
            && primitive_holds(s, theta, Primitive::EqCore(path, GTerm::Constant(b)), event)),
    {}

    pub proof fn lemma_lift_test_stable(a: Graph, b: Graph, i: nat)
        requires tables_extend(a, b), i < a.tests.len(),
        ensures lift_test(a, i) == lift_test(b, i),
        decreases i,
    {
        assert(a.tests[i as int] == b.tests[i as int]);
        match a.tests[i as int] {
            TestNode::And(cs) | TestNode::Or(cs) => {
                assert forall|j: int| 0 <= j < cs.len()
                    implies lift_tests(a, cs, i)[j] == lift_tests(b, cs, i)[j] by {
                    if cs[j] < i { lemma_lift_test_stable(a, b, cs[j]); }
                }
                assert(lift_tests(a, cs, i) =~= lift_tests(b, cs, i));
            },
            _ => {},
        }
    }

    pub proof fn lemma_lift_regex_stable(a: Graph, b: Graph, i: nat)
        requires tables_wf(a), tables_extend(a, b), i < a.regexes.len(),
        ensures lift_regex(a, i) == lift_regex(b, i),
        decreases i, 2nat,
    {
        assert(a.regexes[i as int] == b.regexes[i as int]);
        lemma_lift_regex_kind_stable(a, b, a.regexes[i as int].kind, i);
    }

    pub proof fn lemma_lift_regex_kind_stable(a: Graph, b: Graph, node: RegexKindNode, bound: nat)
        requires tables_wf(a), tables_extend(a, b), bound <= a.regexes.len(), regex_kind_wf_at(a, node, bound),
        ensures lift_regex_kind_bounded(a, node, bound) == lift_regex_kind_bounded(b, node, bound),
        decreases bound, 1nat,
    {
        match node {
            RegexKindNode::Test(t) => { lemma_lift_test_stable(a, b, t); },
            RegexKindNode::Star(r) | RegexKindNode::Not(r) => { lemma_lift_regex_stable(a, b, r); },
            RegexKindNode::Union(cs) | RegexKindNode::Concat(cs) | RegexKindNode::Intersect(cs) => {
                assert forall|j: int| 0 <= j < cs.len()
                    implies lift_regexes_bounded(a, cs, bound)[j] == lift_regexes_bounded(b, cs, bound)[j] by {
                    lemma_lift_regex_stable(a, b, cs[j]);
                }
                assert(lift_regexes_bounded(a, cs, bound) =~= lift_regexes_bounded(b, cs, bound));
            },
            _ => {},
        }
    }

    pub proof fn lemma_lift_transition_stable(a: Graph, b: Graph, i: nat)
        requires tables_wf(a), tables_extend(a, b), i < a.transitions.len(),
        ensures lift_transition(a, i) == lift_transition(b, i),
        decreases i,
    {
        assert(a.transitions[i as int] == b.transitions[i as int]);
        match a.transitions[i as int] {
            TransitionNode::Const(r) => { lemma_lift_regex_stable(a, b, r); },
            TransitionNode::If(t, x, y) => {
                lemma_lift_test_stable(a, b, t);
                lemma_lift_transition_stable(a, b, x);
                lemma_lift_transition_stable(a, b, y);
            },
            TransitionNode::Not(t) => { lemma_lift_transition_stable(a, b, t); },
            TransitionNode::Union(cs) | TransitionNode::Intersect(cs) => {
                assert forall|j: int| 0 <= j < cs.len()
                    implies lift_transitions(a, cs, i)[j] == lift_transitions(b, cs, i)[j] by {
                    lemma_lift_transition_stable(a, b, cs[j]);
                }
                assert(lift_transitions(a, cs, i) =~= lift_transitions(b, cs, i));
            },
            TransitionNode::Append(t, rs) => {
                lemma_lift_transition_stable(a, b, t);
                assert forall|j: int| 0 <= j < rs.len()
                    implies lift_regexes(a, rs)[j] == lift_regexes(b, rs)[j] by {
                    lemma_lift_regex_stable(a, b, rs[j]);
                }
                assert(lift_regexes(a, rs) =~= lift_regexes(b, rs));
            },
        }
    }

    pub proof fn lemma_lift_stable_under_extends(a: Graph, b: Graph)
        requires tables_wf(a), tables_extend(a, b),
        ensures
            forall|i: nat| i < a.tests.len() ==> lift_test(a, i) == lift_test(b, i),
            forall|i: nat| i < a.regexes.len() ==> lift_regex(a, i) == lift_regex(b, i),
            forall|i: nat| i < a.transitions.len() ==> lift_transition(a, i) == lift_transition(b, i),
    {
        assert forall|i: nat| i < a.tests.len() implies lift_test(a, i) == lift_test(b, i) by { lemma_lift_test_stable(a, b, i); }
        assert forall|i: nat| i < a.regexes.len() implies lift_regex(a, i) == lift_regex(b, i) by { lemma_lift_regex_stable(a, b, i); }
        assert forall|i: nat| i < a.transitions.len() implies lift_transition(a, i) == lift_transition(b, i) by { lemma_lift_transition_stable(a, b, i); }
    }

    pub proof fn lemma_old_nodes_wf_under_extends(a: Graph, b: Graph)
        requires tables_wf(a), tables_extend(a, b),
        ensures
            forall|i: int| 0 <= i < a.tests.len() ==> test_node_wf_at(b, #[trigger] a.tests[i], i as nat),
            forall|i: int| 0 <= i < a.regexes.len() ==> regex_node_wf_at(b, #[trigger] a.regexes[i], i as nat),
            forall|i: int| 0 <= i < a.transitions.len() ==> transition_node_wf_at(b, #[trigger] a.transitions[i], i as nat),
    {
        assert forall|i: int| 0 <= i < a.regexes.len()
            implies regex_node_wf_at(b, #[trigger] a.regexes[i], i as nat) by {
            lemma_lift_regex_kind_stable(a, b, a.regexes[i].kind, i as nat);
        }
        assert forall|i: int| 0 <= i < a.transitions.len()
            implies transition_node_wf_at(b, #[trigger] a.transitions[i], i as nat) by {
            match a.transitions[i] {
                TransitionNode::Append(_, rs) => {
                    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] < b.regexes.len() by {}
                },
                _ => {},
            }
        }
    }

    pub open spec fn append_test(g: Graph, node: TestNode) -> Graph { Graph { tests: g.tests.push(node), ..g } }
    pub open spec fn append_regex(g: Graph, node: RegexNode) -> Graph { Graph { regexes: g.regexes.push(node), ..g } }
    pub open spec fn append_transition(g: Graph, node: TransitionNode) -> Graph { Graph { transitions: g.transitions.push(node), ..g } }

    pub proof fn lemma_constants_stable(a: Graph, b: Graph)
        requires constants_wf(a), graph_extends(a, b),
        ensures constants_wf(b),
    {}

    pub proof fn lemma_tables_wf_append_test(g: Graph, node: TestNode)
        requires tables_wf(g), test_node_wf(g, node),
        ensures tables_wf(append_test(g, node)), graph_extends(g, append_test(g, node)),
            graph_wf(g) && !g.tests.contains(node) ==> graph_wf(append_test(g, node)),
    {
        reveal(graph_wf);
        let next = append_test(g, node);
        lemma_old_nodes_wf_under_extends(g, next);
        assert forall|i: int| 0 <= i < next.tests.len()
            implies test_node_wf_at(next, #[trigger] next.tests[i], i as nat) by {
            if i == g.tests.len() {} else { assert(next.tests[i] == g.tests[i]); }
        }
        if constants_wf(g) { lemma_constants_stable(g, next); }
    }

    pub proof fn lemma_tables_wf_append_regex(g: Graph, node: RegexNode)
        requires tables_wf(g), regex_node_wf(g, node),
        ensures tables_wf(append_regex(g, node)), graph_extends(g, append_regex(g, node)),
            graph_wf(g) && !g.regexes.contains(node) ==> graph_wf(append_regex(g, node)),
    {
        reveal(graph_wf);
        let next = append_regex(g, node);
        lemma_old_nodes_wf_under_extends(g, next);
        lemma_lift_regex_kind_stable(g, next, node.kind, g.regexes.len());
        assert forall|i: int| 0 <= i < next.regexes.len()
            implies regex_node_wf_at(next, #[trigger] next.regexes[i], i as nat) by {
            if i == g.regexes.len() {} else { assert(next.regexes[i] == g.regexes[i]); }
        }
        if constants_wf(g) { lemma_constants_stable(g, next); }
    }

    pub proof fn lemma_tables_wf_append_transition(g: Graph, node: TransitionNode)
        requires tables_wf(g), transition_node_wf(g, node),
        ensures tables_wf(append_transition(g, node)), graph_extends(g, append_transition(g, node)),
            graph_wf(g) && !g.transitions.contains(node) ==> graph_wf(append_transition(g, node)),
    {
        reveal(graph_wf);
        let next = append_transition(g, node);
        lemma_old_nodes_wf_under_extends(g, next);
        assert forall|i: int| 0 <= i < next.transitions.len()
            implies transition_node_wf_at(next, #[trigger] next.transitions[i], i as nat) by {
            if i == g.transitions.len() {} else { assert(next.transitions[i] == g.transitions[i]); }
        }
        if constants_wf(g) { lemma_constants_stable(g, next); }
    }

    }
}

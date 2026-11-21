//! `event_laws` (`history_syntax::spec::events`) for the built-in event types: tuples and Frunk coproducts (`sec:events`).

use crate::event::specs::EventSpec;
use crate::event::{Component2, Component3, Component4, Event};
use crate::key_hash::KeyHash;
use crate::spec::events::{arity, event_laws, event_view, well_tagged};
use core::fmt::Debug;
use core::hash::Hash;
use frunk_core::coproduct::{CNil, Coproduct};
use vstd::prelude::*;

verus! {

/// A pair projects each coordinate with its own tag and every well-tagged pair is a view.
pub proof fn lemma_event_laws_pair<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash>()
    ensures event_laws::<(A, B)>(),
{
    assert forall|xs: Seq<Component2<A, B>>| #[trigger] well_tagged::<(A, B)>(xs)
        implies exists|e: (A, B)| event_view(e) == xs by {
        let a = match xs[0] { Component2::C0(a) => a, _ => arbitrary() };
        let b = match xs[1] { Component2::C1(b) => b, _ => arbitrary() };
        let e = (a, b);
        assert(event_view(e) =~= xs);
    }
}

/// A triple projects each coordinate with its own tag and every well-tagged triple is a view.
pub proof fn lemma_event_laws_triple<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash,
    C: Copy + Debug + Eq + Hash + KeyHash>()
    ensures event_laws::<(A, B, C)>(),
{
    assert forall|xs: Seq<Component3<A, B, C>>| #[trigger] well_tagged::<(A, B, C)>(xs)
        implies exists|e: (A, B, C)| event_view(e) == xs by {
        let a = match xs[0] { Component3::C0(a) => a, _ => arbitrary() };
        let b = match xs[1] { Component3::C1(b) => b, _ => arbitrary() };
        let c = match xs[2] { Component3::C2(c) => c, _ => arbitrary() };
        let e = (a, b, c);
        assert(event_view(e) =~= xs);
    }
}

/// A quadruple projects each coordinate with its own tag and every well-tagged quadruple is a view.
pub proof fn lemma_event_laws_quad<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash,
    C: Copy + Debug + Eq + Hash + KeyHash, D: Copy + Debug + Eq + Hash + KeyHash>()
    ensures event_laws::<(A, B, C, D)>(),
{
    assert forall|xs: Seq<Component4<A, B, C, D>>| #[trigger] well_tagged::<(A, B, C, D)>(xs)
        implies exists|e: (A, B, C, D)| event_view(e) == xs by {
        let a = match xs[0] { Component4::C0(a) => a, _ => arbitrary() };
        let b = match xs[1] { Component4::C1(b) => b, _ => arbitrary() };
        let c = match xs[2] { Component4::C2(c) => c, _ => arbitrary() };
        let d = match xs[3] { Component4::C3(d) => d, _ => arbitrary() };
        let e = (a, b, c, d);
        assert(event_view(e) =~= xs);
    }
}

/// The final coproduct variant inherits `H`'s laws (its `CNil` arm has no values).
pub proof fn lemma_event_laws_coproduct_nil<H: Event>()
    requires event_laws::<H>(),
    ensures event_laws::<Coproduct<H, CNil>>(),
{
    assert forall|xs: Seq<H::Component>| #[trigger] well_tagged::<Coproduct<H, CNil>>(xs)
        implies exists|e: Coproduct<H, CNil>| event_view(e) == xs by {
        assert(well_tagged::<H>(xs));
        let h = choose|h: H| event_view(h) == xs;
        assert(event_view(Coproduct::<H, CNil>::Inl(h)) =~= xs);
    }
}

/// A head variant inherits the laws of its head and of the rest of the union, provided the rest
/// tags components the way the head does (the union projects with the head's `coordinate`).
pub proof fn lemma_event_laws_coproduct_cons<H, T, Rest>()
    where
        H: Event,
        Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>,
    requires event_laws::<H>(), event_laws::<Coproduct<T, Rest>>(),
        forall|c: H::Component| #[trigger] <Coproduct<T, Rest> as EventSpec>::coordinate_spec(c)
            == H::coordinate_spec(c),
    ensures event_laws::<Coproduct<H, Coproduct<T, Rest>>>(),
{
    assert forall|e: Coproduct<H, Coproduct<T, Rest>>, i: int| 0 <= i < arity::<H>()
        implies H::coordinate_spec(#[trigger] e.component_spec(i)) == i by {
        match e {
            Coproduct::Inl(head) => assert(e.component_spec(i) == head.component_spec(i)),
            Coproduct::Inr(tail) => assert(e.component_spec(i) == tail.component_spec(i)),
        }
    }
    assert forall|xs: Seq<H::Component>| #[trigger] well_tagged::<Coproduct<H, Coproduct<T, Rest>>>(xs)
        implies exists|e: Coproduct<H, Coproduct<T, Rest>>| event_view(e) == xs by {
        assert(well_tagged::<H>(xs));
        let h = choose|h: H| event_view(h) == xs;
        assert(event_view(Coproduct::<H, Coproduct<T, Rest>>::Inl(h)) =~= xs);
    }
}

} // verus!

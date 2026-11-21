//! Compact, statically dispatched events with policy-selected coordinates.

use core::fmt::Debug;
use core::hash::Hash;
use frunk_core::coproduct::{CNil, Coproduct};

use crate::key_hash::{KeyHash, mix};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use self::specs::{AritySpec, EventSpec};

verus! {
/// Largest arity any event type may declare; sizes inline numeric tuples.
pub const MAX_ARITY: usize = 8;
}

mod sealed {
    #[vstd::prelude::verus_verify]
    pub trait Sealed {}
}

/// Type-level event arity. Only [`N1`] through [`N8`] implement this trait.
pub trait Arity: sealed::Sealed {
    /// Number of coordinates, between one and [`MAX_ARITY`] inclusive.
    fn value() -> usize;
}

macro_rules! arities {
    ($($name:ident = $value:literal),+ $(,)?) => {$ (
        #[doc = concat!("An event with ", stringify!($value), " coordinates.")]
        #[verus_verify]
        pub struct $name;

        #[verus_verify]
        impl sealed::Sealed for $name {}

        #[verus_verify]
        impl Arity for $name {
            fn value() -> usize { $value }
        }

        #[cfg(verus_keep_ghost)]
        verus! {
            impl specs::AritySpecImpl for $name {
                open spec fn value_spec() -> nat { $value }
            }
        }
    )+};
}

arities!(
    N1 = 1,
    N2 = 2,
    N3 = 3,
    N4 = 4,
    N5 = 5,
    N6 = 6,
    N7 = 7,
    N8 = 8
);

/// Event matched by heads and tail atoms.
///
/// Equality and hashing describe the full event, including its variant and payload.
/// Projections, equality and hashing must remain stable while values are used by a policy.
pub trait Event: Copy + Debug + Eq + Hash {
    /// Tagged value of one coordinate, with one variant per coordinate.
    type Component: Copy + Debug + Eq + Hash + KeyHash;
    /// Number of coordinates in this event.
    type Arity: Arity;

    /// Projects coordinate `index`; out-of-range indices map to the last coordinate.
    fn component(self, index: usize) -> Self::Component;
    /// Returns the coordinate of a tagged value.
    ///
    /// For every valid `i`, `Self::coordinate(event.component(i)) == i`.
    fn coordinate(component: Self::Component) -> usize;
}

/// Tagged coordinates of a two-component tuple event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component2<A, B> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
}

/// Tagged coordinates of a three-component tuple event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component3<A, B, C> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
    /// Coordinate two.
    C2(C),
}

/// Tagged coordinates of a four-component tuple event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component4<A, B, C, D> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
    /// Coordinate two.
    C2(C),
    /// Coordinate three.
    C3(D),
}

#[verus_verify]
impl<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash> Event for (A, B)
where
    (A, B): Copy,
{
    type Component = Component2<A, B>;
    type Arity = N2;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component2::C0(self.0),
            _ => Component2::C1(self.1),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component2::C0(_) => 0,
            Component2::C1(_) => 1,
        }
    }
}

#[verus_verify]
impl<
    A: Copy + Debug + Eq + Hash + KeyHash,
    B: Copy + Debug + Eq + Hash + KeyHash,
    C: Copy + Debug + Eq + Hash + KeyHash,
> Event for (A, B, C)
where
    (A, B, C): Copy,
{
    type Component = Component3<A, B, C>;
    type Arity = N3;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component3::C0(self.0),
            1 => Component3::C1(self.1),
            _ => Component3::C2(self.2),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component3::C0(_) => 0,
            Component3::C1(_) => 1,
            Component3::C2(_) => 2,
        }
    }
}

#[verus_verify]
impl<
    A: Copy + Debug + Eq + Hash + KeyHash,
    B: Copy + Debug + Eq + Hash + KeyHash,
    C: Copy + Debug + Eq + Hash + KeyHash,
    D: Copy + Debug + Eq + Hash + KeyHash,
> Event for (A, B, C, D)
where
    (A, B, C, D): Copy,
{
    type Component = Component4<A, B, C, D>;
    type Arity = N4;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component4::C0(self.0),
            1 => Component4::C1(self.1),
            2 => Component4::C2(self.2),
            _ => Component4::C3(self.3),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component4::C0(_) => 0,
            Component4::C1(_) => 1,
            Component4::C2(_) => 2,
            Component4::C3(_) => 3,
        }
    }
}

#[verus_verify]
impl<A: KeyHash, B: KeyHash> KeyHash for Component2<A, B> {
    fn key_hash(&self) -> u64 {
        match self {
            Component2::C0(a) => mix(0, a.key_hash()),
            Component2::C1(b) => mix(1, b.key_hash()),
        }
    }
}

#[verus_verify]
impl<A: KeyHash, B: KeyHash, C: KeyHash> KeyHash for Component3<A, B, C> {
    fn key_hash(&self) -> u64 {
        match self {
            Component3::C0(a) => mix(0, a.key_hash()),
            Component3::C1(b) => mix(1, b.key_hash()),
            Component3::C2(c) => mix(2, c.key_hash()),
        }
    }
}

#[verus_verify]
impl<A: KeyHash, B: KeyHash, C: KeyHash, D: KeyHash> KeyHash for Component4<A, B, C, D> {
    fn key_hash(&self) -> u64 {
        match self {
            Component4::C0(a) => mix(0, a.key_hash()),
            Component4::C1(b) => mix(1, b.key_hash()),
            Component4::C2(c) => mix(2, c.key_hash()),
            Component4::C3(d) => mix(3, d.key_hash()),
        }
    }
}

// The pinned verifier rejects zero-arm matches; this leaf eliminates only Frunk's empty CNil.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures false)]
fn absurd_nil<T>(nil: CNil) -> T {
    match nil {}
}

/// Final variant of a Frunk event union.
#[verus_verify]
impl<H: Event> Event for Coproduct<H, CNil> {
    type Component = H::Component;
    type Arity = H::Arity;

    fn component(self, index: usize) -> Self::Component {
        match self {
            Coproduct::Inl(head) => head.component(index),
            Coproduct::Inr(nil) => absurd_nil(nil),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        H::coordinate(component)
    }
}

/// Head variant of a Frunk event union sharing tagged coordinates and arity.
#[verus_verify]
impl<H, T, Rest> Event for Coproduct<H, Coproduct<T, Rest>>
where
    H: Event,
    Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>,
{
    type Component = H::Component;
    type Arity = H::Arity;

    fn component(self, index: usize) -> Self::Component {
        match self {
            Coproduct::Inl(head) => head.component(index),
            Coproduct::Inr(tail) => tail.component(index),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        H::coordinate(component)
    }
}

/// Conditional native projection boundary; implementations need not opt in.
#[cfg(verus_keep_ghost)]
pub mod specs {
    use super::*;
    use crate::key_hash::specs::{KeyHashSpec, KeyHashSpecImpl, spec_mix};
    use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};
    verus! {

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(AritySpec via AritySpecImpl)]
    pub trait ExArity: sealed::Sealed {
        type ExternalTraitSpecificationFor: Arity;
        spec fn value_spec() -> nat;
        fn value() -> (result: usize)
            ensures 1 <= result <= MAX_ARITY, result == Self::value_spec();
    }

    // Transparent specifications expose exactly the Frunk enum variants to body proofs.
    #[verifier::external_type_specification]
    #[verifier::accept_recursive_types(H)]
    #[verifier::reject_recursive_types_in_ground_variants(T)]
    pub struct ExCoproduct<H, T>(Coproduct<H, T>);

    #[verifier::external_type_specification]
    // Like vstd's Infallible: the pinned verifier cannot represent a zero-variant datatype.
    #[verifier::external_body]
    pub struct ExCNil(CNil);

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(EventSpec via EventSpecImpl)]
    pub trait ExEvent: Copy + Debug + Eq + Hash {
        type ExternalTraitSpecificationFor: Event;
        type Component: Copy + Debug + Eq + Hash + KeyHash;
        type Arity: Arity;

        spec fn obeys_projection_spec() -> bool;
        spec fn component_spec(self, index: int) -> Self::Component;
        spec fn coordinate_spec(component: Self::Component) -> nat;

        fn component(self, index: usize) -> (result: Self::Component)
            ensures Self::obeys_projection_spec() ==> result == self.component_spec(index as int);
        fn coordinate(component: Self::Component) -> (result: usize)
            ensures Self::obeys_projection_spec() ==>
                result as nat == Self::coordinate_spec(component)
                && result < Self::Arity::value_spec();
    }

    impl<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash> EventSpecImpl for (A, B)
    where (A, B): Copy,
    {
        open spec fn obeys_projection_spec() -> bool { true }
        open spec fn component_spec(self, index: int) -> Self::Component {
            if index == 0 { Component2::C0(self.0) } else { Component2::C1(self.1) }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            match component { Component2::C0(_) => 0, Component2::C1(_) => 1 }
        }
    }

    impl<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash,
        C: Copy + Debug + Eq + Hash + KeyHash> EventSpecImpl for (A, B, C)
    where (A, B, C): Copy,
    {
        open spec fn obeys_projection_spec() -> bool { true }
        open spec fn component_spec(self, index: int) -> Self::Component {
            if index == 0 { Component3::C0(self.0) }
            else if index == 1 { Component3::C1(self.1) }
            else { Component3::C2(self.2) }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            match component { Component3::C0(_) => 0, Component3::C1(_) => 1, Component3::C2(_) => 2 }
        }
    }

    impl<A: Copy + Debug + Eq + Hash + KeyHash, B: Copy + Debug + Eq + Hash + KeyHash,
        C: Copy + Debug + Eq + Hash + KeyHash, D: Copy + Debug + Eq + Hash + KeyHash> EventSpecImpl for (A, B, C, D)
    where (A, B, C, D): Copy,
    {
        open spec fn obeys_projection_spec() -> bool { true }
        open spec fn component_spec(self, index: int) -> Self::Component {
            if index == 0 { Component4::C0(self.0) }
            else if index == 1 { Component4::C1(self.1) }
            else if index == 2 { Component4::C2(self.2) }
            else { Component4::C3(self.3) }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            match component {
                Component4::C0(_) => 0, Component4::C1(_) => 1,
                Component4::C2(_) => 2, Component4::C3(_) => 3,
            }
        }
    }

    /// `eq_spec` of a tagged component: same coordinate and payloads `eq_spec`-equal; the derived
    /// `PartialEq` compares the variant and then the payload, so it is faithful when the payloads' are.
    impl<A: PartialEq + PartialEqSpec, B: PartialEq + PartialEqSpec> PartialEqSpecImpl for Component2<A, B> {
        open spec fn obeys_eq_spec() -> bool { A::obeys_eq_spec() && B::obeys_eq_spec() }
        open spec fn eq_spec(&self, other: &Self) -> bool {
            match (self, other) {
                (Component2::C0(a), Component2::C0(b)) => a.eq_spec(b),
                (Component2::C1(a), Component2::C1(b)) => a.eq_spec(b),
                _ => false,
            }
        }
    }

    impl<A: PartialEq + PartialEqSpec, B: PartialEq + PartialEqSpec, C: PartialEq + PartialEqSpec>
        PartialEqSpecImpl for Component3<A, B, C>
    {
        open spec fn obeys_eq_spec() -> bool {
            A::obeys_eq_spec() && B::obeys_eq_spec() && C::obeys_eq_spec()
        }
        open spec fn eq_spec(&self, other: &Self) -> bool {
            match (self, other) {
                (Component3::C0(a), Component3::C0(b)) => a.eq_spec(b),
                (Component3::C1(a), Component3::C1(b)) => a.eq_spec(b),
                (Component3::C2(a), Component3::C2(b)) => a.eq_spec(b),
                _ => false,
            }
        }
    }

    impl<A: PartialEq + PartialEqSpec, B: PartialEq + PartialEqSpec,
        C: PartialEq + PartialEqSpec, D: PartialEq + PartialEqSpec> PartialEqSpecImpl for Component4<A, B, C, D>
    {
        open spec fn obeys_eq_spec() -> bool {
            A::obeys_eq_spec() && B::obeys_eq_spec() && C::obeys_eq_spec() && D::obeys_eq_spec()
        }
        open spec fn eq_spec(&self, other: &Self) -> bool {
            match (self, other) {
                (Component4::C0(a), Component4::C0(b)) => a.eq_spec(b),
                (Component4::C1(a), Component4::C1(b)) => a.eq_spec(b),
                (Component4::C2(a), Component4::C2(b)) => a.eq_spec(b),
                (Component4::C3(a), Component4::C3(b)) => a.eq_spec(b),
                _ => false,
            }
        }
    }

    /// `hash_spec` of a tagged component mixes the coordinate tag with the payload's `hash_spec`.
    impl<A: KeyHash, B: KeyHash> KeyHashSpecImpl for Component2<A, B> {
        open spec fn obeys_hash_spec() -> bool { A::obeys_hash_spec() && B::obeys_hash_spec() }
        open spec fn hash_spec(&self) -> u64 {
            match self {
                Component2::C0(a) => spec_mix(0, a.hash_spec()),
                Component2::C1(b) => spec_mix(1, b.hash_spec()),
            }
        }
    }

    impl<A: KeyHash, B: KeyHash, C: KeyHash> KeyHashSpecImpl for Component3<A, B, C> {
        open spec fn obeys_hash_spec() -> bool {
            A::obeys_hash_spec() && B::obeys_hash_spec() && C::obeys_hash_spec()
        }
        open spec fn hash_spec(&self) -> u64 {
            match self {
                Component3::C0(a) => spec_mix(0, a.hash_spec()),
                Component3::C1(b) => spec_mix(1, b.hash_spec()),
                Component3::C2(c) => spec_mix(2, c.hash_spec()),
            }
        }
    }

    impl<A: KeyHash, B: KeyHash, C: KeyHash, D: KeyHash> KeyHashSpecImpl for Component4<A, B, C, D> {
        open spec fn obeys_hash_spec() -> bool {
            A::obeys_hash_spec() && B::obeys_hash_spec() && C::obeys_hash_spec() && D::obeys_hash_spec()
        }
        open spec fn hash_spec(&self) -> u64 {
            match self {
                Component4::C0(a) => spec_mix(0, a.hash_spec()),
                Component4::C1(b) => spec_mix(1, b.hash_spec()),
                Component4::C2(c) => spec_mix(2, c.hash_spec()),
                Component4::C3(d) => spec_mix(3, d.hash_spec()),
            }
        }
    }

    impl<H: Event> EventSpecImpl for Coproduct<H, CNil> {
        open spec fn obeys_projection_spec() -> bool { H::obeys_projection_spec() }
        // CNil has no values; projecting through an arbitrary `H` keeps `H`'s projection laws.
        open spec fn component_spec(self, index: int) -> Self::Component {
            match self {
                Coproduct::Inl(head) => head.component_spec(index),
                Coproduct::Inr(_) => arbitrary::<H>().component_spec(index),
            }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            H::coordinate_spec(component)
        }
    }

    impl<H, T, Rest> EventSpecImpl for Coproduct<H, Coproduct<T, Rest>>
    where
        H: Event,
        Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>,
    {
        open spec fn obeys_projection_spec() -> bool {
            H::obeys_projection_spec() && <Coproduct<T, Rest> as EventSpec>::obeys_projection_spec()
        }
        open spec fn component_spec(self, index: int) -> Self::Component {
            match self {
                Coproduct::Inl(head) => head.component_spec(index),
                Coproduct::Inr(tail) => tail.component_spec(index),
            }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            H::coordinate_spec(component)
        }
    }
    }
}

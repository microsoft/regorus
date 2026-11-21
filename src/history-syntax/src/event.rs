//! Compact, statically dispatched events with policy-selected coordinates.

use core::fmt::Debug;
use core::hash::Hash;

use crate::key_hash::{KeyHash, mix};

/// Largest arity any event type may declare; sizes inline numeric tuples.
pub const MAX_ARITY: usize = 8;

mod sealed {
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
        pub struct $name;

        impl sealed::Sealed for $name {}

        impl Arity for $name {
            fn value() -> usize { $value }
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component2<A, B> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
}

/// Tagged coordinates of a three-component tuple event.
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

impl<A: KeyHash, B: KeyHash> KeyHash for Component2<A, B> {
    fn key_hash(&self) -> u64 {
        match self {
            Component2::C0(a) => mix(0, a.key_hash()),
            Component2::C1(b) => mix(1, b.key_hash()),
        }
    }
}

impl<A: KeyHash, B: KeyHash, C: KeyHash> KeyHash for Component3<A, B, C> {
    fn key_hash(&self) -> u64 {
        match self {
            Component3::C0(a) => mix(0, a.key_hash()),
            Component3::C1(b) => mix(1, b.key_hash()),
            Component3::C2(c) => mix(2, c.key_hash()),
        }
    }
}

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

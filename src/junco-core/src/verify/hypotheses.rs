//! Concrete witnesses for `event_obligations` (`junco_core::spec::hypotheses`): the built-in key
//! and event types satisfy every conjunct; nothing here is trusted.

use crate::spec::hypotheses::{eq_equivalence, event_obligations, hash_respects_eq, key_laws};
use core::fmt::Debug;
use core::hash::Hash;
use history_syntax::KeyHash;
use history_syntax::event::{Component2, Component3, Component4};
use history_syntax::key_hash::specs::KeyHashSpec;
use history_syntax::verify::events::{
    lemma_event_laws_pair, lemma_event_laws_quad, lemma_event_laws_triple,
};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

/// Primitive keys: vstd's `eq_spec` is `==` and `hash_spec` is a function of the value.
macro_rules! primitive_key_laws {
    ($($lemma:ident: $t:ty),+ $(,)?) => {$(
        verus! {
            pub proof fn $lemma()
                ensures key_laws::<$t>(),
            {
            }
        }
    )+};
}

primitive_key_laws!(
    lemma_key_laws_bool: bool,
    lemma_key_laws_u8: u8,
    lemma_key_laws_u16: u16,
    lemma_key_laws_u32: u32,
    lemma_key_laws_u64: u64,
    lemma_key_laws_usize: usize,
);

verus! {

/// A pair is a hash key when its components are: vstd's tuple `eq_spec` is componentwise and
/// `hash_spec` mixes the components' hashes.
pub proof fn lemma_key_laws_pair<A: Eq + KeyHash, B: Eq + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(),
    ensures key_laws::<(A, B)>(),
{
}

/// A tagged pair component is a hash key when its payloads are.
pub proof fn lemma_key_laws_component2<A: Eq + KeyHash, B: Eq + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(),
    ensures key_laws::<Component2<A, B>>(),
{
    assert forall|a: Component2<A, B>, b: Component2<A, B>, c: Component2<A, B>|
        #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) implies a.eq_spec(&c) by {
        match (a, b, c) {
            (Component2::C0(x), Component2::C0(y), Component2::C0(z)) => assert(x.eq_spec(&z)),
            (Component2::C1(x), Component2::C1(y), Component2::C1(z)) => assert(x.eq_spec(&z)),
            _ => {}
        }
    }
    assert forall|a: Component2<A, B>, b: Component2<A, B>| #[trigger] a.eq_spec(&b)
        implies a.hash_spec() == b.hash_spec() by {
        match (a, b) {
            (Component2::C0(x), Component2::C0(y)) => assert(x.hash_spec() == y.hash_spec()),
            (Component2::C1(x), Component2::C1(y)) => assert(x.hash_spec() == y.hash_spec()),
            _ => {}
        }
    }
}

/// A tagged triple component is a hash key when its payloads are.
pub proof fn lemma_key_laws_component3<A: Eq + KeyHash, B: Eq + KeyHash, C: Eq + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(), key_laws::<C>(),
    ensures key_laws::<Component3<A, B, C>>(),
{
    assert forall|a: Component3<A, B, C>, b: Component3<A, B, C>, c: Component3<A, B, C>|
        #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) implies a.eq_spec(&c) by {
        match (a, b, c) {
            (Component3::C0(x), Component3::C0(y), Component3::C0(z)) => assert(x.eq_spec(&z)),
            (Component3::C1(x), Component3::C1(y), Component3::C1(z)) => assert(x.eq_spec(&z)),
            (Component3::C2(x), Component3::C2(y), Component3::C2(z)) => assert(x.eq_spec(&z)),
            _ => {}
        }
    }
    assert forall|a: Component3<A, B, C>, b: Component3<A, B, C>| #[trigger] a.eq_spec(&b)
        implies a.hash_spec() == b.hash_spec() by {
        match (a, b) {
            (Component3::C0(x), Component3::C0(y)) => assert(x.hash_spec() == y.hash_spec()),
            (Component3::C1(x), Component3::C1(y)) => assert(x.hash_spec() == y.hash_spec()),
            (Component3::C2(x), Component3::C2(y)) => assert(x.hash_spec() == y.hash_spec()),
            _ => {}
        }
    }
}

/// A tagged quadruple component is a hash key when its payloads are.
pub proof fn lemma_key_laws_component4<A: Eq + KeyHash, B: Eq + KeyHash, C: Eq + KeyHash, D: Eq + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(), key_laws::<C>(), key_laws::<D>(),
    ensures key_laws::<Component4<A, B, C, D>>(),
{
    assert forall|a: Component4<A, B, C, D>, b: Component4<A, B, C, D>, c: Component4<A, B, C, D>|
        #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) implies a.eq_spec(&c) by {
        match (a, b, c) {
            (Component4::C0(x), Component4::C0(y), Component4::C0(z)) => assert(x.eq_spec(&z)),
            (Component4::C1(x), Component4::C1(y), Component4::C1(z)) => assert(x.eq_spec(&z)),
            (Component4::C2(x), Component4::C2(y), Component4::C2(z)) => assert(x.eq_spec(&z)),
            (Component4::C3(x), Component4::C3(y), Component4::C3(z)) => assert(x.eq_spec(&z)),
            _ => {}
        }
    }
    assert forall|a: Component4<A, B, C, D>, b: Component4<A, B, C, D>| #[trigger] a.eq_spec(&b)
        implies a.hash_spec() == b.hash_spec() by {
        match (a, b) {
            (Component4::C0(x), Component4::C0(y)) => assert(x.hash_spec() == y.hash_spec()),
            (Component4::C1(x), Component4::C1(y)) => assert(x.hash_spec() == y.hash_spec()),
            (Component4::C2(x), Component4::C2(y)) => assert(x.hash_spec() == y.hash_spec()),
            (Component4::C3(x), Component4::C3(y)) => assert(x.hash_spec() == y.hash_spec()),
            _ => {}
        }
    }
}

/// `event_obligations` for a pair event whose payloads are hash keys.
pub proof fn lemma_pair_event_hypotheses<A: Copy + Debug + Eq + Hash + KeyHash,
    B: Copy + Debug + Eq + Hash + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(),
    ensures event_obligations::<(A, B)>(),
{
    lemma_event_laws_pair::<A, B>();
    lemma_key_laws_component2::<A, B>();
}

/// `event_obligations` for a triple event whose payloads are hash keys.
pub proof fn lemma_triple_event_hypotheses<A: Copy + Debug + Eq + Hash + KeyHash,
    B: Copy + Debug + Eq + Hash + KeyHash, C: Copy + Debug + Eq + Hash + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(), key_laws::<C>(),
    ensures event_obligations::<(A, B, C)>(),
{
    lemma_event_laws_triple::<A, B, C>();
    lemma_key_laws_component3::<A, B, C>();
}

/// `event_obligations` for a quadruple event whose payloads are hash keys.
pub proof fn lemma_quad_event_hypotheses<A: Copy + Debug + Eq + Hash + KeyHash,
    B: Copy + Debug + Eq + Hash + KeyHash, C: Copy + Debug + Eq + Hash + KeyHash,
    D: Copy + Debug + Eq + Hash + KeyHash>()
    requires key_laws::<A>(), key_laws::<B>(), key_laws::<C>(), key_laws::<D>(),
    ensures event_obligations::<(A, B, C, D)>(),
{
    lemma_event_laws_quad::<A, B, C, D>();
    lemma_key_laws_component4::<A, B, C, D>();
}

/// `(u32, u64)` events satisfy `event_obligations` outright.
pub proof fn lemma_u32_u64_event_hypotheses()
    ensures event_obligations::<(u32, u64)>(),
{
    lemma_key_laws_u32();
    lemma_key_laws_u64();
    lemma_pair_event_hypotheses::<u32, u64>();
}

/// `(u8, u8, u8)` events satisfy `event_obligations` outright.
pub proof fn lemma_u8_triple_event_hypotheses()
    ensures event_obligations::<(u8, u8, u8)>(),
{
    lemma_key_laws_u8();
    lemma_triple_event_hypotheses::<u8, u8, u8>();
}

/// `(u32, u8, bool)` events satisfy `event_obligations` outright.
pub proof fn lemma_u32_mixed_event_hypotheses()
    ensures event_obligations::<(u32, u8, bool)>(),
{
    lemma_key_laws_u32();
    lemma_key_laws_u8();
    lemma_key_laws_bool();
    lemma_triple_event_hypotheses::<u32, u8, bool>();
}

} // verus!

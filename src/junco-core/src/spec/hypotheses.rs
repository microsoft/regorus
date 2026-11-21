//! The hypothesis bundles every monitor and analyzer guarantee assumes about its event type.
//! They have no uninterpreted conjunct: `key_laws` is proved for every built-in key type
//! (`junco_core::verify::hypotheses`), so `event_obligations::<E>()` is a theorem for the
//! built-in events.

use crate::spec::semantics::*;
use history_syntax::key_hash::specs::KeyHashSpec;
use history_syntax::spec::events::event_laws;
use history_syntax::{Event, KeyHash};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// `eq_spec` is an equivalence relation on `T`.
pub open spec fn eq_equivalence<T: PartialEq>() -> bool {
    &&& forall|a: T| #[trigger] a.eq_spec(&a)
    &&& forall|a: T, b: T| #[trigger] a.eq_spec(&b) == b.eq_spec(&a)
    &&& forall|a: T, b: T, c: T| #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) ==> a.eq_spec(&c)
}

/// `hash_spec` is constant on `eq_spec` classes, so a table keyed by it is a map on those classes.
/// Proved per key type in `junco_core::verify::hypotheses`; never assumed.
pub open spec fn hash_respects_eq<K: PartialEq + KeyHash>() -> bool {
    forall|a: K, b: K| #[trigger] a.eq_spec(&b) ==> a.hash_spec() == b.hash_spec()
}

/// What a hash-container key must satisfy: `Eq` agrees with `eq_spec`, which is an equivalence,
/// and `key_hash` agrees with `hash_spec`, which respects `eq_spec`.
pub open spec fn key_laws<K: Eq + KeyHash>() -> bool {
    K::obeys_eq_spec() && eq_equivalence::<K>() && K::obeys_hash_spec() && hash_respects_eq::<K>()
}

/// The one bundle every monitor and analyzer guarantee assumes about the event type `E`
/// (`event_laws` from `history_syntax::spec::events` plus `key_laws` of its component type).
pub open spec fn event_obligations<E: Event>() -> bool {
    event_laws::<E>() && key_laws::<E::Component>()
}

} // verus!

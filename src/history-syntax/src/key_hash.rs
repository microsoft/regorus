//! Verified key hashing: `key_hash` is fixed by the spec function `hash_spec`, so a hash table
//! keyed by it is a map on `eq_spec` classes by proof (`junco_core::spec::hypotheses::hash_respects_eq`),
//! never by assumption about `std::hash::Hash`.

use vstd::prelude::*;

/// Hash of a table key.
///
/// Verified impls return `hash_spec(self)`; unverified types use [`hash_via_std`].
pub trait KeyHash {
    /// The key's 64-bit hash.
    fn key_hash(&self) -> u64;
}

/// FNV-1a 64 over `Hash::hash`; for unverified glue types only.
pub fn hash_via_std<T: core::hash::Hash + ?Sized>(value: &T) -> u64 {
    struct Fnv1a(u64);
    impl core::hash::Hasher for Fnv1a {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            for byte in bytes {
                self.0 = (self.0 ^ u64::from(*byte)).wrapping_mul(0x100000001b3);
            }
        }
    }
    let mut hasher = Fnv1a(0xcbf29ce484222325);
    value.hash(&mut hasher);
    hasher.0
}

/// One FNV-1a combining step.
#[verus_verify]
#[verus_spec(r => ensures r == specs::spec_mix(h, x))]
pub fn mix(h: u64, x: u64) -> u64 {
    (h ^ x).wrapping_mul(0x100000001b3)
}

#[verus_verify]
impl KeyHash for () {
    fn key_hash(&self) -> u64 {
        0
    }
}

#[verus_verify]
impl KeyHash for bool {
    fn key_hash(&self) -> u64 {
        if *self { 1 } else { 0 }
    }
}

macro_rules! unsigned_key_hash {
    ($($t:ty),+) => {$(
        #[verus_verify]
        impl KeyHash for $t {
            fn key_hash(&self) -> u64 {
                *self as u64
            }
        }
        #[cfg(verus_keep_ghost)]
        verus! {
            impl specs::KeyHashSpecImpl for $t {
                open spec fn obeys_hash_spec() -> bool { true }
                open spec fn hash_spec(&self) -> u64 { *self as u64 }
            }
        }
    )+};
}

unsigned_key_hash!(u8, u16, u32, u64, usize);

#[verus_verify]
impl<A: KeyHash, B: KeyHash> KeyHash for (A, B) {
    fn key_hash(&self) -> u64 {
        mix(self.0.key_hash(), self.1.key_hash())
    }
}

/// Spec bridge: `hash_spec` names the hash a verified impl returns.
#[cfg(verus_keep_ghost)]
pub mod specs {
    use super::*;
    use vstd::wrapping::u64_specs;

    verus! {

    /// The step `mix` computes.
    pub open spec fn spec_mix(h: u64, x: u64) -> u64 {
        u64_specs::wrapping_mul(h ^ x, 0x100000001b3)
    }

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(KeyHashSpec via KeyHashSpecImpl)]
    pub trait ExKeyHash {
        type ExternalTraitSpecificationFor: KeyHash;

        spec fn obeys_hash_spec() -> bool;
        spec fn hash_spec(&self) -> u64;

        fn key_hash(&self) -> (h: u64)
            ensures Self::obeys_hash_spec() ==> h == self.hash_spec();
    }

    impl KeyHashSpecImpl for () {
        open spec fn obeys_hash_spec() -> bool { true }
        open spec fn hash_spec(&self) -> u64 { 0 }
    }

    impl KeyHashSpecImpl for bool {
        open spec fn obeys_hash_spec() -> bool { true }
        open spec fn hash_spec(&self) -> u64 { if *self { 1u64 } else { 0u64 } }
    }

    impl<A: KeyHash, B: KeyHash> KeyHashSpecImpl for (A, B) {
        open spec fn obeys_hash_spec() -> bool { A::obeys_hash_spec() && B::obeys_hash_spec() }
        open spec fn hash_spec(&self) -> u64 { spec_mix(self.0.hash_spec(), self.1.hash_spec()) }
    }

    } // verus!
}

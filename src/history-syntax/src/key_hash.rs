//! Key hashing for history table keys.

/// Hash of a table key.
///
/// Glue types without a hand-written impl use [`hash_via_std`].
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
pub fn mix(h: u64, x: u64) -> u64 {
    (h ^ x).wrapping_mul(0x100000001b3)
}

impl KeyHash for () {
    fn key_hash(&self) -> u64 {
        0
    }
}

impl KeyHash for bool {
    fn key_hash(&self) -> u64 {
        if *self { 1 } else { 0 }
    }
}

macro_rules! unsigned_key_hash {
    ($($t:ty),+) => {$(
        impl KeyHash for $t {
            fn key_hash(&self) -> u64 {
                *self as u64
            }
        }
    )+};
}

unsigned_key_hash!(u8, u16, u32, u64, usize);

impl<A: KeyHash, B: KeyHash> KeyHash for (A, B) {
    fn key_hash(&self) -> u64 {
        mix(self.0.key_hash(), self.1.key_hash())
    }
}

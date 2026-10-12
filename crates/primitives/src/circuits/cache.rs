//! This module defines the keys and value types of the entries that
//! commit-and-prove gadgets store in a constraint system's `cache_map`.

use ark_std::hash::{BuildHasherDefault, Hasher};
use hashbrown::HashSet;

/// [`IdentityHasher`] is a [`Hasher`] for `usize` keys that uses the key itself
/// as the hash.
#[derive(Default)]
pub struct IdentityHasher {
    value: u64,
}

impl Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        self.value
    }

    fn write(&mut self, _: &[u8]) {
        panic!("IdentityHasher only supports usize");
    }

    fn write_usize(&mut self, value: usize) {
        self.value = value as u64;
    }
}

/// [`UsizeSet`] is a set of `usize` (e.g., variable indices) hashed with
/// [`IdentityHasher`].
pub type UsizeSet = HashSet<usize, BuildHasherDefault<IdentityHasher>>;

/// [`CommittedCache`] is the cache key for the [`UsizeSet`] of indices of the
/// witness variables committed to by commit-and-prove gadgets.
pub struct CommittedCache;
/// [`CommitmentKeyCache`] is the cache key for the commitment keys used by
/// commit-and-prove gadgets, collected in the order of the `open` calls during
/// setup.
pub struct CommitmentKeyCache;
/// [`RandomnessCache`] is the cache key for the commitment randomness used by
/// commit-and-prove gadgets, collected in the order of the `open` calls during
/// proving.
pub struct RandomnessCache;

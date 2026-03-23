// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Compiled-pattern caches for Rego builtins.
//!
//! When the `cache` feature is enabled, compiled [`regex::Regex`] and
//! [`globset::GlobMatcher`] objects are held in bounded LRU caches so that
//! repeated evaluations of the same pattern avoid recompilation.
//!
//! # Examples
//!
//! ```ignore
//! use regorus::cache;
//!
//! // Configure cache capacities (0 = disabled).
//! cache::configure(cache::Config {
//!     regex: 256,
//!     glob: 128,
//! });
//!
//! // Flush all cached patterns.
//! cache::clear();
//! ```

use core::num::NonZeroUsize;
use lazy_static::lazy_static;
use spin::Mutex;

use alloc::string::String;

/// Configuration for builtin pattern caches.
///
/// Each field controls the maximum number of compiled patterns held in the
/// corresponding LRU cache.  A value of `0` disables that cache entirely
/// (every lookup recompiles).
#[derive(Debug, Clone, Copy)]
pub struct Config {
    /// Maximum compiled regex patterns (default 256).
    pub regex: usize,
    /// Maximum compiled glob matchers (default 128).
    pub glob: usize,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            regex: 256,
            glob: 128,
        }
    }
}

// ---------------------------------------------------------------------------
// Internal generic LRU wrapper
// ---------------------------------------------------------------------------

pub(crate) struct LruCache<V> {
    inner: Option<lru::LruCache<String, V>>,
}

impl<V> LruCache<V> {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            inner: NonZeroUsize::new(capacity).map(lru::LruCache::new),
        }
    }

    /// Look up a key, returning a reference if present. Promotes to most-recent.
    pub(crate) fn get(&mut self, key: &str) -> Option<&V> {
        self.inner.as_mut()?.get(key)
    }

    /// Insert a key-value pair. Evicts the least-recently-used entry if full.
    pub(crate) fn put(&mut self, key: String, value: V) {
        if let Some(cache) = self.inner.as_mut() {
            cache.put(key, value);
        }
    }

    /// Remove all entries.
    pub(crate) fn clear(&mut self) {
        if let Some(cache) = self.inner.as_mut() {
            cache.clear();
        }
    }

    /// Resize the cache. If new capacity is 0, disables the cache.
    pub(crate) fn resize(&mut self, capacity: usize) {
        match NonZeroUsize::new(capacity) {
            Some(cap) => match self.inner.as_mut() {
                Some(cache) => cache.resize(cap),
                None => self.inner = Some(lru::LruCache::new(cap)),
            },
            None => {
                self.inner = None;
            }
        }
    }

    /// Number of entries currently cached.
    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.inner.as_ref().map_or(0, lru::LruCache::len)
    }
}

// ---------------------------------------------------------------------------
// Global regex cache
// ---------------------------------------------------------------------------

lazy_static! {
    pub(crate) static ref REGEX_CACHE: Mutex<LruCache<regex::Regex>> =
        Mutex::new(LruCache::new(Config::default().regex));
}

// ---------------------------------------------------------------------------
// Global glob cache
// ---------------------------------------------------------------------------

#[cfg(feature = "glob")]
lazy_static! {
    pub(crate) static ref GLOB_CACHE: Mutex<LruCache<globset::GlobMatcher>> =
        Mutex::new(LruCache::new(Config::default().glob));
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Apply a new cache configuration.
///
/// Resizes each cache to the specified capacity.  Existing entries are
/// preserved (subject to LRU eviction if the new capacity is smaller).
pub fn configure(config: Config) {
    REGEX_CACHE.lock().resize(config.regex);

    #[cfg(feature = "glob")]
    GLOB_CACHE.lock().resize(config.glob);
}

/// Remove all entries from every pattern cache.
pub fn clear() {
    REGEX_CACHE.lock().clear();

    #[cfg(feature = "glob")]
    GLOB_CACHE.lock().clear();
}

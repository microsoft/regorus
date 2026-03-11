// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(not(any(target_family = "wasm", miri)))]
pub mod mimalloc;

#[cfg(feature = "allocator-memory-limits")]
#[cfg(not(any(target_family = "wasm", miri)))]
pub use mimalloc::{
    allocation_stats_snapshot, current_thread_allocation_stats, global_allocation_stats_snapshot,
    GlobalAllocationStats, ThreadAllocationStats,
};

#[cfg(feature = "allocator-memory-limits")]
#[cfg(not(any(target_family = "wasm", miri)))]
pub mod limits;

/// Declare a global allocator if the platform supports it.
#[macro_export]
macro_rules! assign_global {
    () => {
        #[cfg(not(any(target_family = "wasm", miri)))]
        #[global_allocator]
        static GLOBAL: mimalloc::mimalloc::Mimalloc = mimalloc::mimalloc::Mimalloc;
    };
}

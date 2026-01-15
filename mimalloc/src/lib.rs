// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(not(any(target_family = "wasm")))]
pub mod mimalloc;

#[cfg(not(any(target_family = "wasm")))]
pub use mimalloc::{global_stats_snapshot, reset_global_stats, GlobalMemoryStats};

/// Declare a global allocator if the platform supports it.
#[macro_export]
macro_rules! assign_global {
    () => {
        #[cfg(not(any(target_family = "wasm")))]
        #[global_allocator]
        static GLOBAL: mimalloc::mimalloc::Mimalloc = mimalloc::mimalloc::Mimalloc;
    };
}

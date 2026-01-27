// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Helpers for cooperative execution time and memory limits.

#![allow(dead_code)]

mod error;
#[cfg(feature = "allocator-memory-limits")]
mod memory;
#[allow(unused_imports)]
pub use error::LimitError;
#[allow(unused_imports)]
#[cfg(feature = "allocator-memory-limits")]
pub use memory::{
    check_global_memory_limit, enforce_memory_limit, flush_thread_memory_counters,
    global_memory_limit, set_global_memory_limit, set_thread_flush_threshold_override,
    thread_memory_flush_threshold,
};

#[cfg(feature = "allocator-memory-limits")]
#[inline]
pub fn check_memory_limit_if_needed() -> core::result::Result<(), LimitError> {
    memory::check_memory_limit_if_needed()
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[inline]
pub const fn enforce_memory_limit() -> core::result::Result<(), LimitError> {
    Ok(())
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[inline]
pub const fn check_memory_limit_if_needed() -> core::result::Result<(), LimitError> {
    Ok(())
}

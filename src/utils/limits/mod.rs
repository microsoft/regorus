// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Helpers for cooperative execution time and memory limits.

#![allow(dead_code)]

mod error;
mod length;
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
mod memory;
mod time;

#[allow(unused_imports)]
pub use error::LimitError;

#[allow(unused_imports)]
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[cfg_attr(docsrs, doc(cfg(feature = "allocator-memory-limits")))]
pub use memory::{
    check_global_memory_limit, enforce_memory_limit, flush_thread_memory_counters,
    global_memory_limit, set_global_memory_limit, set_thread_flush_threshold_override,
    thread_memory_flush_threshold, MemoryBudgetConfig,
};
#[cfg(all(feature = "rvm", feature = "allocator-memory-limits", not(miri)))]
pub(crate) use memory::{current_thread_live_bytes, MemoryBudgetAccount};

#[allow(unused_imports)]
pub use time::{
    fallback_execution_timer_config, monotonic_now, set_fallback_execution_timer_config,
    ExecutionTimer, ExecutionTimerConfig, TimeSource,
};

pub use length::PolicyLengthConfig;
pub(crate) use length::{DEFAULT_MAX_COL, DEFAULT_MAX_FILE_BYTES, DEFAULT_MAX_LINES};

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[inline]
pub(crate) fn without_memory_budget_scope<R>(operation: impl FnOnce() -> R) -> R {
    mimalloc::limits::with_unowned_memory_budget_scope(operation)
}

#[cfg(any(miri, not(feature = "allocator-memory-limits")))]
#[inline]
pub(crate) fn without_memory_budget_scope<R>(operation: impl FnOnce() -> R) -> R {
    operation()
}

/// Run a binding-side read-only operation without attributing its allocations
/// to an active VM execution budget.
///
/// This doc-hidden bridge is needed by the separately compiled FFI crate,
/// which cannot call the crate-private selector helper. Process-global
/// allocation accounting remains enabled.
#[doc(hidden)]
#[inline]
pub fn with_unowned_memory_budget_scope_for_ffi<R>(operation: impl FnOnce() -> R) -> R {
    without_memory_budget_scope(operation)
}

#[cfg(test)]
pub use time::acquire_limits_test_lock;

#[cfg(any(test, not(feature = "std")))]
#[allow(unused_imports)]
pub use time::{set_time_source, TimeSourceRegistrationError};

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[inline]
pub fn check_memory_limit_if_needed() -> core::result::Result<(), LimitError> {
    memory::check_memory_limit_if_needed()
}

#[cfg(any(miri, not(feature = "allocator-memory-limits")))]
#[inline]
pub const fn enforce_memory_limit() -> core::result::Result<(), LimitError> {
    Ok(())
}

#[cfg(any(miri, not(feature = "allocator-memory-limits")))]
#[inline]
pub const fn check_memory_limit_if_needed() -> core::result::Result<(), LimitError> {
    Ok(())
}

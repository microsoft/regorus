// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::error::LimitError;
use core::cell::Cell;
use core::sync::atomic::{AtomicU64, Ordering};
use std::thread_local;

static GLOBAL_MEMORY_LIMIT: AtomicU64 = AtomicU64::new(u64::MAX);

// Maximum iteration count before forcing a global memory check.
const MEMORY_CHECK_STRIDE: u32 = 16;
// Pending per-thread allocator delta (bytes) that triggers a memory check. Chosen at 32 KiB to
// catch short bursts before they exceed typical entry budgets while still amortizing the atomic.
const MEMORY_CHECK_DELTA_BYTES: u64 = 32 * 1024;

thread_local! {
    // Per-thread stride counter used to amortize global memory checks.
    static MEMORY_CHECK_TICKS: Cell<u32> = const { Cell::new(0) };
}

/// Sets the global memory limit in bytes; `None` disables enforcement.
///
/// # Examples
///
/// ```rust
/// #![cfg(feature = "allocator-memory-limits")]
/// use regorus::{set_global_memory_limit, Engine, LimitError, Value};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// const LIMIT: u64 = 32 * 1024;
/// set_global_memory_limit(Some(LIMIT));
///
/// let mut engine = Engine::new();
/// engine.add_policy(
///     "limit.rego".to_string(),
///     "package limit\nallow if input.blob != \"\"".to_string(),
/// )?;
///
/// let payload = format!("{{\"blob\":\"{}\"}}", "x".repeat(128 * 1024));
///
/// // Prepare input while the limit is relaxed so parsing succeeds on constrained builds.
/// set_global_memory_limit(Some(LIMIT * 32));
/// engine.set_input(Value::from_json_str(&payload)?);
///
/// // Tighten the budget and observe evaluation fail fast on the smaller limit.
/// set_global_memory_limit(Some(LIMIT));
/// let err = engine
///     .eval_query("data.limit.allow".to_string(), false)
///     .unwrap_err();
/// let limit = err.downcast_ref::<LimitError>().copied();
/// assert!(matches!(
///     limit,
///     Some(LimitError::MemoryLimitExceeded { limit: LIMIT, .. })
/// ));
///
/// // Raise the ceiling and the same evaluation succeeds.
/// set_global_memory_limit(Some(LIMIT * 32));
/// let result = engine.eval_query("data.limit.allow".to_string(), false)?;
/// assert_eq!(result.result.len(), 1);
/// # Ok(())
/// # }
/// ```
pub fn set_global_memory_limit(limit: Option<u64>) {
    let value = limit.unwrap_or(u64::MAX);
    GLOBAL_MEMORY_LIMIT.store(value, Ordering::Relaxed);
}

/// Flushes this thread's Regorus allocation counters into the global aggregates.
///
/// Regorus batches per-thread deltas to keep hot paths uncontended. Automatic publication occurs when
/// [`check_global_memory_limit`] runs, when the configured threshold (see
/// [`thread_memory_flush_threshold`]) is exceeded, or when allocation statistics are queried.
/// Workloads that burst and then idle—or threads that are about to terminate—can call this helper to
/// push their pending deltas immediately and avoid dropping buffered usage.
///
/// ```rust
/// #![cfg(feature = "allocator-memory-limits")]
/// use regorus::flush_thread_memory_counters;
///
/// flush_thread_memory_counters();
/// ```
///
/// Flush before a worker thread terminates:
/// ```no_run
/// # use regorus::flush_thread_memory_counters;
/// std::thread::spawn(|| {
///     // ... do work ...
///     flush_thread_memory_counters(); // publish before exiting
/// });
/// ```
pub fn flush_thread_memory_counters() {
    mimalloc::limits::flush_thread_counters();
}

/// Configures the per-thread flush threshold in bytes.
///
/// Each thread buffers allocation deltas locally and publishes them automatically once the absolute
/// difference since the last flush exceeds this threshold. Passing `None` restores the default of
/// 1&nbsp;MiB. Setting the threshold to zero disables automatic flushing, requiring manual calls to
/// [`flush_thread_memory_counters()`]. Values larger than [`i64::MAX`] are saturated.
pub fn set_thread_flush_threshold_override(bytes: Option<u64>) {
    mimalloc::limits::set_thread_flush_threshold(bytes);
}

/// Returns the current per-thread flush threshold in bytes, if automatic flushing is enabled.
///
/// When the threshold is disabled (zero or negative), `None` is returned. Otherwise the value
/// represents the absolute delta that will trigger an automatic flush.
///
/// ```rust
/// #![cfg(feature = "allocator-memory-limits")]
/// use regorus::{set_thread_flush_threshold_override, thread_memory_flush_threshold};
///
/// set_thread_flush_threshold_override(Some(256 * 1024));
/// assert_eq!(thread_memory_flush_threshold(), Some(256 * 1024));
///
/// set_thread_flush_threshold_override(Some(0));
/// assert_eq!(thread_memory_flush_threshold(), None);
/// ```
pub fn thread_memory_flush_threshold() -> Option<u64> {
    mimalloc::limits::thread_flush_threshold()
}

/// Validates the current allocation usage against the configured global limit.
///
/// This helper consults the global memory limit and returns [`LimitError::MemoryLimitExceeded`]
/// if tracked usage exceeds the configured ceiling.
///
/// ```rust
/// #![cfg(feature = "allocator-memory-limits")]
/// use regorus::{check_global_memory_limit, set_global_memory_limit, LimitError};
///
/// const LIMIT: u64 = 32 * 1024;
/// set_global_memory_limit(Some(LIMIT));
/// let _buffer = vec![0u8; 128 * 1024];
///
/// let outcome = check_global_memory_limit();
/// assert!(matches!(
///     outcome,
///     Err(LimitError::MemoryLimitExceeded { limit: LIMIT, .. })
/// ));
///
/// set_global_memory_limit(Some(LIMIT * 32));
/// check_global_memory_limit().unwrap();
/// ```
pub fn check_global_memory_limit() -> Result<(), LimitError> {
    if let Some(limit) = global_memory_limit() {
        let (stats, _) = mimalloc::allocation_stats_snapshot();
        let usage = stats.allocated;
        if usage > limit {
            return Err(LimitError::MemoryLimitExceeded { usage, limit });
        }
    }
    Ok(())
}

/// Enforces the currently configured memory ceiling, if any.
#[inline]
pub fn enforce_memory_limit() -> Result<(), LimitError> {
    check_global_memory_limit()
}

/// Performs a throttled global memory check, combining a lightweight stride counter
/// with the allocator's pending per-thread delta to avoid excessive atomics on hot paths.
/// The global limit is only evaluated when the stride expires or the pending delta crosses
/// the configured watermark.
pub(super) fn check_memory_limit_if_needed() -> Result<(), LimitError> {
    if global_memory_limit().is_none() {
        // Reset state when enforcement is disabled to avoid stale counters.
        MEMORY_CHECK_TICKS.with(|ticks| ticks.set(0));
        let _ = mimalloc::limits::take_thread_flushed_since_check_flag();
        return Ok(());
    }

    // Inspect unflushed per-thread allocator usage to catch large bursts early.
    let pending_delta = mimalloc::limits::thread_allocation_pending_delta().unsigned_abs() as u64;
    let flush_hint = mimalloc::limits::take_thread_flushed_since_check_flag();

    MEMORY_CHECK_TICKS.with(|ticks| {
        let next = ticks.get().wrapping_add(1);
        if flush_hint || next >= MEMORY_CHECK_STRIDE || pending_delta >= MEMORY_CHECK_DELTA_BYTES {
            // Publish usage when either the stride or delta threshold is hit.
            ticks.set(0);
            check_global_memory_limit()
        } else {
            ticks.set(next);
            Ok(())
        }
    })
}

/// Returns the currently-configured global memory limit in bytes, if any.
///
/// When [`set_global_memory_limit`] is called with `Some(value)`, that value is reported here.
/// Passing `None` to [`set_global_memory_limit`] removes the limit, causing this function to return
/// `None`.
///
/// # Examples
///
/// ```rust
/// #![cfg(feature = "allocator-memory-limits")]
/// use regorus::{global_memory_limit, set_global_memory_limit};
/// set_global_memory_limit(Some(123));
/// assert_eq!(global_memory_limit(), Some(123));
///
/// set_global_memory_limit(None);
/// assert_eq!(global_memory_limit(), None);
/// ```
pub fn global_memory_limit() -> Option<u64> {
    let limit = GLOBAL_MEMORY_LIMIT.load(Ordering::Relaxed);
    (limit != u64::MAX).then_some(limit)
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Memory allocation tracking helpers used by the mimalloc shim.
//! When the `allocator-memory-limits` feature is enabled the shim keeps
//! process-wide counters of bytes allocated through the Rust global allocator.
//! Otherwise the functions become no-ops so the rest of the crate can call
//! them unconditionally.

use core::cell::Cell;
use core::sync::atomic::{AtomicI64, Ordering};
use std::thread_local;

// Total memory allocated through the global allocator.
static GLOBAL_ALLOCATED: AtomicI64 = AtomicI64::new(0);

// Peak memory allocated through the global allocator.
static GLOBAL_PEAK: AtomicI64 = AtomicI64::new(0);

const DEFAULT_THREAD_FLUSH_THRESHOLD: i64 = 1024 * 1024;
static THREAD_FLUSH_THRESHOLD: AtomicI64 = AtomicI64::new(DEFAULT_THREAD_FLUSH_THRESHOLD);

thread_local! {
    // Each thread tracks its own allocations and deallocations. Periodically the thread's
    // stats are flushed into the global counters. Such a design minimizes contention on the
    // global atomic variables on each allocation/free operation.
    static THREAD_COUNTERS: ThreadAllocationCounters = const { ThreadAllocationCounters::new() };
    // Marks that this thread published allocator deltas since the last limit check.
    static THREAD_FLUSHED_SINCE_CHECK: Cell<bool> = const { Cell::new(false) };
}

/// Process-wide view of allocator usage at the moment of sampling.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GlobalAllocationStats {
    /// Total bytes currently live across all threads.
    pub allocated: u64,
    /// Highest live byte count observed so far.
    pub peak: u64,
}

/// Per-thread view of allocator usage at the moment of sampling.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ThreadAllocationStats {
    /// Current live bytes for this thread. May be negative if this thread freed
    /// allocations that originated elsewhere.
    pub allocated: i64,
    /// Thread-local peak live bytes reached since thread start.
    pub peak: i64,
}

/// Per-thread accumulator that buffers allocation deltas before flushing.
struct ThreadAllocationCounters {
    // Live bytes tracked for this thread.
    // Incremented on allocation, decremented on free.
    // Note that a thread may free memory allocated by another thread, and thus
    // this value may go negative.
    allocated: Cell<i64>,
    // Highest live byte count observed for this thread.
    peak: Cell<i64>,
    // Value most recently flushed into the global counters.
    last_flushed: Cell<i64>,
}

impl ThreadAllocationCounters {
    /// Creates an empty counter set for a new thread.
    const fn new() -> Self {
        Self {
            allocated: Cell::new(0),
            peak: Cell::new(0),
            last_flushed: Cell::new(0),
        }
    }

    /// Records an allocation and updates the thread peak.
    fn on_alloc(&self, size: i64) {
        if size == 0 {
            return;
        }

        let new_total = self.allocated.get().saturating_add(size);
        self.allocated.set(new_total);
        // Track the highest live byte count the thread has seen.
        self.peak.set(self.peak.get().max(new_total));
        self.flush_if_threshold_exceeded();
    }

    /// Records a free possibly making the thread total negative.
    fn on_free(&self, size: i64) {
        if size == 0 {
            return;
        }

        let new_total = self.allocated.get().saturating_sub(size);
        self.allocated.set(new_total);
        self.flush_if_threshold_exceeded();
    }

    /// Captures the thread-local stats without flushing.
    fn snapshot(&self) -> ThreadAllocationStats {
        ThreadAllocationStats {
            allocated: self.allocated.get(),
            peak: self.peak.get(),
        }
    }

    /// Pushes thread stats into the global counters.
    fn flush(&self) -> Option<(i64, i64)> {
        // Snapshot the latest per-thread total and remember it as the new baseline.
        let thread_total = self.allocated.get();
        let last_flushed_total = self.last_flushed.replace(thread_total);
        // The delta accounts for allocations or frees since the previous flush.
        let delta = thread_total - last_flushed_total;
        if delta != 0 {
            // Apply the delta to the process-wide totals.
            let global_total = GLOBAL_ALLOCATED.fetch_add(delta, Ordering::Relaxed) + delta;
            // Ensure the recorded global peak stays monotonic.
            let peak = update_global_peak(global_total);
            THREAD_FLUSHED_SINCE_CHECK.with(|flag| flag.set(true));
            Some((global_total, peak))
        } else {
            None
        }
    }

    fn flush_if_threshold_exceeded(&self) {
        let threshold = THREAD_FLUSH_THRESHOLD.load(Ordering::Relaxed);
        if threshold <= 0 {
            return;
        }

        let current_total = self.allocated.get();
        let last_flushed_total = self.last_flushed.get();
        let delta = current_total - last_flushed_total;
        if delta >= threshold || delta <= -threshold {
            let _ = self.flush();
        }
    }

    fn pending_delta(&self) -> i64 {
        self.allocated.get() - self.last_flushed.get()
    }
}

/// Record a new allocation of `size` bytes for the current thread.
pub fn record_alloc(size: usize) {
    if size == 0 {
        return;
    }

    let size = size.min(i64::MAX as usize) as i64;

    THREAD_COUNTERS.with(|counters| counters.on_alloc(size));
}

/// Record that `size` bytes were freed by the current thread.
pub fn record_free(size: usize) {
    if size == 0 {
        return;
    }

    let size = size.min(i64::MAX as usize) as i64;

    THREAD_COUNTERS.with(|counters| counters.on_free(size));
}

/// Flush the current thread's counters into the global aggregates.
pub fn flush_thread_counters() {
    THREAD_COUNTERS.with(|counters| {
        counters.flush();
    });
}

/// Returns true if this thread published allocator deltas since the last call.
pub fn take_thread_flushed_since_check_flag() -> bool {
    THREAD_COUNTERS.with(|_| {
        THREAD_FLUSHED_SINCE_CHECK.with(|flag| {
            let flagged = flag.get();
            if flagged {
                flag.set(false);
            }
            flagged
        })
    })
}

/// Return the global and current-thread allocation statistics.
pub fn allocation_stats_snapshot() -> (GlobalAllocationStats, ThreadAllocationStats) {
    let (thread_stats, global_total, global_peak) = THREAD_COUNTERS.with(|counters| {
        let (global_total, global_peak) = match counters.flush() {
            Some((total, peak)) => (total, peak),
            None => load_global_counters(),
        };
        (counters.snapshot(), global_total, global_peak)
    });

    let global_stats = GlobalAllocationStats {
        allocated: global_total.max(0) as u64,
        peak: global_peak.max(0) as u64,
    };

    (global_stats, thread_stats)
}

/// Return only the global allocation statistics.
pub fn global_allocation_stats_snapshot() -> GlobalAllocationStats {
    allocation_stats_snapshot().0
}

/// Return only the current thread allocation statistics.
pub fn current_thread_allocation_stats() -> ThreadAllocationStats {
    allocation_stats_snapshot().1
}

/// Return the unflushed allocation delta for the current thread.
pub fn thread_allocation_pending_delta() -> i64 {
    THREAD_COUNTERS.with(|counters| counters.pending_delta())
}

/// Ensures the global peak tracks the highest observed value.
fn update_global_peak(candidate: i64) -> i64 {
    if candidate <= 0 {
        return GLOBAL_PEAK.load(Ordering::Relaxed).max(0);
    }

    let mut observed = GLOBAL_PEAK.load(Ordering::Relaxed);
    while candidate > observed {
        // Retry until we manage to publish the higher peak without blocking.
        match GLOBAL_PEAK.compare_exchange(
            observed,
            candidate,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            Ok(_) => return candidate,
            Err(next) => observed = next,
        }
    }
    observed.max(candidate)
}

/// Loads the global counters without modifying thread state.
fn load_global_counters() -> (i64, i64) {
    let total = GLOBAL_ALLOCATED.load(Ordering::Relaxed);
    let peak = update_global_peak(total);
    (total, peak)
}

/// Updates the per-thread flush threshold. `None` restores the default (1 MiB).
///
/// Values larger than `i64::MAX` are saturated. Setting the threshold to zero disables automatic
/// flushing, requiring callers to publish deltas manually via [`flush_thread_counters`].
pub fn set_thread_flush_threshold(bytes: Option<u64>) {
    let value = match bytes {
        Some(bytes) => (bytes.min(i64::MAX as u64)) as i64,
        None => DEFAULT_THREAD_FLUSH_THRESHOLD,
    };
    THREAD_FLUSH_THRESHOLD.store(value, Ordering::Relaxed);
}

/// Returns the currently configured per-thread flush threshold in bytes.
///
/// A return value of `None` indicates that automatic flushing is disabled (threshold set to zero or
/// negative). Otherwise the returned number denotes the absolute delta that will trigger a flush.
pub fn thread_flush_threshold() -> Option<u64> {
    let value = THREAD_FLUSH_THRESHOLD.load(Ordering::Relaxed);
    (value > 0).then_some(value as u64)
}

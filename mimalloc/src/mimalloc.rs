// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::c_void;
use mimalloc_sys::{
    mi_free, mi_malloc_aligned, mi_realloc_aligned, mi_stats_reset, mi_stats_summary,
    mi_stats_summary_t, mi_zalloc_aligned, MI_ALIGNMENT_MAX,
};
fn record_alloc(_size: usize) {}

fn record_free(_size: usize) {}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GlobalMemoryStats {
    pub committed_current: u64,
    pub committed_peak: u64,
    pub reserved_current: u64,
    pub reserved_peak: u64,
}

/// Reset the global mimalloc statistics counters.
pub fn reset_global_stats() {
    unsafe {
        mi_stats_reset();
    }
}

/// Capture a snapshot of the global mimalloc statistics.
pub fn global_stats_snapshot() -> GlobalMemoryStats {
    let mut summary = mi_stats_summary_t::default();
    unsafe {
        mi_stats_summary(&mut summary);
    }
    GlobalMemoryStats {
        committed_current: summary.committed_current,
        committed_peak: summary.committed_peak,
        reserved_current: summary.reserved_current,
        reserved_peak: summary.reserved_peak,
    }
}

pub struct Mimalloc;

unsafe impl GlobalAlloc for Mimalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        let ptr = mi_malloc_aligned(layout.size(), layout.align()).cast::<u8>();
        if !ptr.is_null() {
            record_alloc(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        record_free(layout.size());
        mi_free(ptr.cast::<c_void>());
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        let ptr = mi_zalloc_aligned(layout.size(), layout.align()).cast::<u8>();
        if !ptr.is_null() {
            record_alloc(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        let result =
            mi_realloc_aligned(ptr.cast::<c_void>(), new_size, layout.align()).cast::<u8>();
        if !result.is_null() {
            record_free(layout.size());
            record_alloc(new_size);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;

    #[test]
    fn memory_can_be_allocated_and_freed() -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(8, 8)?;
        let alloc = Mimalloc;

        unsafe {
            let ptr = alloc.alloc(layout);
            assert!(!ptr.cast::<c_void>().is_null());
            alloc.dealloc(ptr, layout);
        }
        Ok(())
    }

    #[test]
    fn memory_can_be_alloc_zeroed_and_freed() -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(8, 8)?;
        let alloc = Mimalloc;

        unsafe {
            let ptr = alloc.alloc_zeroed(layout);
            assert!(!ptr.cast::<c_void>().is_null());
            alloc.dealloc(ptr, layout);
        }
        Ok(())
    }

    #[test]
    fn large_chunks_of_memory_can_be_allocated_and_freed() -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(2 * 1024 * 1024 * 1024, 8)?;
        let alloc = Mimalloc;

        unsafe {
            let ptr = alloc.alloc(layout);
            assert!(!ptr.cast::<c_void>().is_null());
            alloc.dealloc(ptr, layout);
        }
        Ok(())
    }

    #[test]
    fn global_stats_snapshot_reports_totals() {
        reset_global_stats();
        let stats = global_stats_snapshot();
        assert!(stats.committed_peak >= stats.committed_current);
        assert!(stats.reserved_peak >= stats.reserved_current);
    }
}

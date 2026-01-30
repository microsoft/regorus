// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::c_void;
use mimalloc_sys::{
    mi_free, mi_malloc_aligned, mi_realloc_aligned, mi_zalloc_aligned, MI_ALIGNMENT_MAX,
};

#[cfg(feature = "allocator-memory-limits")]
pub use crate::limits::{
    allocation_stats_snapshot, current_thread_allocation_stats, flush_thread_counters,
    global_allocation_stats_snapshot, record_alloc, record_free, set_thread_flush_threshold,
    GlobalAllocationStats, ThreadAllocationStats,
};
pub struct Mimalloc;

unsafe impl GlobalAlloc for Mimalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        let ptr = mi_malloc_aligned(layout.size(), layout.align()).cast::<u8>();

        #[cfg(feature = "allocator-memory-limits")]
        if !ptr.is_null() {
            record_alloc(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        #[cfg(feature = "allocator-memory-limits")]
        record_free(_layout.size());
        mi_free(ptr.cast::<c_void>());
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        let ptr = mi_zalloc_aligned(layout.size(), layout.align()).cast::<u8>();

        #[cfg(feature = "allocator-memory-limits")]
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

        #[cfg(feature = "allocator-memory-limits")]
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

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn allocation_stats_report_live_usage() -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(4 * 1024, 8)?;
        let alloc = Mimalloc;

        let before_global = global_allocation_stats_snapshot().allocated;
        let before_thread = current_thread_allocation_stats().allocated;

        unsafe {
            let ptr = alloc.alloc(layout);
            assert!(!ptr.cast::<c_void>().is_null());
            let during_thread = current_thread_allocation_stats().allocated;
            assert!(during_thread >= before_thread + layout.size() as i64);
            alloc.dealloc(ptr, layout);
        }

        let after_thread = current_thread_allocation_stats().allocated;
        assert_eq!(after_thread, before_thread);

        let after_global = global_allocation_stats_snapshot().allocated;
        assert!(after_global >= before_global);
        Ok(())
    }
}

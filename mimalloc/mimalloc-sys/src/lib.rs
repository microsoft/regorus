// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::ffi::c_void;

pub const MI_ALIGNMENT_MAX: usize = 1024 * 1024; // 1 MiB

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct mi_stats_summary_t {
    pub committed_current: u64,
    pub committed_peak: u64,
    pub reserved_current: u64,
    pub reserved_peak: u64,
}

// Define core functions from mimalloc needed for the allocator
extern "C" {
    /// Allocate `size` bytes aligned by `alignment`.
    /// Returns a pointer to the allocated memory, or null if out of memory. The returned pointer is aligned by `alignment`.
    pub fn mi_malloc_aligned(size: usize, alignment: usize) -> *mut c_void;
    pub fn mi_zalloc_aligned(size: usize, alignment: usize) -> *mut c_void;

    /// Free previously allocated memory.
    /// The pointer `p` must have been allocated before (or be nullptr).
    pub fn mi_free(p: *mut c_void);
    pub fn mi_realloc_aligned(p: *mut c_void, newsize: usize, alignment: usize) -> *mut c_void;

    /// Reset allocator statistics.
    pub fn mi_stats_reset();

    /// Return a minimal snapshot of the global allocator statistics.
    pub fn mi_stats_summary(summary: *mut mi_stats_summary_t);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_can_be_allocated_and_freed() {
        let ptr = unsafe { mi_malloc_aligned(8, 8) }.cast::<u8>();
        assert!(!ptr.cast::<c_void>().is_null());
        unsafe { mi_free(ptr.cast::<c_void>()) };
    }

    #[test]
    fn memory_can_be_allocated_zeroed_and_freed() {
        let ptr = unsafe { mi_zalloc_aligned(8, 8) }.cast::<u8>();
        assert!(!ptr.cast::<c_void>().is_null());
        unsafe { mi_free(ptr.cast::<c_void>()) };
    }

    #[test]
    fn memory_can_be_reallocated_and_freed() {
        let ptr = unsafe { mi_malloc_aligned(8, 8) }.cast::<u8>();
        assert!(!ptr.cast::<c_void>().is_null());
        let realloc_ptr = unsafe { mi_realloc_aligned(ptr.cast::<c_void>(), 8, 8) }.cast::<u8>();
        assert!(!realloc_ptr.cast::<c_void>().is_null());
        unsafe { mi_free(ptr.cast::<c_void>()) };
    }

    #[test]
    fn stats_summary_can_be_fetched() {
        let mut summary = mi_stats_summary_t::default();
        unsafe {
            mi_stats_reset();
            mi_stats_summary(&mut summary);
        }
        // After a reset the current usage should be zero.
        assert_eq!(summary.committed_current, 0);
    }
}

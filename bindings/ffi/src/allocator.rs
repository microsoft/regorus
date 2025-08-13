// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(feature = "custom_allocator")]
extern "C" {
    fn regorus_aligned_alloc(alignment: usize, size: usize) -> *mut u8;
    fn regorus_free(ptr: *mut u8);
}

#[cfg(feature = "custom_allocator")]
mod allocator {
    use std::alloc::{GlobalAlloc, Layout};

    struct RegorusAllocator {}

    unsafe impl GlobalAlloc for RegorusAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let size = layout.size();
            let align = layout.align();

            crate::allocator::regorus_aligned_alloc(align, size)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
            crate::allocator::regorus_free(ptr)
        }
    }

    #[global_allocator]
    static ALLOCATOR: RegorusAllocator = RegorusAllocator {};
}

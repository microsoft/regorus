// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::c_void;
#[cfg(feature = "allocator-memory-limits")]
use core::mem::{align_of, size_of};
#[cfg(feature = "allocator-memory-limits")]
use core::ptr;
use mimalloc_sys::{
    mi_free, mi_malloc_aligned, mi_realloc_aligned, mi_zalloc_aligned, MI_ALIGNMENT_MAX,
};

#[cfg(feature = "allocator-memory-limits")]
pub use crate::limits::{
    allocation_stats_snapshot, current_thread_allocation_stats, current_thread_live_bytes,
    flush_thread_counters, global_allocation_stats_snapshot, record_alloc, record_free,
    set_thread_flush_threshold, GlobalAllocationStats, MemoryBudgetAccount, ThreadAllocationStats,
};

#[cfg(feature = "allocator-memory-limits")]
use crate::limits::{
    current_memory_budget_account, record_memory_budget_alloc, record_memory_budget_free,
    release_memory_budget_account, retain_memory_budget_account,
};

#[cfg(feature = "allocator-memory-limits")]
#[repr(C)]
#[derive(Clone, Copy)]
struct AllocationHeader {
    requested_size: usize,
    account: *mut c_void,
}

#[cfg(feature = "allocator-memory-limits")]
fn allocation_header_padding(align: usize) -> usize {
    // Layout alignments are powers of two; this rounds the prefix without overflowing.
    size_of::<AllocationHeader>().wrapping_neg() & align.saturating_sub(1)
}

#[cfg(feature = "allocator-memory-limits")]
fn allocation_header_layout(layout: Layout) -> Option<(usize, usize, usize)> {
    let header_size = size_of::<AllocationHeader>();
    let align = layout.align();
    let offset = header_size.checked_add(allocation_header_padding(align))?;
    let raw_size = offset.checked_add(layout.size())?;
    let raw_align = align.max(align_of::<AllocationHeader>());
    Some((offset, raw_align, raw_size))
}

#[cfg(feature = "allocator-memory-limits")]
unsafe fn allocate_with_account(layout: Layout, account: *mut c_void, zeroed: bool) -> *mut u8 {
    let Some((offset, raw_align, raw_size)) = allocation_header_layout(layout) else {
        return ptr::null_mut();
    };
    let base = if zeroed {
        mi_zalloc_aligned(raw_size, raw_align)
    } else {
        mi_malloc_aligned(raw_size, raw_align)
    };
    if base.is_null() {
        return ptr::null_mut();
    }

    let user = base.cast::<u8>().add(offset);
    let header = user
        .sub(size_of::<AllocationHeader>())
        .cast::<AllocationHeader>();
    retain_memory_budget_account(account);
    header.write(AllocationHeader {
        requested_size: layout.size(),
        account,
    });
    user
}

#[cfg(feature = "allocator-memory-limits")]
unsafe fn allocation_header(ptr: *mut u8) -> *mut AllocationHeader {
    ptr.sub(size_of::<AllocationHeader>())
        .cast::<AllocationHeader>()
}

#[cfg(feature = "allocator-memory-limits")]
unsafe fn allocation_base(ptr: *mut u8, align: usize) -> *mut c_void {
    allocation_header(ptr)
        .cast::<u8>()
        .sub(allocation_header_padding(align))
        .cast::<c_void>()
}

pub struct Mimalloc;

unsafe impl GlobalAlloc for Mimalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        #[cfg(feature = "allocator-memory-limits")]
        let ptr = {
            let account = current_memory_budget_account();
            let ptr = allocate_with_account(layout, account, false);
            if !ptr.is_null() {
                record_memory_budget_alloc(account, layout.size());
                record_alloc(layout.size());
            }
            ptr
        };

        #[cfg(not(feature = "allocator-memory-limits"))]
        let ptr = mi_malloc_aligned(layout.size(), layout.align()).cast::<u8>();
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        #[cfg(feature = "allocator-memory-limits")]
        {
            let header = allocation_header(ptr).read();
            let base = allocation_base(ptr, _layout.align());
            record_memory_budget_free(header.account, header.requested_size);
            release_memory_budget_account(header.account);
            record_free(header.requested_size);
            mi_free(base);
        }

        #[cfg(not(feature = "allocator-memory-limits"))]
        {
            mi_free(ptr.cast::<c_void>());
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        #[cfg(feature = "allocator-memory-limits")]
        let ptr = {
            let account = current_memory_budget_account();
            let ptr = allocate_with_account(layout, account, true);
            if !ptr.is_null() {
                record_memory_budget_alloc(account, layout.size());
                record_alloc(layout.size());
            }
            ptr
        };

        #[cfg(not(feature = "allocator-memory-limits"))]
        let ptr = mi_zalloc_aligned(layout.size(), layout.align()).cast::<u8>();
        ptr
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        #[cfg(feature = "allocator-memory-limits")]
        let result = {
            let Ok(new_layout) = Layout::from_size_align(new_size, layout.align()) else {
                return ptr::null_mut();
            };
            let old_header = allocation_header(ptr).read();
            let old_base = allocation_base(ptr, layout.align());
            let Some((offset, raw_align, raw_size)) = allocation_header_layout(new_layout) else {
                return ptr::null_mut();
            };
            let account = current_memory_budget_account();
            retain_memory_budget_account(account);
            #[cfg(test)]
            let base = if tests::take_next_native_realloc_failure_for_test() {
                ptr::null_mut()
            } else {
                mi_realloc_aligned(old_base, raw_size, raw_align)
            };
            #[cfg(not(test))]
            let base = mi_realloc_aligned(old_base, raw_size, raw_align);
            if base.is_null() {
                release_memory_budget_account(account);
                return ptr::null_mut();
            }

            let result = base.cast::<u8>().add(offset);
            allocation_header(result).write(AllocationHeader {
                requested_size: new_size,
                account,
            });
            record_memory_budget_free(old_header.account, old_header.requested_size);
            record_memory_budget_alloc(account, new_size);
            record_free(old_header.requested_size);
            record_alloc(new_size);
            release_memory_budget_account(old_header.account);
            result
        };

        #[cfg(not(feature = "allocator-memory-limits"))]
        let result =
            mi_realloc_aligned(ptr.cast::<c_void>(), new_size, layout.align()).cast::<u8>();
        result
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "allocator-memory-limits")]
    use super::MemoryBudgetAccount;
    use super::*;
    use std::error::Error;

    #[cfg(feature = "allocator-memory-limits")]
    std::thread_local! {
        static FAIL_NEXT_NATIVE_REALLOC_FOR_TEST: core::cell::Cell<bool> =
            const { core::cell::Cell::new(false) };
    }

    #[cfg(feature = "allocator-memory-limits")]
    struct FailNextNativeReallocGuard {
        previous: bool,
    }

    #[cfg(feature = "allocator-memory-limits")]
    impl FailNextNativeReallocGuard {
        fn arm() -> Self {
            let previous =
                FAIL_NEXT_NATIVE_REALLOC_FOR_TEST.with(|should_fail| should_fail.replace(true));
            Self { previous }
        }
    }

    #[cfg(feature = "allocator-memory-limits")]
    impl Drop for FailNextNativeReallocGuard {
        fn drop(&mut self) {
            FAIL_NEXT_NATIVE_REALLOC_FOR_TEST.with(|should_fail| should_fail.set(self.previous));
        }
    }

    #[cfg(feature = "allocator-memory-limits")]
    pub(super) fn take_next_native_realloc_failure_for_test() -> bool {
        FAIL_NEXT_NATIVE_REALLOC_FOR_TEST.with(|should_fail| should_fail.replace(false))
    }

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

    #[cfg(all(feature = "allocator-memory-limits", target_pointer_width = "64"))]
    #[test]
    fn two_word_header_uses_expected_alignment_eight_geometry() -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(1, 8)?;
        let native_request = allocation_header_layout(layout);
        let allocator = Mimalloc;
        let ptr = unsafe { allocator.alloc(layout) };
        assert!(!ptr.is_null());
        let user_to_header = ptr as usize - unsafe { allocation_header(ptr) } as usize;
        unsafe { allocator.dealloc(ptr, layout) };

        println!(
            "geometry discriminator observed native_request={native_request:?}, user_to_header={user_to_header}; expected native_request=Some((16, 8, 17)), user_to_header=16"
        );
        assert_eq!(
            user_to_header, 16,
            "alignment-8 user pointer displacement should be the two-word header size"
        );
        assert_eq!(
            native_request,
            Some((16, 8, 17)),
            "alignment-8 raw native allocation should request 16-byte prefix plus 1 user byte"
        );
        Ok(())
    }

    #[cfg(all(feature = "allocator-memory-limits", target_pointer_width = "64"))]
    #[test]
    fn header_geometry_preserves_zeroed_aligned_reallocations() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let cases = [
            (1, (16, 8, 33)),
            (8, (16, 8, 33)),
            (16, (16, 16, 33)),
            (64, (64, 64, 81)),
            (256, (256, 256, 273)),
        ];

        for (align, expected_native_request) in cases {
            let old_layout = Layout::from_size_align(17, align)?;
            assert_eq!(
                allocation_header_layout(old_layout),
                Some(expected_native_request),
                "unexpected native geometry for alignment {align}"
            );

            let ptr = unsafe { allocator.alloc_zeroed(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                assert_eq!((ptr as usize) % align, 0);
                assert!((0..old_layout.size()).all(|index| unsafe { *ptr.add(index) == 0 }));
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            }

            let new_size = 33;
            let ptr = unsafe { allocator.realloc(ptr, old_layout, new_size) };
            assert!(!ptr.is_null());
            assert_eq!((ptr as usize) % align, 0);
            assert!((0..old_layout.size()).all(|index| unsafe { *ptr.add(index) == 0x5a }));

            unsafe { allocator.dealloc(ptr, Layout::from_size_align(new_size, align)?) };
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

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_tracks_requested_bytes_and_origin_free_across_threads(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let outer = MemoryBudgetAccount::new();
        let inner = MemoryBudgetAccount::default();
        let unowned_layout = Layout::from_size_align(11, 8)?;
        let outer_layout = Layout::from_size_align(13, 8)?;
        let inner_layout = Layout::from_size_align(19, 64)?;
        let after_inner_layout = Layout::from_size_align(7, 8)?;

        let unowned = unsafe { allocator.alloc(unowned_layout) };
        assert!(!unowned.is_null());
        let (outer_ptr, after_inner_ptr, inner_ptr) = outer.with_scope(|| {
            let outer_ptr = unsafe { allocator.alloc(outer_layout) };
            assert!(!outer_ptr.is_null());
            assert_eq!(outer.live_bytes(), 13);
            assert_eq!(inner.live_bytes(), 0);

            let inner_ptr = inner.with_scope(|| unsafe { allocator.alloc_zeroed(inner_layout) });
            assert!(!inner_ptr.is_null());

            assert_eq!(outer.live_bytes(), 13);
            assert_eq!(inner.live_bytes(), 19);
            assert_eq!((inner_ptr as usize) % 64, 0);
            assert!((0..19).all(|offset| unsafe { *inner_ptr.add(offset) == 0 }));

            let after_inner_ptr = unsafe { allocator.alloc(after_inner_layout) };
            assert!(!after_inner_ptr.is_null());
            assert_eq!(outer.live_bytes(), 20);
            unsafe { allocator.dealloc(unowned, unowned_layout) };
            assert_eq!(outer.live_bytes(), 20);
            (outer_ptr, after_inner_ptr, inner_ptr)
        });

        let inner_address = inner_ptr as usize;
        std::thread::spawn(move || unsafe {
            Mimalloc.dealloc(inner_address as *mut u8, inner_layout);
        })
        .join()
        .expect("cross-thread free");
        assert_eq!(inner.live_bytes(), 0);

        unsafe {
            allocator.dealloc(outer_ptr, outer_layout);
            allocator.dealloc(after_inner_ptr, after_inner_layout);
        }
        assert_eq!(outer.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_account_tracks_exact_boundary_and_alias_free() -> Result<(), Box<dyn Error>>
    {
        let allocator = Mimalloc;
        let account = MemoryBudgetAccount::new();
        let limit = 32_u64;
        let layout = Layout::from_size_align(limit as usize, 8)?;
        let extra_layout = Layout::from_size_align(1, 8)?;

        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(layout) };
            assert!(!ptr.is_null());
            assert_eq!(account.live_bytes(), limit);
            assert!(account.live_bytes() <= limit);

            let extra = unsafe { allocator.alloc(extra_layout) };
            assert!(!extra.is_null());
            assert_eq!(account.live_bytes(), limit + 1);
            assert!(account.live_bytes() > limit);
            unsafe { allocator.dealloc(extra, extra_layout) };
            assert_eq!(account.live_bytes(), limit);
            ptr
        });

        let alias = ptr;
        unsafe { allocator.dealloc(alias, layout) };
        assert_eq!(account.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn successful_realloc_transfers_origin_and_failed_realloc_preserves_it(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let first = MemoryBudgetAccount::new();
        let second = MemoryBudgetAccount::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;

        let mut ptr = first.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            ptr
        });
        assert_eq!(first.live_bytes(), 16);

        let global_before_failure = global_allocation_stats_snapshot().allocated;
        let failed =
            second.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, usize::MAX) });
        assert!(failed.is_null());
        assert_eq!(first.live_bytes(), 16);
        assert_eq!(second.live_bytes(), 0);
        assert_eq!(
            global_allocation_stats_snapshot().allocated,
            global_before_failure
        );
        assert!((0..16).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

        ptr =
            second.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
        assert!(!ptr.is_null());
        assert_eq!(first.live_bytes(), 0);
        assert_eq!(second.live_bytes(), 64);
        assert_eq!((ptr as usize) % new_layout.align(), 0);
        assert!((0..16).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

        unsafe { allocator.dealloc(ptr, new_layout) };
        assert_eq!(second.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn injected_native_realloc_failure_preserves_origin_and_is_one_shot(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let first = MemoryBudgetAccount::new();
        let current = MemoryBudgetAccount::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;
        let global_before = global_allocation_stats_snapshot().allocated;

        let ptr = first.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            ptr
        });
        assert_eq!(first.live_bytes(), old_layout.size() as u64);
        assert_eq!(current.live_bytes(), 0);
        assert_eq!(first.reference_count_for_test(), 2);
        assert_eq!(current.reference_count_for_test(), 1);

        let failure = FailNextNativeReallocGuard::arm();
        let result =
            current.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
        drop(failure);
        if !result.is_null() {
            unsafe { allocator.dealloc(result, new_layout) };
        }
        assert!(
            result.is_null(),
            "the fail-next test hook should force the native null-result path"
        );
        assert_eq!(first.live_bytes(), old_layout.size() as u64);
        assert_eq!(current.live_bytes(), 0);
        assert_eq!(first.reference_count_for_test(), 2);
        assert_eq!(current.reference_count_for_test(), 1);
        assert_eq!(
            global_allocation_stats_snapshot().allocated,
            global_before + old_layout.size() as u64
        );
        let header = unsafe { allocation_header(ptr).read() };
        assert_eq!(header.requested_size, old_layout.size());
        assert!(!header.account.is_null());
        assert!((0..old_layout.size()).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

        drop(first);
        unsafe { allocator.dealloc(ptr, old_layout) };

        let next = current.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x6b, old_layout.size()) };
            ptr
        });
        let next = current
            .with_scope(|| unsafe { allocator.realloc(next, old_layout, new_layout.size()) });
        assert!(!next.is_null());
        assert_eq!(current.live_bytes(), new_layout.size() as u64);
        assert!((0..old_layout.size()).all(|offset| unsafe { *next.add(offset) == 0x6b }));
        unsafe { allocator.dealloc(next, new_layout) };
        assert_eq!(current.live_bytes(), 0);
        assert_eq!(global_allocation_stats_snapshot().allocated, global_before);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn realloc_updates_requested_bytes_for_each_origin_transition() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let first = MemoryBudgetAccount::new();
        let second = MemoryBudgetAccount::new();
        let third = MemoryBudgetAccount::new();
        let mut layout = Layout::from_size_align(23, 64)?;
        let mut ptr = first.with_scope(|| {
            let ptr = unsafe { allocator.alloc(layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x5a, layout.size()) };
            ptr
        });

        let transitions: [(Option<&MemoryBudgetAccount>, usize); 6] = [
            (Some(&first), 47),
            (Some(&second), 31),
            (None, 63),
            (None, 55),
            (Some(&third), 77),
            (Some(&third), 51),
        ];
        for (next_owner, new_size) in transitions {
            let global_before = global_allocation_stats_snapshot().allocated;
            ptr = if let Some(next_owner) = next_owner {
                next_owner.with_scope(|| unsafe { allocator.realloc(ptr, layout, new_size) })
            } else {
                unsafe { allocator.realloc(ptr, layout, new_size) }
            };
            assert!(!ptr.is_null());
            assert_eq!((ptr as usize) % layout.align(), 0);
            assert!((0..23).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));
            assert_eq!(
                global_allocation_stats_snapshot().allocated,
                global_before - layout.size() as u64 + new_size as u64
            );

            layout = Layout::from_size_align(new_size, layout.align())?;
            assert_eq!(
                first.live_bytes(),
                if next_owner.map_or(false, |owner| core::ptr::eq(owner, &first)) {
                    new_size as u64
                } else {
                    0
                }
            );
            assert_eq!(
                second.live_bytes(),
                if next_owner.map_or(false, |owner| core::ptr::eq(owner, &second)) {
                    new_size as u64
                } else {
                    0
                }
            );
            assert_eq!(
                third.live_bytes(),
                if next_owner.map_or(false, |owner| core::ptr::eq(owner, &third)) {
                    new_size as u64
                } else {
                    0
                }
            );
        }

        unsafe { allocator.dealloc(ptr, layout) };
        assert_eq!(third.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn realloc_transfers_origin_across_threads_and_free_debits_it() -> Result<(), Box<dyn Error>> {
        let first = MemoryBudgetAccount::new();
        let second = MemoryBudgetAccount::new();
        let old_layout = Layout::from_size_align(17, 64)?;
        let new_layout = Layout::from_size_align(257, 64)?;
        let ptr = first.with_scope(|| {
            let ptr = unsafe { Mimalloc.alloc(old_layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            ptr
        });

        let address = ptr as usize;
        let worker_account = second.clone();
        let (sender, receiver) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let ptr = address as *mut u8;
            let ptr = worker_account
                .with_scope(|| unsafe { Mimalloc.realloc(ptr, old_layout, new_layout.size()) });
            sender.send(ptr as usize).expect("send reallocated pointer");
        });
        worker.join().expect("cross-thread realloc");
        let ptr = receiver.recv().expect("receive reallocated pointer") as *mut u8;

        assert!(!ptr.is_null());
        assert_eq!(first.live_bytes(), 0);
        assert_eq!(second.live_bytes(), new_layout.size() as u64);
        assert_eq!((ptr as usize) % new_layout.align(), 0);
        assert!((0..old_layout.size()).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

        let address = ptr as usize;
        let (sender, receiver) = std::sync::mpsc::channel();
        let freer = std::thread::spawn(move || {
            unsafe { Mimalloc.dealloc(address as *mut u8, new_layout) };
            sender.send(()).expect("send free completion");
        });
        receiver.recv().expect("receive free completion");
        freer.join().expect("cross-thread free");
        assert_eq!(second.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn native_aligned_realloc_reuses_a_same_bin_shrink() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let account = MemoryBudgetAccount::new();
        let old_layout = Layout::from_size_align(32, 8)?;
        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            ptr
        });

        // This characterizes vendored mimalloc's same-bin shrink, not GlobalAlloc pointer stability.
        let original = ptr;
        let ptr = account.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, 31) });
        assert!(!ptr.is_null());
        assert_eq!(ptr, original);
        assert_eq!(account.live_bytes(), 31);
        assert!((0..31).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

        unsafe { allocator.dealloc(ptr, Layout::from_size_align(31, 8)?) };
        assert_eq!(account.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn native_aligned_realloc_moves_for_small_to_large_growth() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let account = MemoryBudgetAccount::new();
        let old_layout = Layout::from_size_align(17, 16)?;
        let new_layout = Layout::from_size_align(1024, 16)?;
        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            ptr
        });
        let original = ptr;

        let ptr =
            account.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
        assert!(!ptr.is_null());
        assert_ne!(
            ptr, original,
            "vendored aligned realloc must move when this growth needs a larger native block"
        );
        assert_eq!(account.live_bytes(), new_layout.size() as u64);
        assert_eq!((ptr as usize) % new_layout.align(), 0);
        assert!((0..old_layout.size()).all(|index| unsafe { *ptr.add(index) == 0x5a }));

        unsafe { allocator.dealloc(ptr, new_layout) };
        assert_eq!(account.live_bytes(), 0);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn successful_realloc_to_unowned_debits_the_origin_account() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let account = MemoryBudgetAccount::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;

        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            ptr
        });
        assert_eq!(account.live_bytes(), 16);

        let ptr = unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) };
        assert!(!ptr.is_null());
        assert_eq!(account.live_bytes(), 0);
        assert_eq!((ptr as usize) % new_layout.align(), 0);
        unsafe { allocator.dealloc(ptr, new_layout) };
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_account_outlives_its_vm_handle_while_blocks_are_live(
    ) -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(32, 8)?;
        let ptr = {
            let account = MemoryBudgetAccount::new();
            account.with_scope(|| {
                let ptr = unsafe { Mimalloc.alloc(layout) };
                assert!(!ptr.is_null());
                ptr
            })
        };

        unsafe { Mimalloc.dealloc(ptr, layout) };
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_scope_restores_nested_accounts_after_unwind() -> Result<(), Box<dyn Error>>
    {
        let allocator = Mimalloc;
        let outer = MemoryBudgetAccount::new();
        let inner = MemoryBudgetAccount::new();
        let layout = Layout::from_size_align(8, 8)?;

        let outer_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            outer.with_scope(|| {
                let outer_ptr = unsafe { allocator.alloc(layout) };
                assert!(!outer_ptr.is_null());
                assert_eq!(outer.live_bytes(), 8);

                let inner_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    inner.with_scope(|| {
                        let inner_ptr = unsafe { allocator.alloc(layout) };
                        assert!(!inner_ptr.is_null());
                        assert_eq!(inner.live_bytes(), 8);
                        unsafe { allocator.dealloc(inner_ptr, layout) };
                        panic!("inner scope unwind");
                    });
                }));
                assert!(inner_result.is_err());
                assert_eq!(inner.live_bytes(), 0);
                assert_eq!(outer.live_bytes(), 8);
                unsafe { allocator.dealloc(outer_ptr, layout) };
                panic!("outer scope unwind");
            });
        }));

        assert!(outer_result.is_err());
        assert_eq!(outer.live_bytes(), 0);
        assert_eq!(inner.live_bytes(), 0);
        let unowned = unsafe { allocator.alloc(layout) };
        assert!(!unowned.is_null());
        assert_eq!(outer.live_bytes(), 0);
        assert_eq!(inner.live_bytes(), 0);
        unsafe { allocator.dealloc(unowned, layout) };
        Ok(())
    }
}

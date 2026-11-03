// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::c_void;
use core::ptr;
use mimalloc_sys::{
    mi_free, mi_malloc_aligned, mi_realloc_aligned, mi_zalloc_aligned, MI_ALIGNMENT_MAX,
};

#[cfg(feature = "allocator-memory-limits")]
pub use crate::limits::{
    allocation_stats_snapshot, current_thread_allocation_stats, current_thread_live_bytes,
    flush_thread_counters, global_allocation_stats_snapshot, record_alloc, record_free,
    set_thread_flush_threshold, GlobalAllocationStats, MemoryBudgetUsage, ThreadAllocationStats,
};

#[cfg(feature = "allocator-memory-limits")]
use crate::limits::record_memory_budget_alloc;

pub struct Mimalloc;

unsafe impl GlobalAlloc for Mimalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        let ptr = mi_malloc_aligned(layout.size(), layout.align()).cast::<u8>();
        #[cfg(feature = "allocator-memory-limits")]
        if !ptr.is_null() {
            record_memory_budget_alloc(layout.size());
            record_alloc(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        if ptr.is_null() {
            return;
        }
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
            record_memory_budget_alloc(layout.size());
            record_alloc(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        debug_assert!(layout.align() < MI_ALIGNMENT_MAX);
        if ptr.is_null() || Layout::from_size_align(new_size, layout.align()).is_err() {
            return ptr::null_mut();
        }

        #[cfg(all(test, feature = "allocator-memory-limits"))]
        let result = if tests::take_next_native_realloc_failure_for_test() {
            ptr::null_mut()
        } else {
            mi_realloc_aligned(ptr.cast::<c_void>(), new_size, layout.align()).cast::<u8>()
        };
        #[cfg(not(all(test, feature = "allocator-memory-limits")))]
        let result =
            mi_realloc_aligned(ptr.cast::<c_void>(), new_size, layout.align()).cast::<u8>();
        if !result.is_null() {
            #[cfg(feature = "allocator-memory-limits")]
            record_memory_budget_alloc(new_size);
            #[cfg(feature = "allocator-memory-limits")]
            {
                record_free(layout.size());
                record_alloc(new_size);
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "allocator-memory-limits")]
    use super::MemoryBudgetUsage;
    use super::*;
    use std::error::Error;

    #[cfg(feature = "allocator-memory-limits")]
    struct TestBudgetUsage {
        usage: Option<MemoryBudgetUsage>,
    }

    #[cfg(feature = "allocator-memory-limits")]
    impl Default for TestBudgetUsage {
        fn default() -> Self {
            Self {
                usage: Some(MemoryBudgetUsage::default()),
            }
        }
    }

    #[cfg(feature = "allocator-memory-limits")]
    impl TestBudgetUsage {
        fn new() -> Self {
            Self::default()
        }

        fn requested_bytes(&self) -> u64 {
            self.usage.map_or(0, MemoryBudgetUsage::requested_bytes)
        }

        fn with_scope<R>(&mut self, operation: impl FnOnce() -> R) -> R {
            let initial = self.usage;
            crate::limits::with_memory_budget_usage_scope(initial, &mut self.usage, operation)
        }
    }

    #[cfg(feature = "allocator-memory-limits")]
    fn current_requested_bytes() -> u64 {
        crate::limits::current_memory_budget_usage().map_or(0, MemoryBudgetUsage::requested_bytes)
    }

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
            if ptr.cast::<c_void>().is_null() {
                assert!(!ptr.cast::<c_void>().is_null());
            } else {
                alloc.dealloc(ptr, layout);
            }
        }
        Ok(())
    }

    #[test]
    fn memory_can_be_alloc_zeroed_and_freed() -> Result<(), Box<dyn Error>> {
        let layout = Layout::from_size_align(8, 8)?;
        let alloc = Mimalloc;

        unsafe {
            let ptr = alloc.alloc_zeroed(layout);
            if ptr.cast::<c_void>().is_null() {
                assert!(!ptr.cast::<c_void>().is_null());
            } else {
                alloc.dealloc(ptr, layout);
            }
        }
        Ok(())
    }

    #[cfg(all(feature = "allocator-memory-limits", target_pointer_width = "64"))]
    #[test]
    fn allocator_preserves_zeroed_aligned_reallocations() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let alignments = [1, 8, 16, 64, 256];

        for align in alignments {
            let old_layout = Layout::from_size_align(17, align)?;
            let ptr = unsafe { allocator.alloc_zeroed(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                assert_eq!((ptr as usize) % align, 0);
                assert!((0..old_layout.size()).all(|index| unsafe { *ptr.add(index) == 0 }));
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };

                let new_size = 33;
                let ptr = unsafe { allocator.realloc(ptr, old_layout, new_size) };
                if ptr.is_null() {
                    assert!(!ptr.is_null());
                } else {
                    assert_eq!((ptr as usize) % align, 0);
                    assert!((0..old_layout.size()).all(|index| unsafe { *ptr.add(index) == 0x5a }));

                    unsafe { allocator.dealloc(ptr, Layout::from_size_align(new_size, align)?) };
                }
            }
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
    fn execution_budget_tracks_requests_in_active_scopes_across_threads(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut outer = TestBudgetUsage::new();
        let mut inner = TestBudgetUsage::default();
        let unowned_layout = Layout::from_size_align(11, 8)?;
        let outer_layout = Layout::from_size_align(13, 8)?;
        let inner_layout = Layout::from_size_align(19, 64)?;
        let after_inner_layout = Layout::from_size_align(7, 8)?;

        let unowned = unsafe { allocator.alloc(unowned_layout) };
        assert!(!unowned.is_null());
        let (outer_ptr, after_inner_ptr, inner_ptr) = outer.with_scope(|| {
            let outer_ptr = unsafe { allocator.alloc(outer_layout) };
            assert!(!outer_ptr.is_null());
            assert_eq!(current_requested_bytes(), 13);

            let inner_ptr = inner.with_scope(|| unsafe { allocator.alloc_zeroed(inner_layout) });
            assert!(!inner_ptr.is_null());

            assert_eq!(current_requested_bytes(), 13);
            assert_eq!(inner.requested_bytes(), 19);
            assert_eq!((inner_ptr as usize) % 64, 0);
            assert!((0..19).all(|offset| unsafe { *inner_ptr.add(offset) == 0 }));

            let after_inner_ptr = unsafe { allocator.alloc(after_inner_layout) };
            assert!(!after_inner_ptr.is_null());
            assert_eq!(current_requested_bytes(), 20);
            unsafe { allocator.dealloc(unowned, unowned_layout) };
            assert_eq!(current_requested_bytes(), 20);
            (outer_ptr, after_inner_ptr, inner_ptr)
        });

        let inner_address = inner_ptr as usize;
        std::thread::spawn(move || unsafe {
            Mimalloc.dealloc(inner_address as *mut u8, inner_layout);
        })
        .join()
        .expect("cross-thread free");
        assert_eq!(inner.requested_bytes(), 19);

        unsafe {
            allocator.dealloc(outer_ptr, outer_layout);
            allocator.dealloc(after_inner_ptr, after_inner_layout);
        }
        assert_eq!(outer.requested_bytes(), 20);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_counts_gross_requests_at_the_exact_boundary() -> Result<(), Box<dyn Error>>
    {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let limit = 32_u64;
        let layout = Layout::from_size_align(limit as usize, 8)?;
        let extra_layout = Layout::from_size_align(1, 8)?;

        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(layout) };
            assert!(!ptr.is_null());
            assert_eq!(current_requested_bytes(), limit);
            assert!(current_requested_bytes() <= limit);

            let extra = unsafe { allocator.alloc(extra_layout) };
            assert!(!extra.is_null());
            assert_eq!(current_requested_bytes(), limit + 1);
            assert!(current_requested_bytes() > limit);
            unsafe { allocator.dealloc(extra, extra_layout) };
            assert_eq!(current_requested_bytes(), limit + 1);
            ptr
        });

        let alias = ptr;
        unsafe { allocator.dealloc(alias, layout) };
        assert_eq!(account.requested_bytes(), limit + 1);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn successful_realloc_charges_current_account_and_failure_charges_nothing(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut first = TestBudgetUsage::new();
        let mut second = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;

        let mut ptr = first.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            }
            ptr
        });
        if ptr.is_null() {
            assert!(!ptr.is_null());
        } else {
            assert_eq!(first.requested_bytes(), 16);

            let live_bytes_before_failure = current_thread_live_bytes();
            let failed =
                second.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, usize::MAX) });
            assert!(failed.is_null());
            assert_eq!(first.requested_bytes(), 16);
            assert_eq!(second.requested_bytes(), 0);
            assert_eq!(current_thread_live_bytes() - live_bytes_before_failure, 0);
            assert!((0..16).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

            ptr = second
                .with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                assert_eq!(first.requested_bytes(), 16);
                assert_eq!(second.requested_bytes(), 64);
                assert_eq!((ptr as usize) % new_layout.align(), 0);
                assert!((0..16).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

                unsafe { allocator.dealloc(ptr, new_layout) };
                assert_eq!(second.requested_bytes(), 64);
            }
        }
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn injected_native_realloc_failure_is_one_shot_without_accounting_side_effects(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut first = TestBudgetUsage::new();
        let mut current = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;
        let live_bytes_before = current_thread_live_bytes();

        let ptr = first.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            }
            ptr
        });
        if ptr.is_null() {
            assert!(!ptr.is_null());
        } else {
            assert_eq!(first.requested_bytes(), old_layout.size() as u64);
            assert_eq!(current.requested_bytes(), 0);

            let failure = FailNextNativeReallocGuard::arm();
            let result = current
                .with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
            drop(failure);
            if !result.is_null() {
                unsafe { allocator.dealloc(result, new_layout) };
            }
            assert!(
                result.is_null(),
                "the fail-next test hook should force the native null-result path"
            );
            assert_eq!(first.requested_bytes(), old_layout.size() as u64);
            assert_eq!(current.requested_bytes(), 0);
            assert_eq!(
                current_thread_live_bytes() - live_bytes_before,
                i64::try_from(old_layout.size())?
            );
            assert!((0..old_layout.size()).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

            unsafe { allocator.dealloc(ptr, old_layout) };

            let next = current.with_scope(|| {
                let ptr = unsafe { allocator.alloc(old_layout) };
                if ptr.is_null() {
                    assert!(!ptr.is_null());
                } else {
                    unsafe { ptr.write_bytes(0x6b, old_layout.size()) };
                }
                ptr
            });
            if next.is_null() {
                assert!(!next.is_null());
            } else {
                let next = current.with_scope(|| unsafe {
                    allocator.realloc(next, old_layout, new_layout.size())
                });
                if next.is_null() {
                    assert!(!next.is_null());
                } else {
                    assert_eq!(
                        current.requested_bytes(),
                        (old_layout.size() + new_layout.size()) as u64
                    );
                    assert!(
                        (0..old_layout.size()).all(|offset| unsafe { *next.add(offset) == 0x6b })
                    );
                    unsafe { allocator.dealloc(next, new_layout) };
                    assert_eq!(
                        current.requested_bytes(),
                        (old_layout.size() + new_layout.size()) as u64
                    );
                    assert_eq!(current_thread_live_bytes() - live_bytes_before, 0);
                }
            }
        }
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn realloc_charges_each_success_to_its_current_execution_scope() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut first = TestBudgetUsage::new();
        let mut second = TestBudgetUsage::new();
        let mut third = TestBudgetUsage::new();
        let mut layout = Layout::from_size_align(23, 64)?;
        let mut ptr = first.with_scope(|| {
            let ptr = unsafe { allocator.alloc(layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                unsafe { ptr.write_bytes(0x5a, layout.size()) };
            }
            ptr
        });

        let transitions: [(Option<usize>, usize, u64, u64, u64); 6] = [
            (Some(0), 47, 70, 0, 0),
            (Some(1), 31, 70, 31, 0),
            (None, 63, 70, 31, 0),
            (None, 55, 70, 31, 0),
            (Some(2), 77, 70, 31, 77),
            (Some(2), 51, 70, 31, 128),
        ];
        for (next_owner, new_size, first_total, second_total, third_total) in transitions {
            let live_bytes_before_realloc = current_thread_live_bytes();
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                ptr =
                    if let Some(next_owner) = next_owner {
                        match next_owner {
                            0 => first
                                .with_scope(|| unsafe { allocator.realloc(ptr, layout, new_size) }),
                            1 => second
                                .with_scope(|| unsafe { allocator.realloc(ptr, layout, new_size) }),
                            _ => third
                                .with_scope(|| unsafe { allocator.realloc(ptr, layout, new_size) }),
                        }
                    } else {
                        unsafe { allocator.realloc(ptr, layout, new_size) }
                    };
                if ptr.is_null() {
                    assert!(!ptr.is_null());
                } else {
                    assert_eq!((ptr as usize) % layout.align(), 0);
                    assert!((0..23).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));
                    let expected_live_bytes_delta =
                        i64::try_from(new_size)? - i64::try_from(layout.size())?;
                    assert_eq!(
                        current_thread_live_bytes() - live_bytes_before_realloc,
                        expected_live_bytes_delta
                    );

                    layout = Layout::from_size_align(new_size, layout.align())?;
                    assert_eq!(first.requested_bytes(), first_total);
                    assert_eq!(second.requested_bytes(), second_total);
                    assert_eq!(third.requested_bytes(), third_total);
                }
            }
        }

        if ptr.is_null() {
            assert!(!ptr.is_null());
        } else {
            unsafe { allocator.dealloc(ptr, layout) };
            assert_eq!(third.requested_bytes(), 128);
        }
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn realloc_charges_the_active_account_after_thread_migration() -> Result<(), Box<dyn Error>> {
        let mut first = TestBudgetUsage::new();
        let second = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(17, 64)?;
        let new_layout = Layout::from_size_align(257, 64)?;
        let ptr = first.with_scope(|| {
            let ptr = unsafe { Mimalloc.alloc(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            }
            ptr
        });
        if ptr.is_null() {
            assert!(!ptr.is_null());
        } else {
            let address = ptr as usize;
            let worker_account = second;
            let (sender, receiver) = std::sync::mpsc::channel();
            let worker = std::thread::spawn(move || {
                let mut worker_account = worker_account;
                let ptr = address as *mut u8;
                if ptr.is_null() {
                    assert!(!ptr.is_null());
                } else {
                    let ptr = worker_account.with_scope(|| unsafe {
                        Mimalloc.realloc(ptr, old_layout, new_layout.size())
                    });
                    sender
                        .send((ptr as usize, worker_account))
                        .expect("send reallocated pointer");
                }
            });
            worker.join().expect("cross-thread realloc");
            let (address, second) = receiver.recv().expect("receive reallocated pointer");
            let ptr = address as *mut u8;

            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                assert_eq!(first.requested_bytes(), old_layout.size() as u64);
                assert_eq!(second.requested_bytes(), new_layout.size() as u64);
                assert_eq!((ptr as usize) % new_layout.align(), 0);
                assert!((0..old_layout.size()).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

                let address = ptr as usize;
                let (sender, receiver) = std::sync::mpsc::channel();
                let freer = std::thread::spawn(move || {
                    let ptr = address as *mut u8;
                    if ptr.is_null() {
                        assert!(!ptr.is_null());
                    } else {
                        unsafe { Mimalloc.dealloc(ptr, new_layout) };
                    }
                    sender.send(()).expect("send free completion");
                });
                receiver.recv().expect("receive free completion");
                freer.join().expect("cross-thread free");
                assert_eq!(second.requested_bytes(), new_layout.size() as u64);
            }
        }
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn native_aligned_realloc_reuses_a_same_bin_shrink() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(32, 8)?;
        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            }
            ptr
        });

        if ptr.is_null() {
            assert!(!ptr.is_null());
        } else {
            // This characterizes vendored mimalloc's same-bin shrink, not GlobalAlloc pointer stability.
            let original = ptr;
            let ptr = account.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, 31) });
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                assert_eq!(ptr, original);
                assert_eq!(account.requested_bytes(), 63);
                assert!((0..31).all(|offset| unsafe { *ptr.add(offset) == 0x5a }));

                unsafe { allocator.dealloc(ptr, Layout::from_size_align(31, 8)?) };
                assert_eq!(account.requested_bytes(), 63);
            }
        }
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn native_aligned_realloc_moves_for_small_to_large_growth() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(17, 16)?;
        let new_layout = Layout::from_size_align(1024, 16)?;
        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                unsafe { ptr.write_bytes(0x5a, old_layout.size()) };
            }
            ptr
        });
        if ptr.is_null() {
            assert!(!ptr.is_null());
        } else {
            let original = ptr;
            let ptr = account
                .with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
            if ptr.is_null() {
                assert!(!ptr.is_null());
            } else {
                assert_ne!(
                    ptr, original,
                    "vendored aligned realloc must move when this growth needs a larger native block"
                );
                assert_eq!(
                    account.requested_bytes(),
                    (old_layout.size() + new_layout.size()) as u64
                );
                assert_eq!((ptr as usize) % new_layout.align(), 0);
                assert!((0..old_layout.size()).all(|index| unsafe { *ptr.add(index) == 0x5a }));

                unsafe { allocator.dealloc(ptr, new_layout) };
                assert_eq!(
                    account.requested_bytes(),
                    (old_layout.size() + new_layout.size()) as u64
                );
            }
        }
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn unowned_realloc_does_not_change_the_execution_account() -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;

        let ptr = account.with_scope(|| {
            let ptr = unsafe { allocator.alloc(old_layout) };
            assert!(!ptr.is_null());
            ptr
        });
        assert_eq!(account.requested_bytes(), 16);

        let ptr = unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) };
        assert!(!ptr.is_null());
        assert_eq!(account.requested_bytes(), 16);
        assert_eq!((ptr as usize) % new_layout.align(), 0);
        unsafe { allocator.dealloc(ptr, new_layout) };
        assert_eq!(account.requested_bytes(), 16);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_counts_requested_bytes_after_blocks_are_freed() -> Result<(), Box<dyn Error>>
    {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let layout = Layout::from_size_align(64, 8)?;

        account.with_scope(|| {
            let first = unsafe { allocator.alloc(layout) };
            assert!(!first.is_null());
            unsafe { allocator.dealloc(first, layout) };

            let second = unsafe { allocator.alloc(layout) };
            assert!(!second.is_null());
            unsafe { allocator.dealloc(second, layout) };
        });

        assert_eq!(account.requested_bytes(), 128);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_counts_zeroed_allocations_after_blocks_are_freed(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let layout = Layout::from_size_align(64, 8)?;

        account.with_scope(|| {
            let first = unsafe { allocator.alloc_zeroed(layout) };
            assert!(!first.is_null());
            assert!((0..layout.size()).all(|index| unsafe { *first.add(index) == 0 }));
            unsafe { allocator.dealloc(first, layout) };

            let second = unsafe { allocator.alloc_zeroed(layout) };
            assert!(!second.is_null());
            unsafe { allocator.dealloc(second, layout) };
        });

        assert_eq!(account.requested_bytes(), 128);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_realloc_counts_full_new_size_only_after_success(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut account = TestBudgetUsage::new();
        let old_layout = Layout::from_size_align(16, 16)?;
        let new_layout = Layout::from_size_align(64, 16)?;
        let ptr = account.with_scope(|| unsafe { allocator.alloc(old_layout) });
        assert!(!ptr.is_null());
        assert_eq!(account.requested_bytes(), 16);

        let failed = account.with_scope(|| {
            let _failure = FailNextNativeReallocGuard::arm();
            unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) }
        });
        assert!(failed.is_null());
        assert_eq!(account.requested_bytes(), 16);

        let resized =
            account.with_scope(|| unsafe { allocator.realloc(ptr, old_layout, new_layout.size()) });
        assert!(!resized.is_null());
        assert_eq!(account.requested_bytes(), 80);
        unsafe { allocator.dealloc(resized, new_layout) };
        assert_eq!(account.requested_bytes(), 80);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_survives_cross_thread_free_and_account_migration(
    ) -> Result<(), Box<dyn Error>> {
        let mut account = TestBudgetUsage::new();
        let layout = Layout::from_size_align(64, 8)?;
        let first_address = account.with_scope(|| unsafe { Mimalloc.alloc(layout) }) as usize;
        assert_ne!(first_address, 0);

        let (account, second_address) = std::thread::spawn(move || {
            let mut account = account;
            unsafe { Mimalloc.dealloc(first_address as *mut u8, layout) };
            let second = account.with_scope(|| unsafe { Mimalloc.alloc(layout) });
            assert!(!second.is_null());
            (account, second as usize)
        })
        .join()
        .expect("allocation account migrates to another thread");

        assert_eq!(account.requested_bytes(), 128);
        unsafe { Mimalloc.dealloc(second_address as *mut u8, layout) };
        assert_eq!(account.requested_bytes(), 128);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_scopes_restore_parent_and_exclude_unowned_allocations(
    ) -> Result<(), Box<dyn Error>> {
        let allocator = Mimalloc;
        let mut outer = TestBudgetUsage::new();
        let mut inner = TestBudgetUsage::new();
        let layout = Layout::from_size_align(8, 8)?;

        outer.with_scope(|| {
            let outer_ptr = unsafe { allocator.alloc(layout) };
            assert!(!outer_ptr.is_null());

            crate::limits::with_unowned_memory_budget_scope(|| {
                let unowned = unsafe { allocator.alloc(layout) };
                assert!(!unowned.is_null());
                unsafe { allocator.dealloc(unowned, layout) };
            });

            let inner_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                inner.with_scope(|| {
                    let inner_ptr = unsafe { allocator.alloc(layout) };
                    assert!(!inner_ptr.is_null());
                    unsafe { allocator.dealloc(inner_ptr, layout) };
                    panic!("inner scope unwind");
                });
            }));
            assert!(inner_result.is_err());
            assert_eq!(inner.requested_bytes(), 8);
            assert_eq!(current_requested_bytes(), 8);

            let after_unwind = unsafe { allocator.alloc(layout) };
            assert!(!after_unwind.is_null());
            assert_eq!(current_requested_bytes(), 16);
            unsafe {
                allocator.dealloc(outer_ptr, layout);
                allocator.dealloc(after_unwind, layout);
            }
            assert_eq!(current_requested_bytes(), 16);
        });

        assert_eq!(outer.requested_bytes(), 16);
        assert_eq!(inner.requested_bytes(), 8);
        Ok(())
    }

    #[cfg(feature = "allocator-memory-limits")]
    #[test]
    fn execution_budget_scope_restores_nested_accounts_after_unwind() -> Result<(), Box<dyn Error>>
    {
        let allocator = Mimalloc;
        let mut outer = TestBudgetUsage::new();
        let mut inner = TestBudgetUsage::new();
        let layout = Layout::from_size_align(8, 8)?;

        let outer_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            outer.with_scope(|| {
                let outer_ptr = unsafe { allocator.alloc(layout) };
                assert!(!outer_ptr.is_null());
                assert_eq!(current_requested_bytes(), 8);

                let inner_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    inner.with_scope(|| {
                        let inner_ptr = unsafe { allocator.alloc(layout) };
                        assert!(!inner_ptr.is_null());
                        assert_eq!(current_requested_bytes(), 8);
                        unsafe { allocator.dealloc(inner_ptr, layout) };
                        panic!("inner scope unwind");
                    });
                }));
                assert!(inner_result.is_err());
                assert_eq!(inner.requested_bytes(), 8);
                assert_eq!(current_requested_bytes(), 8);
                unsafe { allocator.dealloc(outer_ptr, layout) };
                assert_eq!(current_requested_bytes(), 8);
                panic!("outer scope unwind");
            });
        }));

        assert!(outer_result.is_err());
        assert_eq!(outer.requested_bytes(), 8);
        assert_eq!(inner.requested_bytes(), 8);
        let unowned = unsafe { allocator.alloc(layout) };
        assert!(!unowned.is_null());
        assert_eq!(outer.requested_bytes(), 8);
        assert_eq!(inner.requested_bytes(), 8);
        unsafe { allocator.dealloc(unowned, layout) };
        Ok(())
    }
}

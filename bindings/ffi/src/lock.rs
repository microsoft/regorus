// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Abstractions over synchronization primitives used by the FFI layer.
//!
//! For `std` builds we rely on `parking_lot::RwLock` so we can detect
//! contention across threads. For `no_std` builds we fall back to
//! `RefCell`, which still lets us detect aliasing within a single thread.

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(all(feature = "std", feature = "contention_checks"))]
mod locking {
    use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};
    use std::sync::Arc;

    pub(crate) type Handle<T> = Arc<RwLock<T>>;
    pub(crate) type ReadGuard<'a, T> = RwLockReadGuard<'a, T>;
    pub(crate) type WriteGuard<'a, T> = RwLockWriteGuard<'a, T>;

    #[inline]
    pub(crate) fn new_handle<T>(value: T) -> Handle<T> {
        Arc::new(RwLock::new(value))
    }

    #[inline]
    pub(crate) fn try_write<'a, T>(handle: &'a Handle<T>) -> Option<WriteGuard<'a, T>> {
        handle.try_write()
    }

    #[inline]
    pub(crate) fn try_read<'a, T>(handle: &'a Handle<T>) -> Option<ReadGuard<'a, T>> {
        handle.try_read()
    }

    #[inline]
    pub(crate) fn read<'a, T>(handle: &'a Handle<T>) -> ReadGuard<'a, T> {
        handle.read()
    }
}

#[cfg(all(feature = "std", not(feature = "contention_checks")))]
mod locking {
    use std::cell::{Ref, RefCell, RefMut};
    use std::rc::Rc;

    pub(crate) type Handle<T> = Rc<RefCell<T>>;
    pub(crate) type ReadGuard<'a, T> = Ref<'a, T>;
    pub(crate) type WriteGuard<'a, T> = RefMut<'a, T>;

    #[inline]
    pub(crate) fn new_handle<T>(value: T) -> Handle<T> {
        Rc::new(RefCell::new(value))
    }

    #[inline]
    pub(crate) fn try_write<'a, T>(handle: &'a Handle<T>) -> Option<WriteGuard<'a, T>> {
        handle.try_borrow_mut().ok()
    }

    #[inline]
    pub(crate) fn try_read<'a, T>(handle: &'a Handle<T>) -> Option<ReadGuard<'a, T>> {
        handle.try_borrow().ok()
    }

    #[inline]
    pub(crate) fn read<'a, T>(handle: &'a Handle<T>) -> ReadGuard<'a, T> {
        handle.borrow()
    }
}

#[cfg(not(feature = "std"))]
mod locking {
    use alloc::rc::Rc;
    use core::cell::{Ref, RefCell, RefMut};

    pub(crate) type Handle<T> = Rc<RefCell<T>>;
    pub(crate) type ReadGuard<'a, T> = Ref<'a, T>;
    pub(crate) type WriteGuard<'a, T> = RefMut<'a, T>;

    #[inline]
    pub(crate) fn new_handle<T>(value: T) -> Handle<T> {
        Rc::new(RefCell::new(value))
    }

    #[inline]
    pub(crate) fn try_write<'a, T>(handle: &'a Handle<T>) -> Option<WriteGuard<'a, T>> {
        handle.try_borrow_mut().ok()
    }

    #[inline]
    pub(crate) fn try_read<'a, T>(handle: &'a Handle<T>) -> Option<ReadGuard<'a, T>> {
        handle.try_borrow().ok()
    }

    #[inline]
    pub(crate) fn read<'a, T>(handle: &'a Handle<T>) -> ReadGuard<'a, T> {
        handle.borrow()
    }
}

pub(crate) use locking::{new_handle, read, try_read, try_write, Handle, ReadGuard, WriteGuard};

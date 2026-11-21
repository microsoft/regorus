// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

#[cfg(any(test, feature = "test-util"))]
std::thread_local! {
    static RESERVATION_FAILURE_AFTER: core::cell::Cell<Option<usize>> = const {
        core::cell::Cell::new(None)
    };
}

/// Restores the previous reservation-failure setting when dropped.
#[cfg(any(test, feature = "test-util"))]
pub struct ReservationFailureGuard(Option<usize>);

#[cfg(any(test, feature = "test-util"))]
impl Drop for ReservationFailureGuard {
    fn drop(&mut self) {
        RESERVATION_FAILURE_AFTER.with(|remaining| remaining.set(self.0));
    }
}

/// Makes this thread's reservations fail after `successful` more succeed.
#[cfg(any(test, feature = "test-util"))]
pub fn fail_reservations_after(successful: usize) -> ReservationFailureGuard {
    ReservationFailureGuard(
        RESERVATION_FAILURE_AFTER.with(|remaining| remaining.replace(Some(successful))),
    )
}

#[cfg(any(test, feature = "test-util"))]
pub fn reservation_checkpoint() -> Result<(), alloc::collections::TryReserveError> {
    let fail = RESERVATION_FAILURE_AFTER.with(|remaining| match remaining.get() {
        None => false,
        Some(0) => true,
        Some(count) => {
            remaining.set(Some(count - 1));
            false
        }
    });
    if fail {
        Vec::<u8>::new().try_reserve(usize::MAX)
    } else {
        Ok(())
    }
}

/// Capability for native reservation observations during one history operation.
pub struct ObservationWorld;

impl ObservationWorld {
    // Native reservation may fail but must preserve every existing element.
    #[inline]
    pub fn try_reserve_vec<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        #[cfg(any(test, feature = "test-util"))]
        reservation_checkpoint()?;
        values.try_reserve(additional)
    }

    // Vec::try_reserve_exact is unsupported by Verus; reservation preserves elements.
    #[inline]
    pub fn try_reserve_vec_exact<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        #[cfg(any(test, feature = "test-util"))]
        reservation_checkpoint()?;
        values.try_reserve_exact(additional)
    }
}

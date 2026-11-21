// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

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
        values.try_reserve(additional)
    }

    // Vec::try_reserve_exact is unsupported by Verus; reservation preserves elements.
    #[inline]
    pub fn try_reserve_vec_exact<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        values.try_reserve_exact(additional)
    }
}

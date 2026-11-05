// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Allocation preflight and checked capacity growth for cooperative ceilings.

use super::global_allocation_stats_snapshot;
use core::fmt;
use std::collections::TryReserveError;

/// A requested allocation would exceed the supplied live-byte ceiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryLimitExceeded {
    /// Projected live bytes, saturated at `u64::MAX` on arithmetic overflow.
    pub usage: u64,
    /// The caller's memory ceiling in bytes.
    pub limit: u64,
}

impl fmt::Display for MemoryLimitExceeded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "memory allocation exceeds limit (usage={}, limit={})",
            self.usage, self.limit
        )
    }
}

impl std::error::Error for MemoryLimitExceeded {}

/// An error while checking or growing string capacity.
#[derive(Debug)]
pub enum ReservationError {
    /// The projected allocation exceeds the supplied ceiling.
    LimitExceeded(MemoryLimitExceeded),
    /// The requested string length cannot be represented by `usize`.
    CapacityOverflow,
    /// The allocator could not satisfy the reservation.
    Allocation(TryReserveError),
}

impl fmt::Display for ReservationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LimitExceeded(error) => error.fmt(f),
            Self::CapacityOverflow => f.write_str("memory reservation size overflow"),
            Self::Allocation(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ReservationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::LimitExceeded(error) => Some(error),
            Self::CapacityOverflow => None,
            Self::Allocation(error) => Some(error),
        }
    }
}

/// Check a proposed allocation against the caller's process-wide live-byte limit.
///
/// `bytes` is the full new allocation, including when replacing an existing block:
/// the old block is still counted as live. No memory is reserved or charged here.
/// Usage equal to the limit succeeds; arithmetic overflow always fails. Tracking
/// is cooperative, so another thread can allocate after this snapshot.
pub fn check_allocation(bytes: usize, limit: u64) -> Result<(), MemoryLimitExceeded> {
    let live = global_allocation_stats_snapshot().allocated;
    let usage = u64::try_from(bytes)
        .ok()
        .and_then(|bytes| live.checked_add(bytes));
    match usage {
        Some(usage) if usage <= limit => Ok(()),
        usage => Err(MemoryLimitExceeded {
            usage: usage.unwrap_or(u64::MAX),
            limit,
        }),
    }
}

/// Reserve room for `additional` string bytes, checking any new allocation first.
///
/// Existing spare capacity is reused without an allocation or a limit check.
/// Growth prefers geometric capacity, falling back to the exact request when
/// only that fits the ceiling. The full new block is checked while the old one
/// is still live, and tracked usage is checked again after allocation.
/// A post-allocation limit error preserves the contents but may leave increased
/// capacity; the reservation is not rolled back.
pub fn try_reserve_string(
    output: &mut String,
    additional: usize,
    limit: u64,
) -> Result<(), ReservationError> {
    if additional <= output.capacity() - output.len() {
        return Ok(());
    }
    let needed = output
        .len()
        .checked_add(additional)
        .ok_or(ReservationError::CapacityOverflow)?;
    let growing = needed.max(output.capacity().saturating_mul(2));
    let capacity = if check_allocation(growing, limit).is_ok() {
        growing
    } else {
        check_allocation(needed, limit).map_err(ReservationError::LimitExceeded)?;
        needed
    };
    output
        .try_reserve_exact(capacity - output.len())
        .map_err(ReservationError::Allocation)?;
    check_allocation(0, limit).map_err(ReservationError::LimitExceeded)
}

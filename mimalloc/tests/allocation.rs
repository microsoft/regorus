// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(all(
    feature = "allocator-memory-limits",
    not(any(target_family = "wasm", miri))
))]

use mimalloc::limits::{check_allocation, try_reserve_string, ReservationError};
use regorus_mimalloc as mimalloc;

regorus_mimalloc::assign_global!();

#[test]
fn preflight_rejection_preserves_the_existing_string_and_capacity() {
    let mut output = String::from("λ-prefix");
    let capacity = output.capacity();
    let error = try_reserve_string(&mut output, 1024 * 1024, 0).unwrap_err();
    assert!(matches!(error, ReservationError::LimitExceeded(error) if error.limit == 0));
    assert_eq!(output, "λ-prefix");
    assert_eq!(output.capacity(), capacity);
}

#[test]
fn successful_reservation_preserves_utf8_and_leaves_room_for_the_suffix() {
    let mut output = String::from("λ-prefix");
    let suffix = "-😀-suffix";
    try_reserve_string(&mut output, suffix.len(), u64::MAX).unwrap();
    let capacity = output.capacity();
    output.push_str(suffix);
    assert_eq!(output, "λ-prefix-😀-suffix");
    assert_eq!(output.capacity(), capacity);
}

#[test]
fn overflowing_reservation_fails_without_changing_the_string() {
    let mut output = String::from("prefix");
    let capacity = output.capacity();
    assert!(matches!(
        try_reserve_string(&mut output, usize::MAX, u64::MAX),
        Err(ReservationError::CapacityOverflow)
    ));
    assert_eq!(output, "prefix");
    assert_eq!(output.capacity(), capacity);
}

#[test]
fn allocation_check_reports_projected_usage_before_allocating() {
    let error = check_allocation(1024 * 1024, 0).unwrap_err();
    assert_eq!(error.limit, 0);
    assert!(error.usage >= 1024 * 1024);
    check_allocation(0, u64::MAX).unwrap();
}

#[cfg(target_pointer_width = "64")]
#[test]
fn projected_usage_overflow_exceeds_even_the_maximum_limit() {
    let error = check_allocation(usize::MAX, u64::MAX).unwrap_err();
    assert_eq!(error.limit, u64::MAX);
    assert_eq!(error.usage, u64::MAX);
}

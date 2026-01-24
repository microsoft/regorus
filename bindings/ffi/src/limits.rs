// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::{RegorusResult, RegorusStatus};
use alloc::format;

#[cfg(feature = "allocator-memory-limits")]
fn some_or_none(flag: bool, value: u64) -> Option<u64> {
    if flag {
        Some(value)
    } else {
        None
    }
}

#[cfg(feature = "allocator-memory-limits")]
fn optional_u64_to_result(value: Option<u64>) -> RegorusResult {
    match value {
        Some(bytes) => {
            if bytes > i64::MAX as u64 {
                RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!(
                        "value {bytes} exceeds i64::MAX ({max}) bridge limit",
                        max = i64::MAX
                    ),
                )
            } else {
                let mut result = RegorusResult::ok_int(bytes as i64);
                result.bool_value = true;
                result
            }
        }
        None => {
            let mut result = RegorusResult::ok_void();
            result.bool_value = false;
            result
        }
    }
}

#[cfg(feature = "allocator-memory-limits")]
#[no_mangle]
pub extern "C" fn regorus_set_global_memory_limit(limit: u64, has_limit: bool) -> RegorusResult {
    ::regorus::set_global_memory_limit(some_or_none(has_limit, limit));
    RegorusResult::ok_void()
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[no_mangle]
pub extern "C" fn regorus_set_global_memory_limit(_limit: u64, _has_limit: bool) -> RegorusResult {
    feature_disabled("regorus_set_global_memory_limit")
}

#[cfg(feature = "allocator-memory-limits")]
#[no_mangle]
pub extern "C" fn regorus_get_global_memory_limit() -> RegorusResult {
    optional_u64_to_result(::regorus::global_memory_limit())
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[no_mangle]
pub extern "C" fn regorus_get_global_memory_limit() -> RegorusResult {
    feature_disabled("regorus_get_global_memory_limit")
}

#[cfg(feature = "allocator-memory-limits")]
#[no_mangle]
pub extern "C" fn regorus_check_global_memory_limit() -> RegorusResult {
    match ::regorus::check_global_memory_limit() {
        Ok(()) => RegorusResult::ok_void(),
        Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
    }
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[no_mangle]
pub extern "C" fn regorus_check_global_memory_limit() -> RegorusResult {
    feature_disabled("regorus_check_global_memory_limit")
}

#[cfg(feature = "allocator-memory-limits")]
#[no_mangle]
pub extern "C" fn regorus_flush_thread_memory_counters() -> RegorusResult {
    ::regorus::flush_thread_memory_counters();
    RegorusResult::ok_void()
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[no_mangle]
pub extern "C" fn regorus_flush_thread_memory_counters() -> RegorusResult {
    feature_disabled("regorus_flush_thread_memory_counters")
}

#[cfg(feature = "allocator-memory-limits")]
#[no_mangle]
pub extern "C" fn regorus_set_thread_flush_threshold_override(
    bytes: u64,
    has_threshold: bool,
) -> RegorusResult {
    ::regorus::set_thread_flush_threshold_override(some_or_none(has_threshold, bytes));
    RegorusResult::ok_void()
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[no_mangle]
pub extern "C" fn regorus_set_thread_flush_threshold_override(
    _bytes: u64,
    _has_threshold: bool,
) -> RegorusResult {
    feature_disabled("regorus_set_thread_flush_threshold_override")
}

#[cfg(feature = "allocator-memory-limits")]
#[no_mangle]
pub extern "C" fn regorus_get_thread_memory_flush_threshold() -> RegorusResult {
    optional_u64_to_result(::regorus::thread_memory_flush_threshold())
}

#[cfg(not(feature = "allocator-memory-limits"))]
#[no_mangle]
pub extern "C" fn regorus_get_thread_memory_flush_threshold() -> RegorusResult {
    feature_disabled("regorus_get_thread_memory_flush_threshold")
}

#[cfg(not(feature = "allocator-memory-limits"))]
fn feature_disabled(function: &str) -> RegorusResult {
    RegorusResult::err_with_message(
        RegorusStatus::InvalidArgument,
        format!("{function} unavailable: regorus built without allocator-memory-limits feature"),
    )
}

#[cfg(test)]
mod tests {
    use super::{
        optional_u64_to_result, regorus_get_global_memory_limit, regorus_set_global_memory_limit,
    };
    use crate::common::{regorus_result_drop, RegorusDataType, RegorusStatus};

    #[test]
    fn optional_some_returns_integer() {
        let result = optional_u64_to_result(Some(123));
        assert!(result.bool_value);
        assert!(matches!(result.data_type, RegorusDataType::Integer));
        assert_eq!(result.int_value, 123);
    }

    #[test]
    fn optional_none_returns_void() {
        let result = optional_u64_to_result(None);
        assert!(!result.bool_value);
        assert!(matches!(result.data_type, RegorusDataType::None));
        assert_eq!(result.int_value, 0);
    }

    #[test]
    fn ffi_roundtrips_global_limit() {
        let limit = 456_u64;
        let result = regorus_set_global_memory_limit(limit, true);
        assert!(matches!(result.status, RegorusStatus::Ok));
        regorus_result_drop(result);

        let result = regorus_get_global_memory_limit();
        assert!(matches!(result.status, RegorusStatus::Ok));
        assert!(result.bool_value);
        assert!(matches!(result.data_type, RegorusDataType::Integer));
        assert_eq!(result.int_value, 456);
        regorus_result_drop(result);

        let result = regorus_set_global_memory_limit(0, false);
        regorus_result_drop(result);
    }
}

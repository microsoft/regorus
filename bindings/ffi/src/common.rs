// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::ffi::CString;
use alloc::format;
use alloc::string::{String, ToString};
use anyhow::{anyhow, bail, Result};
use core::ffi::{c_char, c_longlong, c_void, CStr};
use core::ptr;

/// Status of a call on `RegorusEngine`.
#[repr(C)]
pub enum RegorusStatus {
    /// The operation was successful.
    Ok,

    /// The operation was unsuccessful.
    Error,

    /// Invalid data format provided.
    InvalidDataFormat,

    /// Invalid entrypoint rule specified.
    InvalidEntrypoint,

    /// Compilation failed.
    CompilationFailed,

    /// Invalid argument provided.
    InvalidArgument,

    /// Invalid module ID.
    InvalidModuleId,

    /// Invalid policy content.
    InvalidPolicy,
}

/// Type of data contained in RegorusResult
#[repr(C)]
#[allow(unused)]
pub enum RegorusDataType {
    /// No data / void
    None,
    /// String data (output field is valid)
    String,
    /// Boolean data (bool_value field is valid)  
    Boolean,
    /// Integer data (int_value field is valid)
    Integer,
    /// Pointer data (pointer_value field is valid)
    Pointer,
}

/// Result of a call on `RegorusEngine`.
///
/// Must be freed using `regorus_result_drop`.
#[repr(C)]
pub struct RegorusResult {
    /// Status
    pub(crate) status: RegorusStatus,

    /// Type of data contained in this result
    pub(crate) data_type: RegorusDataType,

    /// String output produced by the call.
    /// Valid when data_type is String. Owned by Rust.
    pub(crate) output: *mut c_char,

    /// Boolean value.
    /// Valid when data_type is Boolean.
    pub(crate) bool_value: bool,

    /// Integer value.
    /// Valid when data_type is Integer.
    pub(crate) int_value: c_longlong,

    /// Pointer value.
    /// Valid when data_type is Pointer.
    pub(crate) pointer_value: *mut c_void,

    /// Errors produced by the call.
    /// Owned by Rust.
    pub(crate) error_message: *mut c_char,
}

impl RegorusResult {
    /// Create a successful result with no data.
    pub(crate) fn ok_void() -> Self {
        Self {
            status: RegorusStatus::Ok,
            data_type: RegorusDataType::None,
            output: ptr::null_mut(),
            bool_value: false,
            int_value: 0,
            pointer_value: ptr::null_mut(),
            error_message: ptr::null_mut(),
        }
    }

    /// Create a successful result with string output.
    pub(crate) fn ok_string(output: String) -> Self {
        Self {
            status: RegorusStatus::Ok,
            data_type: RegorusDataType::String,
            output: to_c_str(output),
            bool_value: false,
            int_value: 0,
            pointer_value: ptr::null_mut(),
            error_message: ptr::null_mut(),
        }
    }

    /// Create a successful result with boolean value.
    #[allow(unused)]
    pub(crate) fn ok_bool(value: bool) -> Self {
        Self {
            status: RegorusStatus::Ok,
            data_type: RegorusDataType::Boolean,
            output: ptr::null_mut(),
            bool_value: value,
            int_value: 0,
            pointer_value: ptr::null_mut(),
            error_message: ptr::null_mut(),
        }
    }

    /// Create a successful result with integer value.
    #[allow(unused)]
    pub(crate) fn ok_int(value: i64) -> Self {
        Self {
            status: RegorusStatus::Ok,
            data_type: RegorusDataType::Integer,
            output: ptr::null_mut(),
            bool_value: false,
            int_value: value as c_longlong,
            pointer_value: ptr::null_mut(),
            error_message: ptr::null_mut(),
        }
    }

    /// Create a successful result with pointer value.
    pub(crate) fn ok_pointer(pointer: *mut c_void) -> Self {
        Self {
            status: RegorusStatus::Ok,
            data_type: RegorusDataType::Pointer,
            output: ptr::null_mut(),
            bool_value: false,
            int_value: 0,
            pointer_value: pointer,
            error_message: ptr::null_mut(),
        }
    }

    /// Create an error result with specific status.
    pub(crate) fn err(status: RegorusStatus) -> Self {
        Self {
            status,
            data_type: RegorusDataType::None,
            output: ptr::null_mut(),
            bool_value: false,
            int_value: 0,
            pointer_value: ptr::null_mut(),
            error_message: ptr::null_mut(),
        }
    }

    /// Create an error result with status and message.
    pub(crate) fn err_with_message(status: RegorusStatus, message: String) -> Self {
        Self {
            status,
            data_type: RegorusDataType::None,
            output: ptr::null_mut(),
            bool_value: false,
            int_value: 0,
            pointer_value: ptr::null_mut(),
            error_message: to_c_str(message),
        }
    }
}

pub(crate) fn to_c_str(s: String) -> *mut c_char {
    match CString::new(s) {
        Ok(cs) => cs.into_raw(),
        _ => to_c_str("binding error: failed to create c-style string".to_string()),
    }
}

pub(crate) fn from_c_str(s: *const c_char) -> Result<String> {
    if s.is_null() {
        bail!("null pointer");
    }
    unsafe {
        CStr::from_ptr(s)
            .to_str()
            .map_err(|e| anyhow!("invalid utf8: {e}"))
            .map(|s| s.to_string())
    }
}

pub(crate) fn to_ref<'a, T>(t: *mut T) -> Result<&'a mut T> {
    unsafe { t.as_mut().ok_or_else(|| anyhow!("null pointer")) }
}

pub(crate) fn to_regorus_result(r: Result<()>) -> RegorusResult {
    match r {
        Ok(()) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{e}")),
    }
}

pub(crate) fn to_regorus_string_result(r: Result<String>) -> RegorusResult {
    match r {
        Ok(s) => RegorusResult::ok_string(s),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{e}")),
    }
}

/// Drop a `RegorusResult`.
///
/// `output` and `error_message` strings are not valid after drop.
#[no_mangle]
pub extern "C" fn regorus_result_drop(r: RegorusResult) {
    unsafe {
        if !r.error_message.is_null() {
            let _ = CString::from_raw(r.error_message);
        }
        if !r.output.is_null() {
            let _ = CString::from_raw(r.output);
        }
    }
}

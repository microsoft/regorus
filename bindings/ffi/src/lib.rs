// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, bail, Result};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

/// Status of a call on `RegorusEngine`.
#[repr(C)]
pub enum RegorusStatus {
    /// The operation was successful.
    RegorusStatusOk,

    /// The operation was unsuccessful.
    RegorusStatusError,
}

/// Result of a call on `RegorusEngine`.
///
/// Must be freed using `regorus_result_drop`.
#[repr(C)]
pub struct RegorusResult {
    /// Status
    status: RegorusStatus,

    /// Output produced by the call.
    /// Owned by Rust.
    output: *mut c_char,

    /// Errors produced by the call.
    /// Owned by Rust.
    error_message: *mut c_char,
}

fn to_c_str(s: String) -> *mut c_char {
    match CString::new(s) {
        Ok(cs) => cs.into_raw(),
        _ => to_c_str("binding error: failed to create c-style string".to_string()),
    }
}

fn from_c_str(s: *const c_char) -> Result<String> {
    if s.is_null() {
        bail!("null pointer");
    }
    unsafe {
        CStr::from_ptr(s)
            .to_str()
            .map_err(|_| anyhow!("`path`: invalid utf8"))
            .map(|s| s.to_string())
    }
}

fn to_ref<T>(t: &*mut T) -> Result<&mut T> {
    unsafe { t.as_mut().ok_or_else(|| anyhow!("null pointer")) }
}

fn to_regorus_result(r: Result<()>) -> RegorusResult {
    match r {
        Ok(()) => RegorusResult {
            status: RegorusStatus::RegorusStatusOk,
            output: std::ptr::null_mut(),
            error_message: std::ptr::null_mut(),
        },
        Err(e) => RegorusResult {
            status: RegorusStatus::RegorusStatusError,
            output: std::ptr::null_mut(),
            error_message: to_c_str(format!("{e}")),
        },
    }
}

/// Wrapper for `regorus::Engine`.
#[derive(Clone)]
pub struct RegorusEngine {
    engine: ::regorus::Engine,
}

/// Drop a `RegorusResult`.
///
/// `output` and `error_message` strings are not valid after drop.
#[no_mangle]
pub extern "C" fn regorus_result_drop(r: RegorusResult) {
    if !r.error_message.is_null() {
        unsafe {
            let _ = CString::from_raw(r.error_message);
        }
    }
}

#[no_mangle]
/// Construct a new Engine
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html
pub extern "C" fn regorus_engine_new() -> *mut RegorusEngine {
    let engine = ::regorus::Engine::new();
    Box::into_raw(Box::new(RegorusEngine { engine }))
}

/// Clone a [`RegorusEngine`]
///
/// To avoid having to parse same policy again, the engine can be cloned
/// after policies and data have been added.
#[no_mangle]
pub extern "C" fn regorus_engine_clone(engine: *mut RegorusEngine) -> *mut RegorusEngine {
    unsafe {
        if engine.is_null() {
            return std::ptr::null_mut();
        }
        Box::into_raw(Box::new((*engine).clone()))
    }
}

#[no_mangle]
pub extern "C" fn regorus_engine_drop(engine: *mut RegorusEngine) {
    if !engine.is_null() {
        unsafe {
            let _ = Box::from_raw(engine);
        }
    }
}

/// Add a policy
///
/// The policy is parsed into AST.
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_policy
///
/// * `path`: A filename to be associated with the policy.
/// * `rego`: Rego policy.
#[no_mangle]
pub extern "C" fn regorus_engine_add_policy(
    engine: *mut RegorusEngine,
    path: *const c_char,
    rego: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .add_policy(from_c_str(path)?, from_c_str(rego)?)
    }())
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_add_policy_from_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .add_policy_from_file(from_c_str(path)?)
    }())
}

/// Add policy data.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
/// * `data`: JSON encoded value to be used as policy data.
#[no_mangle]
pub extern "C" fn regorus_engine_add_data_json(
    engine: *mut RegorusEngine,
    data: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .add_data(regorus::Value::from_json_str(&from_c_str(data)?)?)
    }())
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_add_data_from_json_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .add_data(regorus::Value::from_json_file(&from_c_str(path)?)?)
    }())
}

/// Clear policy data.
///
/// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.clear_data
#[no_mangle]
pub extern "C" fn regorus_engine_clear_data(engine: *mut RegorusEngine) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?.engine.clear_data();
        Ok(())
    }())
}

/// Set input.
///
/// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.set_input
/// * `input`: JSON encoded value to be used as input to query.
#[no_mangle]
pub extern "C" fn regorus_engine_set_input_json(
    engine: *mut RegorusEngine,
    input: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .set_input(regorus::Value::from_json_str(&from_c_str(input)?)?);
        Ok(())
    }())
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_set_input_from_json_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .set_input(regorus::Value::from_json_file(&from_c_str(path)?)?);
        Ok(())
    }())
}

/// Evaluate query.
///
/// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.eval_query
/// * `query`: Rego expression to be evaluate.
#[no_mangle]
pub extern "C" fn regorus_engine_eval_query(
    engine: *mut RegorusEngine,
    query: *const c_char,
) -> RegorusResult {
    let output = || -> Result<String> {
        let results = to_ref(&engine)?
            .engine
            .eval_query(from_c_str(query)?, false)?;
        Ok(serde_json::to_string_pretty(&results)?)
    }();
    match output {
        Ok(out) => RegorusResult {
            status: RegorusStatus::RegorusStatusOk,
            output: to_c_str(out),
            error_message: std::ptr::null_mut(),
        },
        Err(e) => to_regorus_result(Err(e)),
    }
}

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

            crate::regorus_aligned_alloc(align, size)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
            crate::regorus_free(ptr)
        }
    }

    #[global_allocator]
    static ALLOCATOR: RegorusAllocator = RegorusAllocator {};
}

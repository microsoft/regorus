// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, bail, Result};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::os::raw::c_void;
use std::cell::RefCell;
use std::thread_local;
use std::collections::HashMap;

/// Status of a call on `RegorusEngine`.
#[repr(C)]
pub enum RegorusStatus {
    /// The operation was successful.
    RegorusStatusOk,

    /// The operation was unsuccessful.
    RegorusStatusError,
}

// Define callback function type for orchestration to Regorus communication
pub type RegorusCallbackFn = extern "C" fn(payload: *const c_char, context: *mut c_void) -> *mut c_char;

// RegorusCallbackFn uses context pointer, so it doesn't provide Send/Sync
// Using thread_local instead of lazy_static to avoid Send/Sync requirements
// It limits invoke to single-threaded usage
thread_local! {
    static CALLBACK_MAP: RefCell<HashMap<String, (RegorusCallbackFn, *mut c_void)>> = RefCell::new(HashMap::new());
}

// Store a callback function and its context
#[no_mangle]
pub extern "C" fn regorus_register_callback(
    name: *const c_char, 
    callback: RegorusCallbackFn, 
    context: *mut c_void
) -> RegorusStatus {
    if name.is_null() {
        return RegorusStatus::RegorusStatusError;
    }
    
    let name_str = match from_c_str("name", name) {
        Ok(s) => s,
        Err(_) => return RegorusStatus::RegorusStatusError,
    };
    
    let result = CALLBACK_MAP.with(|callbacks| {
        callbacks.borrow_mut().insert(name_str, (callback, context));
        RegorusStatus::RegorusStatusOk
    });
    
    result
}

// Remove a callback function
#[no_mangle]
pub extern "C" fn regorus_unregister_callback(name: *const c_char) -> RegorusStatus {
    if name.is_null() {
        return RegorusStatus::RegorusStatusError;
    }
    
    let name_str = match from_c_str("name", name) {
        Ok(s) => s,
        Err(_) => return RegorusStatus::RegorusStatusError,
    };
    
    let result = CALLBACK_MAP.with(|callbacks| {
        callbacks.borrow_mut().remove(&name_str);
        RegorusStatus::RegorusStatusOk
    });
    
    result
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

fn from_c_str(name: &str, s: *const c_char) -> Result<String> {
    if s.is_null() {
        bail!("null pointer");
    }
    unsafe {
        CStr::from_ptr(s)
            .to_str()
            .map_err(|e| anyhow!("`{name}`: invalid utf8.\n{e}"))
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

fn to_regorus_string_result(r: Result<String>) -> RegorusResult {
    match r {
        Ok(s) => RegorusResult {
            status: RegorusStatus::RegorusStatusOk,
            output: to_c_str(s),
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
    unsafe {
        if !r.error_message.is_null() {
            let _ = CString::from_raw(r.error_message);
        }
        if !r.output.is_null() {
            let _ = CString::from_raw(r.output);
        }
    }
}
// Extension function to invoke callback
fn invoke_callback(mut params: Vec<::regorus::Value>) -> Result<::regorus::Value> {
    if params.len() != 2 {
        bail!("invoke requires exactly two parameters: function_name and payload");
    }
    
    let function_name = match params.remove(0) {
        ::regorus::Value::String(s) => s.as_ref().to_string(),
        _ => bail!("function_name must be a string"),
    };
    
    // Serialize the payload to JSON
    let payload = serde_json::to_string(&params.remove(0))
        .map_err(|e| anyhow!("Failed to serialize payload: {}", e))?;
    
    // Look up the callback function using thread_local storage
    let callback_option = CALLBACK_MAP.with(|callbacks| {
        callbacks.borrow().get(&function_name).cloned()
    });
    
    let (callback_fn, context) = match callback_option {
        Some(cb) => cb,
        None => bail!("No callback registered with name: {}", function_name),
    };
    
    // Convert payload to C string
    let payload_c_str = match CString::new(payload) {
        Ok(cs) => cs,
        Err(_) => bail!("Failed to convert payload to C string"),
    };
    
    // Call the orchestration function
    let result_ptr = callback_fn(payload_c_str.as_ptr(), context);
    
    if result_ptr.is_null() {
        return Ok(::regorus::Value::Null);
    }
    
    // Convert the result back to a Value
    let result_str = unsafe {
        let result = CStr::from_ptr(result_ptr)
            .to_str()
            .map_err(|e| anyhow!("Invalid UTF-8 in callback result: {}", e))?
            .to_string();
            
        // Free the memory allocated by C#
        let _ = CString::from_raw(result_ptr as *mut c_char);
        
        result
    };
    
    // Convert result string to Value
    ::regorus::Value::from_json_str(&result_str)
        .map_err(|e| anyhow!("Failed to parse callback result as JSON: {}", e))
}

#[no_mangle]
/// Construct a new Engine
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html
pub extern "C" fn regorus_engine_new() -> *mut RegorusEngine {
    let mut engine = ::regorus::Engine::new();
    let _ = engine.add_extension("invoke".to_string(), 2, Box::new(invoke_callback));
    Box::into_raw(Box::new(RegorusEngine { engine }))
}

/// Clone a [`RegorusEngine`]
///
/// To avoid having to parse same policy again, the engine can be cloned
/// after policies and data have been added.
///
#[no_mangle]
pub extern "C" fn regorus_engine_clone(engine: *mut RegorusEngine) -> *mut RegorusEngine {
    match to_ref(&engine) {
        Ok(e) => Box::into_raw(Box::new(e.clone())),
        _ => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn regorus_engine_drop(engine: *mut RegorusEngine) {
    if let Ok(e) = to_ref(&engine) {
        unsafe {
            let _ = Box::from_raw(std::ptr::from_mut(e));
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
    to_regorus_string_result(|| -> Result<String> {
        to_ref(&engine)?
            .engine
            .add_policy(from_c_str("path", path)?, from_c_str("rego", rego)?)
    }())
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_add_policy_from_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    to_regorus_string_result(|| -> Result<String> {
        to_ref(&engine)?
            .engine
            .add_policy_from_file(from_c_str("path", path)?)
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
            .add_data(regorus::Value::from_json_str(&from_c_str("data", data)?)?)
    }())
}

/// Get list of loaded Rego packages as JSON.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_packages
#[no_mangle]
pub extern "C" fn regorus_engine_get_packages(engine: *mut RegorusEngine) -> RegorusResult {
    to_regorus_string_result(|| -> Result<String> {
        serde_json::to_string_pretty(&to_ref(&engine)?.engine.get_packages()?)
            .map_err(anyhow::Error::msg)
    }())
}

/// Get list of policies as JSON.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_policies
#[no_mangle]
pub extern "C" fn regorus_engine_get_policies(engine: *mut RegorusEngine) -> RegorusResult {
    to_regorus_string_result(|| -> Result<String> {
        to_ref(&engine)?.engine.get_policies_as_json()
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
            .add_data(regorus::Value::from_json_file(from_c_str("path", path)?)?)
    }())
}

/// Clear policy data.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_data
#[no_mangle]
pub extern "C" fn regorus_engine_clear_data(engine: *mut RegorusEngine) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?.engine.clear_data();
        Ok(())
    }())
}

/// Set input.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_input
/// * `input`: JSON encoded value to be used as input to query.
#[no_mangle]
pub extern "C" fn regorus_engine_set_input_json(
    engine: *mut RegorusEngine,
    input: *const c_char,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?
            .engine
            .set_input(regorus::Value::from_json_str(&from_c_str("input", input)?)?);
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
            .set_input(regorus::Value::from_json_file(from_c_str("path", path)?)?);
        Ok(())
    }())
}

/// Evaluate query.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_query
/// * `query`: Rego expression to be evaluate.
#[no_mangle]
pub extern "C" fn regorus_engine_eval_query(
    engine: *mut RegorusEngine,
    query: *const c_char,
) -> RegorusResult {
    let output = || -> Result<String> {
        let results = to_ref(&engine)?
            .engine
            .eval_query(from_c_str("query", query)?, false)?;
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

/// Evaluate specified rule.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_rule
/// * `rule`: Path to the rule.
#[no_mangle]
pub extern "C" fn regorus_engine_eval_rule(
    engine: *mut RegorusEngine,
    rule: *const c_char,
) -> RegorusResult {
    let output = || -> Result<String> {
        to_ref(&engine)?
            .engine
            .eval_rule(from_c_str("rule", rule)?)?
            .to_json_str()
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

/// Enable/disable coverage.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_enable_coverage
/// * `enable`: Whether to enable or disable coverage.
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_set_enable_coverage(
    engine: *mut RegorusEngine,
    enable: bool,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?.engine.set_enable_coverage(enable);
        Ok(())
    }())
}

/// Get coverage report.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_coverage_report
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_get_coverage_report(engine: *mut RegorusEngine) -> RegorusResult {
    let output = || -> Result<String> {
        Ok(serde_json::to_string_pretty(
            &to_ref(&engine)?.engine.get_coverage_report()?,
        )?)
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

/// Get pretty printed coverage report.
///
/// See https://docs.rs/regorus/latest/regorus/coverage/struct.Report.html#method.to_string_pretty
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_get_coverage_report_pretty(
    engine: *mut RegorusEngine,
) -> RegorusResult {
    let output = || -> Result<String> {
        to_ref(&engine)?
            .engine
            .get_coverage_report()?
            .to_string_pretty()
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

/// Clear coverage data.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_coverage_data
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_clear_coverage_data(engine: *mut RegorusEngine) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?.engine.clear_coverage_data();
        Ok(())
    }())
}

/// Whether to gather output of print statements.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_gather_prints
/// * `enable`: Whether to enable or disable gathering print statements.
#[no_mangle]
pub extern "C" fn regorus_engine_set_gather_prints(
    engine: *mut RegorusEngine,
    enable: bool,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        to_ref(&engine)?.engine.set_gather_prints(enable);
        Ok(())
    }())
}

/// Take all the gathered print statements.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.take_prints
#[no_mangle]
pub extern "C" fn regorus_engine_take_prints(engine: *mut RegorusEngine) -> RegorusResult {
    let output = || -> Result<String> {
        Ok(serde_json::to_string_pretty(
            &to_ref(&engine)?.engine.take_prints()?,
        )?)
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

/// Get AST of policies.
///
/// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_ast_as_json
#[no_mangle]
#[cfg(feature = "ast")]
pub extern "C" fn regorus_engine_get_ast_as_json(engine: *mut RegorusEngine) -> RegorusResult {
    let output = || -> Result<String> { to_ref(&engine)?.engine.get_ast_as_json() }();
    match output {
        Ok(out) => RegorusResult {
            status: RegorusStatus::RegorusStatusOk,
            output: to_c_str(out),
            error_message: std::ptr::null_mut(),
        },
        Err(e) => to_regorus_result(Err(e)),
    }
}

/// Enable/disable rego v1.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_rego_v0
#[no_mangle]
pub extern "C" fn regorus_engine_set_rego_v0(
    engine: *mut RegorusEngine,
    enable: bool,
) -> RegorusResult {
    let output = || -> Result<()> {
        to_ref(&engine)?.engine.set_rego_v0(enable);
        Ok(())
    }();
    match output {
        Ok(()) => RegorusResult {
            status: RegorusStatus::RegorusStatusOk,
            output: std::ptr::null_mut(),
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

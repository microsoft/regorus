// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::common::{from_c_str, RegorusResult, RegorusStatus};
use crate::compiled_policy::RegorusCompiledPolicy;
use crate::panic_guard::with_unwind_guard;
use alloc::boxed::Box;
use alloc::format;
use alloc::vec::Vec;
use core::ffi::{c_char, c_void};
use regorus::{compile_policy_with_entrypoint, PolicyModule, Value};

#[cfg(feature = "azure_policy")]
use regorus::compile_policy_for_target;

/// FFI wrapper for PolicyModule struct.
#[repr(C)]
pub struct RegorusPolicyModule {
    pub id: *const c_char,
    pub content: *const c_char,
}

/// Compiles a policy from data and modules with a specific entry point rule.
///
/// This is a convenience function that wraps [`regorus::compile_policy_with_entrypoint`].
/// It sets up an Engine internally and calls the appropriate compilation method.
///
/// # Parameters
/// * `data_json` - JSON string containing static data for policy evaluation
/// * `modules` - Array of policy modules to compile
/// * `modules_len` - Number of modules in the array
/// * `entry_point_rule` - The specific rule path to evaluate (e.g., "data.policy.allow")
///
/// # Returns
/// Returns a RegorusResult containing a RegorusCompiledPolicy handle on success.
///
/// # Safety
/// All string parameters must be valid null-terminated UTF-8 strings.
/// The modules array must contain exactly `modules_len` valid elements.
/// The caller must eventually call regorus_compiled_policy_drop on the returned handle.
#[no_mangle]
pub extern "C" fn regorus_compile_policy_with_entrypoint(
    data_json: *const c_char,
    modules: *const RegorusPolicyModule,
    modules_len: usize,
    entry_point_rule: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let data_str = match from_c_str(data_json) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("Invalid data JSON string: {e}"),
                )
            }
        };

        let entry_rule = match from_c_str(entry_point_rule) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidEntrypoint,
                    format!("Invalid entry point rule string: {e}"),
                )
            }
        };

        let data = match Value::from_json_str(&data_str) {
            Ok(data) => data,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("Failed to parse data JSON: {e}"),
                )
            }
        };

        let policy_modules = match convert_c_modules_to_rust(modules, modules_len) {
            Ok(modules) => modules,
            Err(status) => return RegorusResult::err(status),
        };

        match compile_policy_with_entrypoint(data, &policy_modules, entry_rule.into()) {
            Ok(compiled_policy) => {
                let wrapped_policy = RegorusCompiledPolicy { compiled_policy };
                let boxed_policy = Box::new(wrapped_policy);
                RegorusResult::ok_pointer(Box::into_raw(boxed_policy) as *mut c_void)
            }
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("Policy compilation failed: {e}"),
            ),
        }
    })
}

/// Compiles a target-aware policy from data and modules.
///
/// This is a convenience function that wraps [`regorus::compile_policy_for_target`].
/// It sets up an Engine internally and calls target-aware compilation.
///
/// # Parameters
/// * `data_json` - JSON string containing static data for policy evaluation
/// * `modules` - Array of policy modules to compile
/// * `modules_len` - Number of modules in the array
///
/// # Returns
/// Returns a RegorusResult containing a RegorusCompiledPolicy handle on success.
///
/// # Note
/// This function is only available when the `azure_policy` feature is enabled.
/// At least one module must contain a `__target__` declaration.
///
/// # Safety
/// All string parameters must be valid null-terminated UTF-8 strings.
/// The modules array must contain exactly `modules_len` valid elements.
/// The caller must eventually call regorus_compiled_policy_drop on the returned handle.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_compile_policy_for_target(
    data_json: *const c_char,
    modules: *const RegorusPolicyModule,
    modules_len: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        let data_str = match from_c_str(data_json) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("Invalid data JSON string: {e}"),
                )
            }
        };

        let data = match Value::from_json_str(&data_str) {
            Ok(data) => data,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("Failed to parse data JSON: {e}"),
                )
            }
        };

        let policy_modules = match convert_c_modules_to_rust(modules, modules_len) {
            Ok(modules) => modules,
            Err(status) => return RegorusResult::err(status),
        };

        match compile_policy_for_target(data, &policy_modules) {
            Ok(compiled_policy) => {
                let wrapped_policy = RegorusCompiledPolicy { compiled_policy };
                let boxed_policy = Box::new(wrapped_policy);
                RegorusResult::ok_pointer(Box::into_raw(boxed_policy) as *mut c_void)
            }
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("Target-aware policy compilation failed: {e}"),
            ),
        }
    })
}

/// Helper function to convert C module array to Rust Vec<PolicyModule>.
fn convert_c_modules_to_rust(
    modules: *const RegorusPolicyModule,
    modules_len: usize,
) -> Result<Vec<PolicyModule>, RegorusStatus> {
    if modules.is_null() && modules_len > 0 {
        return Err(RegorusStatus::InvalidArgument);
    }

    let mut policy_modules = Vec::with_capacity(modules_len);

    for i in 0..modules_len {
        unsafe {
            let module = modules.add(i);
            if module.is_null() {
                return Err(RegorusStatus::InvalidArgument);
            }

            let module_ref = &*module;

            let id = match from_c_str(module_ref.id) {
                Ok(s) => s,
                Err(e) => {
                    report_module_error(i, "module ID", &e);
                    return Err(RegorusStatus::InvalidModuleId);
                }
            };

            let content = match from_c_str(module_ref.content) {
                Ok(s) => s,
                Err(e) => {
                    report_module_error(i, "module content", &e);
                    return Err(RegorusStatus::InvalidPolicy);
                }
            };

            policy_modules.push(PolicyModule {
                id: id.into(),
                content: content.into(),
            });
        }
    }

    Ok(policy_modules)
}

#[cfg(feature = "std")]
fn report_module_error(index: usize, kind: &str, err: &anyhow::Error) {
    eprintln!("Invalid {} at index {}: {}", kind, index, err);
}

#[cfg(not(feature = "std"))]
fn report_module_error(_index: usize, _kind: &str, _err: &anyhow::Error) {}

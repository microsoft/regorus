// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(feature = "azure_policy")]

use crate::common::*;
use crate::panic_guard::with_unwind_guard;
use anyhow::Result;
use std::os::raw::c_char;

/// Register a target from JSON definition.
///
/// The target JSON should follow the target schema format.
/// Once registered, the target can be referenced in Rego policies using `__target__` rules.
///
/// * `target_json`: JSON encoded target definition
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_register_target_from_json(target_json: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let target_str = from_c_str(target_json)?;
            let target = regorus::Target::from_json_str(&target_str)?;
            regorus::registry::targets::register(regorus::Rc::new(target))?;
            Ok(())
        }())
    })
}

/// Check if a target is registered.
///
/// # Parameters
/// * `name` - Name of the target to check
///
/// # Returns
/// Returns a RegorusResult with boolean value indicating if the target is registered.
///
/// # Safety
/// The name parameter must be a valid null-terminated UTF-8 string.
#[no_mangle]
pub extern "C" fn regorus_target_registry_contains(name: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        let target_name = match from_c_str(name) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("Invalid target name string: {e}"),
                )
            }
        };

        let contains = regorus::registry::targets::contains(&target_name);
        RegorusResult::ok_bool(contains)
    })
}

/// Get a list of all registered target names as JSON array.
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_target_registry_list_names() -> RegorusResult {
    with_unwind_guard(|| {
        let names = regorus::registry::targets::list_names();
        let output = serde_json::to_string_pretty(&names).map_err(anyhow::Error::msg);

        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Remove a target from the registry by name.
///
/// * `name`: The target name to remove
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_target_registry_remove(name: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let name_str = from_c_str(name)?;
            regorus::registry::targets::remove(&name_str);
            Ok(())
        }())
    })
}

/// Clear all targets from the registry.
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_target_registry_clear() -> RegorusResult {
    with_unwind_guard(|| {
        regorus::registry::targets::clear();
        RegorusResult::ok_void()
    })
}

/// Get the number of registered targets.
///
/// # Returns
/// Returns a RegorusResult with the count as an integer value.
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_target_registry_len() -> RegorusResult {
    with_unwind_guard(|| {
        let count = regorus::registry::targets::len();
        RegorusResult::ok_int(count as i64)
    })
}

/// Check if the target registry is empty.
///
/// # Returns
/// Returns a RegorusResult with boolean value indicating if the registry is empty.
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_target_registry_is_empty() -> RegorusResult {
    with_unwind_guard(|| {
        let is_empty = regorus::registry::targets::is_empty();
        RegorusResult::ok_bool(is_empty)
    })
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Schema registry functions for FFI.
//!
//! These functions provide access to regorus's resource schema registry functionality,
//! enabling registration and management of Azure Policy resource schemas.

#![cfg(feature = "azure_policy")]

use crate::common::{from_c_str, RegorusResult, RegorusStatus};
use crate::panic_guard::with_unwind_guard;
use regorus::{registry::schemas, Schema};

use std::os::raw::c_char;

// Resource Schema Registry Functions

/// Register a resource schema from JSON with a given name.
///
/// # Parameters
/// * `name` - Name to register the schema under
/// * `schema_json` - JSON string representing the schema
///
/// # Returns
/// Returns a RegorusResult with success/error status.
///
/// # Safety
/// All string parameters must be valid null-terminated UTF-8 strings.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_register(
    name: *const c_char,
    schema_json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let schema_name = match from_c_str(name) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("Invalid schema name string: {e}"),
                )
            }
        };

        let schema_str = match from_c_str(schema_json) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("Invalid schema JSON string: {e}"),
                )
            }
        };

        let schema = match Schema::from_json_str(&schema_str) {
            Ok(schema) => schema,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("Failed to parse schema JSON: {e}"),
                )
            }
        };

        match schemas::resource::register(schema_name, schema.into()) {
            Ok(()) => RegorusResult::ok_pointer(std::ptr::null_mut()),
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::Error,
                format!("Failed to register schema: {e}"),
            ),
        }
    })
}

/// Check if a resource schema with the given name exists.
///
/// # Parameters
/// * `name` - Name of the schema to check
///
/// # Returns
/// Returns a RegorusResult with "true" or "false" string output.
///
/// # Safety
/// The name parameter must be a valid null-terminated UTF-8 string.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_contains(name: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        let schema_name = match from_c_str(name) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("Invalid schema name string: {e}"),
                )
            }
        };

        let contains = schemas::resource::contains(&schema_name);
        RegorusResult::ok_bool(contains)
    })
}

/// Get the number of registered resource schemas.
///
/// # Returns
/// Returns a RegorusResult with the count as a string.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_len() -> RegorusResult {
    with_unwind_guard(|| {
        let count = schemas::resource::len();
        RegorusResult::ok_int(count as i64)
    })
}

/// Check if the resource schema registry is empty.
///
/// # Returns
/// Returns a RegorusResult with "true" or "false" string output.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_is_empty() -> RegorusResult {
    with_unwind_guard(|| {
        let is_empty = schemas::resource::is_empty();
        RegorusResult::ok_bool(is_empty)
    })
}

/// List all registered resource schema names as a JSON array.
///
/// # Returns
/// Returns a RegorusResult with a JSON array of schema names.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_list_names() -> RegorusResult {
    with_unwind_guard(|| {
        let names = schemas::resource::list_names();
        match serde_json::to_string(&names) {
            Ok(json_str) => RegorusResult::ok_string(json_str),
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::Error,
                format!("Failed to serialize schema names to JSON: {e}"),
            ),
        }
    })
}

/// Remove a resource schema by name.
///
/// # Parameters
/// * `name` - Name of the schema to remove
///
/// # Returns
/// Returns a RegorusResult with "true" if removed, "false" if not found.
///
/// # Safety
/// The name parameter must be a valid null-terminated UTF-8 string.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_remove(name: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        let schema_name = match from_c_str(name) {
            Ok(s) => s,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("Invalid schema name string: {e}"),
                )
            }
        };

        let removed = schemas::resource::remove(&schema_name).is_some();
        RegorusResult::ok_bool(removed)
    })
}

/// Clear all resource schemas from the registry.
///
/// # Returns
/// Returns a RegorusResult with success status.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_resource_schema_clear() -> RegorusResult {
    with_unwind_guard(|| {
        schemas::resource::clear();
        RegorusResult::ok_pointer(std::ptr::null_mut())
    })
}

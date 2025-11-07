// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Effect schema registry functions for FFI.
//!
//! These functions provide access to regorus's effect schema registry functionality,
//! enabling registration and management of Azure Policy effect schemas.

#![cfg(feature = "azure_policy")]
use crate::common::{from_c_str, RegorusResult, RegorusStatus};
use regorus::{registry::schemas, Schema};

use std::os::raw::c_char;

/// Register an effect schema from JSON with a given name.
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
pub extern "C" fn regorus_effect_schema_register(
    name: *const c_char,
    schema_json: *const c_char,
) -> RegorusResult {
    let schema_name = match from_c_str(name) {
        Ok(s) => s,
        Err(e) => {
            return RegorusResult::err_with_message(
                RegorusStatus::InvalidArgument,
                format!("Invalid effect schema name string: {e}"),
            )
        }
    };

    let schema_str = match from_c_str(schema_json) {
        Ok(s) => s,
        Err(e) => {
            return RegorusResult::err_with_message(
                RegorusStatus::InvalidDataFormat,
                format!("Invalid effect schema JSON string: {e}"),
            )
        }
    };

    // Parse schema from JSON
    let schema = match Schema::from_json_str(&schema_str) {
        Ok(schema) => schema,
        Err(e) => {
            return RegorusResult::err_with_message(
                RegorusStatus::InvalidDataFormat,
                format!("Failed to parse effect schema JSON: {e}"),
            )
        }
    };

    // Register the schema
    match schemas::effect::register(schema_name, schema.into()) {
        Ok(()) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(
            RegorusStatus::Error,
            format!("Failed to register effect schema: {e}"),
        ),
    }
}

/// Check if an effect schema with the given name exists.
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
pub extern "C" fn regorus_effect_schema_contains(name: *const c_char) -> RegorusResult {
    let schema_name = match from_c_str(name) {
        Ok(s) => s,
        Err(e) => {
            return RegorusResult::err_with_message(
                RegorusStatus::InvalidArgument,
                format!("Invalid effect schema name string: {e}"),
            )
        }
    };

    let contains = schemas::effect::contains(&schema_name);
    RegorusResult::ok_bool(contains)
}

/// Get the number of registered effect schemas.
///
/// # Returns
/// Returns a RegorusResult with the count as a string.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_effect_schema_len() -> RegorusResult {
    let count = schemas::effect::len();
    RegorusResult::ok_int(count as i64)
}

/// Check if the effect schema registry is empty.
///
/// # Returns
/// Returns a RegorusResult with "true" or "false" string output.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_effect_schema_is_empty() -> RegorusResult {
    let is_empty = schemas::effect::is_empty();
    RegorusResult::ok_bool(is_empty)
}

/// List all registered effect schema names as a JSON array.
///
/// # Returns
/// Returns a RegorusResult with a JSON array of schema names.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_effect_schema_list_names() -> RegorusResult {
    let names = schemas::effect::list_names();
    match serde_json::to_string(&names) {
        Ok(json_str) => RegorusResult::ok_string(json_str),
        Err(e) => RegorusResult::err_with_message(
            RegorusStatus::Error,
            format!("Failed to serialize effect schema names to JSON: {e}"),
        ),
    }
}

/// Remove an effect schema by name.
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
pub extern "C" fn regorus_effect_schema_remove(name: *const c_char) -> RegorusResult {
    let schema_name = match from_c_str(name) {
        Ok(s) => s,
        Err(e) => {
            return RegorusResult::err_with_message(
                RegorusStatus::InvalidArgument,
                format!("Invalid effect schema name string: {e}"),
            )
        }
    };

    let removed = schemas::effect::remove(&schema_name).is_some();
    RegorusResult::ok_bool(removed)
}

/// Clear all effect schemas from the registry.
///
/// # Returns
/// Returns a RegorusResult with success status.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_effect_schema_clear() -> RegorusResult {
    schemas::effect::clear();
    RegorusResult::ok_void()
}

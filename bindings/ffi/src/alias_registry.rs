// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! FFI bindings for `AliasRegistry` – Azure Policy alias catalog management.

#![cfg(feature = "azure_policy")]

use crate::common::{from_c_str, to_ref, RegorusResult, RegorusStatus};
use crate::panic_guard::with_unwind_guard;

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use anyhow::Result;
use core::ffi::c_char;
use core::ptr;

use regorus::languages::azure_policy::aliases::AliasRegistry;

/// Opaque wrapper for `AliasRegistry`.
pub struct RegorusAliasRegistry {
    registry: AliasRegistry,
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

/// Create a new, empty `AliasRegistry`.
///
/// The caller must eventually call `regorus_alias_registry_drop` to free the handle.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_new() -> *mut RegorusAliasRegistry {
    let wrapper = RegorusAliasRegistry {
        registry: AliasRegistry::new(),
    };
    Box::into_raw(Box::new(wrapper))
}

/// Drop a `RegorusAliasRegistry`.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_drop(registry: *mut RegorusAliasRegistry) {
    if let Ok(r) = to_ref(registry) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(r));
        }
    }
}

// ---------------------------------------------------------------------------
// Loading
// ---------------------------------------------------------------------------

/// Load control-plane alias data (array of `ProviderAliases`) into the registry.
///
/// `json` must be a valid null-terminated UTF-8 string containing the JSON
/// array returned by `Get-AzPolicyAlias` or the static
/// `ResourceTypesAndAliases.json` file.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_load_json(
    registry: *mut RegorusAliasRegistry,
    json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<()> {
            let json_str = from_c_str(json)?;
            to_ref(registry)?.registry.load_from_json(&json_str)?;
            Ok(())
        }();

        match output {
            Ok(()) => RegorusResult::ok_void(),
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::InvalidDataFormat,
                format!("Failed to load alias catalog: {e}"),
            ),
        }
    })
}

/// Load a data-plane policy manifest into the registry.
///
/// `json` must be a valid null-terminated UTF-8 string containing a single
/// `DataPolicyManifest` JSON object.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_load_manifest(
    registry: *mut RegorusAliasRegistry,
    json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<()> {
            let json_str = from_c_str(json)?;
            to_ref(registry)?
                .registry
                .load_data_policy_manifest_json(&json_str)?;
            Ok(())
        }();

        match output {
            Ok(()) => RegorusResult::ok_void(),
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::InvalidDataFormat,
                format!("Failed to load data-plane manifest: {e}"),
            ),
        }
    })
}

// ---------------------------------------------------------------------------
// Queries
// ---------------------------------------------------------------------------

/// Return the number of resource types loaded in the alias registry.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_len(registry: *mut RegorusAliasRegistry) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<i64> {
            let len = to_ref(registry)?.registry.len();
            Ok(len as i64)
        }();

        match output {
            Ok(n) => RegorusResult::ok_int(n),
            Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{e}")),
        }
    })
}

// ---------------------------------------------------------------------------
// Normalize / Denormalize
// ---------------------------------------------------------------------------

/// Normalize an ARM resource JSON and wrap it into the standard input envelope.
///
/// Returns a JSON string:
/// `{ "resource": <normalized>, "context": <context>, "parameters": <params> }`.
///
/// * `resource_json` – raw ARM resource JSON
/// * `api_version` – API version string (e.g. `"2023-01-01"`), or null to use
///   the default alias paths
/// * `context_json` – JSON object for additional context (pass `"{}"` if none)
/// * `parameters_json` – JSON object of policy parameter values (pass `"{}"` if none)
#[no_mangle]
pub extern "C" fn regorus_alias_registry_normalize_and_wrap(
    registry: *mut RegorusAliasRegistry,
    resource_json: *const c_char,
    api_version: *const c_char,
    context_json: *const c_char,
    parameters_json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let resource_str = from_c_str(resource_json)?;
            let api_ver = if api_version.is_null() {
                None
            } else {
                let s = from_c_str(api_version)?;
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let context_str = from_c_str(context_json)?;
            let params_str = from_c_str(parameters_json)?;

            let resource = regorus::Value::from_json_str(&resource_str)?;
            let context = regorus::Value::from_json_str(&context_str)?;
            let params = regorus::Value::from_json_str(&params_str)?;

            let wrapped = to_ref(registry)?.registry.normalize_and_wrap(
                &resource,
                api_ver.as_deref(),
                Some(context),
                Some(params),
            );
            wrapped.to_json_str()
        }();

        match output {
            Ok(s) => RegorusResult::ok_string(s),
            Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{e}")),
        }
    })
}

/// Denormalize a previously-normalized resource JSON back to ARM format.
///
/// * `normalized_json` – the normalized resource JSON
/// * `api_version` – API version string, or null to use the default alias paths
///
/// Returns the denormalized ARM JSON string.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_denormalize(
    registry: *mut RegorusAliasRegistry,
    normalized_json: *const c_char,
    api_version: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let normalized_str = from_c_str(normalized_json)?;
            let api_ver = if api_version.is_null() {
                None
            } else {
                let s = from_c_str(api_version)?;
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };

            let normalized = regorus::Value::from_json_str(&normalized_str)?;

            let result = to_ref(registry)?
                .registry
                .denormalize(&normalized, api_ver.as_deref());
            result.to_json_str()
        }();

        match output {
            Ok(s) => RegorusResult::ok_string(s),
            Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{e}")),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::regorus_result_drop;
    use core::ffi::CStr;
    use std::ffi::CString;

    /// Helper: create a C string from a Rust &str.
    fn c(s: &str) -> CString {
        CString::new(s).expect("CString::new failed")
    }

    /// Helper: assert a RegorusResult has Ok status and extract string output.
    fn assert_ok_string(r: &RegorusResult) -> String {
        assert_eq!(r.status, RegorusStatus::Ok, "expected Ok status");
        assert!(!r.output.is_null(), "expected non-null output");
        let s = unsafe { CStr::from_ptr(r.output) }
            .to_str()
            .expect("invalid UTF-8 in output")
            .to_string();
        s
    }

    /// Helper: assert a RegorusResult has Ok status with integer output.
    fn assert_ok_int(r: &RegorusResult) -> i64 {
        assert_eq!(r.status, RegorusStatus::Ok, "expected Ok status");
        r.int_value
    }

    const ALIASES: &str = r#"[{
        "namespace": "Microsoft.Storage",
        "resourceTypes": [{
            "resourceType": "storageAccounts",
            "aliases": [{
                "name": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly",
                "defaultPath": "properties.supportsHttpsTrafficOnly",
                "paths": []
            }]
        }]
    }]"#;

    const MANIFEST: &str = r#"{
        "dataNamespace": "Microsoft.KeyVault.Data",
        "aliases": [],
        "resourceTypeAliases": [{
            "resourceType": "vaults/certificates",
            "aliases": [{
                "name": "Microsoft.KeyVault.Data/vaults/certificates/keySize",
                "paths": [{ "path": "keySize", "apiVersions": ["7.0"] }]
            }]
        }]
    }"#;

    #[test]
    fn lifecycle_new_and_drop() {
        let reg = regorus_alias_registry_new();
        assert!(!reg.is_null());
        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn load_json_and_check_len() {
        let reg = regorus_alias_registry_new();
        let json = c(ALIASES);

        let r = regorus_alias_registry_load_json(reg, json.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let r = regorus_alias_registry_len(reg);
        assert_eq!(assert_ok_int(&r), 1);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn load_manifest_and_check_len() {
        let reg = regorus_alias_registry_new();
        let json = c(MANIFEST);

        let r = regorus_alias_registry_load_manifest(reg, json.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let r = regorus_alias_registry_len(reg);
        assert_eq!(assert_ok_int(&r), 1);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn load_invalid_json_returns_error() {
        let reg = regorus_alias_registry_new();
        let bad = c("not valid json");

        let r = regorus_alias_registry_load_json(reg, bad.as_ptr());
        assert_ne!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn normalize_and_wrap_round_trip() {
        let reg = regorus_alias_registry_new();
        let aliases = c(ALIASES);
        let r = regorus_alias_registry_load_json(reg, aliases.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let resource = c(r#"{
            "name": "acct1",
            "type": "Microsoft.Storage/storageAccounts",
            "properties": { "supportsHttpsTrafficOnly": true }
        }"#);
        let api = c("2023-01-01");
        let ctx = c(r#"{"resourceGroup": {"name": "rg1"}}"#);
        let params = c(r#"{"env": "prod"}"#);

        // Normalize
        let r = regorus_alias_registry_normalize_and_wrap(
            reg,
            resource.as_ptr(),
            api.as_ptr(),
            ctx.as_ptr(),
            params.as_ptr(),
        );
        let envelope_json = assert_ok_string(&r);
        regorus_result_drop(r);

        // Parse and verify structure
        let envelope: serde_json::Value =
            serde_json::from_str(&envelope_json).expect("invalid JSON output");
        assert!(
            envelope.get("resource").is_some(),
            "envelope missing 'resource'"
        );
        assert!(
            envelope.get("parameters").is_some(),
            "envelope missing 'parameters'"
        );
        assert!(
            envelope.get("context").is_some(),
            "envelope missing 'context'"
        );

        // The normalized resource should have lowercased alias fields
        let res = &envelope["resource"];
        assert_eq!(res["supportshttpstrafficonly"], true);
        assert_eq!(res["name"], "acct1");

        // Context and parameters should be passed through
        assert_eq!(envelope["context"]["resourceGroup"]["name"], "rg1");
        assert_eq!(envelope["parameters"]["env"], "prod");

        // Denormalize the resource portion
        let resource_json = serde_json::to_string(&res).expect("serialize resource");
        let norm_cstr = c(&resource_json);

        let r = regorus_alias_registry_denormalize(reg, norm_cstr.as_ptr(), api.as_ptr());
        let denorm_json = assert_ok_string(&r);
        regorus_result_drop(r);

        let denorm: serde_json::Value =
            serde_json::from_str(&denorm_json).expect("invalid denorm JSON");
        // Should be back under properties with restored casing
        assert_eq!(
            denorm["properties"]["supportsHttpsTrafficOnly"], true,
            "expected restored casing under properties"
        );

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn denormalize_invalid_json_returns_error() {
        let reg = regorus_alias_registry_new();
        let aliases = c(ALIASES);
        let r = regorus_alias_registry_load_json(reg, aliases.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let bad = c("not json");
        let api = c("2023-01-01");
        let r = regorus_alias_registry_denormalize(reg, bad.as_ptr(), api.as_ptr());
        assert_ne!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn normalize_data_plane_manifest() {
        let reg = regorus_alias_registry_new();
        let manifest = c(MANIFEST);
        let r = regorus_alias_registry_load_manifest(reg, manifest.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let resource = c(r#"{
            "type": "Microsoft.KeyVault.Data/vaults/certificates",
            "keySize": 2048
        }"#);
        let api = c("7.0");
        let ctx = c("{}");
        let params = c("{}");

        let r = regorus_alias_registry_normalize_and_wrap(
            reg,
            resource.as_ptr(),
            api.as_ptr(),
            ctx.as_ptr(),
            params.as_ptr(),
        );
        let envelope_json = assert_ok_string(&r);
        regorus_result_drop(r);

        let envelope: serde_json::Value =
            serde_json::from_str(&envelope_json).expect("invalid JSON output");
        assert_eq!(envelope["resource"]["keysize"], 2048);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn empty_registry_normalize() {
        let reg = regorus_alias_registry_new();
        let resource = c(r#"{"name": "test", "type": "Unknown/type", "properties": {"foo": 1}}"#);
        let api = c("");
        let ctx = c("{}");
        let params = c("{}");

        let r = regorus_alias_registry_normalize_and_wrap(
            reg,
            resource.as_ptr(),
            api.as_ptr(),
            ctx.as_ptr(),
            params.as_ptr(),
        );
        let json = assert_ok_string(&r);
        regorus_result_drop(r);

        let envelope: serde_json::Value = serde_json::from_str(&json).expect("invalid JSON");
        // Without aliases, properties should still be flattened
        assert_eq!(envelope["resource"]["foo"], 1);
        assert_eq!(envelope["resource"]["name"], "test");

        regorus_alias_registry_drop(reg);
    }
}

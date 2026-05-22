// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! FFI bindings for `AliasRegistry` – Azure Policy alias catalog management.

#![cfg(feature = "azure_policy")]

use crate::common::{from_c_str, to_ref, to_shared_ref, RegorusResult, RegorusStatus};
use crate::panic_guard::with_unwind_guard;

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::sync::Arc;
use anyhow::{anyhow, Result};
use core::ffi::{c_char, c_void};
use core::{mem, ptr};

use regorus::languages::azure_policy::aliases::AliasRegistry;

/// Mutable builder for `AliasRegistry`.
///
/// This handle is intentionally single-threaded and must not be used
/// concurrently. Callers should finish loading alias data and then freeze it
/// into a `RegorusAliasRegistry` via `regorus_alias_registry_builder_build`.
pub struct RegorusAliasRegistryBuilder {
    registry: AliasRegistry,
    built: bool,
}

impl RegorusAliasRegistryBuilder {
    fn new() -> Self {
        Self {
            registry: AliasRegistry::new(),
            built: false,
        }
    }

    fn registry_mut(&mut self) -> Result<&mut AliasRegistry> {
        if self.built {
            return Err(anyhow!("alias registry builder has already been built"));
        }
        Ok(&mut self.registry)
    }

    fn build(&mut self) -> Result<RegorusAliasRegistry> {
        if self.built {
            return Err(anyhow!("alias registry builder has already been built"));
        }

        self.built = true;
        Ok(RegorusAliasRegistry {
            registry: Arc::new(mem::replace(&mut self.registry, AliasRegistry::new())),
        })
    }
}

/// Frozen, immutable alias registry.
pub struct RegorusAliasRegistry {
    registry: Arc<AliasRegistry>,
}

impl RegorusAliasRegistry {
    /// Return a shared reference to the inner registry for use by the compiler.
    pub(crate) fn inner(&self) -> Arc<AliasRegistry> {
        Arc::clone(&self.registry)
    }
}

// ---------------------------------------------------------------------------
// Builder lifecycle
// ---------------------------------------------------------------------------

/// Create a new, empty `AliasRegistry` builder.
///
/// The caller must eventually call `regorus_alias_registry_builder_drop`.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_builder_new() -> *mut RegorusAliasRegistryBuilder {
    Box::into_raw(Box::new(RegorusAliasRegistryBuilder::new()))
}

/// Drop a `RegorusAliasRegistryBuilder`.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_builder_drop(builder: *mut RegorusAliasRegistryBuilder) {
    if let Ok(builder) = to_ref(builder) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(builder));
        }
    }
}

// ---------------------------------------------------------------------------
// Builder loading
// ---------------------------------------------------------------------------

/// Load control-plane alias data (array of `ProviderAliases`) into the builder.
///
/// `json` must be a valid null-terminated UTF-8 string containing the JSON
/// array returned by `Get-AzPolicyAlias` or the static
/// `ResourceTypesAndAliases.json` file.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_builder_load_json(
    builder: *mut RegorusAliasRegistryBuilder,
    json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<()> {
            let json_str = from_c_str(json)?;
            to_ref(builder)?.registry_mut()?.load_from_json(&json_str)?;
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

/// Load a data-plane policy manifest into the builder.
///
/// `json` must be a valid null-terminated UTF-8 string containing a single
/// `DataPolicyManifest` JSON object.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_builder_load_manifest(
    builder: *mut RegorusAliasRegistryBuilder,
    json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<()> {
            let json_str = from_c_str(json)?;
            to_ref(builder)?
                .registry_mut()?
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

/// Freeze a builder into an immutable `RegorusAliasRegistry`.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_builder_build(
    builder: *mut RegorusAliasRegistryBuilder,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusAliasRegistry> {
            let registry = to_ref(builder)?.build()?;
            Ok(Box::into_raw(Box::new(registry)))
        }();

        match output {
            Ok(registry) => RegorusResult::ok_pointer(registry as *mut c_void),
            Err(e) => {
                RegorusResult::err_with_message(RegorusStatus::InvalidArgument, format!("{e}"))
            }
        }
    })
}

// ---------------------------------------------------------------------------
// Frozen registry lifecycle
// ---------------------------------------------------------------------------

/// Drop a `RegorusAliasRegistry`.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_drop(registry: *mut RegorusAliasRegistry) {
    if let Ok(registry) = to_ref(registry) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(registry));
        }
    }
}

// ---------------------------------------------------------------------------
// Frozen registry queries
// ---------------------------------------------------------------------------

/// Return the number of resource types loaded in the alias registry.
#[no_mangle]
pub extern "C" fn regorus_alias_registry_len(
    registry: *const RegorusAliasRegistry,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<i64> {
            let len = to_shared_ref(registry)?.registry.len();
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
#[no_mangle]
pub extern "C" fn regorus_alias_registry_normalize_and_wrap(
    registry: *const RegorusAliasRegistry,
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

            let wrapped = to_shared_ref(registry)?.registry.normalize_and_wrap(
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
#[no_mangle]
pub extern "C" fn regorus_alias_registry_denormalize(
    registry: *const RegorusAliasRegistry,
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

            let result = to_shared_ref(registry)?
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

    fn c(s: &str) -> CString {
        CString::new(s).expect("CString::new failed")
    }

    fn assert_ok_string(r: &RegorusResult) -> String {
        assert_eq!(r.status, RegorusStatus::Ok, "expected Ok status");
        assert!(!r.output.is_null(), "expected non-null output");
        let s = unsafe { CStr::from_ptr(r.output) }
            .to_str()
            .expect("invalid UTF-8 in output")
            .to_string();
        s
    }

    fn assert_ok_int(r: &RegorusResult) -> i64 {
        assert_eq!(r.status, RegorusStatus::Ok, "expected Ok status");
        r.int_value
    }

    fn assert_ok_pointer(r: &RegorusResult) -> *mut c_void {
        assert_eq!(r.status, RegorusStatus::Ok, "expected Ok status");
        assert!(matches!(
            r.data_type,
            crate::common::RegorusDataType::Pointer
        ));
        assert!(!r.pointer_value.is_null());
        r.pointer_value
    }

    fn build_registry_with_json(json: &str) -> *mut RegorusAliasRegistry {
        let builder = regorus_alias_registry_builder_new();
        let json = c(json);

        let r = regorus_alias_registry_builder_load_json(builder, json.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let r = regorus_alias_registry_builder_build(builder);
        let registry = assert_ok_pointer(&r) as *mut RegorusAliasRegistry;
        regorus_result_drop(r);
        regorus_alias_registry_builder_drop(builder);
        registry
    }

    fn build_registry_with_manifest(json: &str) -> *mut RegorusAliasRegistry {
        let builder = regorus_alias_registry_builder_new();
        let json = c(json);

        let r = regorus_alias_registry_builder_load_manifest(builder, json.as_ptr());
        assert_eq!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let r = regorus_alias_registry_builder_build(builder);
        let registry = assert_ok_pointer(&r) as *mut RegorusAliasRegistry;
        regorus_result_drop(r);
        regorus_alias_registry_builder_drop(builder);
        registry
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
    fn lifecycle_builder_build_and_drop() {
        let builder = regorus_alias_registry_builder_new();
        assert!(!builder.is_null());

        let r = regorus_alias_registry_builder_build(builder);
        let registry = assert_ok_pointer(&r) as *mut RegorusAliasRegistry;
        regorus_result_drop(r);

        regorus_alias_registry_builder_drop(builder);
        regorus_alias_registry_drop(registry);
    }

    #[test]
    fn load_json_and_check_len() {
        let reg = build_registry_with_json(ALIASES);

        let r = regorus_alias_registry_len(reg);
        assert_eq!(assert_ok_int(&r), 1);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn load_manifest_and_check_len() {
        let reg = build_registry_with_manifest(MANIFEST);

        let r = regorus_alias_registry_len(reg);
        assert_eq!(assert_ok_int(&r), 1);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn load_invalid_json_returns_error() {
        let builder = regorus_alias_registry_builder_new();
        let bad = c("not valid json");

        let r = regorus_alias_registry_builder_load_json(builder, bad.as_ptr());
        assert_ne!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        regorus_alias_registry_builder_drop(builder);
    }

    #[test]
    fn builder_cannot_be_reused_after_build() {
        let builder = regorus_alias_registry_builder_new();
        let r = regorus_alias_registry_builder_build(builder);
        let registry = assert_ok_pointer(&r) as *mut RegorusAliasRegistry;
        regorus_result_drop(r);

        let aliases = c(ALIASES);
        let r = regorus_alias_registry_builder_load_json(builder, aliases.as_ptr());
        assert_ne!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        let r = regorus_alias_registry_builder_build(builder);
        assert_ne!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        regorus_alias_registry_builder_drop(builder);
        regorus_alias_registry_drop(registry);
    }

    #[test]
    fn normalize_and_wrap_round_trip() {
        let reg = build_registry_with_json(ALIASES);

        let resource = c(r#"{
            "name": "acct1",
            "type": "Microsoft.Storage/storageAccounts",
            "properties": { "supportsHttpsTrafficOnly": true }
        }"#);
        let api = c("2023-01-01");
        let ctx = c(r#"{"resourceGroup": {"name": "rg1"}}"#);
        let params = c(r#"{"env": "prod"}"#);

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

        let res = &envelope["resource"];
        assert_eq!(res["supportshttpstrafficonly"], true);
        assert_eq!(res["name"], "acct1");

        assert_eq!(envelope["context"]["resourceGroup"]["name"], "rg1");
        assert_eq!(envelope["parameters"]["env"], "prod");

        let resource_json = serde_json::to_string(&res).expect("serialize resource");
        let norm_cstr = c(&resource_json);

        let r = regorus_alias_registry_denormalize(reg, norm_cstr.as_ptr(), api.as_ptr());
        let denorm_json = assert_ok_string(&r);
        regorus_result_drop(r);

        let denorm: serde_json::Value =
            serde_json::from_str(&denorm_json).expect("invalid denorm JSON");
        assert_eq!(
            denorm["properties"]["supportsHttpsTrafficOnly"], true,
            "expected restored casing under properties"
        );

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn denormalize_invalid_json_returns_error() {
        let reg = build_registry_with_json(ALIASES);

        let bad = c("not json");
        let api = c("2023-01-01");
        let r = regorus_alias_registry_denormalize(reg, bad.as_ptr(), api.as_ptr());
        assert_ne!(r.status, RegorusStatus::Ok);
        regorus_result_drop(r);

        regorus_alias_registry_drop(reg);
    }

    #[test]
    fn normalize_data_plane_manifest() {
        let reg = build_registry_with_manifest(MANIFEST);

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
        let builder = regorus_alias_registry_builder_new();
        let r = regorus_alias_registry_builder_build(builder);
        let reg = assert_ok_pointer(&r) as *mut RegorusAliasRegistry;
        regorus_result_drop(r);
        regorus_alias_registry_builder_drop(builder);

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
        assert_eq!(envelope["resource"]["foo"], 1);
        assert_eq!(envelope["resource"]["name"], "test");

        regorus_alias_registry_drop(reg);
    }
}

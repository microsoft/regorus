// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::common::{from_c_str, to_shared_ref, RegorusResult, RegorusStatus};
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

// ---------------------------------------------------------------------------
// Azure Policy JSON compilation
// ---------------------------------------------------------------------------

/// Compile an Azure Policy JSON policy rule into an RVM program.
///
/// Parses the JSON `policyRule` (the `{ "if": ..., "then": ... }` object),
/// resolves aliases using the provided registry, and compiles the result
/// into an RVM [`Program`] that can be loaded into a [`RegorusRvm`].
///
/// # Parameters
/// * `registry` - Alias registry handle, or null.
/// * `policy_rule_json` - JSON string containing the policyRule object
///
/// # Null registry behavior
///
/// When `registry` is null, compilation proceeds **without alias resolution**.
/// Field references that correspond to Azure resource provider aliases
/// (e.g. `Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly`) will
/// be compiled as raw property paths rather than being resolved to their
/// short forms.  This means:
///
/// - Policies that rely on aliases will **silently produce incorrect
///   evaluation results** because the field paths won't match the
///   normalized resource structure.
/// - **Modify / Append** effect policies will **skip the modifiability
///   validation** that normally rejects writes to non-modifiable aliases
///   at compile time.
///
/// Pass null only when the policy is known to contain no alias references
/// (e.g. simple `type` / `location` checks, or in unit-test scenarios).
///
/// # Returns
/// Returns a `RegorusResult` containing a `RegorusProgram` pointer on success.
///
/// # Safety
/// `policy_rule_json` must be a valid null-terminated UTF-8 string.
/// If `registry` is non-null it must be a valid `RegorusAliasRegistry` pointer.
/// The caller must eventually call `regorus_program_drop` on the returned handle.
#[cfg(all(feature = "azure_policy", feature = "rvm"))]
#[no_mangle]
pub extern "C" fn regorus_compile_azure_policy_rule(
    registry: *const crate::alias_registry::RegorusAliasRegistry,
    policy_rule_json: *const c_char,
) -> RegorusResult {
    use crate::alias_registry::RegorusAliasRegistry;
    use crate::rvm::RegorusProgram;
    use alloc::sync::Arc;
    use regorus::languages::azure_policy::{compiler, parser};
    use regorus::Rc;
    use regorus::Source;

    with_unwind_guard(|| {
        let result = || -> Result<RegorusProgram, (RegorusStatus, alloc::string::String)> {
            let json_str = from_c_str(policy_rule_json).map_err(|e| {
                (
                    RegorusStatus::InvalidDataFormat,
                    format!("Invalid policy rule JSON string: {e}"),
                )
            })?;

            let source = Source::from_contents("policy_rule".into(), json_str).map_err(|e| {
                (
                    RegorusStatus::InvalidDataFormat,
                    format!("Failed to create source: {e}"),
                )
            })?;

            let ast = parser::parse_policy_rule(&source).map_err(|e| {
                (
                    RegorusStatus::InvalidPolicy,
                    format!("Failed to parse policy rule: {e}"),
                )
            })?;

            let program = if registry.is_null() {
                compiler::compile_policy_rule(&ast)
            } else {
                let reg: &RegorusAliasRegistry = to_shared_ref(registry).map_err(|e| {
                    (
                        RegorusStatus::InvalidArgument,
                        format!("Invalid alias registry: {e}"),
                    )
                })?;
                compiler::compile_policy_rule_with_aliases(&ast, reg.inner())
            };

            program
                .map(|p| RegorusProgram {
                    program: Arc::new(Rc::try_unwrap(p).unwrap_or_else(|rc| (*rc).clone())),
                })
                .map_err(|e| {
                    (
                        RegorusStatus::CompilationFailed,
                        format!("Failed to compile policy rule: {e}"),
                    )
                })
        }();

        match result {
            Ok(program) => {
                RegorusResult::ok_pointer(Box::into_raw(Box::new(program)) as *mut c_void)
            }
            Err((status, msg)) => RegorusResult::err_with_message(status, msg),
        }
    })
}

/// Compile a full Azure Policy definition JSON into an RVM program.
///
/// Parses the JSON policy definition (which includes `policyRule`, `parameters`,
/// `displayName`, etc.), resolves aliases using the provided registry, and
/// compiles the result into an RVM [`Program`].
///
/// The definition JSON may be in either wrapped or unwrapped form:
/// - **Wrapped**: `{ "properties": { "policyRule": ..., "parameters": ... }, "id": ... }`
/// - **Unwrapped**: `{ "policyRule": ..., "parameters": ..., "displayName": ... }`
///
/// # Parameters
/// * `registry` - Alias registry handle, or null.
/// * `policy_definition_json` - JSON string containing the full policy definition
///
/// # Null registry behavior
///
/// When `registry` is null, compilation proceeds **without alias resolution**.
/// Field references that correspond to Azure resource provider aliases will
/// be compiled as raw property paths rather than being resolved.  This means:
///
/// - Policies that rely on aliases will **silently produce incorrect
///   evaluation results**.
/// - **Modify / Append** effect policies will **skip the modifiability
///   validation** that normally rejects writes to non-modifiable aliases
///   at compile time.
///
/// Pass null only when the policy is known to contain no alias references
/// (e.g. simple `type` / `location` checks, or in unit-test scenarios).
///
/// # Returns
/// Returns a `RegorusResult` containing a `RegorusProgram` pointer on success.
///
/// # Safety
/// `policy_definition_json` must be a valid null-terminated UTF-8 string.
/// If `registry` is non-null it must be a valid `RegorusAliasRegistry` pointer.
/// The caller must eventually call `regorus_program_drop` on the returned handle.
#[cfg(all(feature = "azure_policy", feature = "rvm"))]
#[no_mangle]
pub extern "C" fn regorus_compile_azure_policy_definition(
    registry: *const crate::alias_registry::RegorusAliasRegistry,
    policy_definition_json: *const c_char,
) -> RegorusResult {
    use crate::alias_registry::RegorusAliasRegistry;
    use crate::rvm::RegorusProgram;
    use alloc::sync::Arc;
    use regorus::languages::azure_policy::{compiler, parser};
    use regorus::Rc;
    use regorus::Source;

    with_unwind_guard(|| {
        let result = || -> Result<RegorusProgram, (RegorusStatus, alloc::string::String)> {
            let json_str = from_c_str(policy_definition_json).map_err(|e| {
                (
                    RegorusStatus::InvalidDataFormat,
                    format!("Invalid policy definition JSON string: {e}"),
                )
            })?;

            let source =
                Source::from_contents("policy_definition".into(), json_str).map_err(|e| {
                    (
                        RegorusStatus::InvalidDataFormat,
                        format!("Failed to create source: {e}"),
                    )
                })?;

            let defn = parser::parse_policy_definition(&source).map_err(|e| {
                (
                    RegorusStatus::InvalidPolicy,
                    format!("Failed to parse policy definition: {e}"),
                )
            })?;

            let program = if registry.is_null() {
                compiler::compile_policy_definition(&defn)
            } else {
                let reg: &RegorusAliasRegistry = to_shared_ref(registry).map_err(|e| {
                    (
                        RegorusStatus::InvalidArgument,
                        format!("Invalid alias registry: {e}"),
                    )
                })?;
                compiler::compile_policy_definition_with_aliases(&defn, reg.inner())
            };

            program
                .map(|p| RegorusProgram {
                    program: Arc::new(Rc::try_unwrap(p).unwrap_or_else(|rc| (*rc).clone())),
                })
                .map_err(|e| {
                    (
                        RegorusStatus::CompilationFailed,
                        format!("Failed to compile policy definition: {e}"),
                    )
                })
        }();

        match result {
            Ok(program) => {
                RegorusResult::ok_pointer(Box::into_raw(Box::new(program)) as *mut c_void)
            }
            Err((status, msg)) => RegorusResult::err_with_message(status, msg),
        }
    })
}

#[cfg(feature = "std")]
fn report_module_error(index: usize, kind: &str, err: &anyhow::Error) {
    eprintln!("Invalid {} at index {}: {}", kind, index, err);
}

#[cfg(not(feature = "std"))]
fn report_module_error(_index: usize, _kind: &str, _err: &anyhow::Error) {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::regorus_result_drop;
    use core::ffi::CStr;
    use std::ffi::CString;

    fn c(s: &str) -> CString {
        CString::new(s).expect("CString::new failed")
    }

    fn assert_ok_pointer(r: &RegorusResult) -> *mut c_void {
        assert_eq!(
            r.status,
            RegorusStatus::Ok,
            "expected Ok, got {:?}",
            r.status
        );
        assert!(!r.pointer_value.is_null(), "expected non-null pointer");
        r.pointer_value
    }

    #[cfg(all(feature = "azure_policy", feature = "rvm"))]
    mod azure_policy_json {
        use super::*;
        use crate::alias_registry::regorus_alias_registry_drop;
        use crate::rvm::{
            regorus_program_drop, regorus_rvm_drop, regorus_rvm_execute_entry_point_by_name,
            regorus_rvm_load_program, regorus_rvm_new, regorus_rvm_set_context,
            regorus_rvm_set_input, RegorusProgram,
        };

        const ALIASES: &str = r#"[{
            "namespace": "Microsoft.Storage",
            "resourceTypes": [{
                "resourceType": "storageAccounts",
                "aliases": [{
                    "name": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly",
                    "defaultPath": "properties.supportsHttpsTrafficOnly",
                    "paths": []
                }, {
                    "name": "Microsoft.Storage/storageAccounts/minimumTlsVersion",
                    "defaultPath": "properties.minimumTlsVersion",
                    "paths": []
                }]
            }]
        }]"#;

        const SIMPLE_POLICY_RULE: &str = r#"{
            "if": {
                "field": "type",
                "equals": "Microsoft.Storage/storageAccounts"
            },
            "then": { "effect": "audit" }
        }"#;

        const ALIAS_POLICY_RULE: &str = r#"{
            "if": {
                "allOf": [
                    { "field": "type", "equals": "Microsoft.Storage/storageAccounts" },
                    { "field": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly", "equals": false }
                ]
            },
            "then": { "effect": "deny" }
        }"#;

        const POLICY_DEFINITION: &str = r#"{
            "displayName": "Require HTTPS for storage accounts",
            "policyType": "Custom",
            "mode": "Indexed",
            "parameters": {
                "effect": {
                    "type": "String",
                    "defaultValue": "deny"
                }
            },
            "policyRule": {
                "if": {
                    "allOf": [
                        { "field": "type", "equals": "Microsoft.Storage/storageAccounts" },
                        { "field": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly", "equals": false }
                    ]
                },
                "then": { "effect": "[parameters('effect')]" }
            }
        }"#;

        /// Wrap a normalized resource JSON into the input envelope expected by
        /// the compiled Azure Policy RVM program.
        fn wrap_input(resource_json: &str, parameters_json: &str) -> String {
            format!(r#"{{"resource": {resource_json}, "parameters": {parameters_json}}}"#)
        }

        fn build_registry_with_json(
            json: &str,
        ) -> *mut crate::alias_registry::RegorusAliasRegistry {
            let builder = crate::alias_registry::regorus_alias_registry_builder_new();
            let json_c = c(json);
            let r = crate::alias_registry::regorus_alias_registry_builder_load_json(
                builder,
                json_c.as_ptr(),
            );
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            let r = crate::alias_registry::regorus_alias_registry_builder_build(builder);
            let registry =
                assert_ok_pointer(&r) as *mut crate::alias_registry::RegorusAliasRegistry;
            regorus_result_drop(r);
            crate::alias_registry::regorus_alias_registry_builder_drop(builder);
            registry
        }

        /// Helper: compile a policy rule, execute it with input, and return the
        /// result string.
        unsafe fn compile_and_eval_rule(
            registry: *const crate::alias_registry::RegorusAliasRegistry,
            policy_rule: &str,
            input_json: &str,
        ) -> String {
            let rule_c = c(policy_rule);
            let r = regorus_compile_azure_policy_rule(registry, rule_c.as_ptr());
            let program_ptr = assert_ok_pointer(&r) as *mut RegorusProgram;
            regorus_result_drop(r);

            let vm = regorus_rvm_new();
            assert!(!vm.is_null());

            let r = regorus_rvm_load_program(vm, program_ptr);
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            let input_c = c(input_json);
            let r = regorus_rvm_set_input(vm, input_c.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            let entry = c("main");
            let r = regorus_rvm_execute_entry_point_by_name(vm, entry.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok, "execute failed");
            let output = CStr::from_ptr(r.output)
                .to_str()
                .expect("invalid UTF-8")
                .to_string();
            regorus_result_drop(r);

            regorus_rvm_drop(vm);
            regorus_program_drop(program_ptr);
            output
        }

        #[test]
        fn compile_simple_rule_no_aliases() {
            let rule_c = c(SIMPLE_POLICY_RULE);
            let r = regorus_compile_azure_policy_rule(core::ptr::null_mut(), rule_c.as_ptr());
            let ptr = assert_ok_pointer(&r);
            regorus_result_drop(r);
            regorus_program_drop(ptr as *mut RegorusProgram);
        }

        #[test]
        fn compile_rule_with_aliases() {
            let reg = build_registry_with_json(ALIASES);

            let rule_c = c(ALIAS_POLICY_RULE);
            let r = regorus_compile_azure_policy_rule(reg, rule_c.as_ptr());
            let ptr = assert_ok_pointer(&r);
            regorus_result_drop(r);

            regorus_program_drop(ptr as *mut RegorusProgram);
            regorus_alias_registry_drop(reg);
        }

        #[test]
        fn compile_and_eval_simple_rule_matching() {
            let input = wrap_input(r#"{"type":"microsoft.storage/storageaccounts"}"#, "{}");
            let result =
                unsafe { compile_and_eval_rule(core::ptr::null_mut(), SIMPLE_POLICY_RULE, &input) };
            let parsed: serde_json::Value =
                serde_json::from_str(&result).expect("result should be valid JSON");
            assert_eq!(
                parsed["effect"], "audit",
                "expected audit effect, got: {result}"
            );
        }

        #[test]
        fn compile_and_eval_simple_rule_not_matching() {
            let input = wrap_input(r#"{"type":"microsoft.compute/virtualmachines"}"#, "{}");
            let result =
                unsafe { compile_and_eval_rule(core::ptr::null_mut(), SIMPLE_POLICY_RULE, &input) };
            // When the "if" condition doesn't match, the result should be undefined
            assert!(
                result.contains("undefined"),
                "expected undefined for non-matching input, got: {result}"
            );
        }

        #[test]
        fn compile_and_eval_alias_rule_deny() {
            let reg = build_registry_with_json(ALIASES);

            // Non-compliant resource: HTTPS not enabled (normalized form)
            let input = wrap_input(
                r#"{"type": "microsoft.storage/storageaccounts", "supportshttpstrafficonly": false}"#,
                "{}",
            );
            let result = unsafe { compile_and_eval_rule(reg, ALIAS_POLICY_RULE, &input) };
            let parsed: serde_json::Value = serde_json::from_str(&result).expect("valid JSON");
            assert_eq!(parsed["effect"], "deny", "expected deny, got: {result}");

            regorus_alias_registry_drop(reg);
        }

        #[test]
        fn compile_and_eval_alias_rule_compliant() {
            let reg = build_registry_with_json(ALIASES);

            // Compliant resource: HTTPS enabled (normalized form)
            let input = wrap_input(
                r#"{"type": "microsoft.storage/storageaccounts", "supportshttpstrafficonly": true}"#,
                "{}",
            );
            let result = unsafe { compile_and_eval_rule(reg, ALIAS_POLICY_RULE, &input) };
            assert!(
                result.contains("undefined"),
                "expected undefined for compliant resource, got: {result}"
            );

            regorus_alias_registry_drop(reg);
        }

        #[test]
        fn compile_definition_no_aliases() {
            let defn_c = c(POLICY_DEFINITION);
            let r = regorus_compile_azure_policy_definition(core::ptr::null_mut(), defn_c.as_ptr());
            let ptr = assert_ok_pointer(&r);
            regorus_result_drop(r);
            regorus_program_drop(ptr as *mut RegorusProgram);
        }

        #[test]
        fn compile_definition_with_aliases_and_eval() {
            let reg = build_registry_with_json(ALIASES);

            let defn_c = c(POLICY_DEFINITION);
            let r = regorus_compile_azure_policy_definition(reg, defn_c.as_ptr());
            let program_ptr = assert_ok_pointer(&r) as *mut RegorusProgram;
            regorus_result_drop(r);

            // Evaluate with a non-compliant resource (normalized form, wrapped in envelope)
            unsafe {
                let vm = regorus_rvm_new();
                let r = regorus_rvm_load_program(vm, program_ptr);
                assert_eq!(r.status, RegorusStatus::Ok);
                regorus_result_drop(r);

                let input_json = wrap_input(
                    r#"{"type": "microsoft.storage/storageaccounts", "supportshttpstrafficonly": false}"#,
                    "{}",
                );
                let input = c(&input_json);
                let r = regorus_rvm_set_input(vm, input.as_ptr());
                assert_eq!(r.status, RegorusStatus::Ok);
                regorus_result_drop(r);

                let entry = c("main");
                let r = regorus_rvm_execute_entry_point_by_name(vm, entry.as_ptr());
                assert_eq!(r.status, RegorusStatus::Ok);
                let result = CStr::from_ptr(r.output)
                    .to_str()
                    .expect("UTF-8")
                    .to_string();
                regorus_result_drop(r);

                let parsed: serde_json::Value = serde_json::from_str(&result).unwrap();
                // The default parameter value is "deny"
                assert_eq!(parsed["effect"], "deny", "got: {result}");

                regorus_rvm_drop(vm);
                regorus_program_drop(program_ptr);
            }

            regorus_alias_registry_drop(reg);
        }

        #[test]
        fn invalid_json_returns_error() {
            let bad = c("not valid json");
            let r = regorus_compile_azure_policy_rule(core::ptr::null_mut(), bad.as_ptr());
            assert_ne!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);
        }

        #[test]
        fn invalid_definition_returns_error() {
            let bad = c(r#"{"not": "a policy definition"}"#);
            let r = regorus_compile_azure_policy_definition(core::ptr::null_mut(), bad.as_ptr());
            assert_ne!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);
        }

        /// Policy rule that uses a context function (subscription()).
        const CONTEXT_POLICY_RULE: &str = r#"{
            "if": {
                "allOf": [
                    { "field": "type", "equals": "Microsoft.Storage/storageAccounts" },
                    { "value": "[subscription().subscriptionId]", "equals": "sub-123" }
                ]
            },
            "then": { "effect": "deny" }
        }"#;

        #[test]
        fn context_policy_evaluates_with_set_context() {
            let rule_c = c(CONTEXT_POLICY_RULE);
            let r = regorus_compile_azure_policy_rule(core::ptr::null_mut(), rule_c.as_ptr());
            let program = assert_ok_pointer(&r) as *mut RegorusProgram;
            regorus_result_drop(r);

            let vm = regorus_rvm_new();
            assert!(!vm.is_null());

            let r = regorus_rvm_load_program(vm, program);
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            // Set the context with subscription info
            let context = c(r#"{"subscription": {"subscriptionId": "sub-123"}}"#);
            let r = regorus_rvm_set_context(vm, context.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            // Set matching input
            let input = c(&wrap_input(
                r#"{"type": "microsoft.storage/storageaccounts"}"#,
                "{}",
            ));
            let r = regorus_rvm_set_input(vm, input.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            let entry = c("main");
            let r = regorus_rvm_execute_entry_point_by_name(vm, entry.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok);
            let output = unsafe { CStr::from_ptr(r.output) }.to_str().unwrap();
            assert!(
                output.contains("deny"),
                "expected deny effect with matching context, got: {output}"
            );
            regorus_result_drop(r);

            regorus_rvm_drop(vm);
            regorus_program_drop(program);
        }

        #[test]
        fn context_policy_undefined_without_context() {
            let rule_c = c(CONTEXT_POLICY_RULE);
            let r = regorus_compile_azure_policy_rule(core::ptr::null_mut(), rule_c.as_ptr());
            let program = assert_ok_pointer(&r) as *mut RegorusProgram;
            regorus_result_drop(r);

            let vm = regorus_rvm_new();
            assert!(!vm.is_null());

            let r = regorus_rvm_load_program(vm, program);
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            // No context set — subscription() will be undefined
            let input = c(&wrap_input(
                r#"{"type": "microsoft.storage/storageaccounts"}"#,
                "{}",
            ));
            let r = regorus_rvm_set_input(vm, input.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok);
            regorus_result_drop(r);

            let entry = c("main");
            let r = regorus_rvm_execute_entry_point_by_name(vm, entry.as_ptr());
            assert_eq!(r.status, RegorusStatus::Ok);
            let output = unsafe { CStr::from_ptr(r.output) }.to_str().unwrap();
            assert!(
                output.contains("undefined"),
                "expected undefined without context, got: {output}"
            );
            regorus_result_drop(r);

            regorus_rvm_drop(vm);
            regorus_program_drop(program);
        }
    }
}

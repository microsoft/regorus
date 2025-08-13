// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::*;
use anyhow::Result;
use std::os::raw::c_char;

/// Wrapper for `regorus::CompiledPolicy`.
#[derive(Clone)]
pub struct RegorusCompiledPolicy {
    pub(crate) compiled_policy: regorus::CompiledPolicy,
}

/// Drop a `RegorusCompiledPolicy`.
#[no_mangle]
pub extern "C" fn regorus_compiled_policy_drop(compiled_policy: *mut RegorusCompiledPolicy) {
    if let Ok(cp) = to_ref(compiled_policy) {
        unsafe {
            let _ = Box::from_raw(std::ptr::from_mut(cp));
        }
    }
}

/// Evaluate the compiled policy with the given input.
///
/// For target policies, evaluates the target's effect rule.
/// For regular policies, evaluates the originally compiled rule.
///
/// * `input`: JSON encoded input data (resource) to validate against the policy.
#[no_mangle]
pub extern "C" fn regorus_compiled_policy_eval_with_input(
    compiled_policy: *mut RegorusCompiledPolicy,
    input: *const c_char,
) -> RegorusResult {
    let output = || -> Result<String> {
        let input_value = regorus::Value::from_json_str(&from_c_str(input)?)?;
        let result = to_ref(compiled_policy)?
            .compiled_policy
            .eval_with_input(input_value)?;
        result.to_json_str()
    }();

    match output {
        Ok(out) => RegorusResult::ok_string(out),
        Err(e) => to_regorus_result(Err(e)),
    }
}

/// Get information about the compiled policy including metadata about modules,
/// target configuration, and resource types.
///
/// Returns a JSON-encoded `PolicyInfo` struct containing comprehensive
/// information about the compiled policy such as module IDs, target name,
/// applicable resource types, entry point rule, and parameters.
#[no_mangle]
pub extern "C" fn regorus_compiled_policy_get_policy_info(
    compiled_policy: *mut RegorusCompiledPolicy,
) -> RegorusResult {
    let output = || -> Result<String> {
        let info = to_ref(compiled_policy)?.compiled_policy.get_policy_info()?;
        serde_json::to_string(&info)
            .map_err(|e| anyhow::anyhow!("Failed to serialize policy info: {}", e))
    }();

    match output {
        Ok(out) => RegorusResult::ok_string(out),
        Err(e) => to_regorus_result(Err(e)),
    }
}

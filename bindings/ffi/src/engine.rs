// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::{
    from_c_str, to_ref, to_regorus_result, to_regorus_string_result, RegorusResult, RegorusStatus,
};
use crate::compiled_policy::RegorusCompiledPolicy;
use crate::limits::RegorusExecutionTimerConfig;
use crate::lock::{new_handle, read, try_read, try_write, Handle, ReadGuard, WriteGuard};
use crate::panic_guard::with_unwind_guard;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use anyhow::{anyhow, Result};
use core::ffi::{c_char, c_void};
use core::ptr;

/// Wrapper for `regorus::Engine`.
pub struct RegorusEngine {
    engine: Handle<::regorus::Engine>,
}

impl RegorusEngine {
    fn new(engine: ::regorus::Engine) -> Self {
        Self {
            engine: new_handle(engine),
        }
    }

    fn contention_error() -> anyhow::Error {
        anyhow!(
            "regorus engine handle is already in use; clone the engine before sharing across threads"
        )
    }

    fn try_write(&self) -> Result<WriteGuard<'_, ::regorus::Engine>> {
        try_write(&self.engine).ok_or_else(Self::contention_error)
    }

    fn try_read(&self) -> Result<ReadGuard<'_, ::regorus::Engine>> {
        try_read(&self.engine).ok_or_else(Self::contention_error)
    }
}

impl Clone for RegorusEngine {
    fn clone(&self) -> Self {
        let guard = read(&self.engine);
        Self::new((*guard).clone())
    }
}

#[cfg(all(test, feature = "contention_checks", feature = "std"))]
mod tests {
    use super::RegorusEngine;

    #[test]
    fn detects_handle_contention() {
        let engine = RegorusEngine::new(::regorus::Engine::new());

        let _first_guard = engine.try_write().expect("initial lock should succeed");
        let err = engine
            .try_write()
            .expect_err("contention detection must reject the second lock");

        assert!(
            err.to_string().contains("engine handle is already in use"),
            "unexpected error message: {err}"
        );
    }
}

#[cfg(all(test, feature = "std"))]
mod panic_tests {
    use super::{
        regorus_engine_drop, regorus_engine_eval_query, regorus_engine_get_policies,
        regorus_engine_new,
    };
    use crate::common::{regorus_result_drop, RegorusStatus};
    use crate::panic_guard::{is_poisoned, reset_poison};
    use alloc::boxed::Box;
    use regorus::Value;
    use std::ffi::{CStr, CString};

    #[test]
    fn catches_extension_panics_and_marks_poison() {
        reset_poison();

        let engine_ptr = regorus_engine_new();
        assert!(!engine_ptr.is_null(), "engine allocation must succeed");
        assert!(!is_poisoned(), "guard must start unpoisoned");

        unsafe {
            let engine = &mut *engine_ptr;
            {
                let mut guard = engine
                    .try_write()
                    .expect("exclusive access to configure engine");
                guard
                    .add_extension(
                        "panic_extension".to_string(),
                        0,
                        Box::new(|_| -> anyhow::Result<Value> { panic!("ffi extension panic") }),
                    )
                    .expect("extension registration must succeed");
                guard
                    .add_policy(
                        "panic.rego".to_string(),
                        "package panic\n\ndefault allow = false\n\nallow if {\n  panic_extension()\n}"
                            .to_string(),
                    )
                    .expect("policy registration must succeed");
            }
        }

        let query = CString::new("data.panic.allow").expect("valid query string");
        let panic_result = regorus_engine_eval_query(engine_ptr, query.as_ptr());
        assert!(matches!(panic_result.status, RegorusStatus::Panic));
        unsafe {
            assert!(
                !panic_result.error_message.is_null(),
                "panic details must be present"
            );
            let message = CStr::from_ptr(panic_result.error_message)
                .to_str()
                .expect("error message utf8");
            assert!(
                message.contains("ffi extension panic"),
                "panic payload must bubble across guard"
            );
        }
        regorus_result_drop(panic_result);
        assert!(is_poisoned(), "engine must be marked poisoned after panic");

        let poisoned_result = regorus_engine_get_policies(engine_ptr);
        assert!(matches!(poisoned_result.status, RegorusStatus::Poisoned));
        unsafe {
            assert!(
                !poisoned_result.error_message.is_null(),
                "poison message must be present"
            );
            let message = CStr::from_ptr(poisoned_result.error_message)
                .to_str()
                .expect("poison message utf8");
            assert!(
                message.contains("regorus is poisoned"),
                "poison message must inform callers"
            );
        }
        regorus_result_drop(poisoned_result);

        regorus_engine_drop(engine_ptr);
        reset_poison();
    }
}

#[no_mangle]
#[cfg(feature = "std")]
pub extern "C" fn regorus_engine_test_trigger_panic() -> RegorusResult {
    with_unwind_guard(|| panic!("regorus ffi test panic"))
}

#[no_mangle]
pub extern "C" fn regorus_engine_test_reset_poison() {
    crate::panic_guard::reset_poison();
}

#[no_mangle]
/// Construct a new Engine
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html
pub extern "C" fn regorus_engine_new() -> *mut RegorusEngine {
    let mut engine = ::regorus::Engine::new();

    // For more OPA compatibility out of the box, we ask builtins to return undefined
    // instead of raising errors in certain failure scenarios.
    engine.set_strict_builtin_errors(false);

    Box::into_raw(Box::new(RegorusEngine::new(engine)))
}

/// Clone a [`RegorusEngine`]
///
/// To avoid having to parse same policy again, the engine can be cloned
/// after policies and data have been added.
///
#[no_mangle]
pub extern "C" fn regorus_engine_clone(engine: *mut RegorusEngine) -> *mut RegorusEngine {
    match to_ref(engine) {
        Ok(e) => Box::into_raw(Box::new(e.clone())),
        _ => ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn regorus_engine_drop(engine: *mut RegorusEngine) {
    if let Ok(e) = to_ref(engine) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(e));
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
    with_unwind_guard(|| {
        to_regorus_string_result(|| -> Result<String> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.add_policy(from_c_str(path)?, from_c_str(rego)?)
        }())
    })
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_add_policy_from_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_string_result(|| -> Result<String> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.add_policy_from_file(from_c_str(path)?)
        }())
    })
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
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.add_data(regorus::Value::from_json_str(&from_c_str(data)?)?)
        }())
    })
}

/// Get list of loaded Rego packages as JSON.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_packages
#[no_mangle]
pub extern "C" fn regorus_engine_get_packages(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_string_result(|| -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            serde_json::to_string_pretty(&guard.get_packages()?).map_err(anyhow::Error::msg)
        }())
    })
}

/// Get list of policies as JSON.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_policies
#[no_mangle]
pub extern "C" fn regorus_engine_get_policies(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_string_result(|| -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            guard.get_policies_as_json()
        }())
    })
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_add_data_from_json_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.add_data(regorus::Value::from_json_file(from_c_str(path)?)?)
        }())
    })
}

/// Clear policy data.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_data
#[no_mangle]
pub extern "C" fn regorus_engine_clear_data(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.clear_data();
            Ok(())
        }())
    })
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
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.set_input(regorus::Value::from_json_str(&from_c_str(input)?)?);
            Ok(())
        }())
    })
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn regorus_engine_set_input_from_json_file(
    engine: *mut RegorusEngine,
    path: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.set_input(regorus::Value::from_json_file(from_c_str(path)?)?);
            Ok(())
        }())
    })
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
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            let results = guard.eval_query(from_c_str(query)?, false)?;
            Ok(serde_json::to_string_pretty(&results)?)
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
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
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.eval_rule(from_c_str(rule)?)?.to_json_str()
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
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
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.set_enable_coverage(enable);
            Ok(())
        }())
    })
}

/// Get coverage report.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_coverage_report
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_get_coverage_report(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            Ok(serde_json::to_string_pretty(&guard.get_coverage_report()?)?)
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Enable/disable strict builtin errors.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_strict_builtin_errors
/// * `strict`: Whether to raise errors or return undefined on certain scenarios.
#[no_mangle]
pub extern "C" fn regorus_engine_set_strict_builtin_errors(
    engine: *mut RegorusEngine,
    strict: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.set_strict_builtin_errors(strict);
            Ok(())
        }())
    })
}

#[no_mangle]
/// Configure the execution timer for a specific engine instance.
pub extern "C" fn regorus_engine_set_execution_timer_config(
    engine: *mut RegorusEngine,
    config: *const RegorusExecutionTimerConfig,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        let engine = to_ref(engine)?;
        let config = unsafe {
            config
                .as_ref()
                .copied()
                .ok_or_else(|| anyhow!("execution timer config pointer is null"))?
        };
        let mut guard = engine.try_write()?;
        guard.set_execution_timer_config(config.to_execution_timer_config()?);
        Ok(())
    }())
}

#[no_mangle]
/// Clear the engine-specific execution timer configuration.
pub extern "C" fn regorus_engine_clear_execution_timer_config(
    engine: *mut RegorusEngine,
) -> RegorusResult {
    to_regorus_result(|| -> Result<()> {
        let engine = to_ref(engine)?;
        let mut guard = engine.try_write()?;
        guard.clear_execution_timer_config();
        Ok(())
    }())
}

/// Get pretty printed coverage report.
///
/// See https://docs.rs/regorus/latest/regorus/coverage/struct.Report.html#method.to_string_pretty
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_get_coverage_report_pretty(
    engine: *mut RegorusEngine,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            guard.get_coverage_report()?.to_string_pretty()
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Clear coverage data.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_coverage_data
#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "C" fn regorus_engine_clear_coverage_data(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.clear_coverage_data();
            Ok(())
        }())
    })
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
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.set_gather_prints(enable);
            Ok(())
        }())
    })
}

/// Take all the gathered print statements.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.take_prints
#[no_mangle]
pub extern "C" fn regorus_engine_take_prints(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            Ok(serde_json::to_string_pretty(&guard.take_prints()?)?)
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Get AST of policies.
///
/// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_ast_as_json
#[no_mangle]
#[cfg(feature = "ast")]
pub extern "C" fn regorus_engine_get_ast_as_json(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            guard.get_ast_as_json()
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Gets the package names defined in each policy added to the engine.
///
/// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_policy_package_names
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_engine_get_policy_package_names(
    engine: *mut RegorusEngine,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            serde_json::to_string_pretty(&guard.get_policy_package_names()?)
                .map_err(anyhow::Error::msg)
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Gets the parameters defined in each policy added to the engine.
///
/// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_policy_parameters
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_engine_get_policy_parameters(
    engine: *mut RegorusEngine,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let engine = to_ref(engine)?;
            let guard = engine.try_read()?;
            serde_json::to_string_pretty(&guard.get_policy_parameters()?)
                .map_err(anyhow::Error::msg)
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Enable/disable rego v1.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_rego_v0
#[no_mangle]
pub extern "C" fn regorus_engine_set_rego_v0(
    engine: *mut RegorusEngine,
    enable: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<()> {
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            guard.set_rego_v0(enable);
            Ok(())
        }();
        match output {
            Ok(()) => RegorusResult::ok_void(),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Compile a target-aware policy from the current engine state.
///
/// This method creates a compiled policy that can work with Azure Policy targets,
/// enabling resource type inference and target-specific evaluation.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.compile_for_target
#[no_mangle]
#[cfg(feature = "azure_policy")]
pub extern "C" fn regorus_engine_compile_for_target(engine: *mut RegorusEngine) -> RegorusResult {
    with_unwind_guard(|| {
        let engine = match to_ref(engine) {
            Ok(engine) => engine,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("Failed to get engine reference: {e}"),
                )
            }
        };

        let mut guard = match engine.try_write() {
            Ok(guard) => guard,
            Err(e) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::Error,
                    format!("Failed to lock engine: {e}"),
                )
            }
        };

        match guard.compile_for_target() {
            Ok(compiled_policy) => {
                let wrapped_policy = RegorusCompiledPolicy { compiled_policy };
                let boxed_policy = Box::new(wrapped_policy);
                RegorusResult::ok_pointer(Box::into_raw(boxed_policy) as *mut c_void)
            }
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("Failed to compile for target: {e}"),
            ),
        }
    })
}

/// Compile a policy with a specific entry point rule.
///
/// This method creates a compiled policy that evaluates a specific rule as the entry point.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.compile_with_entrypoint
/// * `rule`: The specific rule path to evaluate (e.g., "data.policy.allow")
#[no_mangle]
pub extern "C" fn regorus_engine_compile_with_entrypoint(
    engine: *mut RegorusEngine,
    rule: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let result = || -> Result<RegorusCompiledPolicy> {
            let rule_str = from_c_str(rule)?;
            let rule_rc: regorus::Rc<str> = rule_str.into();
            let engine = to_ref(engine)?;
            let mut guard = engine.try_write()?;
            let compiled_policy = guard.compile_with_entrypoint(&rule_rc)?;
            Ok(RegorusCompiledPolicy { compiled_policy })
        }();

        match result {
            Ok(wrapped_policy) => {
                let boxed_policy = Box::new(wrapped_policy);
                RegorusResult::ok_pointer(Box::into_raw(boxed_policy) as *mut c_void)
            }
            Err(e) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("Failed to compile with entrypoint: {e}"),
            ),
        }
    })
}

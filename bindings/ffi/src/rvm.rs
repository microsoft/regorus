// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::{
    from_c_str, to_ref, to_regorus_result, to_shared_ref, RegorusBuffer, RegorusResult,
    RegorusStatus,
};
use crate::compile::RegorusPolicyModule;
use crate::compiled_policy::RegorusCompiledPolicy;
use crate::limits::{RegorusExecutionTimerConfig, RegorusMemoryBudgetConfig};
use crate::lock::{new_handle, try_read, try_write, Handle, ReadGuard, WriteGuard};
use crate::panic_guard::with_unwind_guard;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use anyhow::{anyhow, Result};
use core::ffi::{c_char, c_void};
use core::ptr;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{
    generate_assembly_listing, generate_tabular_assembly_listing, AssemblyListingConfig,
    DeserializationResult, Program,
};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::utils::limits::{
    check_memory_limit_if_needed, with_unowned_memory_budget_scope_for_ffi,
};
use regorus::PolicyModule;
use regorus::Value;

/// Wrapper for `regorus::rvm::Program`.
#[derive(Clone)]
pub struct RegorusProgram {
    pub(crate) program: Arc<Program>,
}

/// Wrapper for `regorus::rvm::RegoVM`.
pub struct RegorusRvm {
    vm: Handle<RegoVM>,
}

impl RegorusRvm {
    fn new(vm: RegoVM) -> Self {
        Self { vm: new_handle(vm) }
    }

    fn contention_error() -> anyhow::Error {
        anyhow!("regorus rvm handle is already in use; create a separate VM per thread")
    }

    fn try_write(&self) -> Result<WriteGuard<'_, RegoVM>> {
        try_write(&self.vm).ok_or_else(Self::contention_error)
    }

    fn try_read(&self) -> Result<ReadGuard<'_, RegoVM>> {
        try_read(&self.vm).ok_or_else(Self::contention_error)
    }
}

fn to_rvm_error_result(err: anyhow::Error) -> RegorusResult {
    let status = match err.downcast_ref::<VmError>() {
        Some(VmError::MemoryBudgetExceeded { .. }) => RegorusStatus::MemoryBudgetExceeded,
        _ => RegorusStatus::Error,
    };
    RegorusResult::err_with_message(status, err.to_string())
}

enum RvmExecution {
    Main,
    Named(String),
    Indexed(usize),
}

fn execute_to_rvm_result(vm: *mut RegorusRvm, execution: RvmExecution) -> RegorusResult {
    let output = || -> Result<RegorusResult> {
        let vm = to_shared_ref(vm as *const RegorusRvm)?;
        let mut guard = vm.try_write()?;

        let output = match execution {
            RvmExecution::Main => guard.execute_to_c_string_for_ffi()?,
            RvmExecution::Named(entry_point) => {
                guard.execute_entry_point_by_name_to_c_string_for_ffi(&entry_point)?
            }
            RvmExecution::Indexed(index) => {
                guard.execute_entry_point_by_index_to_c_string_for_ffi(index)?
            }
        };
        Ok(RegorusResult::ok_c_string(output))
    }();

    match output {
        Ok(result) => result,
        Err(err) => to_rvm_error_result(err),
    }
}

/// Drop a `RegorusProgram`.
#[no_mangle]
pub extern "C" fn regorus_program_drop(program: *mut RegorusProgram) {
    if let Ok(program) = to_ref(program) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(program));
        }
    }
}

/// Drop a `RegorusRvm`.
#[no_mangle]
pub extern "C" fn regorus_rvm_drop(vm: *mut RegorusRvm) {
    if let Ok(vm) = to_ref(vm) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(vm));
        }
    }
}

/// Compile a compiled policy into an RVM program.
///
/// * `compiled_policy` - Compiled policy handle
/// * `entry_points` - Array of entry point rule paths
/// * `entry_points_len` - Number of entry points
#[no_mangle]
pub extern "C" fn regorus_program_compile_from_policy(
    compiled_policy: *mut RegorusCompiledPolicy,
    entry_points: *const *const c_char,
    entry_points_len: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusProgram> {
            if entry_points.is_null() && entry_points_len > 0 {
                return Err(anyhow!("null entry_points pointer"));
            }

            let mut entry_points_vec = Vec::with_capacity(entry_points_len);
            for i in 0..entry_points_len {
                unsafe {
                    let entry_ptr = entry_points.add(i);
                    if entry_ptr.is_null() {
                        return Err(anyhow!("null entry point at index {i}"));
                    }
                    let entry = from_c_str(*entry_ptr)?;
                    entry_points_vec.push(entry);
                }
            }

            let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();

            let compiled_policy =
                &to_shared_ref(compiled_policy as *const RegorusCompiledPolicy)?.compiled_policy;
            let program = Compiler::compile_from_policy(compiled_policy, &entry_points_ref)?;
            Ok(Box::into_raw(Box::new(RegorusProgram { program })))
        }();

        match output {
            Ok(program) => RegorusResult::ok_pointer(program as *mut c_void),
            Err(err) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("RVM compilation failed: {err}"),
            ),
        }
    })
}

/// Shared implementation for compiling an RVM program from data/modules/entry-points
/// with optional host-await builtins.
#[allow(clippy::too_many_arguments)]
fn compile_from_modules_inner(
    data_json: *const c_char,
    modules: *const RegorusPolicyModule,
    modules_len: usize,
    entry_points: *const *const c_char,
    entry_points_len: usize,
    host_await_builtins: *const RegorusHostAwaitBuiltin,
    host_await_builtins_len: usize,
    host_await_builtin_size: usize,
) -> Result<*mut RegorusProgram> {
    if entry_points_len == 0 {
        return Err(anyhow!("entry_points must contain at least one entry"));
    }

    let data_str = from_c_str(data_json)?;
    let data = Value::from_json_str(&data_str)?;
    let policy_modules = convert_c_modules_to_rust(modules, modules_len)?;
    let entry_points_vec = convert_c_entry_points(entry_points, entry_points_len)?;
    let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();

    // Safe: early-return above guarantees entry_points_len > 0, and
    // convert_c_entry_points preserves length, so the slice is non-empty.
    let entry_rule = entry_points_ref[0];

    let compiled_policy =
        regorus::compile_policy_with_entrypoint(data, &policy_modules, entry_rule.into())?;

    // `Compiler::compile_from_policy_with_host_await` with an empty builtins
    // slice is equivalent to `compile_from_policy`, so both FFI entry points
    // route through this single path. A null `host_await_builtins` pointer
    // with `len == 0` is the canonical "no builtins" shape.
    let ha_builtins = convert_c_host_await_builtins(
        host_await_builtins,
        host_await_builtins_len,
        host_await_builtin_size,
    )?;
    let ha_ref: Vec<(&str, usize)> = ha_builtins.iter().map(|(n, a)| (n.as_str(), *a)).collect();

    let program = Compiler::compile_from_policy_with_host_await(
        &compiled_policy,
        &entry_points_ref,
        &ha_ref,
    )?;
    Ok(Box::into_raw(Box::new(RegorusProgram { program })))
}

fn compile_from_modules_result(output: Result<*mut RegorusProgram>) -> RegorusResult {
    match output {
        Ok(program) => RegorusResult::ok_pointer(program as *mut c_void),
        Err(err) => RegorusResult::err_with_message(
            RegorusStatus::CompilationFailed,
            format!("RVM compilation failed: {err}"),
        ),
    }
}

/// Compile an RVM program from data/modules and entry points.
///
/// * `data_json` - JSON string containing static data for policy evaluation
/// * `modules` - Array of policy modules to compile
/// * `modules_len` - Number of modules in the array
/// * `entry_points` - Array of entry point rule paths
/// * `entry_points_len` - Number of entry points
#[no_mangle]
pub extern "C" fn regorus_program_compile_from_modules(
    data_json: *const c_char,
    modules: *const RegorusPolicyModule,
    modules_len: usize,
    entry_points: *const *const c_char,
    entry_points_len: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        compile_from_modules_result(compile_from_modules_inner(
            data_json,
            modules,
            modules_len,
            entry_points,
            entry_points_len,
            core::ptr::null(),
            0,
            core::mem::size_of::<RegorusHostAwaitBuiltin>(),
        ))
    })
}

/// Create a new, empty RVM program.
#[no_mangle]
pub extern "C" fn regorus_program_new() -> *mut RegorusProgram {
    let program = Program::new();
    Box::into_raw(Box::new(RegorusProgram {
        program: Arc::new(program),
    }))
}

/// Serialize a program to the binary RVM format.
#[no_mangle]
pub extern "C" fn regorus_program_serialize_binary(program: *mut RegorusProgram) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusBuffer> {
            let program = &to_shared_ref(program as *const RegorusProgram)?.program;
            let bytes = program.serialize_binary().map_err(|e| anyhow!(e))?;
            Ok(RegorusBuffer::from_vec(bytes))
        }();

        match output {
            Ok(buffer) => RegorusResult::ok_pointer(buffer as *mut c_void),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Deserialize a program from the binary RVM format.
///
/// Returns a `RegorusProgram` handle and sets `is_partial` to true when the
/// program requires recompilation.
#[no_mangle]
pub extern "C" fn regorus_program_deserialize_binary(
    data: *const u8,
    len: usize,
    is_partial: *mut bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<(*mut RegorusProgram, bool)> {
            if data.is_null() {
                if len > 0 {
                    return Err(anyhow!("null data pointer with non-zero length"));
                }
                return Err(anyhow!("null data pointer"));
            }
            let data = unsafe { core::slice::from_raw_parts(data, len) };
            let (program, partial) =
                match Program::deserialize_binary(data).map_err(|e| anyhow!(e))? {
                    DeserializationResult::Complete(program) => (program, false),
                    DeserializationResult::Partial(program) => (program, true),
                };
            Ok((
                Box::into_raw(Box::new(RegorusProgram {
                    program: Arc::new(program),
                })),
                partial,
            ))
        }();

        match output {
            Ok((program, partial)) => {
                if !is_partial.is_null() {
                    unsafe {
                        *is_partial = partial;
                    }
                }
                RegorusResult::ok_pointer(program as *mut c_void)
            }
            Err(err) => {
                RegorusResult::err_with_message(RegorusStatus::InvalidDataFormat, err.to_string())
            }
        }
    })
}

/// Generate a default assembly listing for the program.
#[no_mangle]
pub extern "C" fn regorus_program_generate_listing(program: *mut RegorusProgram) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let program = &to_shared_ref(program as *const RegorusProgram)?.program;
            Ok(generate_assembly_listing(
                program,
                &AssemblyListingConfig::default(),
            ))
        }();

        match output {
            Ok(listing) => RegorusResult::ok_string(listing),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Generate a tabular assembly listing for the program.
#[no_mangle]
pub extern "C" fn regorus_program_generate_tabular_listing(
    program: *mut RegorusProgram,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let program = &to_shared_ref(program as *const RegorusProgram)?.program;
            Ok(generate_tabular_assembly_listing(
                program,
                &AssemblyListingConfig::default(),
            ))
        }();

        match output {
            Ok(listing) => RegorusResult::ok_string(listing),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Construct a new RVM instance.
#[no_mangle]
pub extern "C" fn regorus_rvm_new() -> *mut RegorusRvm {
    Box::into_raw(Box::new(RegorusRvm::new(RegoVM::new())))
}

/// Construct a new RVM instance with a compiled policy for default rule evaluation.
#[no_mangle]
pub extern "C" fn regorus_rvm_new_with_policy(
    compiled_policy: *mut RegorusCompiledPolicy,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusRvm> {
            let policy = to_shared_ref(compiled_policy as *const RegorusCompiledPolicy)?
                .compiled_policy
                .clone();
            Ok(Box::into_raw(Box::new(RegorusRvm::new(
                RegoVM::new_with_policy(policy),
            ))))
        }();

        match output {
            Ok(vm) => RegorusResult::ok_pointer(vm as *mut c_void),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Load a program into the RVM.
#[no_mangle]
pub extern "C" fn regorus_rvm_load_program(
    vm: *mut RegorusRvm,
    program: *mut RegorusProgram,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let program = to_shared_ref(program as *const RegorusProgram)?
                .program
                .clone();
            guard.load_program(program);
            Ok(())
        }())
    })
}

/// Set the VM data document from JSON.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_data(vm: *mut RegorusRvm, data: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let data_value = Value::from_json_str(&from_c_str(data)?)?;
            guard.set_data(data_value)?;
            Ok(())
        }())
    })
}

/// Set the VM input document from JSON.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_input(
    vm: *mut RegorusRvm,
    input: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let input_value = Value::from_json_str(&from_c_str(input)?)?;
            guard.set_input(input_value);
            Ok(())
        }())
    })
}

/// Set the VM context document from JSON.
///
/// The context provides host-supplied ambient data (e.g. `resourceGroup()`,
/// `subscription()`) that Azure Policy functions can access via `LoadContext`
/// instructions. This must be called before `regorus_rvm_execute` when
/// evaluating policies that reference context functions.
///
/// # Safety
/// - `vm` must be a valid pointer to a `RegorusRvm` created by `regorus_rvm_new`.
/// - `context_json` must be a valid null-terminated UTF-8 string.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_rvm_set_context(
    vm: *mut RegorusRvm,
    context_json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let context_value = Value::from_json_str(&from_c_str(context_json)?)?;
            guard.set_context(context_value);
            Ok(())
        }())
    })
}

/// Set the maximum number of instructions that can execute.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_max_instructions(
    vm: *mut RegorusRvm,
    max_instructions: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_max_instructions(max_instructions);
            Ok(())
        }())
    })
}

/// Configure strict builtin error behavior.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_strict_builtin_errors(
    vm: *mut RegorusRvm,
    strict: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_strict_builtin_errors(strict);
            Ok(())
        }())
    })
}

/// Configure the execution mode (0 = run-to-completion, 1 = suspendable).
#[no_mangle]
pub extern "C" fn regorus_rvm_set_execution_mode(vm: *mut RegorusRvm, mode: u8) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let mode = match mode {
                0 => ExecutionMode::RunToCompletion,
                1 => ExecutionMode::Suspendable,
                _ => return Err(anyhow!("invalid execution mode: {mode}")),
            };
            guard.set_execution_mode(mode);
            Ok(())
        }())
    })
}

/// Enable or disable step mode when running suspendable execution.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_step_mode(vm: *mut RegorusRvm, enabled: bool) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_step_mode(enabled);
            Ok(())
        }())
    })
}

/// Configure the per-VM execution timer override.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_execution_timer_config(
    vm: *mut RegorusRvm,
    has_config: bool,
    config: RegorusExecutionTimerConfig,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            if has_config {
                guard.set_execution_timer_config(Some(config.to_execution_timer_config()?));
            } else {
                guard.set_execution_timer_config(None);
            }
            Ok(())
        }())
    })
}

/// Configure the per-VM memory budget for run-to-completion execution.
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[no_mangle]
pub extern "C" fn regorus_rvm_set_memory_budget_config(
    vm: *mut RegorusRvm,
    has_config: bool,
    config: RegorusMemoryBudgetConfig,
) -> RegorusResult {
    with_unwind_guard(|| {
        let config = if has_config {
            match config.to_memory_budget_config() {
                Ok(config) => Some(config),
                Err(err) => {
                    return RegorusResult::err_with_message(
                        RegorusStatus::InvalidArgument,
                        err.to_string(),
                    )
                }
            }
        } else {
            None
        };

        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_memory_budget_config(config);
            Ok(())
        }())
    })
}

/// Report that memory budgets are unavailable without allocator tracking.
#[cfg(any(not(feature = "allocator-memory-limits"), miri))]
#[no_mangle]
pub extern "C" fn regorus_rvm_set_memory_budget_config(
    _vm: *mut RegorusRvm,
    _has_config: bool,
    _config: RegorusMemoryBudgetConfig,
) -> RegorusResult {
    RegorusResult::err_with_message(
        RegorusStatus::InvalidArgument,
        "regorus_rvm_set_memory_budget_config unavailable: allocator memory tracking is disabled"
            .into(),
    )
}

/// Execute the program's main entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| execute_to_rvm_result(vm, RvmExecution::Main))
}

/// Execute a named entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_name(
    vm: *mut RegorusRvm,
    entry_point: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let entry_point = match from_c_str(entry_point) {
            Ok(entry_point) => entry_point,
            Err(err) => return to_rvm_error_result(err),
        };
        execute_to_rvm_result(vm, RvmExecution::Named(entry_point))
    })
}

/// Execute an entry point by index.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_index(
    vm: *mut RegorusRvm,
    index: usize,
) -> RegorusResult {
    with_unwind_guard(|| execute_to_rvm_result(vm, RvmExecution::Indexed(index)))
}

/// Resume execution for suspendable runs.
#[no_mangle]
pub extern "C" fn regorus_rvm_resume(
    vm: *mut RegorusRvm,
    resume_value_json: *const c_char,
    has_value: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<RegorusResult> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let output = guard.resume_to_c_string_for_ffi(|| {
                if has_value {
                    let resume_json = from_c_str(resume_value_json).map_err(VmError::from)?;
                    Ok(Some(resume_json))
                } else {
                    Ok(None)
                }
            })?;
            Ok(RegorusResult::ok_c_string(output))
        }();

        match output {
            Ok(result) => result,
            Err(err) => to_rvm_error_result(err),
        }
    })
}

/// Get the current execution state of the VM.
#[no_mangle]
pub extern "C" fn regorus_rvm_get_execution_state(vm: *mut RegorusRvm) -> RegorusResult {
    with_unowned_memory_budget_scope_for_ffi(|| {
        with_unwind_guard(|| {
            let output = || -> Result<String> {
                let vm = to_shared_ref(vm as *const RegorusRvm)?;
                let guard = vm.try_read()?;
                let state: ExecutionState = guard.execution_state().clone();
                Ok(format!("{:?}", state))
            }();

            match output {
                Ok(json) => RegorusResult::ok_string(json),
                Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
            }
        })
    })
}

#[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
mod tests {
    use super::{
        regorus_rvm_drop, regorus_rvm_execute, regorus_rvm_execute_entry_point_by_index,
        regorus_rvm_execute_entry_point_by_name, regorus_rvm_get_execution_state,
        regorus_rvm_get_host_await_argument, regorus_rvm_get_host_await_identifier,
        regorus_rvm_new, regorus_rvm_resume, regorus_rvm_set_data, regorus_rvm_set_execution_mode,
        regorus_rvm_set_memory_budget_config, RegorusRvm,
    };
    use crate::common::{regorus_result_drop, RegorusResult, RegorusStatus};
    use crate::limits::RegorusMemoryBudgetConfig;
    use alloc::boxed::Box;
    use alloc::ffi::CString;
    use alloc::string::String;
    use alloc::string::ToString;
    use alloc::sync::Arc;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::ffi::CStr;
    use regorus::languages::rego::compiler::Compiler;
    use regorus::rvm::instructions::Instruction;
    use regorus::rvm::program::Program;
    use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
    use regorus::{Engine, MemoryBudgetConfig, Rc, Value};

    const POLICY: &str = r#"
package limits.memory
import rego.v1

copy := [value | some value in input]
"#;

    const SUSPENDABLE_HOST_AWAIT_POLICY: &str = r#"
package limits.memory
import rego.v1

result := count(__builtin_host_await(
    __builtin_host_await(input.value, "first"),
    "second"
))
"#;

    const SUSPENDABLE_REPEAT_RESULT_POLICY: &str = r#"
package limits.memory
import rego.v1

value := __builtin_host_await(input.value, "first")
result := [value, value, value, value, value, value, value, value]
"#;

    const TIGHT_MEMORY_BUDGET_BYTES: u64 = 64 * 1024;
    const NESTED_GETTER_MEMORY_BUDGET_BYTES: u64 = 8 * 1024;
    const NESTED_GETTER_REPETITIONS: usize = 2048;

    fn memory_budget(limit: u64) -> MemoryBudgetConfig {
        MemoryBudgetConfig {
            limit: core::num::NonZeroU64::new(limit).expect("non-zero budget"),
        }
    }

    fn assert_memory_budget_failure_state(vm: *mut RegorusRvm, result: RegorusResult) {
        assert!(matches!(result.status, RegorusStatus::MemoryBudgetExceeded));
        assert!(result.output.is_null());
        regorus_result_drop(result);

        assert_execution_state(vm, "Error { error: MemoryBudgetExceeded");
    }

    fn assert_execution_state(vm: *mut RegorusRvm, expected_prefix: &str) {
        let state = regorus_rvm_get_execution_state(vm);
        assert!(matches!(state.status, RegorusStatus::Ok));
        let state_text = unsafe { CStr::from_ptr(state.output) }
            .to_str()
            .expect("execution state UTF-8");
        assert!(
            state_text.starts_with(expected_prefix),
            "unexpected execution state: {state_text}"
        );
        regorus_result_drop(state);
    }

    fn compiled_suspendable_host_await_program() -> Arc<Program> {
        let entrypoint = Rc::from("data.limits.memory.result");
        let mut engine = Engine::new();
        engine
            .add_policy(
                "memory_budget.rego".into(),
                SUSPENDABLE_HOST_AWAIT_POLICY.into(),
            )
            .expect("add policy");
        let compiled = engine
            .compile_with_entrypoint(&entrypoint)
            .expect("compile policy");
        Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .expect("compile VM program")
    }

    fn compiled_suspendable_repeat_result_program() -> Arc<Program> {
        let entrypoint = Rc::from("data.limits.memory.result");
        let mut engine = Engine::new();
        engine
            .add_policy(
                "memory_budget.rego".into(),
                SUSPENDABLE_REPEAT_RESULT_POLICY.into(),
            )
            .expect("add policy");
        let compiled = engine
            .compile_with_entrypoint(&entrypoint)
            .expect("compile policy");
        Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .expect("compile VM program")
    }

    fn suspendable_host_await_vm(program: &Arc<Program>, budget: Option<u64>) -> RegoVM {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(Arc::clone(program));
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#).expect("valid input JSON"));
        if let Some(limit) = budget {
            vm.set_memory_budget_config(Some(memory_budget(limit)));
        }
        vm
    }

    fn assert_getter_scope_restored(
        program: &Arc<Program>,
        child_vm: *mut RegorusRvm,
        getter: extern "C" fn(*mut RegorusRvm) -> RegorusResult,
        expected_output: &str,
        expected_output_is_prefix: bool,
    ) {
        let mut outer_vm =
            suspendable_host_await_vm(program, Some(NESTED_GETTER_MEMORY_BUDGET_BYTES));
        outer_vm
            .execute()
            .expect("outer VM should suspend at HostAwait within its budget");

        let mut getter_result = None;
        let mut parent_probe: Option<Vec<u8>> = None;
        let result = outer_vm.resume_to_c_string_for_ffi(|| {
            getter_result = Some(getter(child_vm));
            parent_probe = Some(vec![0u8; NESTED_GETTER_MEMORY_BUDGET_BYTES as usize]);
            core::hint::black_box(parent_probe.as_ref());
            Err(VmError::Internal {
                message: String::from("stop after the post-getter parent allocation"),
                pc: 0,
            })
        });

        let is_budget_error = match &result {
            Err(VmError::MemoryBudgetExceeded { .. }) => true,
            Ok(_) => false,
            Err(_) => false,
        };
        assert!(
            is_budget_error,
            "post-getter parent allocation should be charged before result serialization: {result:?}"
        );

        let getter_result = getter_result.expect("getter should be invoked");
        assert!(matches!(getter_result.status, RegorusStatus::Ok));
        assert!(!getter_result.output.is_null());
        let output = unsafe { CStr::from_ptr(getter_result.output) }
            .to_str()
            .expect("getter output UTF-8");
        if expected_output_is_prefix {
            assert!(output.starts_with(expected_output));
        } else {
            assert_eq!(output, expected_output);
        }
        regorus_result_drop(getter_result);
    }

    fn preloaded_result_program() -> Arc<Program> {
        let mut program = Program::new();
        program.dispatch_window_size = 1;
        program.max_rule_window_size = 1;
        program.entry_points.insert("main".to_string(), 0);
        program.literals = vec![Value::from("x".repeat(2 * 1024 * 1024))];
        program.instructions = vec![
            Instruction::Load {
                dest: 0,
                literal_idx: 0,
            },
            Instruction::Return { value: 0 },
        ];
        program.instruction_spans = vec![None; program.instructions.len()];
        Arc::new(program)
    }

    #[test]
    fn ffi_memory_budget_setter_validates_and_clears_configuration() {
        let vm = regorus_rvm_new();

        let result = regorus_rvm_set_memory_budget_config(
            vm,
            true,
            RegorusMemoryBudgetConfig { limit_bytes: 0 },
        );
        assert!(matches!(result.status, RegorusStatus::InvalidArgument));
        regorus_result_drop(result);

        let result = regorus_rvm_set_memory_budget_config(
            vm,
            true,
            RegorusMemoryBudgetConfig { limit_bytes: 1024 },
        );
        assert!(matches!(result.status, RegorusStatus::Ok));
        regorus_result_drop(result);

        let result = regorus_rvm_set_memory_budget_config(
            vm,
            false,
            RegorusMemoryBudgetConfig { limit_bytes: 0 },
        );
        assert!(matches!(result.status, RegorusStatus::Ok));
        regorus_result_drop(result);

        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_preloaded_data_is_outside_the_execution_budget() {
        let vm = regorus_rvm_new();
        let set_budget = regorus_rvm_set_memory_budget_config(
            vm,
            true,
            RegorusMemoryBudgetConfig {
                limit_bytes: 16 * 1024,
            },
        );
        assert!(matches!(set_budget.status, RegorusStatus::Ok));
        regorus_result_drop(set_budget);

        let data = CString::new(format!(r#"{{"value":"{}"}}"#, "x".repeat(2 * 1024 * 1024)))
            .expect("preloaded data CString");
        let set_data = regorus_rvm_set_data(vm, data.as_ptr());
        assert!(matches!(set_data.status, RegorusStatus::Ok));
        regorus_result_drop(set_data);

        let result = regorus_rvm_execute(vm);
        assert!(matches!(result.status, RegorusStatus::Ok));
        regorus_result_drop(result);
        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_execution_reports_memory_budget_status() {
        let entrypoint = Rc::from("data.limits.memory.copy");
        let mut engine = Engine::new();
        engine
            .add_policy("memory_budget.rego".into(), POLICY.into())
            .expect("add policy");
        let compiled = engine
            .compile_with_entrypoint(&entrypoint)
            .expect("compile policy");
        let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .expect("compile VM program");

        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_input(
            Value::from_json_str(&format!(
                "[{}]",
                (0..50_000)
                    .map(|value| value.to_string())
                    .collect::<alloc::vec::Vec<_>>()
                    .join(",")
            ))
            .expect("parse input"),
        );
        vm.set_memory_budget_config(Some(memory_budget(TIGHT_MEMORY_BUDGET_BYTES)));

        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));
        let result = regorus_rvm_execute_entry_point_by_index(vm, 0);
        assert!(matches!(result.status, RegorusStatus::MemoryBudgetExceeded));
        assert!(result.output.is_null());
        regorus_result_drop(result);
        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_result_serialization_is_included_in_memory_budget() {
        let mut vm = RegoVM::new();
        vm.load_program(preloaded_result_program());
        vm.set_memory_budget_config(Some(memory_budget(512 * 1024)));
        assert!(vm.execute().is_ok(), "core execution should fit the budget");

        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));
        let entrypoint = CString::new("main").expect("entry point CString");
        assert_memory_budget_failure_state(vm, regorus_rvm_execute(vm));
        assert_memory_budget_failure_state(
            vm,
            regorus_rvm_execute_entry_point_by_name(vm, entrypoint.as_ptr()),
        );
        assert_memory_budget_failure_state(vm, regorus_rvm_execute_entry_point_by_index(vm, 0));

        let clear_budget = regorus_rvm_set_memory_budget_config(
            vm,
            false,
            RegorusMemoryBudgetConfig { limit_bytes: 0 },
        );
        assert!(matches!(clear_budget.status, RegorusStatus::Ok));
        regorus_result_drop(clear_budget);
        let result = regorus_rvm_execute(vm);
        assert!(matches!(result.status, RegorusStatus::Ok));
        regorus_result_drop(result);
        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_suspendable_budget_spans_host_await_resumes_and_charges_json_input() {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(compiled_suspendable_host_await_program());
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#).expect("valid input JSON"));
        vm.set_memory_budget_config(Some(memory_budget(768 * 1024)));
        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));

        let mode = regorus_rvm_set_execution_mode(vm, 1);
        assert!(matches!(mode.status, RegorusStatus::Ok));
        regorus_result_drop(mode);
        let execute = regorus_rvm_execute(vm);
        assert!(matches!(execute.status, RegorusStatus::Ok));
        regorus_result_drop(execute);

        let mode = regorus_rvm_set_execution_mode(vm, 0);
        assert!(matches!(mode.status, RegorusStatus::Ok));
        regorus_result_drop(mode);
        let clear_budget = regorus_rvm_set_memory_budget_config(
            vm,
            false,
            RegorusMemoryBudgetConfig { limit_bytes: 0 },
        );
        assert!(matches!(clear_budget.status, RegorusStatus::Ok));
        regorus_result_drop(clear_budget);

        let first_resume =
            CString::new(format!("\"{}\"", "x".repeat(450 * 1024))).expect("first resume JSON");
        let first = regorus_rvm_resume(vm, first_resume.as_ptr(), true);
        assert!(matches!(first.status, RegorusStatus::Ok));
        regorus_result_drop(first);

        let second_resume =
            CString::new(format!("\"{}\"", "y".repeat(450 * 1024))).expect("second resume JSON");
        assert_memory_budget_failure_state(
            vm,
            regorus_rvm_resume(vm, second_resume.as_ptr(), true),
        );
        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_suspendable_resume_validation_errors_preserve_host_await_continuation() {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(compiled_suspendable_host_await_program());
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#).expect("valid input JSON"));
        vm.set_memory_budget_config(Some(memory_budget(2 * 1024 * 1024)));
        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));

        let execute = regorus_rvm_execute(vm);
        assert!(matches!(execute.status, RegorusStatus::Ok));
        regorus_result_drop(execute);
        assert_execution_state(vm, "Suspended {");

        let missing = regorus_rvm_resume(vm, core::ptr::null(), false);
        assert!(!matches!(missing.status, RegorusStatus::Ok));
        regorus_result_drop(missing);
        assert_execution_state(vm, "Suspended {");

        let malformed_json = CString::new("{").expect("malformed JSON CString");
        let malformed = regorus_rvm_resume(vm, malformed_json.as_ptr(), true);
        assert!(!matches!(malformed.status, RegorusStatus::Ok));
        regorus_result_drop(malformed);
        assert_execution_state(vm, "Suspended {");

        let first_resume = CString::new("\"first\"").expect("first resume JSON");
        let first = regorus_rvm_resume(vm, first_resume.as_ptr(), true);
        assert!(matches!(first.status, RegorusStatus::Ok));
        regorus_result_drop(first);
        assert_execution_state(vm, "Suspended {");

        let second_resume = CString::new("\"second\"").expect("second resume JSON");
        let second = regorus_rvm_resume(vm, second_resume.as_ptr(), true);
        assert!(matches!(second.status, RegorusStatus::Ok));
        regorus_result_drop(second);
        assert_execution_state(vm, "Completed {");

        regorus_rvm_drop(vm);
    }

    #[test]
    fn correction_ffi_malformed_resume_is_retryable_under_global_memory_pressure() {
        let _lock = crate::TEST_GLOBAL_MEMORY_LIMIT_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        struct ResetGlobalMemoryLimit;
        impl Drop for ResetGlobalMemoryLimit {
            fn drop(&mut self) {
                regorus::set_global_memory_limit(None);
            }
        }

        let _reset_global_limit = ResetGlobalMemoryLimit;
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(compiled_suspendable_host_await_program());
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#).expect("valid input JSON"));
        vm.set_memory_budget_config(Some(memory_budget(2 * 1024 * 1024)));
        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));

        let execute = regorus_rvm_execute(vm);
        assert!(matches!(execute.status, RegorusStatus::Ok));
        regorus_result_drop(execute);
        assert_execution_state(vm, "Suspended {");

        regorus::set_global_memory_limit(Some(1));
        let malformed_json = CString::new("{").expect("malformed JSON CString");
        let malformed = regorus_rvm_resume(vm, malformed_json.as_ptr(), true);
        assert!(matches!(malformed.status, RegorusStatus::Error));
        regorus_result_drop(malformed);
        regorus::set_global_memory_limit(None);

        assert_execution_state(vm, "Suspended {");
        let valid_resume = CString::new("\"response\"").expect("valid resume JSON");
        let resumed = regorus_rvm_resume(vm, valid_resume.as_ptr(), true);
        assert!(matches!(resumed.status, RegorusStatus::Ok));
        regorus_result_drop(resumed);
        assert_execution_state(vm, "Suspended {");
        let second_resume = CString::new("\"done\"").expect("second resume JSON");
        let completed = regorus_rvm_resume(vm, second_resume.as_ptr(), true);
        assert!(matches!(completed.status, RegorusStatus::Ok));
        regorus_result_drop(completed);
        assert_execution_state(vm, "Completed {");
        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_valid_resume_global_limit_failure_terminalizes_with_generic_error_status() {
        let _lock = crate::TEST_GLOBAL_MEMORY_LIMIT_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        struct ResetGlobalMemoryLimit;
        impl Drop for ResetGlobalMemoryLimit {
            fn drop(&mut self) {
                regorus::set_global_memory_limit(None);
            }
        }

        let _reset_global_limit = ResetGlobalMemoryLimit;
        regorus::set_global_memory_limit(None);
        regorus::utils::limits::check_memory_limit_if_needed()
            .expect("disabled global limit resets check state");

        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(compiled_suspendable_host_await_program());
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#).expect("valid input JSON"));
        vm.set_memory_budget_config(Some(memory_budget(128 * 1024 * 1024)));
        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));

        let execute = regorus_rvm_execute(vm);
        assert!(matches!(execute.status, RegorusStatus::Ok));
        regorus_result_drop(execute);
        assert_execution_state(vm, "Suspended {");

        let mut json = String::with_capacity(2 + 2 * 4096);
        json.push('[');
        for index in 0..4096 {
            if index > 0 {
                json.push(',');
            }
            json.push('0');
        }
        json.push(']');
        let json = CString::new(json).expect("valid numeric array JSON");

        regorus::set_global_memory_limit(Some(1));
        let baseline_usage = match regorus::utils::limits::check_global_memory_limit() {
            Err(regorus::LimitError::MemoryLimitExceeded { usage, limit: 1 }) => usage,
            other => panic!("expected to observe current usage above one byte, got {other:?}"),
        };
        let global_limit = baseline_usage.saturating_add(32 * 1024);
        regorus::set_global_memory_limit(Some(global_limit));

        let failure = regorus_rvm_resume(vm, json.as_ptr(), true);
        let post_parse_check = regorus::utils::limits::check_global_memory_limit();
        println!(
            "FFI resume conversion RED: baseline={baseline_usage}, limit={global_limit}, post_parse_check={post_parse_check:?}, status={:?}",
            failure.status
        );
        assert!(matches!(failure.status, RegorusStatus::Error));
        assert!(failure.output.is_null());
        regorus_result_drop(failure);
        assert!(
            post_parse_check.is_ok(),
            "partial Value allocations should be gone while the input CString remains"
        );
        assert_execution_state(vm, "Error { error: MemoryLimitExceeded");

        let rejected_json = CString::new("\"rejected\"").expect("rejected resume JSON");
        let rejected = regorus_rvm_resume(vm, rejected_json.as_ptr(), true);
        assert!(matches!(rejected.status, RegorusStatus::Error));
        assert!(rejected.output.is_null());
        regorus_result_drop(rejected);
        assert_execution_state(vm, "Error { error: MemoryLimitExceeded");

        regorus::set_global_memory_limit(None);
        regorus::utils::limits::check_memory_limit_if_needed()
            .expect("clearing the global limit resets check state");
        let restarted = regorus_rvm_execute(vm);
        assert!(matches!(restarted.status, RegorusStatus::Ok));
        regorus_result_drop(restarted);
        assert_execution_state(vm, "Suspended {");
        let first_resume = CString::new("\"independent\"").expect("first resume JSON");
        let first = regorus_rvm_resume(vm, first_resume.as_ptr(), true);
        assert!(matches!(first.status, RegorusStatus::Ok));
        regorus_result_drop(first);
        let second_resume = CString::new("\"done\"").expect("second resume JSON");
        let second = regorus_rvm_resume(vm, second_resume.as_ptr(), true);
        assert!(matches!(second.status, RegorusStatus::Ok));
        regorus_result_drop(second);
        assert_execution_state(vm, "Completed {");

        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_read_only_getters_exclude_nested_output_and_restore_parent_budget_scope() {
        let program = compiled_suspendable_host_await_program();
        let mut child_vm = suspendable_host_await_vm(&program, None);
        child_vm
            .execute()
            .expect("child VM should suspend at HostAwait");
        let child_vm = Box::into_raw(Box::new(RegorusRvm::new(child_vm)));

        let mut outer_vm =
            suspendable_host_await_vm(&program, Some(NESTED_GETTER_MEMORY_BUDGET_BYTES));
        outer_vm
            .execute()
            .expect("outer VM should suspend at HostAwait within its budget");

        let mut getter_results = Vec::with_capacity(NESTED_GETTER_REPETITIONS * 3);
        let mut parent_allocation = None;
        let resumed = outer_vm.resume_to_c_string_for_ffi(|| {
            for _ in 0..NESTED_GETTER_REPETITIONS {
                getter_results.push(regorus_rvm_get_execution_state(child_vm));
                getter_results.push(regorus_rvm_get_host_await_argument(child_vm));
                getter_results.push(regorus_rvm_get_host_await_identifier(child_vm));
            }
            parent_allocation = Some(vec![0u8; 64]);
            core::hint::black_box(parent_allocation.as_ref());
            Ok(Some(String::from("\"response\"")))
        });

        assert!(
            resumed.is_ok(),
            "getter serialization should be excluded from the unrelated outer budget: {resumed:?}"
        );
        assert!(!resumed
            .expect("outer resume should succeed")
            .as_bytes()
            .is_empty());
        assert!(
            alloc::format!("{:?}", outer_vm.execution_state()).starts_with("Suspended {"),
            "outer continuation should remain suspended after its first resume"
        );
        assert_eq!(
            getter_results.len(),
            NESTED_GETTER_REPETITIONS * 3,
            "all three getters should run for every retained output"
        );
        for result in &getter_results {
            assert!(matches!(result.status, RegorusStatus::Ok));
            assert!(!result.output.is_null());
        }

        let mut retained_c_string_bytes = [0usize; 3];
        for getter_results in getter_results.chunks_exact(3) {
            for (total, result) in retained_c_string_bytes.iter_mut().zip(getter_results) {
                let bytes_with_nul = unsafe { CStr::from_ptr(result.output) }
                    .to_bytes_with_nul()
                    .len();
                *total = total
                    .checked_add(bytes_with_nul)
                    .expect("retained getter output byte count");
            }
        }
        for (getter, bytes) in [
            ("execution state", retained_c_string_bytes[0]),
            ("HostAwait argument", retained_c_string_bytes[1]),
            ("HostAwait identifier", retained_c_string_bytes[2]),
        ] {
            assert!(
                bytes > NESTED_GETTER_MEMORY_BUDGET_BYTES as usize,
                "{getter} CString bytes {bytes} must exceed the outer budget of \
                 {NESTED_GETTER_MEMORY_BUDGET_BYTES}"
            );
        }

        let mut first_outputs = getter_results.iter();
        let state = first_outputs.next().expect("execution-state output");
        let argument = first_outputs.next().expect("HostAwait argument output");
        let identifier = first_outputs.next().expect("HostAwait identifier output");
        assert!(unsafe { CStr::from_ptr(state.output) }
            .to_str()
            .expect("execution-state UTF-8")
            .starts_with("Suspended {"));
        assert_eq!(
            unsafe { CStr::from_ptr(argument.output) }
                .to_str()
                .expect("HostAwait argument UTF-8"),
            "\"request\""
        );
        assert_eq!(
            unsafe { CStr::from_ptr(identifier.output) }
                .to_str()
                .expect("HostAwait identifier UTF-8"),
            "first"
        );

        for result in getter_results.drain(..) {
            regorus_result_drop(result);
        }

        assert_getter_scope_restored(
            &program,
            child_vm,
            regorus_rvm_get_execution_state,
            "Suspended {",
            true,
        );
        assert_getter_scope_restored(
            &program,
            child_vm,
            regorus_rvm_get_host_await_argument,
            "\"request\"",
            false,
        );
        assert_getter_scope_restored(
            &program,
            child_vm,
            regorus_rvm_get_host_await_identifier,
            "first",
            false,
        );

        regorus_rvm_drop(child_vm);
    }

    #[test]
    fn ffi_suspendable_result_serialization_uses_active_memory_budget() {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(compiled_suspendable_repeat_result_program());
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#).expect("valid input JSON"));
        vm.set_memory_budget_config(Some(memory_budget(512 * 1024)));
        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));

        let execute = regorus_rvm_execute(vm);
        assert!(matches!(execute.status, RegorusStatus::Ok));
        regorus_result_drop(execute);
        assert_execution_state(vm, "Suspended {");

        let large_resume =
            CString::new(format!("\"{}\"", "x".repeat(128 * 1024))).expect("large resume JSON");
        assert_memory_budget_failure_state(vm, regorus_rvm_resume(vm, large_resume.as_ptr(), true));

        regorus_rvm_drop(vm);
    }

    #[test]
    fn memory_budget_status_values_are_appended() {
        assert_eq!(RegorusStatus::MemoryBudgetExceeded as u32, 10);
        assert_eq!(
            RegorusStatus::MemoryBudgetUnsupportedInSuspendableExecution as u32,
            11
        );
    }
}

#[cfg(all(test, any(not(feature = "allocator-memory-limits"), miri)))]
mod unsupported_memory_budget_tests {
    use super::{regorus_rvm_drop, regorus_rvm_new, regorus_rvm_set_memory_budget_config};
    use crate::common::{regorus_result_drop, RegorusStatus};
    use crate::limits::RegorusMemoryBudgetConfig;

    #[test]
    fn ffi_memory_budget_setter_is_unsupported_without_allocator_tracking() {
        let vm = regorus_rvm_new();
        let result = regorus_rvm_set_memory_budget_config(
            vm,
            true,
            RegorusMemoryBudgetConfig { limit_bytes: 1024 },
        );
        assert!(matches!(result.status, RegorusStatus::InvalidArgument));
        regorus_result_drop(result);
        regorus_rvm_drop(vm);
    }
}

fn convert_c_entry_points(
    entry_points: *const *const c_char,
    entry_points_len: usize,
) -> Result<Vec<String>> {
    if entry_points.is_null() && entry_points_len > 0 {
        return Err(anyhow!("null entry_points pointer"));
    }

    let mut entry_points_vec = Vec::with_capacity(entry_points_len);
    for i in 0..entry_points_len {
        unsafe {
            let entry_ptr = entry_points.add(i);
            if entry_ptr.is_null() {
                return Err(anyhow!("null entry point at index {i}"));
            }
            let entry = from_c_str(*entry_ptr)?;
            entry_points_vec.push(entry);
        }
    }

    Ok(entry_points_vec)
}

fn convert_c_modules_to_rust(
    modules: *const RegorusPolicyModule,
    modules_len: usize,
) -> Result<Vec<PolicyModule>> {
    if modules.is_null() && modules_len > 0 {
        return Err(anyhow!("null modules pointer"));
    }

    let mut policy_modules = Vec::with_capacity(modules_len);

    for i in 0..modules_len {
        unsafe {
            let module = modules.add(i);
            if module.is_null() {
                return Err(anyhow!("null module at index {i}"));
            }

            let module_ref = &*module;

            let id = from_c_str(module_ref.id)
                .map_err(|e| anyhow!("invalid module id at index {i}: {e}"))?;
            let content = from_c_str(module_ref.content)
                .map_err(|e| anyhow!("invalid module content at index {i}: {e}"))?;

            policy_modules.push(PolicyModule {
                id: id.into(),
                content: content.into(),
            });
        }
    }

    Ok(policy_modules)
}

/// A registered host-awaitable builtin passed via FFI.
///
/// The argument count is currently fixed to 1 by the compiler (see
/// `Compiler::register_host_await_builtin`), so it is not exposed at the
/// FFI boundary. The struct exists as a stable layout to allow future
/// expansion (e.g. an explicit `arg_count` field) without breaking ABI
/// when callers pin a fixed-size array of these.
#[repr(C)]
pub struct RegorusHostAwaitBuiltin {
    /// Null-terminated UTF-8 builtin name.
    pub name: *const c_char,
}

/// Compile an RVM program from data/modules and entry points, with registered
/// host-awaitable builtins.
///
/// * `data_json` - JSON string containing static data for policy evaluation
/// * `modules` / `modules_len` - Policy modules to compile
/// * `entry_points` / `entry_points_len` - Entry point rule paths
/// * `host_await_builtins` / `host_await_builtins_len` - Builtins that compile to HostAwait
/// * `host_await_builtin_size` - `sizeof(RegorusHostAwaitBuiltin)` as seen by the
///   caller; used as the array stride so callers built against a different struct
///   layout still walk the array correctly (forward-compatible ABI)
#[allow(clippy::too_many_arguments)]
#[no_mangle]
pub extern "C" fn regorus_program_compile_from_modules_with_host_await(
    data_json: *const c_char,
    modules: *const RegorusPolicyModule,
    modules_len: usize,
    entry_points: *const *const c_char,
    entry_points_len: usize,
    host_await_builtins: *const RegorusHostAwaitBuiltin,
    host_await_builtins_len: usize,
    host_await_builtin_size: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        compile_from_modules_result(compile_from_modules_inner(
            data_json,
            modules,
            modules_len,
            entry_points,
            entry_points_len,
            host_await_builtins,
            host_await_builtins_len,
            host_await_builtin_size,
        ))
    })
}

/// A set of pre-loaded HostAwait response values for a single identifier,
/// passed via FFI to [`regorus_rvm_set_host_await_responses`].
#[repr(C)]
pub struct RegorusHostAwaitResponseSet {
    /// Null-terminated UTF-8 identifier of the host-await builtin.
    pub identifier: *const c_char,
    /// Array of null-terminated UTF-8 JSON response strings.
    pub values_json: *const *const c_char,
    /// Number of responses in `values_json`.
    pub values_len: usize,
}

/// Validate a caller-supplied array stride before any pointer arithmetic.
///
/// `stride` is `sizeof(T)` as the *caller* compiled it. Honoring it as the array
/// stride is what keeps appended trailing fields forward-compatible, but it is
/// caller-controlled data, so it has to be checked before it reaches `ptr::add`
/// or reference formation. Rejects, for a non-empty array:
///
/// * a stride that does not cover the fields this build reads (ABI mismatch),
/// * a stride that is not a multiple of `align_of::<T>()`, which would leave
///   every element after the first misaligned,
/// * a misaligned base pointer, which would misalign *every* element even
///   when the stride itself is well-formed,
/// * a total span that overflows `usize` or exceeds `isize::MAX`, which is
///   outside the range `ptr::add` accepts.
///
/// The span check subsumes a separate `stride > isize::MAX` test: `len >= 1`
/// here, so `span >= stride`. It also covers the last element's end, because
/// `stride >= size_of::<T>()` implies `(len - 1) * stride + size_of::<T>() <= span`.
fn validate_array_stride<T>(
    base: *const T,
    len: usize,
    stride: usize,
    size_param: &str,
    type_name: &str,
) -> Result<()> {
    // No array is walked, so the stride is never used as an offset.
    if len == 0 {
        return Ok(());
    }

    let size = core::mem::size_of::<T>();
    let align = core::mem::align_of::<T>();

    if stride < size {
        return Err(anyhow!(
            "{size_param} ({stride}) is smaller than the expected {type_name} layout \
             ({size} bytes); ABI mismatch"
        ));
    }
    if !stride.is_multiple_of(align) {
        return Err(anyhow!(
            "{size_param} ({stride}) is not a multiple of the {type_name} alignment \
             ({align} bytes); ABI mismatch"
        ));
    }
    if !(base as usize).is_multiple_of(align) {
        return Err(anyhow!(
            "{type_name} array pointer is not {align}-byte aligned"
        ));
    }

    let span = len.checked_mul(stride).ok_or_else(|| {
        anyhow!("{type_name} array span overflows (len {len}, {size_param} {stride})")
    })?;
    if span > isize::MAX as usize {
        return Err(anyhow!(
            "{type_name} array span ({span} bytes) exceeds the maximum addressable range"
        ));
    }

    Ok(())
}

/// Pre-load HostAwait responses for run-to-completion mode.
///
/// Atomically replaces all previously configured responses for **every**
/// identifier with the supplied per-identifier queues. Pass all identifiers
/// the policy may invoke in a single call; calling this function again
/// discards the prior configuration in full.
///
/// * `vm` - RVM instance
/// * `response_sets` - Array of per-identifier response sets
/// * `response_sets_len` - Number of entries in `response_sets`
/// * `response_set_size` - `sizeof(RegorusHostAwaitResponseSet)` as seen by the
///   caller; used as the array stride for forward-compatible ABI
#[no_mangle]
pub extern "C" fn regorus_rvm_set_host_await_responses(
    vm: *mut RegorusRvm,
    response_sets: *const RegorusHostAwaitResponseSet,
    response_sets_len: usize,
    response_set_size: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;

            if response_sets.is_null() && response_sets_len > 0 {
                return Err(anyhow!("null response_sets pointer"));
            }

            // `response_set_size` is `sizeof(RegorusHostAwaitResponseSet)` as the
            // caller compiled it, which is also the array stride. Validate it
            // before any pointer arithmetic, then index by it so a caller built
            // against a different struct layout still walks the array correctly.
            validate_array_stride(
                response_sets,
                response_sets_len,
                response_set_size,
                "response_set_size",
                "RegorusHostAwaitResponseSet",
            )?;

            let mut all = Vec::new();
            all.try_reserve(response_sets_len).map_err(|_| {
                anyhow!(
                    "failed to reserve capacity for {response_sets_len} host-await response sets"
                )
            })?;
            let base = response_sets as *const u8;
            for i in 0..response_sets_len {
                let offset = i.checked_mul(response_set_size).ok_or_else(|| {
                    anyhow!("host-await response set array offset overflow at index {i}")
                })?;
                // SAFETY: caller guarantees `response_sets` points to a contiguous
                // array of `response_sets_len` elements each `response_set_size`
                // bytes wide, and the inner pointers reference valid C strings.
                let set = unsafe { &*(base.add(offset) as *const RegorusHostAwaitResponseSet) };

                let id_str = from_c_str(set.identifier)
                    .map_err(|e| anyhow!("invalid identifier in response set at index {i}: {e}"))?;
                let id_value = Value::String(id_str.into());

                if set.values_json.is_null() && set.values_len > 0 {
                    return Err(anyhow!(
                        "null values_json pointer in response set at index {i}"
                    ));
                }

                let mut values = alloc::collections::VecDeque::new();
                values.try_reserve(set.values_len).map_err(|_| {
                    anyhow!(
                        "failed to reserve capacity for {} response values at index {i}",
                        set.values_len
                    )
                })?;
                for j in 0..set.values_len {
                    let ptr = unsafe { *set.values_json.add(j) };
                    let json_str = from_c_str(ptr).map_err(|e| {
                        anyhow!("invalid JSON pointer at response_sets[{i}].values_json[{j}]: {e}")
                    })?;
                    let val = Value::from_json_str(&json_str).map_err(|e| {
                        anyhow!("invalid JSON at response_sets[{i}].values_json[{j}]: {e}")
                    })?;
                    values.push_back(val);
                    // Charge caller-driven accumulation against the configured
                    // memory budget; a no-op unless a limit is set.
                    check_memory_limit_if_needed()?;
                }

                all.push((id_value, values));
                check_memory_limit_if_needed()?;
            }

            guard.set_host_await_responses(all);
            Ok(())
        }())
    })
}

/// Get the HostAwait argument as a JSON string.
///
/// Returns the argument value if the VM is suspended due to a HostAwait instruction,
/// or None if the VM is not in a HostAwait-suspended state.
#[no_mangle]
pub extern "C" fn regorus_rvm_get_host_await_argument(vm: *mut RegorusRvm) -> RegorusResult {
    with_unowned_memory_budget_scope_for_ffi(|| {
        with_unwind_guard(|| {
            let output = || -> Result<Option<String>> {
                let vm = to_shared_ref(vm as *const RegorusRvm)?;
                let guard = vm.try_read()?;
                match guard.get_host_await_argument() {
                    Some(arg) => Ok(Some(arg.to_json_str()?)),
                    None => Ok(None),
                }
            }();

            match output {
                Ok(Some(json)) => RegorusResult::ok_string(json),
                Ok(None) => RegorusResult::ok_void(),
                Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
            }
        })
    })
}

/// Convert a HostAwait identifier `Value` into the raw string handed back over
/// the C ABI.
///
/// Unlike the argument accessor, the identifier crosses as a raw (non-JSON) C
/// string, so an embedded NUL has no faithful representation: `to_c_str` would
/// silently substitute a placeholder while still reporting `RegorusStatus::Ok`,
/// handing the caller a wrong identifier it cannot route or resume. Reject it
/// instead.
fn host_await_identifier_string(identifier: Option<&Value>) -> Result<Option<String>> {
    match identifier {
        Some(Value::String(s)) => {
            if s.contains('\0') {
                return Err(anyhow!(
                    "host-await identifier contains an embedded NUL and cannot be \
                     represented as a C string"
                ));
            }
            Ok(Some(s.as_ref().to_string()))
        }
        Some(_) => Err(anyhow!("host-await identifier must be a string")),
        None => Ok(None),
    }
}

/// Get the HostAwait identifier as a raw UTF-8 string.
///
/// The returned string is the identifier itself (not JSON-quoted), so it can be
/// passed directly as an identifier to `regorus_rvm_set_host_await_responses`.
/// Returns the identifier value if the VM is suspended due to a HostAwait instruction,
/// or None if the VM is not in a HostAwait-suspended state.
///
/// Identifiers containing an embedded NUL are rejected with an error, because
/// they cannot be round-tripped through the C string ABI.
#[no_mangle]
pub extern "C" fn regorus_rvm_get_host_await_identifier(vm: *mut RegorusRvm) -> RegorusResult {
    with_unowned_memory_budget_scope_for_ffi(|| {
        with_unwind_guard(|| {
            let output = || -> Result<Option<String>> {
                let vm = to_shared_ref(vm as *const RegorusRvm)?;
                let guard = vm.try_read()?;
                host_await_identifier_string(guard.get_host_await_identifier())
            }();

            match output {
                Ok(Some(identifier)) => RegorusResult::ok_string(identifier),
                Ok(None) => RegorusResult::ok_void(),
                Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
            }
        })
    })
}

pub(crate) fn convert_c_host_await_builtins(
    builtins: *const RegorusHostAwaitBuiltin,
    len: usize,
    struct_size: usize,
) -> Result<Vec<(String, usize)>> {
    if builtins.is_null() && len > 0 {
        return Err(anyhow!("null host_await_builtins pointer"));
    }
    // `struct_size` is `sizeof(RegorusHostAwaitBuiltin)` as the caller compiled it,
    // which is also the array stride. Validate it before any pointer arithmetic,
    // then index by it so a caller built against a different (older/newer) struct
    // layout still walks the array correctly.
    validate_array_stride(
        builtins,
        len,
        struct_size,
        "host_await_builtin_size",
        "RegorusHostAwaitBuiltin",
    )?;
    let mut result = Vec::new();
    result
        .try_reserve(len)
        .map_err(|_| anyhow!("failed to reserve capacity for {len} host-await builtins"))?;
    let base = builtins as *const u8;
    for i in 0..len {
        let offset = i
            .checked_mul(struct_size)
            .ok_or_else(|| anyhow!("host-await builtin array offset overflow at index {i}"))?;
        // SAFETY: caller guarantees `len` elements each `struct_size` bytes wide
        // starting at `builtins`, with valid C-string `name` pointers.
        let b = unsafe { &*(base.add(offset) as *const RegorusHostAwaitBuiltin) };
        let name = from_c_str(b.name)
            .map_err(|e| anyhow!("invalid host-await builtin name at index {i}: {e}"))?;
        // Arg count is fixed to 1 by the compiler — see the doc comment
        // on `RegorusHostAwaitBuiltin` and `Compiler::register_host_await_builtin`.
        result.push((name, 1));
        check_memory_limit_if_needed()?;
    }
    Ok(result)
}

#[cfg(test)]
mod host_await_tests {
    use super::*;
    use std::ffi::CString;

    fn c(s: &str) -> CString {
        CString::new(s).expect("CString::new failed")
    }

    /// Simulates a *future* `RegorusHostAwaitBuiltin` that has grown a trailing
    /// field. It shares the same `name: *const c_char` at offset 0, so a caller
    /// built against this wider layout must still be walked correctly as long as
    /// it reports its own (larger) element size as the stride.
    #[repr(C)]
    struct WiderBuiltin {
        name: *const c_char,
        _appended: u64,
    }

    // A caller-supplied array laid out at the exact native element size parses fine.
    #[test]
    fn convert_builtins_native_size_parses_names() {
        let names = [c("translate"), c("fetch")];
        let builtins: Vec<RegorusHostAwaitBuiltin> = names
            .iter()
            .map(|n| RegorusHostAwaitBuiltin { name: n.as_ptr() })
            .collect();
        let size = core::mem::size_of::<RegorusHostAwaitBuiltin>();

        let result =
            convert_c_host_await_builtins(builtins.as_ptr(), builtins.len(), size).unwrap();

        assert_eq!(
            result,
            vec![("translate".to_string(), 1), ("fetch".to_string(), 1)]
        );
    }

    // A caller whose element size is smaller than the native layout is rejected
    // loudly (clean error) instead of walked with a bad stride.
    #[test]
    fn convert_builtins_undersized_stride_is_rejected() {
        let name = c("translate");
        let builtins = [RegorusHostAwaitBuiltin {
            name: name.as_ptr(),
        }];
        let too_small = core::mem::size_of::<RegorusHostAwaitBuiltin>() - 1;

        let err = convert_c_host_await_builtins(builtins.as_ptr(), builtins.len(), too_small)
            .unwrap_err();

        assert!(
            err.to_string().contains("ABI mismatch"),
            "expected an ABI mismatch error, got: {err}"
        );
    }

    // A *newer* caller whose struct has an appended field (larger stride) is still
    // walked correctly: the native side honors the caller-supplied stride and reads
    // `name` at offset 0 of each element. This is the forward-compatible
    // mixed-version direction (new caller + older native library).
    #[test]
    fn convert_builtins_oversized_stride_uses_caller_stride() {
        let names = [c("translate"), c("fetch")];
        let wide: Vec<WiderBuiltin> = names
            .iter()
            .map(|n| WiderBuiltin {
                name: n.as_ptr(),
                _appended: 0,
            })
            .collect();
        let wider_size = core::mem::size_of::<WiderBuiltin>();
        assert!(wider_size > core::mem::size_of::<RegorusHostAwaitBuiltin>());

        // SAFETY: `WiderBuiltin` begins with the same `name: *const c_char` field
        // at offset 0 as `RegorusHostAwaitBuiltin`, and we pass the true element
        // stride (`wider_size`), so every read stays in bounds.
        let result = convert_c_host_await_builtins(
            wide.as_ptr() as *const RegorusHostAwaitBuiltin,
            wide.len(),
            wider_size,
        )
        .unwrap();

        assert_eq!(
            result,
            vec![("translate".to_string(), 1), ("fetch".to_string(), 1)]
        );
    }

    // The no-host-await path passes null/0; the size argument must be ignored
    // (no array is walked, so any size — including 0 — is accepted).
    #[test]
    fn convert_builtins_zero_len_ignores_size() {
        let result = convert_c_host_await_builtins(core::ptr::null(), 0, 0).unwrap();
        assert!(result.is_empty());
    }

    // A plain identifier round-trips as a raw (non-JSON) string, so it can be fed
    // straight back into `regorus_rvm_set_host_await_responses`.
    #[test]
    fn host_await_identifier_returns_raw_string() {
        let id = host_await_identifier_string(Some(&Value::String("translate".into()))).unwrap();
        assert_eq!(id, Some("translate".to_string()));
    }

    // Not being suspended on a HostAwait is a clean "no identifier", not an error.
    #[test]
    fn host_await_identifier_none_when_not_suspended() {
        assert_eq!(host_await_identifier_string(None).unwrap(), None);
    }

    // Without this check the caller gets a placeholder string under an Ok status.
    #[test]
    fn host_await_identifier_rejects_embedded_nul() {
        let err = host_await_identifier_string(Some(&Value::String("a\0b".into()))).unwrap_err();

        assert!(
            err.to_string().contains("embedded NUL"),
            "expected an embedded-NUL error, got: {err}"
        );
    }

    // Non-string identifiers are outside the string-only identifier ABI and must
    // error rather than be coerced.
    #[test]
    fn host_await_identifier_rejects_non_string() {
        let err = host_await_identifier_string(Some(&Value::from(1u64))).unwrap_err();

        assert!(
            err.to_string().contains("must be a string"),
            "expected a non-string identifier error, got: {err}"
        );
    }

    // A well-formed array (exact native stride, aligned base) passes for both
    // caller-facing structs.
    #[test]
    fn validate_stride_accepts_native_layout() {
        let builtins = [RegorusHostAwaitBuiltin {
            name: core::ptr::null(),
        }];
        validate_array_stride(
            builtins.as_ptr(),
            builtins.len(),
            core::mem::size_of::<RegorusHostAwaitBuiltin>(),
            "host_await_builtin_size",
            "RegorusHostAwaitBuiltin",
        )
        .unwrap();

        let sets = [RegorusHostAwaitResponseSet {
            identifier: core::ptr::null(),
            values_json: core::ptr::null(),
            values_len: 0,
        }];
        validate_array_stride(
            sets.as_ptr(),
            sets.len(),
            core::mem::size_of::<RegorusHostAwaitResponseSet>(),
            "response_set_size",
            "RegorusHostAwaitResponseSet",
        )
        .unwrap();
    }

    // A larger, still correctly-aligned stride is the forward-compatible
    // new-caller direction and must keep working.
    #[test]
    fn validate_stride_accepts_aligned_oversized() {
        let wide = [WiderBuiltin {
            name: core::ptr::null(),
            _appended: 0,
        }];
        validate_array_stride(
            wide.as_ptr() as *const RegorusHostAwaitBuiltin,
            wide.len(),
            core::mem::size_of::<WiderBuiltin>(),
            "host_await_builtin_size",
            "RegorusHostAwaitBuiltin",
        )
        .unwrap();
    }

    // A stride below the native layout would read past each element.
    #[test]
    fn validate_stride_rejects_undersized() {
        let sets = [RegorusHostAwaitResponseSet {
            identifier: core::ptr::null(),
            values_json: core::ptr::null(),
            values_len: 0,
        }];
        let err = validate_array_stride(
            sets.as_ptr(),
            sets.len(),
            core::mem::size_of::<RegorusHostAwaitResponseSet>() - 1,
            "response_set_size",
            "RegorusHostAwaitResponseSet",
        )
        .unwrap_err();

        assert!(
            err.to_string().contains("ABI mismatch"),
            "expected an ABI mismatch error, got: {err}"
        );
    }

    // A stride that clears the size floor but is not a multiple of the alignment
    // misaligns every element after the first, which is UB at reference formation.
    #[test]
    fn validate_stride_rejects_misaligned_stride() {
        let sets = [RegorusHostAwaitResponseSet {
            identifier: core::ptr::null(),
            values_json: core::ptr::null(),
            values_len: 0,
        }];
        let odd = core::mem::size_of::<RegorusHostAwaitResponseSet>() + 1;
        assert!(!odd.is_multiple_of(core::mem::align_of::<RegorusHostAwaitResponseSet>()));

        let err = validate_array_stride(
            sets.as_ptr(),
            2,
            odd,
            "response_set_size",
            "RegorusHostAwaitResponseSet",
        )
        .unwrap_err();

        assert!(
            err.to_string().contains("not a multiple"),
            "expected a stride-alignment error, got: {err}"
        );
    }

    // A misaligned base misaligns every element even when the stride is perfect,
    // so it must be rejected independently of the stride checks.
    #[test]
    fn validate_stride_rejects_misaligned_base() {
        let buf = [0u8; 64];
        // SAFETY: only the pointer's address is inspected; it is never dereferenced.
        let misaligned = unsafe { buf.as_ptr().add(1) } as *const RegorusHostAwaitBuiltin;
        assert!(
            !(misaligned as usize).is_multiple_of(core::mem::align_of::<RegorusHostAwaitBuiltin>())
        );

        let err = validate_array_stride(
            misaligned,
            1,
            core::mem::size_of::<RegorusHostAwaitBuiltin>(),
            "host_await_builtin_size",
            "RegorusHostAwaitBuiltin",
        )
        .unwrap_err();

        assert!(
            err.to_string().contains("not 8-byte aligned"),
            "expected a base-alignment error, got: {err}"
        );
    }

    // `len * stride` overflowing `usize` must be caught rather than wrapping into
    // a small offset. The stride is deliberately alignment-clean and above the
    // size floor so it reaches the span check rather than an earlier one.
    #[test]
    fn validate_stride_rejects_span_overflow() {
        let sets = [RegorusHostAwaitResponseSet {
            identifier: core::ptr::null(),
            values_json: core::ptr::null(),
            values_len: 0,
        }];
        let huge = (isize::MAX as usize) + 1; // 2^63, a multiple of 8
        assert!(huge.is_multiple_of(core::mem::align_of::<RegorusHostAwaitResponseSet>()));

        let err = validate_array_stride(
            sets.as_ptr(),
            4,
            huge,
            "response_set_size",
            "RegorusHostAwaitResponseSet",
        )
        .unwrap_err();

        assert!(
            err.to_string().contains("overflows"),
            "expected a span-overflow error, got: {err}"
        );
    }

    // A span past `isize::MAX` that does *not* overflow `usize` is still outside
    // the range `ptr::add` accepts. The reviewer's `len = 2` variant of this case
    // overflows `usize` first and is covered by the test above.
    #[test]
    fn validate_stride_rejects_span_past_isize_max() {
        let sets = [RegorusHostAwaitResponseSet {
            identifier: core::ptr::null(),
            values_json: core::ptr::null(),
            values_len: 0,
        }];
        let huge = (isize::MAX as usize) + 1;

        let err = validate_array_stride(
            sets.as_ptr(),
            1,
            huge,
            "response_set_size",
            "RegorusHostAwaitResponseSet",
        )
        .unwrap_err();

        assert!(
            err.to_string()
                .contains("exceeds the maximum addressable range"),
            "expected an addressable-range error, got: {err}"
        );
    }

    // A zero-length array walks nothing, so any stride — including bogus ones —
    // is accepted, matching the no-host-await call path.
    #[test]
    fn validate_stride_ignores_size_when_empty() {
        validate_array_stride(
            core::ptr::null::<RegorusHostAwaitBuiltin>(),
            0,
            0,
            "host_await_builtin_size",
            "RegorusHostAwaitBuiltin",
        )
        .unwrap();
        validate_array_stride(
            core::ptr::null::<RegorusHostAwaitResponseSet>(),
            0,
            usize::MAX,
            "response_set_size",
            "RegorusHostAwaitResponseSet",
        )
        .unwrap();
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use crate::common::regorus_result_drop;
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

fn to_rvm_string_result(output: Result<String>) -> RegorusResult {
    match output {
        Ok(json) => RegorusResult::ok_string(json),
        Err(err) => to_rvm_error_result(err),
    }
}

fn to_rvm_error_result(err: anyhow::Error) -> RegorusResult {
    let status = match err.downcast_ref::<VmError>() {
        Some(VmError::MemoryBudgetExceeded { .. }) => RegorusStatus::MemoryBudgetExceeded,
        Some(VmError::MemoryBudgetUnsupportedInSuspendableExecution { .. }) => {
            RegorusStatus::MemoryBudgetUnsupportedInSuspendableExecution
        }
        _ => RegorusStatus::Error,
    };
    RegorusResult::err_with_message(status, err.to_string())
}

fn execute_to_rvm_result<F>(vm: *mut RegorusRvm, execute: F) -> RegorusResult
where
    F: FnOnce(&mut RegoVM) -> core::result::Result<Value, VmError>,
{
    let output = || -> Result<RegorusResult> {
        let vm = to_shared_ref(vm as *const RegorusRvm)?;
        let mut guard = vm.try_write()?;
        let value = execute(&mut guard)?;
        let json = value.to_json_str()?;
        let result = RegorusResult::ok_string(json);

        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        if let Err(err) = guard.check_memory_budget() {
            regorus_result_drop(result);
            return Err(err.into());
        }

        Ok(result)
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
        let output = || -> Result<*mut RegorusProgram> {
            if entry_points_len == 0 {
                return Err(anyhow!("entry_points must contain at least one entry"));
            }

            let data_str = from_c_str(data_json)?;
            let data = Value::from_json_str(&data_str)?;
            let policy_modules = convert_c_modules_to_rust(modules, modules_len)?;

            let entry_points_vec = convert_c_entry_points(entry_points, entry_points_len)?;
            let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();

            let entry_rule = entry_points_ref
                .first()
                .ok_or_else(|| anyhow!("entry_points must contain at least one entry"))?;

            let compiled_policy = regorus::compile_policy_with_entrypoint(
                data,
                &policy_modules,
                (*entry_rule).into(),
            )?;

            let program = Compiler::compile_from_policy(&compiled_policy, &entry_points_ref)?;
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
    with_unwind_guard(|| execute_to_rvm_result(vm, RegoVM::execute))
}

/// Execute a named entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_name(
    vm: *mut RegorusRvm,
    entry_point: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let name = match from_c_str(entry_point) {
            Ok(name) => name,
            Err(err) => return to_rvm_error_result(err),
        };
        execute_to_rvm_result(vm, |guard| guard.execute_entry_point_by_name(&name))
    })
}

/// Execute an entry point by index.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_index(
    vm: *mut RegorusRvm,
    index: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        execute_to_rvm_result(vm, |guard| guard.execute_entry_point_by_index(index))
    })
}

/// Resume execution for suspendable runs.
#[no_mangle]
pub extern "C" fn regorus_rvm_resume(
    vm: *mut RegorusRvm,
    resume_value_json: *const c_char,
    has_value: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let value = if has_value {
                Some(Value::from_json_str(&from_c_str(resume_value_json)?)?)
            } else {
                None
            };
            let result = guard.resume(value)?;
            result.to_json_str()
        }();

        to_rvm_string_result(output)
    })
}

/// Get the current execution state of the VM.
#[no_mangle]
pub extern "C" fn regorus_rvm_get_execution_state(vm: *mut RegorusRvm) -> RegorusResult {
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
}

#[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
mod tests {
    use super::{
        regorus_rvm_drop, regorus_rvm_execute, regorus_rvm_execute_entry_point_by_index,
        regorus_rvm_execute_entry_point_by_name, regorus_rvm_new, regorus_rvm_resume,
        regorus_rvm_set_memory_budget_config, RegorusRvm,
    };
    use crate::common::{regorus_result_drop, RegorusStatus};
    use crate::limits::RegorusMemoryBudgetConfig;
    use alloc::boxed::Box;
    use alloc::ffi::CString;
    use alloc::string::ToString;
    use alloc::sync::Arc;
    use alloc::vec;
    use core::ptr;
    use regorus::languages::rego::compiler::Compiler;
    use regorus::rvm::instructions::Instruction;
    use regorus::rvm::program::Program;
    use regorus::rvm::vm::{ExecutionMode, RegoVM};
    use regorus::{Engine, MemoryBudgetConfig, Rc, Value};

    const POLICY: &str = r#"
package limits.memory
import rego.v1

copy := [value | some value in input]
"#;

    const TIGHT_MEMORY_BUDGET_BYTES: u64 = 64 * 1024;

    fn memory_budget(limit: u64) -> MemoryBudgetConfig {
        MemoryBudgetConfig {
            limit: core::num::NonZeroU64::new(limit).expect("non-zero budget"),
        }
    }

    fn host_await_program() -> Arc<Program> {
        let mut program = Program::new();
        program.dispatch_window_size = 3;
        program.max_rule_window_size = 3;
        program.entry_points.insert("main".to_string(), 0);
        program.literals = vec![Value::from("id"), Value::from(1)];
        program.instructions = vec![
            Instruction::Load {
                dest: 0,
                literal_idx: 0,
            },
            Instruction::Load {
                dest: 1,
                literal_idx: 1,
            },
            Instruction::HostAwait {
                dest: 2,
                arg: 1,
                id: 0,
            },
            Instruction::Return { value: 2 },
        ];
        program.instruction_spans = vec![None; program.instructions.len()];
        Arc::new(program)
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
        let results = [
            regorus_rvm_execute(vm),
            regorus_rvm_execute_entry_point_by_name(vm, entrypoint.as_ptr()),
            regorus_rvm_execute_entry_point_by_index(vm, 0),
        ];

        for result in results {
            assert!(matches!(result.status, RegorusStatus::MemoryBudgetExceeded));
            assert!(result.output.is_null());
            regorus_result_drop(result);
        }
        regorus_rvm_drop(vm);
    }

    #[test]
    fn ffi_resume_reports_unsupported_memory_budget_status() {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(host_await_program());
        vm.execute().expect("suspend execution");

        let vm = Box::into_raw(Box::new(RegorusRvm::new(vm)));
        let set_result = regorus_rvm_set_memory_budget_config(
            vm,
            true,
            RegorusMemoryBudgetConfig {
                limit_bytes: 1024 * 1024,
            },
        );
        assert!(matches!(set_result.status, RegorusStatus::Ok));
        regorus_result_drop(set_result);

        let result = regorus_rvm_resume(vm, ptr::null(), false);
        assert!(matches!(
            result.status,
            RegorusStatus::MemoryBudgetUnsupportedInSuspendableExecution
        ));
        regorus_result_drop(result);
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

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::{
    from_c_str, to_ref, to_regorus_result, RegorusBuffer, RegorusResult, RegorusStatus,
};
use crate::compile::RegorusPolicyModule;
use crate::compiled_policy::RegorusCompiledPolicy;
use crate::limits::RegorusExecutionTimerConfig;
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
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
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

            let compiled_policy = &to_ref(compiled_policy)?.compiled_policy;
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
            let program = &to_ref(program)?.program;
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
            if data.is_null() && len > 0 {
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
            let program = &to_ref(program)?.program;
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
            let program = &to_ref(program)?.program;
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
            let policy = to_ref(compiled_policy)?.compiled_policy.clone();
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
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let program = to_ref(program)?.program.clone();
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
            let vm = to_ref(vm)?;
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
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let input_value = Value::from_json_str(&from_c_str(input)?)?;
            guard.set_input(input_value);
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
            let vm = to_ref(vm)?;
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
            let vm = to_ref(vm)?;
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
            let vm = to_ref(vm)?;
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
            let vm = to_ref(vm)?;
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
            let vm = to_ref(vm)?;
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

/// Execute the program's main entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let result = guard.execute()?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Execute a named entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_name(
    vm: *mut RegorusRvm,
    entry_point: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let name = from_c_str(entry_point)?;
            let result = guard.execute_entry_point_by_name(&name)?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Execute an entry point by index.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_index(
    vm: *mut RegorusRvm,
    index: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let result = guard.execute_entry_point_by_index(index)?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
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
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let value = if has_value {
                Some(Value::from_json_str(&from_c_str(resume_value_json)?)?)
            } else {
                None
            };
            let result = guard.resume(value)?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Get the current execution state of the VM.
#[no_mangle]
pub extern "C" fn regorus_rvm_get_execution_state(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_ref(vm)?;
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

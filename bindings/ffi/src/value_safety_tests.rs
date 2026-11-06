// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::common::regorus_result_drop;
use core::ffi::CStr;
use std::ffi::CString;

#[path = "../../../tests/native_depth_support/mod.rs"]
mod native_depth_support;

#[test]
#[cfg_attr(miri, ignore)]
fn returned_values_on_exact_1_mib_stack() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess(
            "rvm::value_safety_tests::returned_values_on_exact_1_mib_stack",
        );
        return;
    }
    std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(|| {
            let entry = CString::new("data.value.echo").unwrap();
            let mut engine = regorus::Engine::new();
            engine
                .add_policy("value.rego".into(), "package value\necho := input".into())
                .unwrap();
            let policy = engine
                .compile_with_entrypoint(&"data.value.echo".into())
                .unwrap();
            let program = Compiler::compile_from_policy(&policy, &["data.value.echo"]).unwrap();
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                let input = (0..512).fold(Value::Null, |v, _| Value::from(vec![v]));
                let expected = input.to_json_str().unwrap();
                vm.set_input(input);
                let handle = Box::into_raw(Box::new(RegorusRvm::new(vm)));
                for entry_kind in 0..3 {
                    let result = match entry_kind {
                        0 => regorus_rvm_execute(handle),
                        1 => regorus_rvm_execute_entry_point_by_name(handle, entry.as_ptr()),
                        _ => regorus_rvm_execute_entry_point_by_index(handle, 0),
                    };
                    assert_eq!(result.status, RegorusStatus::Ok);
                    assert!(result.error_message.is_null());
                    assert!(!result.output.is_null());
                    let text = unsafe { CStr::from_ptr(result.output) }.to_str().unwrap();
                    assert_eq!(text, expected);
                    regorus_result_drop(result);
                }
                {
                    let handle = unsafe { &*handle };
                    handle.try_write().unwrap().set_input(Value::Bool(true));
                }
                let healthy = regorus_rvm_execute_entry_point_by_index(handle, 0);
                assert_eq!(healthy.status, RegorusStatus::Ok);
                assert_eq!(
                    unsafe { CStr::from_ptr(healthy.output) }.to_str().unwrap(),
                    "true"
                );
                regorus_result_drop(healthy);
                regorus_rvm_drop(handle);
            }

            engine
                .add_policy(
                    "limit.rego".into(),
                    "package serialization\nresult := json.marshal(input)".into(),
                )
                .unwrap();
            let policy = engine
                .compile_with_entrypoint(&"data.serialization.result".into())
                .unwrap();
            let program =
                Compiler::compile_from_policy(&policy, &["data.serialization.result"]).unwrap();
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                for strict in [false, true] {
                    let mut vm = RegoVM::new();
                    vm.load_program(program.clone());
                    vm.set_execution_mode(mode);
                    vm.set_strict_builtin_errors(strict);
                    vm.set_input((0..65).fold(Value::Null, |v, _| Value::from(vec![v])));
                    let handle = Box::into_raw(Box::new(RegorusRvm::new(vm)));
                    let rejected = regorus_rvm_execute_entry_point_by_index(handle, 0);
                    assert_eq!(rejected.status, RegorusStatus::Error);
                    assert!(rejected.output.is_null());
                    let message = unsafe { CStr::from_ptr(rejected.error_message) }
                        .to_str()
                        .unwrap();
                    assert!(
                        message.contains("serialization") && message.contains("64"),
                        "{message}"
                    );
                    regorus_result_drop(rejected);
                    let boundary = (0..64).fold(Value::Null, |v, _| Value::from(vec![v]));
                    let expected = Value::from(boundary.to_string()).to_json_str().unwrap();
                    unsafe { &*handle }.try_write().unwrap().set_input(boundary);
                    let accepted = regorus_rvm_execute_entry_point_by_index(handle, 0);
                    assert_eq!(accepted.status, RegorusStatus::Ok);
                    assert_eq!(
                        unsafe { CStr::from_ptr(accepted.output) }.to_str().unwrap(),
                        expected
                    );
                    regorus_result_drop(accepted);
                    unsafe { &*handle }
                        .try_write()
                        .unwrap()
                        .set_input(Value::Null);
                    let healthy = regorus_rvm_execute_entry_point_by_index(handle, 0);
                    assert_eq!(healthy.status, RegorusStatus::Ok);
                    assert_eq!(
                        unsafe { CStr::from_ptr(healthy.output) }.to_str().unwrap(),
                        "\"null\""
                    );
                    regorus_result_drop(healthy);
                    regorus_rvm_drop(handle);
                }
            }

            // SO10: no parser, evaluation, comparison, or formatting before destruction.
            let leaf: regorus::Rc<str> = regorus::Rc::from("destructor-only");
            let mut vm = RegoVM::new();
            vm.set_input((0..8192).fold(Value::String(leaf.clone()), |v, _| Value::from(vec![v])));
            let handle = Box::into_raw(Box::new(RegorusRvm::new(vm)));
            eprintln!("FFI destructor-only handoff complete");
            regorus_rvm_drop(handle);
            assert_eq!(regorus::Rc::strong_count(&leaf), 1);
            eprintln!("FFI destructor-only release complete");
        })
        .unwrap()
        .join()
        .unwrap();
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::common::regorus_result_drop;
use crate::native_depth_support;
use core::ffi::CStr;
use regorus::Value;
use std::ffi::CString;

#[test]
#[cfg_attr(miri, ignore)]
fn query_values_and_bindings_on_exact_1_mib_stack() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess(
            "engine::value_safety_tests::query_values_and_bindings_on_exact_1_mib_stack",
        );
        return;
    }
    std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(|| {
            let handle = regorus_engine_new();
            assert!(!handle.is_null());
            for depth in [65, 512] {
                let input = (0..depth).fold(Value::Null, |child, _| Value::from(vec![child]));
                unsafe { &*handle }
                    .try_write()
                    .unwrap()
                    .set_input(input.clone());
                for query in ["input", "x := input"] {
                    let mut reference = regorus::Engine::new();
                    reference.set_input(input.clone());
                    let expected = reference
                        .eval_query(query.into(), false)
                        .unwrap()
                        .to_json_str()
                        .unwrap();
                    let query = CString::new(query).unwrap();
                    for _ in 0..2 {
                        let result = regorus_engine_eval_query(handle, query.as_ptr());
                        assert_eq!(result.status, RegorusStatus::Ok);
                        assert!(result.error_message.is_null());
                        assert!(!result.output.is_null());
                        assert_eq!(
                            unsafe { CStr::from_ptr(result.output) }.to_str().unwrap(),
                            expected
                        );
                        regorus_result_drop(result);
                    }
                }
                {
                    let engine = unsafe { &*handle };
                    let mut guard = engine.try_write().unwrap();
                    guard.set_strict_builtin_errors(true);
                }
                let query = CString::new("upper(input)").unwrap();
                let rejected = regorus_engine_eval_query(handle, query.as_ptr());
                assert_eq!(rejected.status, RegorusStatus::Error);
                assert!(rejected.output.is_null());
                regorus_result_drop(rejected);
                unsafe { &*handle }
                    .try_write()
                    .unwrap()
                    .set_input(Value::Bool(true));
                let query = CString::new("input").unwrap();
                let healthy = regorus_engine_eval_query(handle, query.as_ptr());
                assert_eq!(healthy.status, RegorusStatus::Ok);
                regorus_result_drop(healthy);
            }
            regorus_engine_drop(handle);
        })
        .unwrap()
        .join()
        .unwrap();
}

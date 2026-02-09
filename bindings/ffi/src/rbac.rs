// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::{from_c_str, RegorusResult, RegorusStatus};
use crate::panic_guard::with_unwind_guard;
use alloc::format;
use core::ffi::c_char;

use regorus::languages::azure_rbac::ast::EvaluationContext;
use regorus::languages::azure_rbac::interpreter::ConditionInterpreter;

#[no_mangle]
/// Evaluate an Azure RBAC condition expression against a JSON evaluation context.
///
/// * `condition`: RBAC condition string.
/// * `context_json`: JSON representation of EvaluationContext.
pub extern "C" fn regorus_rbac_engine_eval_condition(
    condition: *const c_char,
    context_json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let condition = match from_c_str(condition) {
            Ok(value) => value,
            Err(err) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("{err}"),
                )
            }
        };
        let context_json = match from_c_str(context_json) {
            Ok(value) => value,
            Err(err) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidArgument,
                    format!("{err}"),
                )
            }
        };
        let context: EvaluationContext = match serde_json::from_str(&context_json) {
            Ok(context) => context,
            Err(err) => {
                return RegorusResult::err_with_message(
                    RegorusStatus::InvalidDataFormat,
                    format!("invalid context json: {err}"),
                )
            }
        };

        let interpreter = ConditionInterpreter::new(&context);
        match interpreter.evaluate_str(&condition) {
            Ok(result) => RegorusResult::ok_bool(result),
            Err(err) => RegorusResult::err_with_message(
                RegorusStatus::Error,
                format!("condition evaluation failed: {err}"),
            ),
        }
    })
}

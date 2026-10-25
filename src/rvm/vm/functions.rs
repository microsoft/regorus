// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::builtins;
use crate::value::Value;

use super::errors::{Result, VmError};
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;

impl RegoVM {
    pub(super) fn execute_function_call(&mut self, params_index: u16) -> Result<()> {
        let params = self
            .program
            .instruction_data
            .get_function_call_params(params_index)
            .cloned()
            .ok_or(VmError::InvalidFunctionCallParamsIndex {
                index: params_index,
                pc: self.pc,
                available: self.program.instruction_data.function_call_params.len(),
            })?;
        let call_result = match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.execute_call_rule_common(params.dest, params.func_rule_index, Some(&params))
            }
            ExecutionMode::Suspendable => self.execute_call_rule_suspendable(
                params.dest,
                params.func_rule_index,
                Some(&params),
            ),
        };

        call_result?;

        self.memory_check()?;
        Ok(())
    }

    pub(super) fn execute_builtin_call(&mut self, params_index: u16) -> Result<()> {
        let program = self.program.clone();
        let params = program
            .instruction_data
            .get_builtin_call_params(params_index)
            .ok_or(VmError::InvalidBuiltinCallParamsIndex {
                index: params_index,
                pc: self.pc,
                available: program.instruction_data.builtin_call_params.len(),
            })?
            .clone();
        let builtin_info = program.get_builtin_info(params.builtin_index).ok_or(
            VmError::InvalidBuiltinInfoIndex {
                index: params.builtin_index,
                pc: self.pc,
                available: program.builtin_info_table.len(),
            },
        )?;

        let mut args = core::mem::take(&mut self.cached_builtin_args);
        args.clear();
        for &arg_reg in params.arg_registers().iter() {
            let arg_value = match self.get_register(arg_reg) {
                Ok(value) => value.clone(),
                Err(error) => {
                    self.cached_builtin_args = args;
                    return Err(error);
                }
            };
            args.push(arg_value);
        }

        let expected_args = builtin_info.num_args;
        let actual_args = args.len();
        if u16::try_from(actual_args).unwrap_or(u16::MAX) != expected_args {
            self.cached_builtin_args = args;
            return Err(VmError::BuiltinArgumentMismatch {
                expected: expected_args,
                actual: actual_args,
                pc: self.pc,
            });
        }

        if args.iter().any(|a| a == &Value::Undefined) {
            self.cached_builtin_args = args;
            self.set_register(params.dest, Value::Undefined)?;
            self.memory_check()?;
            return Ok(());
        }

        // Extract everything we need from program before releasing the borrow.
        let builtin_fn = match program.get_resolved_builtin(params.builtin_index) {
            Some(fcn) => fcn.0,
            None => {
                self.cached_builtin_args = args;
                return Err(VmError::BuiltinNotResolved {
                    name: builtin_info.name.clone(),
                    pc: self.pc,
                });
            }
        };
        let cache_name = builtins::must_cache(builtin_info.name.as_str());
        #[cfg(feature = "history")]
        let is_history_match = builtin_info.name == "history.match";
        drop(program);

        if let Err(error) = self.ensure_dummy_exprs(args.len()) {
            self.cached_builtin_args = args;
            return Err(error);
        }
        let dummy_span = match self.get_dummy_span() {
            Ok(span) => span.clone(),
            Err(error) => {
                self.cached_builtin_args = args;
                return Err(error);
            }
        };
        // Take the dummy_exprs vec out of self so we can pass it to the builtin
        // while still calling &mut self methods afterwards.
        let dummy_exprs = core::mem::take(&mut self.dummy_exprs);

        if let Some(name) = cache_name {
            if let Some(entries) = self.builtins_cache.get(name) {
                for entry in entries {
                    if entry.0.as_slice() == args.as_slice() {
                        let cached = entry.1.clone();
                        self.dummy_exprs = dummy_exprs;
                        self.cached_builtin_args = args;
                        self.set_register(params.dest, cached)?;
                        self.memory_check()?;
                        return Ok(());
                    }
                }
            }
        }

        #[cfg(feature = "history")]
        let contextual_result = is_history_match.then(|| {
            builtins::history_match_with_context(
                &dummy_span,
                dummy_exprs.get(..args.len()).unwrap_or(&[]),
                &args,
                &mut self.history_match_state,
                &mut self.execution_timer,
            )
        });
        #[cfg(not(feature = "history"))]
        let contextual_result = None;
        #[cfg_attr(not(feature = "history"), allow(clippy::unnecessary_literal_unwrap))]
        let result = contextual_result.unwrap_or_else(|| {
            builtin_fn(
                &dummy_span,
                dummy_exprs.get(..args.len()).unwrap_or(&[]),
                &args,
                self.strict_builtin_errors,
            )
        });
        self.dummy_exprs = dummy_exprs;
        let result = match result {
            Ok(value) => value,
            Err(error) => {
                if self.strict_builtin_errors || builtins::is_fatal_builtin_error(&error) {
                    self.cached_builtin_args = args;
                    #[cfg(feature = "history")]
                    if is_history_match {
                        return Err(Self::history_match_error(error, self.pc));
                    }
                    return Err(error.into());
                }
                Value::Undefined
            }
        };

        if let Some(name) = cache_name {
            // Move args into the cache. The now-empty (zero-capacity) Vec is
            // stored back in cached_builtin_args; the next call will re-allocate.
            // This is acceptable because cache inserts are rare (once per unique
            // argument set) while the hot path (cache hit above) reuses the Vec.
            let cache_args = core::mem::take(&mut args);
            self.cached_builtin_args = args;
            self.builtins_cache
                .entry(name)
                .or_default()
                .push((cache_args, result.clone()));
            self.set_register(params.dest, result)?;
        } else {
            self.cached_builtin_args = args;
            self.set_register(params.dest, result)?;
        }

        self.memory_check()?;

        Ok(())
    }

    #[cfg(feature = "history")]
    pub(super) fn history_match_error(error: anyhow::Error, pc: usize) -> VmError {
        if let Some(limit) = error.downcast_ref::<crate::LimitError>() {
            return match *limit {
                crate::LimitError::TimeLimitExceeded { elapsed, limit } => {
                    VmError::TimeLimitExceeded { elapsed, limit, pc }
                }
                crate::LimitError::MemoryLimitExceeded { usage, limit } => {
                    VmError::MemoryLimitExceeded { usage, limit, pc }
                }
                crate::LimitError::RegexSizeLimitExceeded { limit } => {
                    VmError::RegexSizeLimitExceeded { limit, pc }
                }
            };
        }
        if builtins::is_fatal_builtin_error(&error) {
            return VmError::HistoryMatchFailure {
                message: alloc::format!("{error}"),
                pc,
            };
        }
        VmError::HistoryMatchValidationError {
            message: alloc::format!("{error}"),
            pc,
        }
    }
}

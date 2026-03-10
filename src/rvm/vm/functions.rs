// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::builtins;
use crate::value::Value;
use alloc::vec::Vec;

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

        let mut args = Vec::new();
        for &arg_reg in params.arg_registers().iter() {
            let arg_value = self.get_register(arg_reg)?.clone();
            args.push(arg_value);
        }

        let expected_args = builtin_info.num_args;
        let actual_args = args.len();
        if u16::try_from(actual_args).unwrap_or(u16::MAX) != expected_args {
            return Err(VmError::BuiltinArgumentMismatch {
                expected: expected_args,
                actual: actual_args,
                pc: self.pc,
            });
        }

        if args.iter().any(|a| a == &Value::Undefined) {
            self.set_register(params.dest, Value::Undefined)?;
            self.memory_check()?;
            return Ok(());
        }

        // Extract everything we need from program before releasing the borrow.
        let builtin_fn = match program.get_resolved_builtin(params.builtin_index) {
            Some(fcn) => fcn.0,
            None => {
                return Err(VmError::BuiltinNotResolved {
                    name: builtin_info.name.clone(),
                    pc: self.pc,
                });
            }
        };
        let cache_name = builtins::must_cache(builtin_info.name.as_str());
        drop(program);

        self.ensure_dummy_exprs(args.len())?;
        let dummy_span = self.get_dummy_span()?.clone();
        // Take the dummy_exprs vec out of self so we can pass it to the builtin
        // while still calling &mut self methods afterwards.
        let dummy_exprs = core::mem::take(&mut self.dummy_exprs);

        if let Some(name) = cache_name {
            if let Some(value) = self.builtins_cache.get(&(name, args.clone())) {
                self.dummy_exprs = dummy_exprs;
                self.set_register(params.dest, value.clone())?;
                return Ok(());
            }
        }

        let result = match builtin_fn(
            &dummy_span,
            dummy_exprs.get(..args.len()).unwrap_or(&[]),
            &args,
            self.strict_builtin_errors,
        ) {
            Ok(value) => value,
            Err(_) if !self.strict_builtin_errors => Value::Undefined,
            Err(err) => {
                self.dummy_exprs = dummy_exprs;
                return Err(err.into());
            }
        };

        // Put dummy_exprs back for reuse.
        self.dummy_exprs = dummy_exprs;

        if result == Value::Undefined {
            self.set_register(params.dest, Value::Undefined)?;
        } else {
            self.set_register(params.dest, result.clone())?;
        }

        if let Some(name) = cache_name {
            self.builtins_cache.insert((name, args), result);
        }

        self.memory_check()?;

        Ok(())
    }
}

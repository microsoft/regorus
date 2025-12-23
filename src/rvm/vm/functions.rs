// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::indexing_slicing, clippy::as_conversions)]
use crate::builtins;
use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;

use super::errors::{Result, VmError};
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;

impl RegoVM {
    pub(super) fn execute_function_call(&mut self, params_index: u16) -> Result<()> {
        let params =
            self.program.instruction_data.function_call_params[params_index as usize].clone();
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.execute_call_rule_common(params.dest, params.func_rule_index, Some(&params))
            }
            ExecutionMode::Suspendable => self.execute_call_rule_suspendable(
                params.dest,
                params.func_rule_index,
                Some(&params),
            ),
        }
    }

    pub(super) fn execute_builtin_call(&mut self, params_index: u16) -> Result<()> {
        let params = &self.program.instruction_data.builtin_call_params[params_index as usize];
        let builtin_info = &self.program.builtin_info_table[params.builtin_index as usize];

        let mut args = Vec::new();
        for &arg_reg in params.arg_registers().iter() {
            let arg_value = self.registers[arg_reg as usize].clone();
            args.push(arg_value);
        }

        if (args.len() as u16) != builtin_info.num_args {
            return Err(VmError::BuiltinArgumentMismatch {
                expected: builtin_info.num_args,
                actual: args.len(),
            });
        }

        if args.iter().any(|a| a == &Value::Undefined) {
            self.registers[params.dest as usize] = Value::Undefined;
            return Ok(());
        }

        if let Some(builtin_fcn) = self.program.get_resolved_builtin(params.builtin_index) {
            let dummy_source = crate::lexer::Source::from_contents("arg".into(), String::new())?;
            let dummy_span = crate::lexer::Span {
                source: dummy_source,
                line: 1,
                col: 1,
                start: 0,
                end: 3,
            };

            let mut dummy_exprs: Vec<crate::ast::Ref<crate::ast::Expr>> = Vec::new();
            for _ in 0..args.len() {
                let dummy_expr = crate::ast::Expr::Null {
                    span: dummy_span.clone(),
                    value: Value::Null,
                    eidx: 0,
                };
                dummy_exprs.push(crate::ast::Ref::new(dummy_expr));
            }

            let cache_name = builtins::must_cache(builtin_info.name.as_str());
            if let Some(name) = cache_name {
                if let Some(value) = self.builtins_cache.get(&(name, args.clone())) {
                    self.registers[params.dest as usize] = value.clone();
                    return Ok(());
                }
            }

            let result =
                match (builtin_fcn.0)(&dummy_span, &dummy_exprs, &args, self.strict_builtin_errors)
                {
                    Ok(value) => value,
                    Err(_) if !self.strict_builtin_errors => Value::Undefined,
                    Err(err) => return Err(err.into()),
                };

            if result == Value::Undefined {
                self.registers[params.dest as usize] = Value::Undefined;
            } else {
                self.registers[params.dest as usize] = result.clone();
            }

            if let Some(name) = cache_name {
                self.builtins_cache.insert((name, args), result);
            }
        } else {
            return Err(VmError::BuiltinNotResolved {
                name: builtin_info.name.clone(),
            });
        }

        Ok(())
    }
}

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
        if self.builtin_policy.is_disabled(&builtin_info.name) {
            return Err(VmError::BuiltinDisabled {
                name: builtin_info.name.clone(),
                pc: self.pc,
            });
        }

        let mut args = core::mem::take(&mut self.cached_builtin_args);
        args.clear();
        for &arg_reg in params.arg_registers().iter() {
            let arg_value = self.get_register(arg_reg)?.clone();
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
        drop(program);

        self.ensure_dummy_exprs(args.len())?;
        let dummy_span = self.get_dummy_span()?.clone();
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

        let result = match builtin_fn(
            &dummy_span,
            dummy_exprs.get(..args.len()).unwrap_or(&[]),
            &args,
            self.strict_builtin_errors,
        ) {
            Ok(value) => value,
            // Resource-limit errors must always propagate, even in non-strict
            // mode, to prevent `not builtin(...)` from silently flipping to true.
            Err(e) if !self.strict_builtin_errors => {
                if e.downcast_ref::<crate::LimitError>().is_some() {
                    self.dummy_exprs = dummy_exprs;
                    self.cached_builtin_args = args;
                    return Err(e.into());
                }
                Value::Undefined
            }
            Err(err) => {
                self.dummy_exprs = dummy_exprs;
                self.cached_builtin_args = args;
                return Err(err.into());
            }
        };

        // Put dummy_exprs back for reuse.
        self.dummy_exprs = dummy_exprs;

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
}

#[cfg(all(test, feature = "time"))]
mod tests {
    use super::{RegoVM, VmError};
    use crate::languages::rego::compiler::Compiler;
    use crate::rvm::instructions::Instruction;
    use crate::rvm::BuiltinPolicy;
    use crate::{Engine, Rc, Value};
    use alloc::vec;

    #[allow(clippy::expect_used)]
    #[test]
    fn disabled_cached_builtin_fails_before_cache_lookup() {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "test.rego".into(),
                "package test\nresult := time.now_ns()".into(),
            )
            .expect("add policy");
        let entry_point = "data.test.result";
        let compiled = engine
            .compile_with_entrypoint(&Rc::from(entry_point))
            .expect("compile policy");
        let program =
            Compiler::compile_from_policy(&compiled, &[entry_point]).expect("compile to RVM");
        let params_index = program
            .instructions
            .iter()
            .find_map(|instruction| match instruction {
                &Instruction::BuiltinCall { params_index } => Some(params_index),
                _ => None,
            })
            .expect("builtin call instruction");

        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_builtin_policy(
            BuiltinPolicy::from_disabled_names(&["time.now_ns"]).expect("valid policy"),
        )
        .expect("set builtin policy");
        vm.builtins_cache
            .insert("time.now_ns", vec![(vec![], Value::from(7))]);

        assert!(matches!(
            vm.execute_builtin_call(params_index),
            Err(VmError::BuiltinDisabled { name, .. }) if name == "time.now_ns"
        ));
        assert!(
            vm.builtins_cache.contains_key("time.now_ns"),
            "the preloaded cache entry should not be consumed or removed"
        );
    }
}

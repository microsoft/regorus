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

#[cfg(all(test, feature = "rand"))]
mod tests {
    use super::super::errors::VmError;
    use super::super::execution_model::ExecutionState;
    use super::super::machine::RegoVM;
    use crate::rvm::instructions::BuiltinCallParams;
    use crate::rvm::program::{BuiltinInfo, Program};
    use crate::rvm::{BuiltinPolicy, Instruction};
    use crate::value::Value;
    use alloc::sync::Arc;
    use alloc::vec;

    fn vm_with_restricted_rand_call(args: [u8; 8]) -> RegoVM {
        let mut program = Program::new();
        program.dispatch_window_size = 3;
        let builtin_index = program.add_builtin_info(BuiltinInfo {
            name: "rand.intn".into(),
            num_args: 2,
        });
        let params_index = program.add_builtin_call_params(BuiltinCallParams {
            dest: 2,
            builtin_index,
            num_args: 2,
            args,
        });
        program
            .instructions
            .push(Instruction::BuiltinCall { params_index });
        assert!(
            program.initialize_resolved_builtins().is_ok(),
            "rand.intn resolves in this feature configuration"
        );

        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        let policy = BuiltinPolicy::from_disabled_names(&["rand.intn"]);
        assert!(policy.is_ok(), "rand.intn is a registered builtin");
        if let Ok(policy) = policy {
            vm.builtin_policy = policy;
        }
        vm
    }

    #[test]
    fn disabled_native_guard_precedes_argument_reads_and_cached_results() {
        let mut invalid_register_vm = vm_with_restricted_rand_call([u8::MAX; 8]);
        invalid_register_vm.cached_builtin_args.push(Value::from(9));
        let result = invalid_register_vm.execute_builtin_call(0);
        assert!(matches!(
            result,
            Err(VmError::BuiltinDisabled { name, .. }) if name == "rand.intn"
        ));
        assert_eq!(invalid_register_vm.cached_builtin_args, [Value::from(9)]);

        let mut cached_vm = vm_with_restricted_rand_call([0, 1, 0, 0, 0, 0, 0, 0]);
        assert!(cached_vm.registers.len() > 1);
        let Some(first_register) = cached_vm.registers.get_mut(0) else {
            return;
        };
        *first_register = Value::from(1);
        let Some(second_register) = cached_vm.registers.get_mut(1) else {
            return;
        };
        *second_register = Value::from(2);
        cached_vm.builtins_cache.insert(
            "rand.intn",
            vec![(vec![Value::from(1), Value::from(2)], Value::from(42))],
        );
        let cached_result = cached_vm.execute_builtin_call(0);
        assert!(matches!(
            cached_result,
            Err(VmError::BuiltinDisabled { name, .. }) if name == "rand.intn"
        ));
        assert_eq!(
            cached_vm.builtins_cache.get("rand.intn"),
            Some(&vec![(
                vec![Value::from(1), Value::from(2)],
                Value::from(42)
            )])
        );
    }

    #[test]
    fn busy_policy_replacement_preserves_vm_state_and_accepted_replacement_clears_it() {
        let mut vm = vm_with_restricted_rand_call([0; 8]);
        let original_policy = vm.get_builtin_policy().clone();
        vm.execution_state = ExecutionState::Running;
        vm.evaluated = Value::from("stale result");
        vm.cached_builtin_args.push(Value::from(9));
        vm.builtins_cache.insert(
            "rand.intn",
            vec![(vec![Value::from(1), Value::from(2)], Value::from(42))],
        );

        let result = vm.set_builtin_policy(BuiltinPolicy::default());
        assert!(matches!(
            result,
            Err(VmError::BuiltinPolicyChangeWhileExecuting { .. })
        ));
        assert_eq!(vm.get_builtin_policy(), &original_policy);
        assert!(matches!(vm.execution_state(), ExecutionState::Running));
        assert_eq!(vm.evaluated, Value::from("stale result"));
        assert_eq!(vm.cached_builtin_args, [Value::from(9)]);
        assert_eq!(
            vm.builtins_cache.get("rand.intn"),
            Some(&vec![(
                vec![Value::from(1), Value::from(2)],
                Value::from(42)
            )])
        );

        vm.execution_state = ExecutionState::Completed {
            result: Value::from(42),
        };
        assert!(
            vm.set_builtin_policy(BuiltinPolicy::default()).is_ok(),
            "completed VM can accept a new policy"
        );
        assert!(matches!(vm.execution_state(), ExecutionState::Ready));
        assert!(vm.builtins_cache.is_empty());
        assert!(vm.cached_builtin_args.is_empty());
    }
}

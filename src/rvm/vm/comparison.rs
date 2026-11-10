// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::cmp::Ordering;

use crate::value::{compare_checked, compare_unchecked};
use crate::Value;

use super::errors::{Result, VmError};
use super::machine::RegoVM;

fn operands(registers: &[Value], pc: usize, left: u8, right: u8) -> Result<(&Value, &Value)> {
    let get = |index: u8| {
        registers
            .get(usize::from(index))
            .ok_or(VmError::RegisterIndexOutOfBounds {
                index,
                pc,
                register_count: registers.len(),
            })
    };
    Ok((get(left)?, get(right)?))
}

fn contains_checked<E>(
    collection: &Value,
    value: &Value,
    memory_only: bool,
    checkpoint: &mut impl FnMut() -> core::result::Result<(), E>,
) -> core::result::Result<bool, E> {
    if memory_only && !matches!(value, Value::Array(_) | Value::Set(_) | Value::Object(_)) {
        if let Value::Set(ref items) = *collection {
            // A scalar probe cannot descend into stored containers. Keep the
            // logarithmic lookup when no timer needs to interrupt comparisons.
            checkpoint()?;
            let found = items.contains(value);
            checkpoint()?;
            return Ok(found);
        }
    }

    let mut equals =
        |item: &Value| compare_checked(item, value, true, checkpoint).map(Ordering::is_eq);
    match *collection {
        Value::Array(ref items) => {
            for item in items.iter() {
                if equals(item)? {
                    return Ok(true);
                }
            }
        }
        Value::Object(ref items) => {
            for item in items.values() {
                if equals(item)? {
                    return Ok(true);
                }
            }
        }
        // A B-tree comparator cannot return a resource error mid-traversal.
        Value::Set(ref items) => {
            for item in items.iter_sorted() {
                if equals(item)? {
                    return Ok(true);
                }
            }
        }
        _ => {}
    }
    Ok(false)
}

impl RegoVM {
    fn needs_checked_comparison(&self) -> bool {
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        if self.active_memory_budget_config.is_some()
            || crate::utils::limits::global_memory_limit().is_some()
        {
            return true;
        }
        self.execution_timer.config().is_some()
    }

    pub(super) fn compare_registers(
        &mut self,
        left: u8,
        right: u8,
        equality: bool,
    ) -> Result<Ordering> {
        if !self.needs_checked_comparison() {
            return Ok(compare_unchecked(
                self.get_register(left)?,
                self.get_register(right)?,
                equality,
            ));
        }

        let pc = self.pc;
        let (left, right) = operands(&self.registers, pc, left, right)?;
        let (left, right) = (left.clone(), right.clone());
        compare_checked(&left, &right, equality, &mut || {
            Self::tick_execution_timer(&mut self.execution_timer, pc, 1)?;
            self.check_initial_memory_limit()
        })
    }

    pub(super) fn contains_registers(&mut self, collection: u8, value: u8) -> Result<bool> {
        let pc = self.pc;
        let (value, collection) = operands(&self.registers, pc, value, collection)?;
        if !self.needs_checked_comparison() {
            return Ok(match *collection {
                Value::Set(ref items) => items.contains(value),
                Value::Array(ref items) => items.contains(value),
                Value::Object(ref items) => items.values().any(|item| item == value),
                _ => false,
            });
        }

        let (value, collection) = (value.clone(), collection.clone());
        contains_checked(
            &collection,
            &value,
            self.execution_timer.config().is_none(),
            &mut || {
                Self::tick_execution_timer(&mut self.execution_timer, pc, 1)?;
                self.check_initial_memory_limit()
            },
        )
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    #![allow(clippy::panic_in_result_fn)]

    use super::*;
    use alloc::collections::{BTreeMap, BTreeSet};
    use alloc::sync::Arc;
    use alloc::vec;
    use core::convert::Infallible;
    use core::num::NonZeroU32;
    use core::time::Duration;

    use crate::rvm::instructions::Instruction;
    use crate::rvm::program::Program;
    use crate::rvm::vm::ExecutionMode;
    use crate::utils::limits::{acquire_limits_test_lock, ExecutionTimerConfig};
    use crate::value::{Object, Set};
    use crate::Rc;

    fn dag(depth: usize, wrap: fn(Value) -> Value) -> Value {
        (0..depth).fold(Value::Null, |child, _| {
            let child = wrap(child);
            Value::from(vec![child.clone(), child])
        })
    }

    fn object(value: Value) -> Value {
        Object::from_iter([(Value::from("key"), value)]).into()
    }

    fn set(value: Value) -> Value {
        Set::from_iter([value]).into_value()
    }

    #[test]
    fn checked_comparison_matches_native_semantics() -> anyhow::Result<()> {
        let mut values = vec![
            Value::Null,
            Value::Undefined,
            Value::Bool(false),
            Value::Bool(true),
            Value::from(-1_i64),
            Value::from(0_u64),
            Value::from(1_u64),
            Value::from(1.0_f64),
            Value::from(f64::NAN),
            Value::from(f64::INFINITY),
            Value::from_json_str("1234567890123456789012345678901234567890")?,
            Value::from(""),
            Value::from("alpha"),
            Value::new_array(),
            Value::from(vec![Value::Null]),
            Value::from(vec![Value::Null, Value::Bool(true)]),
            Value::new_object(),
            object(Value::Null),
            object(Value::Bool(true)),
            Object::from_iter([(Value::from(vec![Value::Null]), Value::Undefined)]).into(),
            Value::new_set(),
            set(Value::Null),
            Set::from_iter([Value::Null, Value::Bool(true)]).into_value(),
        ];
        for prefix in [255, 256, 257, 513] {
            for suffix in ["", "a", "z", "\u{100}"] {
                values.push(Value::from(alloc::format!(
                    "{}{suffix}",
                    "x".repeat(prefix)
                )));
            }
        }
        let leaves = values.clone();
        for value in leaves {
            values.push(Value::from(vec![value.clone(), value.clone()]));
            values.push(Value::from(BTreeSet::from([value.clone()])));
            values.push(Value::from(BTreeMap::from([(value.clone(), value)])));
        }
        for wrap in [core::convert::identity, object, set] {
            values.push(dag(4, wrap));
        }
        for left in &values {
            for right in &values {
                for equality in [false, true] {
                    let result =
                        compare_checked(left, right, equality, &mut || Ok::<(), Infallible>(()))?;
                    if equality {
                        assert_eq!(result.is_eq(), left == right);
                    } else {
                        assert_eq!(result, left.cmp(right));
                    }
                }
            }
        }
        Ok(())
    }

    #[test]
    fn checked_comparison_interrupts_and_shortcuts() {
        for equality in [false, true] {
            for (a, b) in [
                (
                    Value::from(vec![Value::Null; 128]),
                    Value::from(vec![Value::Null; 128]),
                ),
                (Value::from("x".repeat(4096)), Value::from("x".repeat(4096))),
            ] {
                let mut count = 0;
                let result = compare_checked(&a, &b, equality, &mut || {
                    count += 1;
                    if count == 4 {
                        Err("deadline")
                    } else {
                        Ok(())
                    }
                });
                assert_eq!(result, Err("deadline"));
                assert_eq!(count, 4);
            }
        }
        for a in [
            Value::from(vec![Value::Null; 128]),
            Value::from(BTreeSet::from([Value::Null])),
            Value::from(BTreeMap::from([(Value::Null, Value::Null)])),
            Value::from("x".repeat(4096)),
        ] {
            let alias = a.clone();
            let mut count = 0;
            assert_eq!(
                compare_checked(&a, &alias, true, &mut || {
                    count += 1;
                    Ok::<(), Infallible>(())
                }),
                Ok(Ordering::Equal)
            );
            assert_eq!(count, 1);
        }
    }

    #[test]
    fn checked_comparison_interrupts_bounded_shared_dags_and_strings() {
        for equality in [false, true] {
            for depth in [4, 8, 12] {
                for wrap in [core::convert::identity, object, set] {
                    let left = dag(depth, wrap);
                    let right = dag(depth, wrap);
                    for stop_at in [1, 3, 7, 31] {
                        let mut checkpoints = 0;
                        assert_eq!(
                            compare_checked(&left, &right, equality, &mut || {
                                checkpoints += 1;
                                if checkpoints == stop_at {
                                    Err("deadline")
                                } else {
                                    Ok(())
                                }
                            }),
                            Err("deadline")
                        );
                        assert_eq!(checkpoints, stop_at);
                    }
                }
            }
            let left = Value::String(Rc::from("x".repeat(2048)));
            let right = Value::String(Rc::from("x".repeat(2048)));
            let mut checkpoints = 0;
            assert_eq!(
                compare_checked(&left, &right, equality, &mut || {
                    checkpoints += 1;
                    if checkpoints == 4 {
                        Err("deadline")
                    } else {
                        Ok(())
                    }
                }),
                Err("deadline")
            );
            assert_eq!(checkpoints, 4);
        }
    }

    #[test]
    fn checked_comparison_keeps_identity_and_equality_length_shortcuts() {
        for value in [
            dag(18, core::convert::identity),
            object(dag(18, core::convert::identity)),
            set(dag(18, core::convert::identity)),
            Value::String(Rc::from("x".repeat(2048))),
        ] {
            let alias = value.clone();
            for equality in [false, true] {
                let mut checkpoints = 0;
                assert_eq!(
                    compare_checked(&value, &alias, equality, &mut || {
                        checkpoints += 1;
                        Ok::<(), Infallible>(())
                    }),
                    Ok(Ordering::Equal)
                );
                assert_eq!(checkpoints, 1);
                assert_eq!(
                    compare_checked(&value, &alias, equality, &mut || Err("deadline")),
                    Err("deadline")
                );
            }
        }
        for (left, right) in [
            (Value::new_array(), Value::from(vec![Value::Null])),
            (Value::new_object(), object(Value::Null)),
            (Value::new_set(), set(Value::Null)),
            (Value::from(""), Value::from("x")),
        ] {
            let mut checkpoints = 0;
            assert_eq!(
                compare_checked(&left, &right, true, &mut || {
                    checkpoints += 1;
                    Ok::<(), Infallible>(())
                }),
                Ok(Ordering::Less)
            );
            assert_eq!(checkpoints, 1);
        }
    }

    #[test]
    fn checked_comparison_visits_ordinary_trees_linearly_with_aliased_roots() -> anyhow::Result<()>
    {
        for width in [1, 8, 64] {
            let json = alloc::format!("[{}]", vec!["[null]"; width].join(","));
            for wrap in [core::convert::identity, object, set] {
                let left = wrap(Value::from_json_str(&json)?);
                let right = wrap(Value::from_json_str(&json)?);
                let owners = (left.clone(), right.clone());
                for equality in [false, true] {
                    let mut checkpoints = 0;
                    assert_eq!(
                        compare_checked(&left, &right, equality, &mut || {
                            checkpoints += 1;
                            Ok::<(), Infallible>(())
                        }),
                        Ok(Ordering::Equal)
                    );
                    assert!(
                        checkpoints <= width.saturating_mul(8).saturating_add(12),
                        "width {width}, checkpoints {checkpoints}"
                    );
                }
                assert_eq!(owners.0, owners.1);
            }
        }
        Ok(())
    }

    fn program(instruction: Instruction) -> Arc<Program> {
        let mut program = Program::new();
        program.dispatch_window_size = 3;
        program.instructions = vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::LoadData { dest: 1 },
            instruction,
            Instruction::Return { value: 2 },
        ];
        Arc::new(program)
    }

    const fn comparisons() -> [(Instruction, Value); 7] {
        [
            (
                Instruction::Eq {
                    dest: 2,
                    left: 0,
                    right: 1,
                },
                Value::Bool(true),
            ),
            (
                Instruction::Ne {
                    dest: 2,
                    left: 0,
                    right: 1,
                },
                Value::Bool(false),
            ),
            (
                Instruction::Lt {
                    dest: 2,
                    left: 0,
                    right: 1,
                },
                Value::Bool(false),
            ),
            (
                Instruction::Le {
                    dest: 2,
                    left: 0,
                    right: 1,
                },
                Value::Bool(true),
            ),
            (
                Instruction::Gt {
                    dest: 2,
                    left: 0,
                    right: 1,
                },
                Value::Bool(false),
            ),
            (
                Instruction::Ge {
                    dest: 2,
                    left: 0,
                    right: 1,
                },
                Value::Bool(true),
            ),
            (
                Instruction::AssertEq { left: 0, right: 1 },
                Value::Undefined,
            ),
        ]
    }

    fn timer(limit: Duration) -> ExecutionTimerConfig {
        ExecutionTimerConfig {
            limit,
            // Four dispatched instructions alone cannot reach this checkpoint.
            check_interval: NonZeroU32::new(8).unwrap_or(NonZeroU32::MIN),
        }
    }

    #[test]
    fn comparison_instructions_expire_inside_one_opcode() -> Result<()> {
        let _guard = acquire_limits_test_lock();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for strict in [false, true] {
                for (instruction, _) in comparisons() {
                    let mut vm = RegoVM::new();
                    vm.load_program(program(instruction));
                    vm.set_execution_mode(mode);
                    vm.set_strict_builtin_errors(strict);
                    vm.set_input(Value::from(vec![Value::Null; 128]));
                    vm.set_data(Value::from(vec![Value::Null; 128]))?;
                    vm.set_execution_timer_config(Some(timer(Duration::ZERO)));
                    assert!(
                        matches!(vm.execute(), Err(VmError::TimeLimitExceeded { pc: 2, .. })),
                        "{mode:?} {strict} {instruction:?}"
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn membership_expires_during_scanning_and_nested_comparison() -> Result<()> {
        let _guard = acquire_limits_test_lock();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for object in [false, true] {
                for nested in [false, true] {
                    let (input, value) = if nested {
                        let input = Value::from(vec![Value::Null; 128]);
                        let input = if object {
                            Object::from_iter([(Value::from("key"), input)]).into()
                        } else {
                            Value::from(vec![input])
                        };
                        (input, Value::from(vec![Value::Null; 128]))
                    } else {
                        let input = if object {
                            Object::from_iter((0..128).map(|key| (Value::from(key), Value::Null)))
                                .into()
                        } else {
                            Value::from(vec![Value::Null; 128])
                        };
                        (input, Value::Bool(false))
                    };
                    let mut vm = RegoVM::new();
                    vm.load_program(program(Instruction::Contains {
                        dest: 2,
                        collection: 0,
                        value: 1,
                    }));
                    vm.set_execution_mode(mode);
                    vm.set_input(input);
                    vm.set_data(value)?;
                    vm.set_execution_timer_config(Some(timer(Duration::ZERO)));
                    assert!(matches!(
                        vm.execute(),
                        Err(VmError::TimeLimitExceeded { pc: 2, .. })
                    ));
                }
            }
        }
        Ok(())
    }

    #[test]
    fn checked_instructions_preserve_results_and_disabled_timer_path() -> Result<()> {
        let _guard = acquire_limits_test_lock();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for config in [None, Some(timer(Duration::from_secs(60)))] {
                for (instruction, expected) in comparisons() {
                    let mut vm = RegoVM::new();
                    vm.load_program(program(instruction));
                    vm.set_execution_mode(mode);
                    vm.set_execution_timer_config(config);
                    vm.set_max_instructions(4);
                    vm.set_input(Value::from(vec![Value::Null; 16]));
                    vm.set_data(Value::from(vec![Value::Null; 16]))?;
                    assert_eq!(vm.execute()?, expected, "{instruction:?}");
                    assert_eq!(vm.executed_instructions, 4);
                }
            }
        }
        Ok(())
    }

    #[test]
    fn checked_membership_preserves_native_results() -> Result<()> {
        let _guard = acquire_limits_test_lock();
        let needle = Value::from(vec![Value::Null]);
        let cases = [
            (Value::from(vec![needle.clone()]), needle.clone(), true),
            (
                Object::from_iter([(Value::from("key"), needle.clone())]).into(),
                needle.clone(),
                true,
            ),
            (Value::from(vec![Value::Null]), needle.clone(), false),
            (Value::new_object(), needle, false),
            (Value::Bool(true), Value::Bool(true), false),
            (Value::from(vec![Value::Undefined]), Value::Undefined, true),
        ];
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for config in [None, Some(timer(Duration::from_secs(60)))] {
                for &(ref input, ref value, expected) in &cases {
                    let mut vm = RegoVM::new();
                    vm.load_program(program(Instruction::Contains {
                        dest: 2,
                        collection: 0,
                        value: 1,
                    }));
                    vm.set_execution_mode(mode);
                    vm.set_execution_timer_config(config);
                    vm.set_input(input.clone());
                    vm.set_data(value.clone())?;
                    assert_eq!(vm.execute()?, Value::Bool(expected));
                }
            }
        }
        Ok(())
    }

    #[test]
    fn memory_only_scalar_membership_has_constant_checkpoint_work() -> anyhow::Result<()> {
        for width in [16, 1024, 16384] {
            let mut items = Set::from_iter((0..width).map(Value::from));
            items.extend([
                Value::Null,
                Value::Bool(true),
                Value::from("scalar"),
                Value::Undefined,
                dag(20, core::convert::identity),
                Value::new_set(),
                Value::new_object(),
            ]);
            let collection = items.into_value();
            for needle in [
                Value::Null,
                Value::Bool(false),
                Value::Bool(true),
                Value::from(width - 1),
                Value::from(width),
                Value::from(1.0_f64),
                Value::from(f64::NAN),
                Value::from_numeric_string("1234567890123456789012345678901234567890")?,
                Value::from("scalar"),
                Value::from("missing"),
                Value::Undefined,
            ] {
                let expected = collection.as_set()?.contains(&needle);
                let mut checkpoints = 0;
                let found = contains_checked(&collection, &needle, true, &mut || {
                    checkpoints += 1;
                    Ok::<(), Infallible>(())
                });
                assert_eq!(found, Ok(expected));
                assert_eq!(checkpoints, 2, "width={width}, needle={needle:?}");
                for fail_at in [1, 2] {
                    let mut failure_checkpoints = 0;
                    assert_eq!(
                        contains_checked(&collection, &needle, true, &mut || {
                            failure_checkpoints += 1;
                            if failure_checkpoints == fail_at {
                                Err("memory")
                            } else {
                                Ok(())
                            }
                        }),
                        Err("memory")
                    );
                    assert_eq!(failure_checkpoints, fail_at);
                }
            }
        }
        Ok(())
    }

    #[test]
    fn checked_set_membership_retains_string_and_compound_checkpoints() {
        for (collection, needle, memory_only) in [
            (
                Set::from_iter([Value::from("x".repeat(4096))]).into_value(),
                Value::from("x".repeat(4096)),
                false,
            ),
            (
                Set::from_iter([dag(8, core::convert::identity)]).into_value(),
                dag(8, core::convert::identity),
                false,
            ),
            (
                Set::from_iter([dag(8, core::convert::identity)]).into_value(),
                dag(8, core::convert::identity),
                true,
            ),
        ] {
            let mut checkpoints = 0;
            assert_eq!(
                contains_checked(&collection, &needle, memory_only, &mut || {
                    checkpoints += 1;
                    if checkpoints == 4 {
                        Err("resource")
                    } else {
                        Ok(())
                    }
                }),
                Err("resource")
            );
            assert_eq!(checkpoints, 4);
        }
    }

    #[test]
    fn checked_comparisons_keep_undefined_and_cross_type_ordering() -> Result<()> {
        let _guard = acquire_limits_test_lock();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for (instruction, _) in comparisons() {
                if matches!(instruction, Instruction::AssertEq { .. }) {
                    continue;
                }
                for strict in [false, true] {
                    let mut vm = RegoVM::new();
                    vm.load_program(program(instruction));
                    vm.set_execution_mode(mode);
                    vm.set_strict_builtin_errors(strict);
                    vm.set_execution_timer_config(Some(timer(Duration::from_secs(60))));
                    for (left, right) in [
                        (Value::Undefined, Value::Null),
                        (Value::Null, Value::Undefined),
                    ] {
                        vm.set_input(left);
                        vm.set_data(right)?;
                        assert_eq!(vm.execute()?, Value::Undefined);
                    }

                    for (left, right, less) in [
                        (Value::Bool(true), Value::Null, false),
                        (Value::Null, Value::Bool(true), true),
                        (Value::from("text"), Value::from(0), false),
                        (Value::from(0), Value::from("text"), true),
                    ] {
                        let expected = match instruction {
                            Instruction::Eq { .. } => false,
                            Instruction::Ne { .. } => true,
                            Instruction::Lt { .. } | Instruction::Le { .. } => less,
                            Instruction::Gt { .. } | Instruction::Ge { .. } => !less,
                            _ => continue,
                        };
                        vm.set_input(left);
                        vm.set_data(right)?;
                        assert_eq!(
                            vm.execute()?,
                            Value::Bool(expected),
                            "{mode:?}, strict={strict}: {instruction:?}"
                        );
                    }
                }
            }
        }
        Ok(())
    }
}

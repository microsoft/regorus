// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::cmp::Ordering;

use crate::{Rc, Value};

use super::errors::{Result, VmError};
use super::machine::RegoVM;

// Explicit reference patterns conflict with needless_borrowed_reference here.
#[allow(clippy::pattern_type_mismatch)]
fn compare_checked<E>(
    left: &Value,
    right: &Value,
    equality: bool,
    checkpoint: &mut impl FnMut() -> core::result::Result<(), E>,
) -> core::result::Result<Ordering, E> {
    checkpoint()?;
    match (left, right) {
        (Value::Array(a), Value::Array(b)) => {
            if equality {
                if Rc::ptr_eq(a, b) {
                    return Ok(Ordering::Equal);
                }
                if a.len() != b.len() {
                    return Ok(Ordering::Less);
                }
            }
            compare_sequence(a.iter(), b.iter(), equality, checkpoint)
        }
        (Value::Object(a), Value::Object(b)) => {
            if equality {
                if Rc::ptr_eq(a, b) {
                    return Ok(Ordering::Equal);
                }
                if a.len() != b.len() {
                    return Ok(Ordering::Less);
                }
            }
            compare_sequence(
                a.iter_sorted().flat_map(|(key, value)| [key, value]),
                b.iter_sorted().flat_map(|(key, value)| [key, value]),
                equality,
                checkpoint,
            )
        }
        (Value::Set(a), Value::Set(b)) => {
            if equality {
                if Rc::ptr_eq(a, b) {
                    return Ok(Ordering::Equal);
                }
                if a.len() != b.len() {
                    return Ok(Ordering::Less);
                }
            }
            compare_sequence(a.iter_sorted(), b.iter_sorted(), equality, checkpoint)
        }
        (Value::String(a), Value::String(b)) => {
            if equality {
                if Rc::ptr_eq(a, b) {
                    return Ok(Ordering::Equal);
                }
                if a.len() != b.len() {
                    return Ok(Ordering::Less);
                }
            }
            for (left_chunk, right_chunk) in a.as_bytes().chunks(256).zip(b.as_bytes().chunks(256))
            {
                checkpoint()?;
                let result = left_chunk.cmp(right_chunk);
                if !result.is_eq() {
                    return Ok(result);
                }
            }
            Ok(a.len().cmp(&b.len()))
        }
        // Less is only an internal unequal sentinel in equality mode.
        _ if equality => Ok(if left == right {
            Ordering::Equal
        } else {
            Ordering::Less
        }),
        _ => Ok(left.cmp(right)),
    }
}

fn compare_sequence<'a, 'b, E>(
    mut left: impl Iterator<Item = &'a Value>,
    mut right: impl Iterator<Item = &'b Value>,
    equality: bool,
    checkpoint: &mut impl FnMut() -> core::result::Result<(), E>,
) -> core::result::Result<Ordering, E> {
    loop {
        match (left.next(), right.next()) {
            (Some(a), Some(b)) => {
                let result = compare_checked(a, b, equality, checkpoint)?;
                if !result.is_eq() {
                    return Ok(result);
                }
            }
            (Some(_), None) => return Ok(Ordering::Greater),
            (None, Some(_)) => return Ok(Ordering::Less),
            (None, None) => return Ok(Ordering::Equal),
        }
    }
}

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

impl RegoVM {
    pub(super) fn compare_registers(
        &mut self,
        left: u8,
        right: u8,
        equality: bool,
    ) -> Result<Ordering> {
        if self.execution_timer.config().is_none() {
            let left = self.get_register(left)?;
            let right = self.get_register(right)?;
            return Ok(if equality {
                if left == right {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            } else {
                left.cmp(right)
            });
        }

        let pc = self.pc;
        let (left, right) = operands(&self.registers, pc, left, right)?;
        compare_checked(left, right, equality, &mut || {
            Self::tick_execution_timer(&mut self.execution_timer, pc, 1)
        })
    }

    pub(super) fn contains_registers(&mut self, collection: u8, value: u8) -> Result<bool> {
        if self.execution_timer.config().is_none() {
            let value = self.get_register(value)?;
            let collection = self.get_register(collection)?;
            return Ok(match *collection {
                Value::Set(ref items) => items.contains(value),
                Value::Array(ref items) => items.contains(value),
                Value::Object(ref items) => items.values().any(|item| item == value),
                _ => false,
            });
        }

        let pc = self.pc;
        let (value, collection) = operands(&self.registers, pc, value, collection)?;
        let mut equals = |item: &Value| {
            compare_checked(item, value, true, &mut || {
                Self::tick_execution_timer(&mut self.execution_timer, pc, 1)
            })
            .map(Ordering::is_eq)
        };
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
            // B-tree key comparisons remain infallible and do not use this path.
            Value::Set(ref items) => return Ok(items.contains(value)),
            _ => {}
        }
        Ok(false)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    #![allow(clippy::panic_in_result_fn)]

    use super::*;
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
    fn checked_equality_keeps_identity_and_length_shortcuts() {
        for value in [
            dag(8, core::convert::identity),
            object(dag(8, core::convert::identity)),
            set(dag(8, core::convert::identity)),
            Value::String(Rc::from("x".repeat(2048))),
        ] {
            let alias = value.clone();
            let mut checkpoints = 0;
            assert_eq!(
                compare_checked(&value, &alias, true, &mut || {
                    checkpoints += 1;
                    Ok::<(), Infallible>(())
                }),
                Ok(Ordering::Equal)
            );
            assert_eq!(checkpoints, 1);
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
                        checkpoints <= width.saturating_mul(2).saturating_add(4),
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
    fn checked_comparisons_keep_undefined_and_strict_type_errors() -> Result<()> {
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
                    vm.set_input(Value::Undefined);
                    vm.set_data(Value::Null)?;
                    assert_eq!(vm.execute()?, Value::Undefined);

                    vm.set_input(Value::Bool(true));
                    let result = vm.execute();
                    if strict
                        && !matches!(instruction, Instruction::Eq { .. } | Instruction::Ne { .. })
                    {
                        assert!(matches!(
                            result,
                            Err(VmError::ArithmeticError { pc: 2, .. })
                        ));
                    } else {
                        assert!(matches!(result?, Value::Bool(_)));
                    }
                }
            }
        }
        Ok(())
    }
}

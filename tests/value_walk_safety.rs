// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "std")]

use regorus::{Engine, Value};
use std::collections::{BTreeMap, BTreeSet};

mod native_depth_support;

fn nested(depth: usize, mut leaf: Value, kind: usize) -> Value {
    for _ in 0..depth {
        leaf = match kind {
            0 => Value::from(vec![leaf]),
            1 => Value::from(BTreeSet::from([leaf])),
            2 => Value::from(BTreeMap::from([(Value::from("k"), leaf)])),
            _ => Value::from(BTreeMap::from([(leaf, Value::Null)])),
        };
    }
    leaf
}

fn walks() {
    for kind in 0..4 {
        let a = nested(4096, Value::Null, kind);
        let b = nested(4096, Value::Null, kind);
        let c = nested(4096, Value::Bool(true), kind);
        assert!(a == b);
        assert!(a < c);
        assert!(c > b);
        assert!(a.cmp(&a).is_eq());
        assert!(!format!("{a:?}").is_empty());

        let mut engine = Engine::new();
        engine.set_input(Value::from(BTreeMap::from([
            (Value::from("a"), a),
            (Value::from("b"), b),
            (Value::from("c"), c),
        ])));
        assert!(engine
            .eval_bool_query("input.a == input.b".into(), false)
            .unwrap());
        assert!(engine
            .eval_bool_query("input.a < input.c".into(), false)
            .unwrap());
        engine.set_strict_builtin_errors(true);
        let error = engine
            .eval_query("upper(input.a)".into(), false)
            .unwrap_err()
            .to_string();
        assert!(error.len() < 1024, "{error}");
        assert!(error.contains("expects string argument"), "{error}");
        assert!(engine.eval_bool_query("true".into(), false).unwrap());
    }

    fn equality_shortcuts() {
        use regorus::value::{Array, Object, Set};

        fn dag() -> Value {
            (0..40).fold(Value::Null, |child, _| {
                Value::from(vec![child.clone(), child])
            })
        }

        // Distinct compact DAGs have exponentially large logical prefixes.
        // A nested length mismatch must reject them before expanding those prefixes.
        for kind in 0..3 {
            let (left, right) = match kind {
                0 => (
                    Value::from(vec![dag()]),
                    Value::from(vec![dag(), Value::Null]),
                ),
                1 => (
                    Set::from_iter([dag()]).into_value(),
                    Set::from_iter([dag(), Value::Undefined]).into_value(),
                ),
                _ => (
                    Object::from_iter([(Value::from("a"), dag())]).into(),
                    Object::from_iter([(Value::from("a"), dag()), (Value::from("b"), Value::Null)])
                        .into(),
                ),
            };
            let array_left = Array::from_iter([left.clone()]);
            let array_right = Array::from_iter([right.clone()]);
            assert!(array_left != array_right);
            assert!(PartialEq::eq(&array_left, &array_left));
            let set_left = Set::from_iter([left.clone()]);
            let set_right = Set::from_iter([right.clone()]);
            assert!(set_left != set_right);
            assert!(PartialEq::eq(&set_left, &set_left));
            let mut object_left = Object::new();
            object_left.insert(Value::from("k"), left.clone());
            let object_right = Object::from_iter([(Value::from("k"), right.clone())]);
            assert!(object_left != object_right);
            assert!(PartialEq::eq(&object_left, &object_left));
            assert!(&object_left == object_left.clone().into_value().as_object().unwrap());
            for (left, right) in [
                (left, right),
                (array_left.into_value(), array_right.into_value()),
                (set_left.into_value(), set_right.into_value()),
                (object_left.into(), object_right.into()),
            ] {
                assert!(left == left.clone());
                assert!(left != right);
                let mut engine = Engine::new();
                engine.set_input(left.clone());
                engine
                    .add_data(Value::from(BTreeMap::from([(
                        Value::from("other"),
                        right.clone(),
                    )])))
                    .unwrap();
                assert!(!engine
                    .eval_bool_query("input == data.other".into(), false)
                    .unwrap());
                assert!(engine
                    .eval_bool_query("input != data.other".into(), false)
                    .unwrap());

                #[cfg(feature = "rvm")]
                {
                    use regorus::rvm::vm::ExecutionMode;
                    use regorus::rvm::{Instruction, Program, RegoVM};
                    use std::sync::Arc;
                    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                        for strict in [false, true] {
                            for instruction in [
                                Instruction::Eq {
                                    dest: 2,
                                    left: 0,
                                    right: 1,
                                },
                                Instruction::Ne {
                                    dest: 2,
                                    left: 0,
                                    right: 1,
                                },
                                Instruction::AssertEq { left: 0, right: 1 },
                            ] {
                                let mut program = Program::new();
                                program.dispatch_window_size = 3;
                                program.instructions = vec![
                                    Instruction::LoadInput { dest: 0 },
                                    Instruction::LoadData { dest: 1 },
                                    instruction,
                                    Instruction::Return { value: 2 },
                                ];
                                let mut vm = RegoVM::new();
                                vm.load_program(Arc::new(program));
                                vm.set_execution_mode(mode);
                                vm.set_strict_builtin_errors(strict);
                                vm.set_input(left.clone());
                                vm.set_data(right.clone()).unwrap();
                                let result = vm.execute();
                                match instruction {
                                    Instruction::AssertEq { .. } => assert!(result.is_err()),
                                    Instruction::Eq { .. } => {
                                        assert_eq!(result.unwrap(), Value::Bool(false))
                                    }
                                    _ => assert_eq!(result.unwrap(), Value::Bool(true)),
                                }
                                vm.set_data(left.clone()).unwrap();
                                let expected = match instruction {
                                    Instruction::Eq { .. } => Value::Bool(true),
                                    Instruction::Ne { .. } => Value::Bool(false),
                                    _ => Value::Undefined,
                                };
                                assert_eq!(vm.execute().unwrap(), expected);
                            }
                        }
                    }
                }
            }
        }
        let left = Value::from(vec![Value::from(2)]);
        let right = Value::from(vec![Value::from(1), Value::from(2)]);
        assert!(left != right);
        assert!(left > right);
    }

    equality_shortcuts();

    for kind in 0..3 {
        let value = nested(512, Value::Null, kind);
        let compact = format!("{value}");
        let (prefix, suffix) = if kind == 2 {
            ("{\"k\":", "}")
        } else {
            ("[", "]")
        };
        assert_eq!(
            compact,
            format!("{}null{}", prefix.repeat(512), suffix.repeat(512))
        );
        assert_eq!(
            value.to_json_str().unwrap().replace([' ', '\n'], ""),
            compact
        );
        let key = Value::from(BTreeMap::from([(value, Value::Bool(true))]));
        let expected = format!("{{{}:true}}", serde_json::to_string(&compact).unwrap());
        assert_eq!(format!("{key}"), expected);
        assert_eq!(serde_json::to_string(&key).unwrap(), expected);
    }

    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(true);
    engine.set_input(Value::from("x".repeat(1_000_000)));
    let error = engine
        .eval_query("abs(input)".into(), false)
        .unwrap_err()
        .to_string();
    assert!(error.len() < 1024);
    assert!(error.contains("String(bytes=1000000)"));
    engine.set_input(Value::from_numeric_string(&"9".repeat(10_000)).unwrap());
    let error = engine
        .eval_query("upper(input)".into(), false)
        .unwrap_err()
        .to_string();
    assert!(error.len() < 1024);
    assert!(error.contains("Got `Number`"));
}

#[cfg(feature = "rvm")]
fn vm_walks() {
    use regorus::rvm::vm::{ExecutionMode, ExecutionState, VmError};
    use regorus::rvm::{Instruction, Program, RegoVM};
    use regorus::utils::limits::ExecutionTimerConfig;
    use std::num::NonZeroU32;
    use std::sync::Arc;
    use std::time::Duration;

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

    let operations = [
        (
            Instruction::Eq {
                dest: 2,
                left: 0,
                right: 1,
            },
            true,
        ),
        (
            Instruction::Ne {
                dest: 2,
                left: 0,
                right: 1,
            },
            false,
        ),
        (
            Instruction::Lt {
                dest: 2,
                left: 0,
                right: 1,
            },
            false,
        ),
        (
            Instruction::Le {
                dest: 2,
                left: 0,
                right: 1,
            },
            true,
        ),
        (
            Instruction::Gt {
                dest: 2,
                left: 0,
                right: 1,
            },
            false,
        ),
        (
            Instruction::Ge {
                dest: 2,
                left: 0,
                right: 1,
            },
            true,
        ),
    ];
    let timer = |limit| {
        Some(ExecutionTimerConfig {
            limit,
            // The four instructions cannot reach this checkpoint without traversal.
            check_interval: NonZeroU32::new(8).unwrap(),
        })
    };
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for kind in 0..4 {
            for (instruction, equal_result) in operations {
                for strict in [false, true] {
                    let mut vm = RegoVM::new();
                    vm.load_program(program(instruction));
                    vm.set_execution_mode(mode);
                    vm.set_strict_builtin_errors(strict);
                    vm.set_input(nested(2048, Value::Null, kind));
                    vm.set_data(nested(2048, Value::Null, kind)).unwrap();
                    for config in [None, timer(Duration::from_secs(60))] {
                        vm.set_execution_timer_config(config);
                        assert_eq!(vm.execute().unwrap(), Value::Bool(equal_result));
                    }
                    vm.set_execution_timer_config(timer(Duration::ZERO));
                    assert!(matches!(
                        vm.execute(),
                        Err(VmError::TimeLimitExceeded { pc: 2, .. })
                    ));
                    vm.set_execution_timer_config(None);
                    assert_eq!(vm.execute().unwrap(), Value::Bool(equal_result));
                }
            }
        }

        // Aliased ordering checkpoints before taking its constant-time shortcut.
        let alias = nested(4096, Value::Null, 0);
        let mut vm = RegoVM::new();
        vm.load_program(program(Instruction::Lt {
            dest: 2,
            left: 0,
            right: 1,
        }));
        vm.set_execution_mode(mode);
        vm.set_input(alias.clone());
        vm.set_data(alias).unwrap();
        vm.set_execution_timer_config(timer(Duration::ZERO));
        assert_eq!(vm.execute().unwrap(), Value::Bool(false));

        for kind in 0..3 {
            let needle = nested(4096, Value::Null, 0);
            let haystack = match kind {
                0 => Value::from(vec![needle]),
                1 => Value::from(BTreeSet::from([needle])),
                _ => Value::from(BTreeMap::from([(Value::from("key"), needle)])),
            };
            vm.load_program(program(Instruction::Contains {
                dest: 2,
                collection: 0,
                value: 1,
            }));
            vm.set_input(haystack);
            vm.set_data(nested(4096, Value::Null, 0)).unwrap();
            vm.set_execution_timer_config(timer(Duration::ZERO));
            assert!(matches!(
                vm.execute(),
                Err(VmError::TimeLimitExceeded { pc: 2, .. })
            ));
            vm.set_execution_timer_config(timer(Duration::from_secs(60)));
            assert_eq!(vm.execute().unwrap(), Value::Bool(true));
        }

        vm.load_program(program(Instruction::Lt {
            dest: 2,
            left: 0,
            right: 1,
        }));
        vm.set_input(nested(8192, Value::Null, 0));
        vm.set_data(Value::from(1)).unwrap();
        vm.set_strict_builtin_errors(true);
        vm.set_execution_timer_config(None);
        let error = vm.execute().unwrap_err().to_string();
        assert!(error.contains("left=Array(len=1), right=Number"), "{error}");
        assert!(error.len() < 256);
        vm.set_input(Value::from(0));
        assert_eq!(vm.execute().unwrap(), Value::Bool(true));

        let mut echo = Program::new();
        echo.instructions = vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::Return { value: 0 },
        ];
        vm.load_program(Arc::new(echo));
        let input = nested(512, Value::Null, 0);
        let expected = input.to_json_str().unwrap();
        vm.set_input(input);
        assert_eq!(
            format!("{}", vm.execute().unwrap()),
            format!("{}null{}", "[".repeat(512), "]".repeat(512))
        );
        assert_eq!(
            vm.execute_to_c_string_for_ffi().unwrap().to_str().unwrap(),
            expected
        );
    }

    for instruction in operations.into_iter().map(|(op, _)| op).chain([
        Instruction::AssertEq { left: 0, right: 1 },
        Instruction::Contains {
            dest: 2,
            collection: 0,
            value: 1,
        },
    ]) {
        let sentinel: regorus::Rc<str> = regorus::Rc::from("resumed-comparison");
        let mut vm = RegoVM::new();
        vm.load_program(program(instruction));
        vm.set_execution_mode(ExecutionMode::Suspendable);
        let input = nested(2048, Value::String(sentinel.clone()), 0);
        vm.set_input(if matches!(instruction, Instruction::Contains { .. }) {
            Value::from(vec![input])
        } else {
            input
        });
        vm.set_data(nested(2048, Value::String(sentinel.clone()), 0))
            .unwrap();
        vm.set_execution_timer_config(timer(Duration::ZERO));
        vm.set_step_mode(true);
        vm.execute().unwrap();
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Suspended { .. }
        ));
        vm.set_step_mode(false);
        assert!(matches!(
            vm.resume(None),
            Err(VmError::TimeLimitExceeded { pc: 2, .. })
        ));
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Error {
                error: VmError::TimeLimitExceeded { pc: 2, .. }
            }
        ));
        assert!(vm.get_registers().is_empty());
        assert!(vm.get_call_stack().is_empty());
        vm.set_input(Value::Null);
        vm.set_data(Value::Null).unwrap();
        assert_eq!(regorus::Rc::strong_count(&sentinel), 1);
        vm.set_execution_timer_config(None);
        assert!(vm.execute().is_ok());
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn value_walks_on_exact_1_mib_stack() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess("value_walks_on_exact_1_mib_stack");
        return;
    }

    std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(|| {
            walks();
            #[cfg(feature = "rvm")]
            vm_walks();
            // A healthy operation after every deep tree has been released.
            assert_eq!(Value::from(vec![Value::Null]).to_string(), "[null]");
        })
        .unwrap()
        .join()
        .unwrap();
}

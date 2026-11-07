// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "std")]

use regorus::{Engine, Value};

mod native_depth_support;

fn on_execution_stack(test_name: &str, check: fn()) {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess(test_name);
        return;
    }
    std::thread::Builder::new()
        .stack_size(1_500_000)
        .spawn(check)
        .unwrap()
        .join()
        .unwrap();
}

fn dependencies(count: usize, functions: bool) -> String {
    let mut policy = String::new();
    for index in 0..count {
        let head = if functions {
            format!("f{index}(x)")
        } else {
            format!("r{index}")
        };
        let value = if index + 1 == count {
            if functions { "[x]" } else { "42" }.to_owned()
        } else if functions {
            format!("f{}(x)", index + 1)
        } else {
            format!("r{}", index + 1)
        };
        policy.push_str(&format!("{head} := {value}\n"));
    }
    policy
}

fn check_interpreter(policy: &str, input: Value, rule: &str, expected: Value) -> Engine {
    let mut engine = Engine::new();
    engine
        .add_policy("continuations.rego".into(), policy.into())
        .unwrap();
    engine.set_input(input.clone());
    for _ in 0..2 {
        assert_eq!(engine.eval_rule(rule.into()).unwrap(), expected, "{rule}");
    }
    engine
}

fn check_backends(policy: &str, input: Value, rule: &str, expected: Value) {
    let mut engine = check_interpreter(policy, input.clone(), rule, expected.clone());
    #[cfg(feature = "rvm")]
    {
        use regorus::languages::rego::compiler::Compiler;
        use regorus::rvm::vm::{ExecutionMode, RegoVM};
        use regorus::Rc;
        let compiled = engine.compile_with_entrypoint(&Rc::from(rule)).unwrap();
        let program = Compiler::compile_from_policy(&compiled, &[rule]).unwrap();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_input(input.clone());
            for _ in 0..2 {
                assert_eq!(
                    vm.execute_entry_point_by_name(rule).unwrap(),
                    expected,
                    "{rule}: {mode:?}"
                );
            }
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn function_value_replacement_preserves_limit_errors() {
    on_execution_stack("function_value_replacement_preserves_limit_errors", || {
        for failure in ["native", "serialization", "builtin-depth"] {
            for negated in [false, true] {
                let replacement = match failure {
                    "serialization" => "bad",
                    "builtin-depth" => "bad_json",
                    _ => "r0",
                };
                let branch = if negated {
                    "allow if { not denied }"
                } else {
                    "allow if { denied }"
                };
                let mut engine = Engine::new();
                engine
                    .add_policy(
                        "with-value.rego".into(),
                        format!(
                            "package probe\n\
                             default allow := false\n\
                             f(x) := x\n\
                             denied if {{ f(0) with f as {replacement} }}\n\
                             {branch}\n\
                             bad := json.marshal(input.deep)\n\
                             bad_json := json.unmarshal(input.text)\n\
                             safe := input.allow\n{}",
                            dependencies(24, false)
                        ),
                    )
                    .unwrap();
                let nested = (0..65).fold(Value::Null, |v, _| Value::from(vec![v]));
                let mut input = Value::new_object();
                input.as_object_mut().unwrap().insert("deep".into(), nested);
                input
                    .as_object_mut()
                    .unwrap()
                    .insert("allow".into(), false.into());
                input.as_object_mut().unwrap().insert(
                    "text".into(),
                    format!("{}null{}", "[".repeat(257), "]".repeat(257)).into(),
                );
                engine.set_input(input);
                for strict in [false, true] {
                    engine.set_strict_builtin_errors(strict);
                    for _ in 0..2 {
                        let error = engine.eval_rule("data.probe.allow".into()).unwrap_err();
                        assert!(
                            error.to_string().contains("native evaluation nesting")
                                || format!("{error:#}").contains("nesting limit")
                                || matches!(
                                    error.downcast_ref::<regorus::LimitError>(),
                                    Some(regorus::LimitError::SerializationDepthExceeded { .. })
                                ),
                            "{error:#}"
                        );
                        assert_eq!(
                            engine.eval_rule("data.probe.safe".into()).unwrap(),
                            Value::Bool(false)
                        );
                    }
                }
            }
        }
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn failed_hoisted_collection_restores_with_state() {
    on_execution_stack("failed_hoisted_collection_restores_with_state", || {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "collection.rego".into(),
                format!(
                    "package probe\n\
                     fail if {{ f0(0)[_] with input as {{\"allow\": true}} }}\n\
                     nested_fail if {{\n\
                       some x in [0] with input.allow as true with data.settings.flag as true with g as true\n\
                       f0(0)[_] with input as {{\"allow\": true}} with data.settings.flag as false with g as false\n\
                     }}\n\
                     g(x) := false\n\
                     safe := input.allow\n\
                     saved := [input.allow, data.settings.flag, g(0)]\n{}",
                    dependencies(24, true)
                ),
            )
            .unwrap();
        engine.set_input_json(r#"{"allow":false}"#).unwrap();
        engine
            .add_data(Value::from_json_str(r#"{"settings":{"flag":false}}"#).unwrap())
            .unwrap();
        for rule in ["data.probe.fail", "data.probe.nested_fail"] {
            for _ in 0..2 {
                let error = engine.eval_rule(rule.into()).unwrap_err();
                assert!(
                    error.to_string().contains("native evaluation nesting"),
                    "{error}"
                );
                assert_eq!(
                    engine.eval_rule("data.probe.safe".into()).unwrap(),
                    Value::Bool(false)
                );
                assert_eq!(
                    engine.eval_rule("data.probe.saved".into()).unwrap(),
                    Value::from(vec![Value::Bool(false); 3])
                );
            }
        }
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn default_failure_preserves_fatal_error_and_active_frames() {
    on_execution_stack(
        "default_failure_preserves_fatal_error_and_active_frames",
        || {
            let nested = |count: usize, value: &str| {
                format!("{}{value}{}", "[".repeat(count), "]".repeat(count))
            };
            let mut engine = Engine::new();
            engine
            .add_policy(
                "default-cleanup.rego".into(),
                format!(
                    "package probe\n\
                     default d := {}\n\
                     deny(x) := true if {{ some y in [0]; {} }}\n\
                     deny(x) := false\n\
                     allow if {{ not deny(0) }}\n\
                     f(x) := x\n\
                     wrapped if {{\n\
                       some outer in [0] with input.flag as true with data.settings.flag as true with f as 7\n\
                       some inner in [0] with input.flag as false with f as 9\n\
                       allow\n\
                     }}\n\
                     safe := [input.flag, data.settings.flag, f(3)]\n",
                    nested(31, "0"),
                    nested(29, "[d,y]"),
                ),
            )
            .unwrap();
            engine.set_strict_builtin_errors(false);
            engine.set_input_json(r#"{"flag":false}"#).unwrap();
            engine
                .add_data(Value::from_json_str(r#"{"settings":{"flag":false}}"#).unwrap())
                .unwrap();
            for rule in ["data.probe.allow", "data.probe.wrapped"] {
                for _ in 0..2 {
                    let error = engine.eval_rule(rule.into()).unwrap_err();
                    assert!(
                        error.to_string().contains("native evaluation nesting"),
                        "expected original fatal nesting error, got {error:#}"
                    );
                    assert_eq!(
                        engine.eval_rule("data.probe.safe".into()).unwrap(),
                        Value::from(vec![false.into(), false.into(), 3.into()])
                    );
                }
            }
        },
    );
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn wide_statement_continuations() {
    on_execution_stack("wide_statement_continuations", || {
        for statements in [
            vec!["input.items[_] == 0"; 128].join(";\n"),
            (0..128)
                .map(|index| format!("some x{index} in [0]"))
                .collect::<Vec<_>>()
                .join(";\n"),
        ] {
            let mut engine = Engine::new();
            engine.set_input_json(r#"{"items":[0]}"#).unwrap();
            engine
                .add_policy(
                    "wide.rego".into(),
                    format!(
                        "package probe\nr := 42 if {{ {statements}; count(f0(0)) == 1 }}\n{}",
                        dependencies(8, true)
                    ),
                )
                .unwrap();
            assert_eq!(
                engine.eval_rule("data.probe.r".into()).unwrap(),
                Value::from(42)
            );
        }
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn wide_bodies_with_helpers_on_both_backends() {
    on_execution_stack("wide_bodies_with_helpers_on_both_backends", || {
        // The RVM's independent u8 register window still bounds compilable body
        // width. These bodies fit; width plus moderate helper nesting formerly
        // exhausted the interpreter's shared native budget.
        for statements in [
            vec!["input.items[_] == 0"; 24].join(";\n"),
            (0..40)
                .map(|index| format!("some x{index} in [0]"))
                .collect::<Vec<_>>()
                .join(";\n"),
        ] {
            check_backends(
                &format!(
                    "package probe\nr := 42 if {{ {statements}; count(f0(0)) == 1 }}\n{}",
                    dependencies(8, true)
                ),
                Value::from_json_str(r#"{"items":[0]}"#).unwrap(),
                "data.probe.r",
                Value::from(42),
            );
        }
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn continuation_backtracking_semantics() {
    on_execution_stack("continuation_backtracking_semantics", || {
        let policy = r#"package probe
            combinations := [[a, k, b, c] |
                some [a, unused] in [[0, 9], [1, 8], [2, 7]]
                a != 1
                some k, b in {"x": 0, "y": 1}
                c := input.items[_]
                c > b
                not input.missing
            ]
            shared_index := [i |
                input.items[i] == input.other[i]
            ]
            set_pairs := {[a, b] |
                some a in {1, 2}
                some b in {3, 4}
                b > a
            }
            default absent_not_false := false
            absent_not_false if { input.missing != false }
            default negative := false
            negative if { not input.flag }
            early := 42 if { some x in [0, "bad"]; x + 1 > 0 }
            every_ok if { some x in [0, 1]; every y in [1, 2] { y > x } }
            empty := [x | some x in []]
            default none := 7
            none := 42 if { some x in input.missing }
        "#;
        let input =
            Value::from_json_str(r#"{"items":[0,1,2],"other":[0,9,2],"flag":false}"#).unwrap();
        for (rule, expected) in [
            (
                "combinations",
                r#"[[0,"x",0,1],[0,"x",0,2],[0,"y",1,2],[2,"x",0,1],[2,"x",0,2],[2,"y",1,2]]"#,
            ),
            ("shared_index", "[0,2]"),
            ("set_pairs", "[[1,3],[1,4],[2,3],[2,4]]"),
            ("absent_not_false", "false"),
            ("negative", "true"),
            ("every_ok", "true"),
            ("empty", "[]"),
            ("none", "7"),
        ] {
            let mut expected = Value::from_json_str(expected).unwrap();
            if rule == "set_pairs" {
                let mut set = Value::new_set();
                set.as_set_mut()
                    .unwrap()
                    .extend(expected.as_array().unwrap().iter().cloned());
                expected = set;
            }
            check_backends(
                policy,
                input.clone(),
                &format!("data.probe.{rule}"),
                expected,
            );
        }
        // The interpreter retains its constant-output early-return optimization.
        // The RVM does not promise to skip later builtin type errors this way.
        check_interpreter(policy, input, "data.probe.early", Value::from(42));
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn continuation_with_lifetimes() {
    on_execution_stack("continuation_with_lifetimes", || {
        let policy = r#"package probe
            f(x) := x
            hoisted := [input.flag |
                input.items[_] == 1 with input.items as [1, 1]
                f(false) == false
            ]
            some_override := [input.flag |
                some x in [0, 1] with input.flag as true
                input.flag
            ]
            restored := [input.flag |
                some x in [0, 1]
                f(1) == 2 with f as 2 with input.flag as true
                not input.flag
            ]
            nested := [[input.flag, y] |
                some x in [0, 1] with input.flag as true
                some y in [2, 3] with input.flag as false
                not input.flag
            ]
        "#;
        let input = Value::from_json_str(r#"{"flag":false,"items":[0]}"#).unwrap();
        for (rule, expected) in [
            ("hoisted", "[false,false]"),
            ("some_override", "[true,true]"),
            ("restored", "[false,false]"),
            ("nested", "[[false,2],[false,3],[false,2],[false,3]]"),
        ] {
            // WITH is currently unsupported by the RVM compiler.
            check_interpreter(
                policy,
                input.clone(),
                &format!("data.probe.{rule}"),
                Value::from_json_str(expected).unwrap(),
            );
        }
    });
}

#[test]
fn hoisted_walk_backtracking() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "walk.rego".into(),
            r#"package probe
                r := [[path, value, x] |
                    walk(input, [path, value])
                    is_number(value)
                    some x in [0, 1]
                    x < value
                ]
            "#
            .into(),
        )
        .unwrap();
    engine.set_input_json(r#"{"a":[1,2]}"#).unwrap();
    assert_eq!(
        engine.eval_rule("data.probe.r".into()).unwrap(),
        Value::from_json_str(r#"[[["a",0],1,0],[["a",1],2,0],[["a",1],2,1]]"#).unwrap()
    );
}

#[test]
#[cfg(feature = "arc")]
#[cfg_attr(miri, ignore = "large independent shared-DAG fixture")]
fn structural_key_continuations_use_shallow_snapshots() {
    use regorus::utils::limits::ExecutionTimerConfig;
    use regorus::Rc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::{Duration, Instant};

    fn dag(depth: usize) -> Value {
        (0..depth).fold(Value::Null, |v, _| Value::from(vec![v.clone(), v]))
    }

    // Constructing ordered collections itself compares the independent equal
    // prefixes. Keep that cost outside evaluation and its timer. The optimized
    // regression exercises depth 28; the debug fixture remains cheap while the
    // snapshot ownership assertion below is deterministic at either depth.
    let depth = if cfg!(debug_assertions) { 12 } else { 28 };
    let setup = Instant::now();
    let left = dag(depth);
    let right = dag(depth);
    let (Value::Array(a), Value::Array(b)) = (&left, &right) else {
        panic!("DAG roots must be arrays");
    };
    assert!(!Rc::ptr_eq(a, b), "prefix roots must be independent");
    let (Value::Array(a0), Value::Array(a1)) = (&a[0], &a[1]) else {
        panic!("DAG children must be arrays");
    };
    assert!(
        Rc::ptr_eq(a0, a1),
        "each binary DAG must share its children"
    );
    let keys = [
        Value::from(vec![left, 0.into()]),
        Value::from(vec![right, 1.into()]),
    ];
    let mut object = Value::new_object();
    let mut set = Value::new_set();
    for (index, key) in keys.iter().enumerate() {
        object
            .as_object_mut()
            .unwrap()
            .insert(key.clone(), Value::from(index));
        set.as_set_mut().unwrap().insert(key.clone());
    }
    eprintln!(
        "structural-key fixture depth={depth}, setup={:?}",
        setup.elapsed()
    );

    for input in [object, set] {
        for body in ["some k, v in input", "v := input[_]"] {
            let mut engine = Engine::new();
            engine.set_strict_builtin_errors(true);
            engine.set_input(input.clone());
            engine
                .add_policy(
                    "structural-keys.rego".into(),
                    format!(
                        "package probe\nsafe := 7\n\
                         result := count([v | {body}; snapshot_observer()])"
                    ),
                )
                .unwrap();
            let Value::Array(last_key) = keys[1].clone() else {
                panic!("key must be an array");
            };
            let baseline = Rc::strong_count(&last_key);
            let calls = std::sync::Arc::new(AtomicUsize::new(0));
            let observed_calls = calls.clone();
            engine
                .add_extension(
                    "snapshot_observer".into(),
                    0,
                    Box::new(move |_| {
                        if observed_calls.fetch_add(1, Ordering::SeqCst) == 0 {
                            assert_eq!(
                                Rc::strong_count(&last_key),
                                baseline + 1,
                                "the unvisited last key must have one shallow snapshot owner"
                            );
                        }
                        Ok(Value::Bool(true))
                    }),
                )
                .unwrap();
            assert_eq!(
                engine.eval_rule("data.probe.safe".into()).unwrap(),
                7.into()
            );
            engine.set_execution_timer_config(ExecutionTimerConfig {
                limit: Duration::from_secs(1),
                check_interval: std::num::NonZeroU32::new(1).unwrap(),
            });
            assert_eq!(
                engine.eval_rule("data.probe.result".into()).unwrap(),
                2.into(),
                "{body}"
            );
            assert_eq!(calls.load(Ordering::SeqCst), 2, "{body}");
            assert_eq!(
                engine.eval_rule("data.probe.safe".into()).unwrap(),
                7.into()
            );
        }
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(feature = "std")]

use regorus::{Engine, LimitError, Value};

#[cfg(feature = "rvm")]
use regorus::{
    languages::rego::compiler::Compiler,
    rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError},
    Rc,
};

mod native_depth_support;

struct NestedInput {
    input: Value,
    owners: Vec<Value>,
}

impl NestedInput {
    fn new(depth: usize, right_leaf: i32) -> Self {
        Self::from_leaves(depth, Value::from(1), Value::from(right_leaf))
    }

    fn from_leaves(depth: usize, mut left: Value, mut right: Value) -> Self {
        let mut owners = Vec::new();
        for _ in 0..depth {
            for value in [&mut left, &mut right] {
                let mut parent = Value::new_object();
                parent
                    .as_object_mut()
                    .unwrap()
                    .insert(Value::from("a"), value.clone());
                *value = parent;
                owners.push(value.clone());
            }
        }
        if depth > 0 {
            for value in [&mut left, &mut right] {
                value.as_object_mut().unwrap().insert(
                    Value::from("0"),
                    Value::from_json_str(r#"{"done":1}"#).unwrap(),
                );
            }
        }
        let mut input = Value::new_object();
        input
            .as_object_mut()
            .unwrap()
            .insert(Value::from("left"), left);
        input
            .as_object_mut()
            .unwrap()
            .insert(Value::from("right"), right);
        Self { input, owners }
    }

    fn leaf(&self, side: &str, depth: usize) -> &Value {
        let mut value = self
            .input
            .as_object()
            .unwrap()
            .get(&Value::from(side))
            .unwrap();
        for _ in 0..depth {
            value = value.as_object().unwrap().get(&Value::from("a")).unwrap();
        }
        value
    }
}

impl Drop for NestedInput {
    fn drop(&mut self) {
        self.input = Value::Null;
        // Keep child owners alive while releasing each parent, independently of Value Drop.
        while self.owners.pop().is_some() {}
    }
}

fn module(expression: &str) -> String {
    let arguments = expression
        .replace("input.left", "a")
        .replace("input.right", "b");
    let mut source = format!(
        "package probe\nimport rego.v1\n\
         safe := 7\n\
         result := {expression}\n\
         negated if {{ not {expression} }}\n\
         default fallback := true\n\
         fallback := {expression}\n\
         wrapped := f(input.left, input.right)\n\
         f(a, b) := {arguments}\n\
         alternatives := h(input.left, input.right)\n\
         h(a, b) := {arguments}\n\
         h(a, b) := 7\n\
         reverse := reverse_h(input.left, input.right)\n\
         reverse_h(a, b) := 7\n\
         reverse_h(a, b) := {arguments}\n\
         wrapped_negated if {{ not f(input.left, input.right) }}\n\
         default default_h(a, b) := 7\n\
         default_h(a, b) := {arguments}\n\
         default_wrapped := default_h(input.left, input.right)\n\
         partial contains value if {{ value := {expression} }}\n\
         branch := value if {{ value := {expression} }} else := 7\n\
         safe_function := safe_f(0, 0)\n\
         safe_f(a, b) := 7\n\
         chain := f0(input.left, input.right)\n"
    );
    // Fifteen function frames plus the entry rule exercise the native rule-depth ceiling.
    for index in 0..14 {
        source.push_str(&format!("f{index}(a, b) := f{}(a, b)\n", index + 1));
    }
    source.push_str(&format!("f14(a, b) := {arguments}\n"));
    source
}

fn check_deep(depth: usize) {
    for expression in [
        "object.subset(input.left, input.right)",
        "object.union(input.left, input.right)",
        "object.union_n([{}, input.left, {}, input.right])",
    ] {
        let builtin = expression.split('(').next().unwrap();
        let right_leaf = if expression.starts_with("object.subset") {
            1
        } else {
            2
        };
        let fixture = NestedInput::new(depth, right_leaf);
        for strict in [false, true] {
            let mut engine = Engine::new();
            engine
                .add_policy("depth.rego".into(), module(expression))
                .unwrap();
            engine.set_strict_builtin_errors(strict);
            let rules = [
                "result",
                "negated",
                "fallback",
                "wrapped",
                "alternatives",
                "reverse",
                "wrapped_negated",
                "default_wrapped",
                "partial",
                "branch",
                "chain",
            ];
            for rule in rules {
                engine.set_input(fixture.input.clone());
                let result = engine.eval_rule(format!("data.probe.{rule}"));
                let Err(err) = result else {
                    panic!("depth exhaustion must be an error: {expression}, {rule}");
                };
                assert!(
                    matches!(
                        err.downcast_ref::<LimitError>(),
                        Some(LimitError::BuiltinDepthLimitExceeded { builtin: name, limit: 32 })
                            if *name == builtin
                    ),
                    "must preserve resource error: {rule}: {err}"
                );
                engine.set_input(Value::Null);
                assert_eq!(
                    engine.eval_rule("data.probe.safe".into()).unwrap(),
                    Value::from(7)
                );
                assert_eq!(
                    engine.eval_rule("data.probe.safe_function".into()).unwrap(),
                    Value::from(7)
                );
                assert_eq!(fixture.leaf("left", depth), &Value::from(1));
                assert_eq!(fixture.leaf("right", depth), &Value::from(right_leaf));
            }
            #[cfg(feature = "rvm")]
            {
                let policy = engine
                    .compile_with_entrypoint(&Rc::from("data.probe.result"))
                    .unwrap();
                let mut entries: Vec<String> = rules
                    .iter()
                    .map(|rule| format!("data.probe.{rule}"))
                    .collect();
                entries.push("data.probe.safe".into());
                entries.push("data.probe.safe_function".into());
                let entries: Vec<&str> = entries.iter().map(String::as_str).collect();
                let program = Compiler::compile_from_policy(&policy, &entries).unwrap();
                for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                    let mut vm = RegoVM::new();
                    vm.load_program(program.clone());
                    vm.set_execution_mode(mode);
                    vm.set_strict_builtin_errors(strict);
                    for step_mode in [false, true] {
                        if step_mode && mode != ExecutionMode::Suspendable {
                            continue;
                        }
                        for rule in &entries[..rules.len()] {
                            vm.set_step_mode(step_mode);
                            vm.set_input(fixture.input.clone());
                            let mut result = vm.execute_entry_point_by_name(rule);
                            for _ in 0..10_000 {
                                if !matches!(vm.execution_state(), ExecutionState::Suspended { .. })
                                {
                                    break;
                                }
                                result = vm.resume(None);
                            }
                            assert!(
                                matches!(result,
                                Err(VmError::BuiltinDepthLimitExceeded { builtin: name, limit: 32, .. })
                                    if name == builtin),
                                "VM must preserve depth error: {rule}"
                            );
                            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
                            assert!(vm.get_call_stack().is_empty());
                            vm.set_step_mode(false);
                            vm.set_input(Value::Null);
                            assert_eq!(
                                vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                                Value::from(7)
                            );
                            assert_eq!(
                                vm.execute_entry_point_by_name("data.probe.safe_function")
                                    .unwrap(),
                                Value::from(7)
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn object_builtin_with_restoration() {
    let fixture = NestedInput::new(64, 1);
    for strict in [false, true] {
        let mut engine = Engine::new();
        let source = format!(
            "{}\noverridden := value if {{ \
             value := safe_f(input.left, input.right) with safe_f as f }}\n",
            module("object.subset(input.left, input.right)")
        );
        engine.add_policy("with.rego".into(), source).unwrap();
        engine.set_strict_builtin_errors(strict);
        engine.set_input(fixture.input.clone());
        let Err(err) = engine.eval_rule("data.probe.overridden".into()) else {
            panic!("an overridden function must preserve depth exhaustion");
        };
        assert!(matches!(
            err.downcast_ref::<LimitError>(),
            Some(LimitError::BuiltinDepthLimitExceeded { .. })
        ));
        assert_eq!(
            engine.eval_rule("data.probe.safe_function".into()).unwrap(),
            Value::from(7)
        );
    }
}

#[test]
fn object_builtin_width_and_short_circuit() {
    let fixture = NestedInput::new(10_000, 1);
    let mut engine = Engine::new();
    engine.set_input(fixture.input.clone());
    assert_eq!(
        engine
            .eval_query("object.union({}, input.left)".into(), false)
            .unwrap()
            .result[0]
            .expressions[0]
            .value
            .as_object()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        engine
            .eval_query(
                r#"object.subset({}, {"missing": input.left})"#.into(),
                false
            )
            .unwrap()
            .result[0]
            .expressions[0]
            .value,
        Value::Bool(false)
    );
    let mut wide = Value::new_object();
    for index in 0..1024 {
        wide.as_object_mut()
            .unwrap()
            .insert(Value::from(index), Value::from(index));
    }
    engine.set_input(wide);
    assert_eq!(
        engine
            .eval_query("object.subset(input, input)".into(), false)
            .unwrap()
            .result[0]
            .expressions[0]
            .value,
        Value::Bool(true)
    );
    let result = engine
        .eval_query(
            "object.union_n([input | some _ in numbers.range(1, 64)])".into(),
            false,
        )
        .unwrap();
    assert_eq!(
        result.result[0].expressions[0]
            .value
            .as_object()
            .unwrap()
            .len(),
        1024
    );
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn object_builtin_deep() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess("object_builtin_deep");
        return;
    }
    std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(|| {
            for depth in [32, 33, 64, 10_000] {
                check_deep(depth);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn object_builtin_boundary() {
    for depth in [30, 31] {
        let fixture = NestedInput::new(depth, 1);
        for expression in [
            "object.subset(input.left, input.right)",
            "object.union(input.left, input.right)",
            "object.union_n([input.left, input.right])",
        ] {
            let mut engine = Engine::new();
            engine
                .add_policy("boundary.rego".into(), module(expression))
                .unwrap();
            engine.set_input(fixture.input.clone());
            let result = engine.eval_rule("data.probe.result".into()).unwrap();
            if expression.starts_with("object.subset") {
                assert_eq!(result, Value::Bool(true));
            } else {
                let mut leaf = &result;
                for _ in 0..depth {
                    leaf = leaf.as_object().unwrap().get(&Value::from("a")).unwrap();
                }
                assert_eq!(leaf, &Value::from(1));
            }
            #[cfg(feature = "rvm")]
            {
                let policy = engine
                    .compile_with_entrypoint(&Rc::from("data.probe.result"))
                    .unwrap();
                let program =
                    Compiler::compile_from_policy(&policy, &["data.probe.result"]).unwrap();
                for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                    let mut vm = RegoVM::new();
                    vm.load_program(program.clone());
                    vm.set_execution_mode(mode);
                    vm.set_input(fixture.input.clone());
                    let value = vm.execute().unwrap();
                    assert_eq!(value, result);
                }
            }
        }
    }
}

#[test]
fn object_builtin_array_set_boundary() {
    for depth in [30, 31] {
        let mut candidate = Value::new_set();
        candidate.as_set_mut().unwrap().insert(Value::from(1));
        let fixture = NestedInput::from_leaves(depth, Value::from(vec![Value::from(1)]), candidate);
        let mut engine = Engine::new();
        engine
            .add_policy(
                "conversion.rego".into(),
                "package probe\nresult := object.subset(input.left, input.right)".into(),
            )
            .unwrap();
        engine.set_input(fixture.input.clone());
        let result = engine.eval_rule("data.probe.result".into());
        if depth == 30 {
            assert_eq!(result.unwrap(), Value::Bool(true));
        } else {
            let Err(err) = result else {
                panic!("array-to-set recursion must consume a helper frame");
            };
            assert!(matches!(
                err.downcast_ref::<LimitError>(),
                Some(LimitError::BuiltinDepthLimitExceeded { .. })
            ));
        }
    }
}

#[test]
fn object_builtin_shallow_semantics() {
    let mut engine = Engine::new();
    for (expression, expected) in [
        (
            r#"object.subset({"a":{"a":1},"extra":2}, {"a":{"a":1}})"#,
            Value::Bool(true),
        ),
        (
            r#"object.subset({"a":{"a":1}}, {"a":{"a":2}})"#,
            Value::Bool(false),
        ),
        (
            r#"object.subset({"a":1}, {"missing":1})"#,
            Value::Bool(false),
        ),
        (r#"object.subset([1,2,3], [2,3])"#, Value::Bool(true)),
        (r#"object.subset([1,2,3], {2,3})"#, Value::Bool(true)),
        (
            r#"object.union({"a":{"a":1},"left":3}, {"a":{"a":2},"right":4})"#,
            Value::from_json_str(r#"{"a":{"a":2},"left":3,"right":4}"#).unwrap(),
        ),
        (
            r#"object.union_n([{"a":{"a":1}}, {"a":{"a":2}}])"#,
            Value::from_json_str(r#"{"a":{"a":2}}"#).unwrap(),
        ),
    ] {
        let results = engine.eval_query(expression.into(), false).unwrap();
        assert_eq!(results.result[0].expressions[0].value, expected);
    }
}

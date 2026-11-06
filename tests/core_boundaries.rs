// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "std")]

use regorus::{Engine, LimitError, Value};
use std::collections::BTreeMap;

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

fn nested(depth: usize, object: bool) -> Value {
    (0..depth).fold(Value::Null, |value, _| {
        if object {
            Value::from(BTreeMap::from([(Value::from("k"), value)]))
        } else {
            Value::from(vec![value])
        }
    })
}

fn evaluate(expression: &str, input: Value, expected: Option<Value>) {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(false);
    let query = "data.boundaries.answer";
    engine
        .add_policy(
            "boundaries.rego".into(),
            format!(
                "package boundaries\ndefault answer := false\nanswer := {expression}\nsafe := 7"
            ),
        )
        .unwrap();
    engine.set_input(input.clone());
    let check = |backend: &str, result: anyhow::Result<Value>| match &expected {
        Some(expected) => assert_eq!(&result.unwrap(), expected, "{expression}"),
        None => {
            let error = result.expect_err(&format!("{backend}: {expression}"));
            let serialization_depth_error = matches!(
                error.downcast_ref::<LimitError>(),
                Some(LimitError::SerializationDepthExceeded { limit: 64 })
            );
            #[cfg(feature = "rvm")]
            let serialization_depth_error = serialization_depth_error
                || matches!(
                    error.downcast_ref::<regorus::rvm::vm::VmError>(),
                    Some(regorus::rvm::vm::VmError::SerializationDepthExceeded { limit: 64, .. })
                );
            assert!(
                format!("{error:#}").contains("nesting limit") || serialization_depth_error,
                "{expression}: {error:#}"
            );
        }
    };
    check("interpreter", engine.eval_rule(query.into()));
    assert_eq!(
        engine.eval_rule("data.boundaries.safe".into()).unwrap(),
        Value::from(7)
    );
    if expected.is_none() {
        engine.set_strict_builtin_errors(true);
        check("strict interpreter", engine.eval_rule(query.into()));
        assert_eq!(
            engine.eval_rule("data.boundaries.safe".into()).unwrap(),
            Value::from(7)
        );
        engine.set_strict_builtin_errors(false);
    }
    #[cfg(feature = "rvm")]
    {
        if expression.contains("walk(") {
            return;
        }
        use regorus::languages::rego::compiler::Compiler;
        use regorus::rvm::vm::{ExecutionMode, RegoVM};
        let compiled = engine.compile_with_entrypoint(&query.into()).unwrap();
        let program =
            Compiler::compile_from_policy(&compiled, &[query, "data.boundaries.safe"]).unwrap();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(false);
            vm.set_input(input.clone());
            check(
                "RVM",
                vm.execute_entry_point_by_name(query).map_err(Into::into),
            );
            assert_eq!(
                vm.execute_entry_point_by_name("data.boundaries.safe")
                    .unwrap(),
                Value::from(7)
            );
            if expected.is_none() {
                vm.set_strict_builtin_errors(true);
                check(
                    "strict RVM",
                    vm.execute_entry_point_by_name(query).map_err(Into::into),
                );
                assert_eq!(
                    vm.execute_entry_point_by_name("data.boundaries.safe")
                        .unwrap(),
                    Value::from(7)
                );
            }
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn object_operations() {
    on_execution_stack("object_operations", || {
        evaluate(
            "object.subset(input, input)",
            nested(2048, true),
            Some(true.into()),
        );
        for depth in [32, 33] {
            let value = nested(depth, true);
            let expected = (depth == 32).then_some(value.clone());
            evaluate(
                "object.union(input, input)",
                value.clone(),
                expected.clone(),
            );
            evaluate("object.union_n([input, input])", value.clone(), expected);
            evaluate(
                "true if { not object.union(input, input) }",
                value.clone(),
                (depth == 32).then_some(false.into()),
            );
            let path = vec!["k"; depth].join("/");
            let input = Value::from(BTreeMap::from([
                (Value::from("value"), value.clone()),
                (Value::from("paths"), Value::from(vec![Value::from(path)])),
            ]));
            evaluate(
                "json.filter(input.value, input.paths)",
                input.clone(),
                (depth == 32).then_some(value),
            );
            evaluate(
                "json.remove(input.value, input.paths)",
                input,
                (depth == 32).then(|| {
                    (0..depth - 1).fold(Value::new_object(), |child, _| {
                        Value::from(BTreeMap::from([(Value::from("k"), child)]))
                    })
                }),
            );
        }
        evaluate(
            "object.union({\"a\": input}, {\"b\": true})",
            nested(2048, false),
            Some(Value::from(BTreeMap::from([
                (Value::from("a"), nested(2048, false)),
                (Value::from("b"), true.into()),
            ]))),
        );
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn traversal_and_formatting() {
    on_execution_stack("traversal_and_formatting", || {
        #[cfg(feature = "graph")]
        evaluate(
            "count([item | walk(input, item)])",
            nested(2048, false),
            Some(2049.into()),
        );
        for format in ["%v", "%s"] {
            evaluate(
                &format!("sprintf(\"{format}\", [input])"),
                nested(2048, false),
                Some(Value::from(format!(
                    "{}null{}",
                    "[".repeat(2048),
                    "]".repeat(2048)
                ))),
            );
        }
        for depth in [128, 129] {
            evaluate(
                "sprintf(\"%q\", [input])",
                nested(depth, false),
                (depth == 128).then(|| {
                    Value::from(format!(
                        "\"{}null{}\"",
                        "[".repeat(depth),
                        "]".repeat(depth)
                    ))
                }),
            );
        }
        #[cfg(feature = "graph")]
        let graph = Value::from(
            (0..4096)
                .map(|index| {
                    (
                        Value::from(index),
                        Value::from(if index == 4095 {
                            vec![]
                        } else {
                            vec![Value::from(index + 1)]
                        }),
                    )
                })
                .collect::<BTreeMap<_, _>>(),
        );
        #[cfg(feature = "graph")]
        evaluate(
            "graph.reachable_paths(input, [0])",
            graph,
            Some(Value::from(std::collections::BTreeSet::from([
                Value::from((0..4096).map(Value::from).collect::<Vec<_>>()),
            ]))),
        );
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn text_and_dom_conversion() {
    on_execution_stack("text_and_dom_conversion", || {
        for depth in [32, 33] {
            for scalar in ["null", "123456789012345678901234567890"] {
                let text = format!("{}{scalar}{}", "[".repeat(depth), "]".repeat(depth));
                let result = Value::from_json_str(&text);
                assert_eq!(result.is_ok(), depth == 32);
                if depth == 32 {
                    assert_eq!(
                        result.unwrap(),
                        (0..depth).fold(Value::from_json_str(scalar).unwrap(), |v, _| Value::from(
                            vec![v]
                        ))
                    );
                }
                #[cfg(feature = "yaml")]
                assert_eq!(Value::from_yaml_str(&text).is_ok(), depth == 32);
                evaluate(
                    "json.is_valid(input)",
                    Value::from(text.clone()),
                    (depth == 32).then_some(true.into()),
                );
                #[cfg(feature = "yaml")]
                evaluate(
                    "yaml.is_valid(input)",
                    Value::from(text),
                    (depth == 32).then_some(true.into()),
                );
            }
        }
        for text in ["[", "{", "not-json"] {
            evaluate("json.is_valid(input)", text.into(), Some(false.into()));
        }
        assert!(nested(2048, false).to_json_str().is_ok());
        for depth in [64, 65] {
            evaluate(
                "json.marshal(input)",
                nested(depth, false),
                (depth == 64).then(|| {
                    Value::from(format!("{}null{}", "[".repeat(depth), "]".repeat(depth)))
                }),
            );
        }
        #[cfg(feature = "yaml")]
        for depth in [64, 65] {
            evaluate(
                "yaml.marshal(input)",
                nested(depth, false),
                (depth == 64).then(|| Value::from(format!("{}null\n", "- ".repeat(depth)))),
            );
        }
        for _ in 0..2 {
            let json = (0..2048).fold(serde_json::Value::Null, |v, _| {
                serde_json::Value::Array(vec![v])
            });
            assert_eq!(Value::from(json), nested(2048, false));
            #[cfg(feature = "yaml")]
            {
                let yaml = (0..2048).fold(yaml_serde::Value::Null, |v, _| {
                    yaml_serde::Value::Sequence(vec![v])
                });
                assert_eq!(Value::from(yaml), nested(2048, false));
            }
        }
        #[cfg(feature = "yaml")]
        {
            let tagged: yaml_serde::Value = yaml_serde::from_str("!example [1]").unwrap();
            assert_eq!(Value::from(tagged), Value::Undefined);
        }
        let malformed = format!("{}[null,@", "[".repeat(33));
        assert!(Value::from_json_str(&malformed).is_err());
        assert_eq!(
            Value::from_json_str("[1]").unwrap(),
            Value::from(vec![1.into()])
        );
    });
}

#[test]
#[cfg(feature = "jsonschema")]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn schema_values() {
    on_execution_stack("schema_values", || {
        for depth in [32, 33] {
            evaluate(
                "json.verify_schema(input)[0]",
                nested(depth, true),
                (depth == 32).then_some(true.into()),
            );
            evaluate(
                "json.match_schema(input, {})[0]",
                nested(depth, false),
                (depth == 32).then_some(true.into()),
            );
        }
        evaluate(
            "json.verify_schema(input)[0]",
            "{".into(),
            Some(false.into()),
        );
    });
}

#[test]
#[cfg(feature = "jsonpatch")]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn patch_composition() {
    on_execution_stack("patch_composition", || {
        for depth in [128, 129] {
            for object in [false, true] {
                evaluate(
                    "json.patch(input, [])",
                    nested(depth, object),
                    (depth == 128).then(|| nested(depth, object)),
                );
            }
            let operation = Value::from(BTreeMap::from([
                (Value::from("op"), Value::from("add")),
                (
                    Value::from("path"),
                    Value::from(format!("/{}", vec!["k"; depth].join("/"))),
                ),
                (Value::from("value"), Value::Null),
            ]));
            // A missing intermediate object is an ordinary patch error.
            evaluate(
                "json.patch({}, [input])",
                operation,
                (depth == 128).then_some(Value::Bool(false)),
            );
        }
        let value = nested(128, true);
        let operation = Value::from(BTreeMap::from([
            (Value::from("op"), Value::from("add")),
            (Value::from("path"), Value::from("/other")),
            (Value::from("value"), value),
        ]));
        evaluate("json.patch({}, [input])", operation, None);
    });
}

#[test]
#[cfg(feature = "rvm")]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn program_formats_and_admission() {
    on_execution_stack("program_formats_and_admission", || {
        use regorus::rvm::program::{DeserializationResult, Program};
        use regorus::rvm::vm::RegoVM;
        for depth in [32, 33] {
            let mut program = Program::new();
            program.literals.push(nested(depth, false));
            let binary = program.serialize_binary();
            let json = program.serialize_json();
            assert_eq!(binary.is_ok(), depth == 32);
            assert_eq!(json.is_ok(), depth == 32);
            if depth == 32 {
                let recovered = Program::deserialize_binary(&binary.unwrap()).unwrap();
                let (DeserializationResult::Complete(recovered)
                | DeserializationResult::Partial(recovered)) = recovered;
                assert_eq!(recovered.literals, program.literals);
                assert_eq!(
                    Program::deserialize_json(&json.unwrap()).unwrap().literals,
                    program.literals
                );
            }
            let mut annotations = Program::new();
            let annotation = (0..depth).fold(Value::Bool(true), |v, _| Value::from(vec![v]));
            annotations
                .metadata
                .annotations
                .insert("note".into(), annotation.clone());
            let binary = annotations.serialize_binary();
            let json = annotations.serialize_json();
            assert_eq!(binary.is_ok(), depth == 32);
            assert_eq!(json.is_ok(), depth == 32);
            assert_eq!(postcard::to_allocvec(&annotations).is_ok(), depth == 32);
            assert_eq!(serde_json::to_string(&annotations).is_ok(), depth == 32);
            if depth == 32 {
                let (DeserializationResult::Complete(recovered)
                | DeserializationResult::Partial(recovered)) =
                    Program::deserialize_binary(&binary.unwrap()).unwrap();
                assert_eq!(
                    recovered.metadata.annotations.get("note"),
                    Some(&annotation)
                );
                assert_eq!(
                    Program::deserialize_json(&json.unwrap())
                        .unwrap()
                        .metadata
                        .annotations
                        .get("note"),
                    Some(&annotation),
                );
                let generic: Program =
                    postcard::from_bytes(&postcard::to_allocvec(&annotations).unwrap()).unwrap();
                assert_eq!(generic.metadata.annotations.get("note"), Some(&annotation));
                let generic: Program =
                    serde_json::from_str(&serde_json::to_string(&annotations).unwrap()).unwrap();
                assert_eq!(generic.metadata.annotations.get("note"), Some(&annotation));
            }
        }
        let mut listing_program = Program::new();
        let listed = nested(2048, false);
        listing_program.literals.push(listed.clone());
        listing_program
            .metadata
            .annotations
            .insert("note".into(), listed);
        listing_program
            .instructions
            .push(regorus::rvm::Instruction::Load {
                dest: 0,
                literal_idx: 0,
            });
        let listing =
            regorus::rvm::program::generate_assembly_listing(&listing_program, &Default::default());
        let literal = format!("{}null{}", "[".repeat(2048), "]".repeat(2048));
        assert_eq!(listing.matches(&literal).count(), 3);
        let mut engine = Engine::new();
        engine
            .add_policy(
                "admission.rego".into(),
                "package admission\nanswer := 7".into(),
            )
            .unwrap();
        let policy = engine
            .compile_with_entrypoint(&"data.admission.answer".into())
            .unwrap();
        let good = regorus::languages::rego::compiler::Compiler::compile_from_policy(
            &policy,
            &["data.admission.answer"],
        )
        .unwrap();
        let mut invalid = (*good).clone();
        invalid.rule_tree = nested(33, true);
        let mut vm = RegoVM::new();
        vm.load_program(std::sync::Arc::new(invalid));
        for mode in [
            regorus::rvm::vm::ExecutionMode::RunToCompletion,
            regorus::rvm::vm::ExecutionMode::Suspendable,
        ] {
            vm.set_execution_mode(mode);
            assert!(vm.execute().is_err());
            assert!(vm
                .execute_entry_point_by_name("data.admission.answer")
                .is_err());
            assert!(vm.execute_entry_point_by_index(0).is_err());
        }
        vm.load_program(good);
        assert_eq!(
            vm.execute_entry_point_by_name("data.admission.answer")
                .unwrap(),
            7.into()
        );
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn checked_comparisons_and_patterns() {
    on_execution_stack("checked_comparisons_and_patterns", || {
        #[cfg(feature = "rvm")]
        {
            use regorus::utils::limits::ExecutionTimerConfig;
            let input = Value::from(vec![nested(4096, false), nested(4096, false)]);
            let mut engine = Engine::new();
            let timer = ExecutionTimerConfig {
                limit: std::time::Duration::from_secs(10),
                check_interval: std::num::NonZeroU32::new(1).unwrap(),
            };
            engine.set_execution_timer_config(timer);
            engine.add_policy("comparison.rego".into(), "package comparison\nanswer := input[0] == input[1]\nordered := input[0] <= input[1]".into()).unwrap();
            let policy = engine
                .compile_with_entrypoint(&"data.comparison.answer".into())
                .unwrap();
            let program = regorus::languages::rego::compiler::Compiler::compile_from_policy(
                &policy,
                &["data.comparison.answer", "data.comparison.ordered"],
            )
            .unwrap();
            let mut vm = regorus::rvm::vm::RegoVM::new();
            vm.load_program(program);
            vm.set_execution_timer_config(Some(timer));
            vm.set_input(input);
            for query in ["data.comparison.answer", "data.comparison.ordered"] {
                assert_eq!(vm.execute_entry_point_by_name(query).unwrap(), true.into());
            }
        }
        #[cfg(feature = "regex")]
        for depth in [250, 251] {
            let pattern = format!("{}a{}", "(".repeat(depth), ")".repeat(depth));
            evaluate(
                "regex.is_valid(input)",
                pattern.into(),
                Some((depth == 250).into()),
            );
        }
        #[cfg(feature = "glob")]
        for depth in [32, 33] {
            let pattern = format!("{}a{}", "{".repeat(depth), "}".repeat(depth));
            evaluate(
                "glob.match(input, [], \"a\")",
                pattern.into(),
                (depth == 32).then_some(true.into()),
            );
        }
    });
}

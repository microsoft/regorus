// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::{Engine, QueryResult, Value};

// One virtual rule and one base-data leaf reproduce the cache bug.
// Expected results were checked against OPA v1.22.0.
fn new_engine() -> Engine {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "example.rego".into(),
            "package example.a\nresult := input.value".into(),
        )
        .unwrap();
    engine
        .add_data(Value::from_json_str(r#"{"example":{"a":{"value":true}}}"#).unwrap())
        .unwrap();
    engine.set_input(Value::new_object());
    engine
}

fn entry_engine() -> Engine {
    let mut engine = new_engine();
    engine
        .add_policy(
            "entry.rego".into(),
            r#"package entry
               default result := false
               result if {
                   some key in input.keys
                   data.example[key].result with input.value as data.example[key].value
               }"#
            .into(),
        )
        .unwrap();
    engine.set_input(Value::from_json_str(r#"{"keys":["a"]}"#).unwrap());
    engine
}

fn assert_query(engine: &mut Engine, query: &str, expected: &[Value]) -> QueryResult {
    let results = engine.eval_query(query.into(), false).unwrap();
    assert_eq!(results.result.len(), 1, "{query}: {results:?}");
    let result = results.result.into_iter().next().unwrap();
    let values: Vec<_> = result
        .expressions
        .iter()
        .map(|expr| expr.value.clone())
        .collect();
    assert_eq!(values, expected, "{query}");
    result
}

#[test]
fn rule_result_is_recomputed_after_loading_a_with_replacement() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "policy.rego".into(),
            "package example\nresult := input.value".into(),
        )
        .unwrap();
    engine
        .add_data(Value::from_json_str(r#"{"example":{"value":true}}"#).unwrap())
        .unwrap();
    engine.set_input(Value::new_object());

    assert_query(
        &mut engine,
        "data.example.result with input.value as data.example.value",
        &[true.into()],
    );
    assert_query(
        &mut engine,
        r#"key := "example"; data[key].result with input.value as data[key].value"#,
        &[true.into(), true.into()],
    );
    assert_query(
        &mut engine,
        r#"some key in ["example"]; data[key].result with input.value as data[key].value"#,
        &[true.into(), true.into()],
    );
    assert_query(
        &mut engine,
        "not input.value; not data.example.result",
        &[true.into(), true.into()],
    );
}

#[test]
fn assignment_bound_replacement_is_defined() {
    assert_query(
        &mut new_engine(),
        r#"key := "a"; data.example[key].value"#,
        &[true.into(), true.into()],
    );
}

#[test]
fn literal_index_with_override() {
    assert_query(
        &mut new_engine(),
        r#"data.example["a"].result with input.value as data.example["a"].value"#,
        &[true.into()],
    );
}

#[test]
fn assignment_bound_index_with_override() {
    for input in ["{}", r#"{"value":false}"#] {
        let mut engine = new_engine();
        engine.set_input(Value::from_json_str(input).unwrap());
        let result = assert_query(
            &mut engine,
            r#"key := "a"; data.example[key].result with input.value as data.example[key].value"#,
            &[true.into(), true.into()],
        );
        assert_eq!(
            result.bindings,
            Value::from_json_str(r#"{"key":"a"}"#).unwrap()
        );
    }
}

#[test]
fn iteration_bound_index_with_override() {
    let result = assert_query(
        &mut new_engine(),
        r#"some key in ["a"]; data.example[key].result with input.value as data.example[key].value"#,
        &[true.into(), true.into()],
    );
    assert_eq!(
        result.bindings,
        Value::from_json_str(r#"{"key":"a"}"#).unwrap()
    );
    assert_query(
        &mut new_engine(),
        r#"[value |
             some key in ["a"]
             value := data.example[key].result with input.value as data.example[key].value
         ]"#,
        &[Value::from(vec![true.into()])],
    );
}

#[test]
fn iteration_restores_overrides_between_true_and_false_values() {
    let mut engine = new_engine();
    engine
        .add_policy(
            "second.rego".into(),
            "package example.b\nresult := input.value".into(),
        )
        .unwrap();
    engine
        .add_policy(
            "selection.rego".into(),
            r#"package selection
               selected contains key if {
                   some key in input.keys
                   data.example[key].result with input.value as data.example[key].value
               }"#
            .into(),
        )
        .unwrap();
    engine
        .add_data(Value::from_json_str(r#"{"example":{"b":{"value":false}}}"#).unwrap())
        .unwrap();
    let mut expected = Value::new_set();
    expected.as_set_mut().unwrap().insert("a".into());
    for input in [r#"{"keys":["a","b"]}"#, r#"{"keys":["b","a"]}"#] {
        engine.set_input(Value::from_json_str(input).unwrap());
        assert_eq!(
            engine.eval_rule("data.selection.selected".into()).unwrap(),
            expected
        );
        assert_query(&mut engine, "not input.value", &[true.into()]);
        assert_query(&mut engine, "not data.example.b.result", &[true.into()]);
    }
}

#[test]
fn top_level_rule() {
    let mut engine = entry_engine();
    assert_query(&mut engine, "data.entry.result", &[true.into()]);
    assert_eq!(
        engine.eval_rule("data.entry.result".into()).unwrap(),
        true.into()
    );
}

#[test]
fn reused_engine_and_compiled_policy_follow_changing_inputs() {
    let mut engine = entry_engine();
    let compiled = engine
        .compile_with_entrypoint(&"data.entry.result".into())
        .unwrap();
    for (input, expected) in [
        (r#"{"keys":["a"]}"#, true),
        (r#"{"keys":["missing"]}"#, false),
        (r#"{"keys":["a"]}"#, true),
    ] {
        let input = Value::from_json_str(input).unwrap();
        engine.set_input(input.clone());
        assert_query(&mut engine, "data.entry.result", &[expected.into()]);
        assert_eq!(
            engine.eval_rule("data.entry.result".into()).unwrap(),
            expected.into()
        );
        assert_eq!(compiled.eval_with_input(input).unwrap(), expected.into());
        assert_query(&mut engine, "not input.value", &[true.into()]);
    }
}

#[test]
fn compiled_policy_with_override_preserves_base_data() {
    for modifier in ["input.unused as true", "data.probe.f as 7"] {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "compiled.rego".into(),
                format!(
                    r#"package probe
                       f(x) := x
                       result := v if {{
                           v := data.base with {modifier}
                       }}"#
                ),
            )
            .unwrap();
        engine
            .add_data(Value::from_json_str(r#"{"base":7}"#).unwrap())
            .unwrap();
        let compiled = engine
            .compile_with_entrypoint(&"data.probe.result".into())
            .unwrap();
        assert_query(&mut engine, "data.probe.result", &[7.into()]);
        assert_eq!(
            compiled.eval_with_input(Value::new_object()).unwrap(),
            7.into()
        );
    }
}

#[test]
fn false_replacement_produces_a_defined_value() {
    let result = assert_query(
        &mut new_engine(),
        "actual := input.value with input.value as false; actual == false",
        &[true.into(), true.into()],
    );
    assert_eq!(
        result.bindings,
        Value::from_json_str(r#"{"actual":false}"#).unwrap()
    );
}

#[test]
fn successful_override_restores_input_and_cached_rules() {
    assert_query(
        &mut new_engine(),
        r#"key := "a";
           not data.example[key].result;
           data.example[key].result with input.value as data.example[key].value;
           not input.value;
           not data.example[key].result"#,
        &vec![true.into(); 5],
    );
}

#[test]
fn overrides_do_not_leak_between_evaluations() {
    let mut engine = new_engine();
    for _ in 0..2 {
        // A defined false replacement must actually be applied.
        let denied = engine
            .eval_query(
                r#"key := "a"; data.example[key].result with input.value as false"#.into(),
                false,
            )
            .unwrap();
        assert!(denied.result.is_empty());

        assert_query(
            &mut engine,
            r#"key := "a"; data.example[key].result with input.value as data.example[key].value"#,
            &[true.into(), true.into()],
        );
        assert_query(&mut engine, "not input.value", &[true.into()]);
        assert_query(&mut engine, "not data.example.a.result", &[true.into()]);
    }
}

#[test]
fn nested_input_override_preserves_and_restores_outer_data_override() {
    let mut engine = entry_engine();
    assert_query(
        &mut engine,
        r#"blocked := data.entry.result with data.example.a.result as false;
           blocked == false;
           data.entry.result"#,
        &vec![true.into(); 3],
    );
    assert_eq!(
        engine.eval_rule("data.entry.result".into()).unwrap(),
        true.into()
    );
}

#[test]
fn rule_replacement_uses_original_input_and_is_recomputed_under_override() {
    for input in [r#"{"number": 1}"#, "{}"] {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "number.rego".into(),
                "package probe\ndefault number := 1\nnumber := input.number".into(),
            )
            .unwrap();
        engine.set_input(Value::from_json_str(input).unwrap());
        // Loading a replacement can cache rule values. The caller's processed
        // markers and values must agree after the override is restored.
        assert_query(
            &mut engine,
            "modified := input.number with input.number as data.probe.number + 1;
             original := data.probe.number;
             [modified, original] == [2, 1]",
            &vec![true.into(); 3],
        );
        assert_query(
            &mut engine,
            "data.probe.number with input.number as data.probe.number + 1",
            &[2.into()],
        );
        // Prime the cache within the same query and check restoration after WITH.
        assert_query(
            &mut engine,
            "before := data.probe.number;
             modified := data.probe.number with input.number as data.probe.number + 1;
             after := data.probe.number;
             [before, modified, after] == [1, 2, 1]",
            &vec![true.into(); 4],
        );
    }
}

#[test]
fn replacements_are_evaluated_before_document_overrides() {
    for root in ["input", "data.base"] {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "document.rego".into(),
                format!(
                    r#"package probe
                   replacement := v if {{
                       v := {root}.x with input.unused as 0
                   }}"#
                ),
            )
            .unwrap();
        engine
            .add_data(Value::from_json_str(r#"{"base":{"x":"old"}}"#).unwrap())
            .unwrap();
        engine.set_input(Value::from_json_str(r#"{"x":"old"}"#).unwrap());
        assert_query(
            &mut engine,
            &format!(
                r#"[{root}.x, input.z]
                   with {root}.x as "new"
                   with input.z as data.probe.replacement"#
            ),
            &[Value::from_json_str(r#"["new","old"]"#).unwrap()],
        );
    }
}

#[test]
fn replacements_are_evaluated_before_function_overrides() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "function.rego".into(),
            "package probe\nf(x) := x\nnumber := data.probe.f(2)".into(),
        )
        .unwrap();
    engine.set_input(Value::new_object());
    assert_query(
        &mut engine,
        "[input.number, data.probe.number] with data.probe.f as 7 with input.number as data.probe.number",
        &[Value::from(vec![2.into(), 7.into()])],
    );
    assert_query(&mut engine, "data.probe.number", &[2.into()]);
    assert_query(&mut engine, "data.probe.f(3)", &[3.into()]);
    assert_query(&mut engine, "input", &[Value::new_object()]);
}

#[test]
fn nested_function_overrides_preserve_and_restore_inherited_mocks() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "functions.rego".into(),
            r#"package probe
               f(x) := x
               g(x) := x
               inner := v if {
                   v := [data.probe.f(1), data.probe.g(2)] with data.probe.g as 9
               }"#
            .into(),
        )
        .unwrap();
    assert_query(
        &mut engine,
        "data.probe.inner with data.probe.f as 7",
        &[Value::from(vec![7.into(), 9.into()])],
    );
    assert_query(
        &mut engine,
        "[data.probe.f(1), data.probe.g(2)]",
        &[Value::from(vec![1.into(), 2.into()])],
    );
}

#[test]
fn replacement_function_rule_cache_does_not_escape_its_scope() {
    for (values, expected) in [
        ("[inner, number]", "[2,7]"),
        ("[number, inner]", "[7,2]"),
        ("[number, inner, number]", "[7,2,7]"),
        ("[number, data.probe.f(0)]", "[7,2]"),
        ("[data.probe.f(0), number]", "[2,7]"),
        ("[number, data.probe.f(0), number]", "[7,2,7]"),
    ] {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "replacement.rego".into(),
                format!(
                    r#"package probe
               f(x) := x
               g(x) := 7 if x == 2
               g(x) := data.probe.number if x != 2
               number := data.probe.f(2)
               inner := v if {{
                   v := input.value with input.value as data.probe.f(0)
               }}
               result := v if {{
                   v := {values} with data.probe.f as data.probe.g
               }}"#
                ),
            )
            .unwrap();
        let compiled = engine
            .compile_with_entrypoint(&"data.probe.result".into())
            .unwrap();
        let expected = Value::from_json_str(expected).unwrap();
        assert_query(
            &mut engine,
            "data.probe.result",
            core::slice::from_ref(&expected),
        );
        assert_eq!(
            compiled.eval_with_input(Value::new_object()).unwrap(),
            expected
        );
        assert_query(
            &mut engine,
            "before := data.probe.number;
             modified := data.probe.result;
             after := data.probe.number;
             [before, modified, after]",
            &[
                true.into(),
                true.into(),
                true.into(),
                Value::from(vec![2.into(), expected.clone(), 2.into()]),
            ],
        );
        assert_query(
            &mut engine,
            "data.probe.result with data.probe.number as 42",
            &[Value::from(vec![
                42.into();
                expected.as_array().unwrap().len()
            ])],
        );
    }
}

#[test]
fn function_mocks_reuse_rule_values_within_an_ordinary_rule_body() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "shared.rego".into(),
            r#"package probe
               f(x) := x
               g(x) := 7 if x == 2
               g(x) := data.probe.number if x != 2
               number := data.probe.f(2)
               shared := [before, modified, after] if {
                   before := number
                   modified := data.probe.f(0)
                   after := number
               }"#
            .into(),
        )
        .unwrap();
    assert_query(
        &mut engine,
        "data.probe.shared with data.probe.f as data.probe.g",
        &[Value::from_json_str("[7,7,7]").unwrap()],
    );
}

#[test]
fn with_terms_are_recomputed_between_iterations_and_after_undefined_results() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "iteration.rego".into(),
            r#"package probe
               f(x) := x
               g(x) := 7 if x == 2
               g(x) := data.probe.number if x != 2
               h(x) := x if x != 0
               number := data.probe.f(2)
               rows := [row |
                   some key in [0, 1, 2]
                   row := [key, number, data.probe.f(key), data.probe.h(key)]
                     with data.probe.f as data.probe.g
               ]"#
            .into(),
        )
        .unwrap();
    assert_query(
        &mut engine,
        "data.probe.rows",
        &[Value::from_json_str("[[1,7,2,1],[2,7,7,2]]").unwrap()],
    );
}

#[test]
fn undefined_with_terms_stop_before_later_errors_and_before_negation() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "undefined.rego".into(),
            "package probe\nu(x) := x if false\nbad(x) := 1 / x".into(),
        )
        .unwrap();
    engine.set_strict_builtin_errors(true);
    for query in [
        "[data.probe.u(1), data.probe.bad(0)] with input.unused as 0",
        "not [data.probe.u(1), data.probe.bad(0)] with input.unused as 0",
        "not [input.missing] with input.unused as 0",
        "not is_number(input.missing) with input.unused as 0",
    ] {
        assert!(
            engine
                .eval_query(query.into(), false)
                .unwrap()
                .result
                .is_empty(),
            "{query}"
        );
        assert!(
            engine
                .eval_query(format!("before := 1; {query}"), false)
                .unwrap()
                .result
                .is_empty(),
            "before := 1; {query}"
        );
    }
    assert_query(
        &mut engine,
        "not data.probe.u(1) with input.unused as 0",
        &[true.into()],
    );
}

#[test]
fn with_print_accepts_undefined_arguments() {
    let mut engine = Engine::new();
    engine.set_gather_prints(true);
    assert_query(
        &mut engine,
        "print(input.missing) with input.unused as 0",
        &[true.into()],
    );
    assert_eq!(engine.take_prints().unwrap().len(), 1);
}

#[test]
fn hoisted_calls_preserve_output_argument_matching() {
    let mut engine = Engine::new();
    engine
        .add_policy("function.rego".into(), "package probe\nf(x) := x".into())
        .unwrap();
    assert_query(
        &mut engine,
        "expected := 7; data.probe.f(input.value, expected) with input.value as 7",
        &[true.into(), true.into()],
    );
    assert_query(
        &mut engine,
        "not data.probe.f(input.value, 8) with input.value as 7",
        &[true.into()],
    );
}

#[test]
fn with_terms_reuse_already_hoisted_loop_values() {
    let mut engine = Engine::new();
    engine.set_gather_prints(true);
    engine
        .add_policy(
            "loop.rego".into(),
            r#"package probe
               items() := v if {
                   print("items evaluated")
                   v := [{"value": 1}, {"value": 2}]
               }"#
            .into(),
        )
        .unwrap();
    let result = assert_query(
        &mut engine,
        "rows := [row |
             row := [data.probe.items()[_].value, input.unused] with input.unused as 9
         ]",
        &[true.into()],
    );
    assert_eq!(
        result.bindings,
        Value::from_json_str(r#"{"rows":[[1,9],[2,9]]}"#).unwrap()
    );
    assert_eq!(engine.take_prints().unwrap().len(), 1);
}

#[test]
fn replacement_evaluation_recomputes_undefined_and_default_rules() {
    for (default_rule, expected) in [
        ("", Value::Undefined),
        (
            "default number := 1",
            Value::from_json_str("[7,1,7]").unwrap(),
        ),
    ] {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "replacement.rego".into(),
                format!(
                    r#"package probe
                   f(x) := x if x != 2
                   g(x) := 7 if x == 2
                   g(x) := data.probe.number if x != 2
                   {default_rule}
                   number := data.probe.f(2)
                   inner := v if {{
                       v := input.value with input.value as data.probe.f(0)
                   }}
                   result := v if {{
                       v := [number, inner, number] with data.probe.f as data.probe.g
                   }}"#
                ),
            )
            .unwrap();
        let compiled = engine
            .compile_with_entrypoint(&"data.probe.result".into())
            .unwrap();
        assert_eq!(
            engine.eval_rule("data.probe.result".into()).unwrap(),
            expected
        );
        assert_eq!(
            compiled.eval_with_input(Value::new_object()).unwrap(),
            expected
        );
    }
}

#[test]
fn nested_replacements_restore_the_parent_cache_and_input() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "nested.rego".into(),
            r#"package probe
               source := input.number
               replacement := v if {
                   v := data.probe.source with input.number as input.number + 1
               }
               result := v if {
                   v := [input.number, data.probe.source]
                     with input.number as data.probe.replacement
               }"#
            .into(),
        )
        .unwrap();
    engine.set_input(Value::from_json_str(r#"{"number":1}"#).unwrap());
    assert_query(
        &mut engine,
        "[data.probe.result, data.probe.source, input.number]",
        &[Value::from_json_str("[[2,2],1,1]").unwrap()],
    );
}

#[test]
fn undefined_replacement_is_not_masked_by_later_modifiers() {
    for modifiers in [
        "with input.a as input.missing with input.b as 2",
        "with input.a as 2 with input.b as input.missing",
    ] {
        let mut engine = new_engine();
        let query = format!("before := 1; true {modifiers}");
        assert!(engine
            .eval_query(query.clone(), false)
            .unwrap()
            .result
            .is_empty());
        assert_query(&mut engine, "input", &[Value::new_object()]);

        let input = Value::from_json_str(r#"{"missing":0}"#).unwrap();
        engine.set_input(input.clone());
        assert_query(&mut engine, &query, &[true.into(), true.into()]);
        assert_query(&mut engine, "input", &[input]);
    }
}

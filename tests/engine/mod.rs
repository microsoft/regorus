// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};
use regorus::*;

#[test]
fn numeric_rule_paths_keep_integer_decimal_equivalence() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "policy.rego".to_string(),
        r#"
        package policy
        items[1].blocked := true
        allow := data.policy.items[1.0].blocked
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&"data.policy.allow".into())?;

    assert_eq!(
        engine.eval_rule("data.policy.allow".to_string())?,
        Value::Bool(true)
    );
    for _ in 0..2 {
        assert_eq!(
            compiled.eval_with_input(Value::new_object())?,
            Value::Bool(true),
            "the compiled policy preserves 1 == 1.0 numeric path lookup"
        );
    }

    Ok(())
}

#[test]
fn static_entrypoints_reject_repeated_unary_scalar_indices() -> Result<()> {
    let repeated_unary_path = format!("data.policy.items[{}1].blocked", "-".repeat(40));
    let mut engine = Engine::new();
    engine.add_policy(
        "policy.rego".to_string(),
        r#"
        package policy
        items[1].blocked := "one"
        items[-1].negative := true
        items[1e1].exponent := "ten"
        "#
        .to_string(),
    )?;

    assert_eq!(
        engine.eval_rule("data.policy.items[1].blocked".to_string())?,
        Value::from("one"),
        "the numeric control path must identify the registered rule"
    );
    let interpreter_result = engine.eval_rule(repeated_unary_path.clone());
    let compiled_result = engine.compile_with_entrypoint(&repeated_unary_path.as_str().into());
    assert!(
        interpreter_result.is_err() && compiled_result.is_err(),
        "static lookups must reject repeated unary indices, got interpreter={interpreter_result:?}, compiled={compiled_result:?}"
    );
    for (path, expected) in [
        ("data.policy.items[-1].negative", Value::Bool(true)),
        ("data.policy.items[1e1].exponent", Value::from("ten")),
    ] {
        assert_eq!(engine.eval_rule(path.to_string())?, expected);
        let compiled = engine.compile_with_entrypoint(&path.into())?;
        assert_eq!(compiled.eval_with_input(Value::new_object())?, expected);
    }

    for index in ["--1", "- -1", "--0", "- -0", "-true", "1+2"] {
        let path = format!("data.policy.items[{index}].blocked");
        assert!(
            engine
                .compile_with_entrypoint(&path.as_str().into())
                .is_err(),
            "static path index {index:?} is not a single literal"
        );
    }

    Ok(())
}

#[test]
fn with_targets_reject_repeated_unary_scalar_indices() -> Result<()> {
    let repeated_unary_target = format!("data.policy.items[{}1].blocked", "-".repeat(40));
    let policy = format!(
        "package policy\nimport rego.v1\nitems[1].blocked := \"one\"\nresult := true if {{ data.policy.items[1].blocked with {repeated_unary_target} as \"override\" }}"
    );
    let mut engine = Engine::new();

    assert!(
        engine
            .add_policy("policy.rego".to_string(), policy)
            .is_err(),
        "WITH targets must reject repeated unary indices while parsing"
    );
    let spaced_target = "data.policy.items[- -1].blocked";
    let spaced_policy = format!(
        "package policy\nimport rego.v1\nitems[1].blocked := \"one\"\nresult := true if {{ data.policy.items[1].blocked with {spaced_target} as \"override\" }}"
    );
    assert!(
        engine
            .add_policy("spaced.rego".to_string(), spaced_policy)
            .is_err(),
        "WITH targets must reject spaced repeated unary indices while parsing"
    );
    Ok(())
}

#[test]
fn with_targets_accept_negative_and_scientific_indices_after_parse_errors() -> Result<()> {
    let mut engine = Engine::new();
    for (file, target) in [
        ("compact.rego", "data.policy.items[--1].blocked"),
        ("spaced.rego", "data.policy.items[- -1].blocked"),
    ] {
        let policy = format!(
            "package policy\nimport rego.v1\nitems[1].blocked := \"one\"\nresult := true if {{ data.policy.items[1].blocked with {target} as \"override\" }}"
        );
        assert!(
            engine.add_policy(file.to_string(), policy).is_err(),
            "invalid WITH target {target:?} must not prevent Engine reuse"
        );
    }

    engine.add_policy(
        "valid.rego".to_string(),
        r#"
        package policy
        import rego.v1
        items[-1].negative := "negative"
        items[1e1].exponent := "ten"
        negative_result := value if {
            value := data.policy.items[-1].negative with data.policy.items[-1].negative as "override-negative"
        }
        exponent_result := value if {
            value := data.policy.items[1e1].exponent with data.policy.items[1e1].exponent as "override-exponent"
        }
        "#
        .to_string(),
    )?;

    for _ in 0..2 {
        assert_eq!(
            engine.eval_rule("data.policy.negative_result".to_string())?,
            Value::from("override-negative")
        );
        assert_eq!(
            engine.eval_rule("data.policy.exponent_result".to_string())?,
            Value::from("override-exponent")
        );
        assert_eq!(
            engine.eval_rule("data.policy.items[-1].negative".to_string())?,
            Value::from("negative")
        );
        assert_eq!(
            engine.eval_rule("data.policy.items[1e1].exponent".to_string())?,
            Value::from("ten")
        );
    }

    Ok(())
}

#[test]
fn scalar_rule_prefixes_keep_boolean_and_null_keys_distinct_from_strings() -> Result<()> {
    let booleans = r#"
        package policy
        graph[true].blocked := "bool-true"
        graph[false].blocked := "bool-false"
        graph[null].blocked := "null"
    "#;
    let booleans_reversed = r#"
        package policy
        graph[null].blocked := "null"
        graph[false].blocked := "bool-false"
        graph[true].blocked := "bool-true"
    "#;
    let strings = r#"
        package policy
        graph["true"].blocked := "string-true"
        graph["false"].blocked := "string-false"
        graph["null"].blocked := "string-null"
    "#;
    let strings_reversed = r#"
        package policy
        graph["null"].blocked := "string-null"
        graph["false"].blocked := "string-false"
        graph["true"].blocked := "string-true"
    "#;
    let result = r#"
        package policy
        default allow := false
        result := {
            "true_bool": data.policy.graph[true].blocked,
            "true_string": data.policy.graph["true"].blocked,
            "false_bool": data.policy.graph[false].blocked,
            "false_string": data.policy.graph["false"].blocked,
            "null_bool": data.policy.graph[null].blocked,
            "null_string": data.policy.graph["null"].blocked,
            "default_allow": data.policy.allow,
        }
    "#;
    let expected = Value::from_json_str(
        r#"{
            "true_bool": "bool-true",
            "true_string": "string-true",
            "false_bool": "bool-false",
            "false_string": "string-false",
            "null_bool": "null",
            "null_string": "string-null",
            "default_allow": false
        }"#,
    )?;

    for reverse in [false, true] {
        let mut engine = Engine::new();
        let modules = if reverse {
            [
                ("strings.rego", strings_reversed),
                ("booleans.rego", booleans_reversed),
                ("result.rego", result),
            ]
        } else {
            [
                ("booleans.rego", booleans),
                ("strings.rego", strings),
                ("result.rego", result),
            ]
        };
        for (name, source) in modules {
            engine.add_policy(name.to_string(), source.to_string())?;
        }

        assert_eq!(
            engine.eval_rule("data.policy.result".to_string())?,
            expected,
            "interpreter result with reverse={reverse}"
        );
        let query = engine.eval_query("data.policy.result".to_string(), false)?;
        assert_eq!(
            query.result[0].expressions[0].value, expected,
            "query result with reverse={reverse}"
        );

        let entrypoint: Rc<str> = "data.policy.result".into();
        let compiled = engine.compile_with_entrypoint(&entrypoint)?;
        for _ in 0..2 {
            assert_eq!(
                compiled.eval_with_input(Value::new_object())?,
                expected,
                "compiled result with reverse={reverse}"
            );
        }
    }

    Ok(())
}

#[test]
fn scalar_override_conflict_does_not_poison_boolean_rule_reuse() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "policy.rego".to_string(),
        r#"
        package policy
        graph[true].blocked := true
        graph["true"].blocked := false
        graph["true"].blocked := true
        "#
        .to_string(),
    )?;

    assert_eq!(
        engine.eval_rule("data.policy.graph[true].blocked".to_string())?,
        Value::Bool(true)
    );
    assert!(
        engine
            .eval_rule("data.policy.graph[\"true\"].blocked".to_string())
            .is_err(),
        "conflicting string rules should remain isolated under their string key"
    );
    assert_eq!(
        engine.eval_rule("data.policy.graph[true].blocked".to_string())?,
        Value::Bool(true),
        "a failed string-key evaluation must not poison the distinct boolean key"
    );

    Ok(())
}

#[test]
fn numeric_rule_paths_keep_typed_identity_for_terminal_and_nested_keys() -> Result<()> {
    let numbers = r#"
        package policy
        exact_exp[1e1] := "numeric-ten"
        exact_exp[10] := "numeric-ten"
        exact_exp["1e1"] := "string-exponent"
        exact_ten[10] := "numeric-ten"
        exact_ten["10"] := "string-ten"
        nested[1e1].blocked := "numeric-ten"
        nested["1e1"].blocked := "nested-string-exponent"
        nested[10].blocked := "numeric-ten"
        nested["10"].blocked := "nested-string-integer"
        nested[1].integer := "one-integer"
        nested[1.0].decimal := "one-decimal"
        nested["1"].string := "one-string"
        nested[-1].negative := "negative"
        nested[9007199254740993].precise := "high-precision"
    "#;
    let numbers_reversed = r#"
        package policy
        nested[9007199254740993].precise := "high-precision"
        nested[-1].negative := "negative"
        nested["1"].string := "one-string"
        nested[1.0].decimal := "one-decimal"
        nested[1].integer := "one-integer"
        nested["10"].blocked := "nested-string-integer"
        nested[10].blocked := "numeric-ten"
        nested["1e1"].blocked := "nested-string-exponent"
        nested[1e1].blocked := "numeric-ten"
        exact_ten["10"] := "string-ten"
        exact_ten[10] := "numeric-ten"
        exact_exp["1e1"] := "string-exponent"
        exact_exp[10] := "numeric-ten"
        exact_exp[1e1] := "numeric-ten"
    "#;
    let result = r#"
        package policy
        default allow := false
        result := {
            "exact_exponent": data.policy.exact_exp[1e1],
            "exact_string_exponent": data.policy.exact_exp["1e1"],
            "exact_integer": data.policy.exact_ten[10],
            "exact_string_integer": data.policy.exact_ten["10"],
            "runtime_exponent": data.policy.exact_exp[input.exponent],
            "runtime_integer": data.policy.exact_ten[input.integer],
            "nested_exponent": data.policy.nested[1e1].blocked,
            "nested_string_exponent": data.policy.nested["1e1"].blocked,
            "nested_integer": data.policy.nested[10].blocked,
            "nested_string_integer": data.policy.nested["10"].blocked,
            "nested_one_integer": data.policy.nested[1].integer,
            "nested_one_decimal": data.policy.nested[1.0].decimal,
            "nested_one_string": data.policy.nested["1"].string,
            "runtime_one_integer": data.policy.nested[input.one].integer,
            "runtime_one_decimal": data.policy.nested[input.one_decimal].decimal,
            "negative": data.policy.nested[-1].negative,
            "high_precision": data.policy.nested[9007199254740993].precise,
            "default_allow": data.policy.allow,
        }
    "#;
    let input = Value::from_json_str(r#"{"exponent":1e1,"integer":10,"one":1,"one_decimal":1.0}"#)?;

    for reverse in [false, true] {
        let mut engine = Engine::new();
        let number_module = if reverse { numbers_reversed } else { numbers };
        for (name, source) in [("numbers.rego", number_module), ("result.rego", result)] {
            engine.add_policy(name.to_string(), source.to_string())?;
        }
        engine.set_input(input.clone());

        let expected = Value::from_json_str(
            r#"{
                "exact_exponent": "numeric-ten",
                "exact_string_exponent": "string-exponent",
                "exact_integer": "numeric-ten",
                "exact_string_integer": "string-ten",
                "runtime_exponent": "numeric-ten",
                "runtime_integer": "numeric-ten",
                "nested_exponent": "numeric-ten",
                "nested_string_exponent": "nested-string-exponent",
                "nested_integer": "numeric-ten",
                "nested_string_integer": "nested-string-integer",
                "nested_one_integer": "one-integer",
                "nested_one_decimal": "one-decimal",
                "nested_one_string": "one-string",
                "runtime_one_integer": "one-integer",
                "runtime_one_decimal": "one-decimal",
                "negative": "negative",
                "high_precision": "high-precision",
                "default_allow": false
            }"#,
        )?;

        assert_eq!(
            engine.eval_rule("data.policy.result".to_string())?,
            expected,
            "interpreter result with reverse={reverse}"
        );
        let query = engine.eval_query("data.policy.result".to_string(), false)?;
        assert_eq!(
            query.result[0].expressions[0].value, expected,
            "query result with reverse={reverse}"
        );

        let entrypoint: Rc<str> = "data.policy.result".into();
        let compiled = engine.compile_with_entrypoint(&entrypoint)?;
        for _ in 0..2 {
            assert_eq!(
                compiled.eval_with_input(input.clone())?,
                expected,
                "compiled result with reverse={reverse}"
            );
        }
    }

    Ok(())
}

#[test]
fn with_string_override_does_not_suppress_numeric_rule() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "policy.rego".to_string(),
        r#"
        package policy
        items[1].blocked := true
        default allow := true
        allow := false if {
            data.policy.items[1].blocked
                with data.policy.items["1"] as {"blocked": false}
        }
        "#
        .to_string(),
    )?;
    let entrypoint: Rc<str> = "data.policy.allow".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;

    assert_eq!(
        engine.eval_rule("data.policy.allow".to_string())?,
        Value::Bool(false)
    );
    assert_eq!(
        compiled.eval_with_input(Value::new_object())?,
        Value::Bool(false)
    );

    Ok(())
}

#[test]
fn nested_boolean_with_keeps_string_rule_available_and_reuses_engine() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "policy.rego".to_string(),
        r#"
        package policy
        import rego.v1
        graph[true].blocked := "boolean-rule"
        graph["true"].blocked := "string-rule"
        lookup := data.policy.graph["true"].blocked if {
            data.policy.graph["true"].blocked with input.enabled as true
        }
        result := data.policy.lookup if {
            data.policy.lookup with data.policy.graph[true] as {"blocked": "override"}
        }
        failing_lookup := data.policy.graph["true"].blocked if {
            data.policy.graph["true"].blocked with input.enabled as (1 / 0)
        }
        failing_result := data.policy.failing_lookup if {
            data.policy.failing_lookup with data.policy.graph[true] as {"blocked": "override"}
        }
        "#
        .to_string(),
    )?;

    assert!(
        engine
            .eval_rule("data.policy.failing_result".to_string())
            .is_err(),
        "the nested WITH arithmetic error should be returned"
    );
    for _ in 0..2 {
        assert_eq!(
            engine.eval_rule("data.policy.result".to_string())?,
            Value::from("string-rule"),
            "a nested WITH must not mistake a boolean path component for an override marker"
        );
    }

    Ok(())
}

#[test]
fn namespace_literal_dot_rule_path_uses_bracketed_component() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "namespace.rego".to_string(),
        r#"
        package graph.defUniqueName["1.0.0"]

        default deny := false
        deny := true if { input.blocked == true }
        "#
        .to_string(),
    )?;
    let path = "data.graph.defUniqueName[\"1.0.0\"].deny";
    let entrypoint: Rc<str> = path.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;

    let inputs = [
        (Value::from_json_str(r#"{"blocked":true}"#)?, true),
        (Value::from_json_str(r#"{"blocked":false}"#)?, false),
        (Value::new_object(), false),
        (Value::Null, false),
        (Value::Undefined, false),
    ];

    for (input, expected) in inputs {
        engine.set_input(input.clone());
        assert_eq!(engine.eval_rule(path.to_string())?, Value::Bool(expected));
        assert_eq!(
            compiled.eval_with_input(input.clone())?,
            Value::Bool(expected)
        );

        let query = engine.eval_query(path.to_string(), false)?;
        assert_eq!(query.result[0].expressions[0].value, Value::Bool(expected));
        let data = engine.eval_query("data".to_string(), false)?;
        let expected_data = Value::from_json_str(&format!(
            r#"{{"graph":{{"defUniqueName":{{"1.0.0":{{"deny":{expected}}}}}}}}}"#
        ))?;
        assert_eq!(data.result[0].expressions[0].value, expected_data);
    }

    Ok(())
}

#[test]
fn namespace_literal_dot_package_metadata_preserves_legacy_dot_join() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy(
        "namespace.rego".to_string(),
        r#"package graph.defUniqueName["1.0.0"]
           value := 1"#
            .to_string(),
    )?;
    let second_package = engine.add_policy(
        "second.rego".to_string(),
        "package second\nvalue := 2".to_string(),
    )?;

    assert_eq!(package, "data.graph.defUniqueName.1.0.0");
    assert_eq!(second_package, "data.second");
    assert_eq!(
        engine.get_packages()?,
        vec!["data.graph.defUniqueName.1.0.0", "data.second"]
    );
    let path = r#"data.graph.defUniqueName["1.0.0"].value"#;
    let compiled = engine.compile_with_entrypoint(&path.into())?;
    for _ in 0..2 {
        assert_eq!(engine.eval_rule(path.to_string())?, Value::from(1));
        assert_eq!(
            compiled.eval_with_input(Value::new_object())?,
            Value::from(1)
        );
    }

    Ok(())
}

#[test]
fn namespace_escaped_literal_component_metadata_preserves_escape_spelling() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy(
        "escaped.rego".to_string(),
        r#"package graph["a\".b"]
           value := 1"#
            .to_string(),
    )?;

    assert_eq!(package, r#"data.graph.a\".b"#);
    let path = r#"data.graph["a\".b"].value"#;
    let compiled = engine.compile_with_entrypoint(&path.into())?;
    for _ in 0..2 {
        assert_eq!(engine.eval_rule(path.to_string())?, Value::from(1));
        assert_eq!(
            compiled.eval_with_input(Value::new_object())?,
            Value::from(1)
        );
    }

    Ok(())
}

#[test]
fn namespace_bracketed_identifier_path_is_equivalent_to_dotted_path() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "identifier.rego".to_string(),
        "package graph.defUniqueName\nvalue := true".to_string(),
    )?;

    assert_eq!(
        engine.eval_rule("data.graph[\"defUniqueName\"].value".to_string())?,
        Value::Bool(true)
    );
    Ok(())
}

#[test]
fn namespace_bracketed_and_dotted_identifiers_share_legacy_metadata_projection() -> Result<()> {
    let mut bracketed = Engine::new();
    let package = bracketed.add_policy(
        "bracketed-identifier.rego".to_string(),
        "package graph[\"defUniqueName\"]\nvalue := true".to_string(),
    )?;
    assert_eq!(package, "data.graph.defUniqueName");
    assert_eq!(bracketed.get_packages()?, vec!["data.graph.defUniqueName"]);
    assert_eq!(
        bracketed.eval_rule(r#"data.graph["defUniqueName"].value"#.to_string())?,
        Value::Bool(true)
    );

    let mut dotted = Engine::new();
    let package = dotted.add_policy(
        "dotted-identifier.rego".to_string(),
        "package graph.defUniqueName\nvalue := true".to_string(),
    )?;
    assert_eq!(package, "data.graph.defUniqueName");
    assert_eq!(bracketed.get_packages()?, dotted.get_packages()?);
    assert_eq!(dotted.get_packages()?, vec!["data.graph.defUniqueName"]);
    assert_eq!(
        dotted.eval_rule(r#"data.graph["defUniqueName"].value"#.to_string())?,
        Value::Bool(true)
    );

    Ok(())
}

#[test]
#[cfg(feature = "std")]
fn namespace_file_package_metadata_preserves_legacy_source_spelling() -> Result<()> {
    let mut engine = Engine::new();
    let package =
        engine.add_policy_from_file("tests/engine/fixtures/legacy_package_projection.rego")?;

    assert_eq!(package, "data.graph.defUniqueName.1.0.0");
    assert_eq!(
        engine.get_packages()?,
        vec!["data.graph.defUniqueName.1.0.0"]
    );
    #[cfg(feature = "azure_policy")]
    {
        let package_names = engine.get_policy_package_names()?;
        assert_eq!(package_names.len(), 1);
        assert_eq!(package_names[0].package_name, "graph.defUniqueName.1.0.0");
        assert_eq!(
            package_names[0].source_file,
            "tests/engine/fixtures/legacy_package_projection.rego"
        );
    }

    let path = r#"data.graph.defUniqueName["1.0.0"].value"#;
    let compiled = engine.compile_with_entrypoint(&path.into())?;
    for _ in 0..2 {
        assert_eq!(engine.eval_rule(path.to_string())?, Value::from(23));
        assert_eq!(
            compiled.eval_with_input(Value::new_object())?,
            Value::from(23)
        );
    }

    Ok(())
}

#[test]
fn namespace_escaped_package_materializes_only_the_decoded_key() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "escaped.rego".to_string(),
        r#"package graph["a\".b"]
           value := 7"#
            .to_string(),
    )?;

    assert_eq!(
        engine.eval_modules(false)?,
        Value::from_json_str(r#"{"graph":{"a\".b":{"value":7}}}"#)?
    );
    Ok(())
}

#[test]
fn namespace_escaped_function_projection_uses_decoded_package_components() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "escaped.rego".to_string(),
        r#"package graph["a\".b"]
           value() := 7"#
            .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"package consumer
           import data.graph["a\".b"] as escaped
           result := escaped.value"#
            .to_string(),
    )?;

    assert_eq!(
        engine.eval_rule("data.consumer.result".to_string())?,
        Value::from(7)
    );
    Ok(())
}

#[test]
fn namespace_escaped_empty_package_materializes_only_the_decoded_key() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "escaped.rego".to_string(),
        r#"package graph["a\".b"]"#.to_string(),
    )?;

    assert_eq!(
        engine.eval_modules(false)?,
        Value::from_json_str(r#"{"graph":{"a\".b":{}}}"#)?
    );
    Ok(())
}

#[test]
fn long_registered_entrypoint_and_bracketed_identifier_compile() -> Result<()> {
    let package_component = "g".repeat(987);
    let package_path = format!("graph.{package_component}");
    let rule_name = format!("value_{}", "r".repeat(57));
    let canonical_path = format!("data.{package_path}.{rule_name}");
    #[cfg(feature = "rvm")]
    let bracketed_path = format!("data[\"graph\"][\"{package_component}\"][\"{rule_name}\"]");
    assert!(canonical_path.len() > 1024);

    let mut engine = Engine::new();
    engine.add_policy(
        "long.rego".to_string(),
        format!("package {package_path}\n{rule_name} := 7"),
    )?;

    let compiled = engine.compile_with_entrypoint(&canonical_path.into())?;
    assert_eq!(compiled.eval_with_input(Value::Null)?, Value::from(7));

    #[cfg(feature = "rvm")]
    {
        let program = regorus::languages::rego::compiler::Compiler::compile_from_policy(
            &compiled,
            &[&bracketed_path],
        )?;
        let mut vm = regorus::rvm::vm::RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name(&bracketed_path)?,
            Value::from(7)
        );
        assert_eq!(vm.execute_entry_point_by_index(0)?, Value::from(7));
    }
    Ok(())
}

#[test]
fn wider_policy_column_limit_does_not_restrict_registered_entrypoints() -> Result<()> {
    use core::num::NonZeroU32;

    let package_component = "g".repeat(1300);
    let package_path = format!("graph.{package_component}");
    let rule_name = format!("value_{}", "r".repeat(57));
    let canonical_path = format!("data.{package_path}.{rule_name}");
    #[cfg(feature = "rvm")]
    let bracketed_path = format!("data[\"graph\"][\"{package_component}\"][\"{rule_name}\"]");

    let mut engine = Engine::new();
    engine.set_policy_length_config(regorus::utils::limits::PolicyLengthConfig {
        max_col: NonZeroU32::new(2048).expect("non-zero column limit"),
        ..Default::default()
    });
    engine.add_policy(
        "long.rego".to_string(),
        format!("package {package_path}\n{rule_name} := 7"),
    )?;

    let compiled = engine.compile_with_entrypoint(&canonical_path.into())?;
    assert_eq!(compiled.eval_with_input(Value::Null)?, Value::from(7));

    #[cfg(feature = "rvm")]
    {
        let program = regorus::languages::rego::compiler::Compiler::compile_from_policy(
            &compiled,
            &[&bracketed_path],
        )?;
        let mut vm = regorus::rvm::vm::RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name(&bracketed_path)?,
            Value::from(7)
        );
    }
    Ok(())
}

#[test]
fn namespace_rule_without_default_remains_undefined() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "no-default.rego".to_string(),
        r#"
        package graph.defUniqueName["1.0.0"]
        deny := true if { input.blocked == true }
        "#
        .to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"blocked":false}"#)?);

    assert_eq!(
        engine.eval_rule("data.graph.defUniqueName[\"1.0.0\"].deny".to_string())?,
        Value::Undefined
    );
    Ok(())
}

#[test]
fn namespace_invalid_and_missing_rule_paths_keep_the_existing_error() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "namespace.rego".to_string(),
        r#"
        package graph["1.0.0"]
        deny := true
        "#
        .to_string(),
    )?;

    for path in [
        "data.graph[1.0.0].deny",
        "data.graph[\"1.0.1\"].deny",
        "data.graph[\"1.0.0\"].deny trailing",
    ] {
        let error = engine.eval_rule(path.to_string()).unwrap_err();
        assert_eq!(error.to_string(), "not a valid rule path");
    }
    Ok(())
}

#[test]
fn dynamic_data_root_lookup_does_not_evaluate_unrelated_modules() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := data[input.namespace].value
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "policy.rego".to_string(),
        r#"
        package policy
        result := data.framework.result
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        r#"
        package target
        value := 7
        "#
        .to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, Value::from(7));

    assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::from(7));
    Ok(())
}

#[test]
fn dynamic_namespace_defaults_follow_ordinary_rules_across_file_orders() -> Result<()> {
    for default_first in [true, false] {
        let mut engine = Engine::new();
        engine.add_policy(
            "framework.rego".to_string(),
            r#"
            package framework
            default allow := true
            allow := false if {
                cfg := data[input.namespace]
                cfg.blocked
            }
            "#
            .to_string(),
        )?;

        let default_policy = "package target\ndefault blocked := false".to_string();
        let ordinary_policy = "package target\nblocked := true".to_string();
        if default_first {
            engine.add_policy("default.rego".to_string(), default_policy)?;
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
        } else {
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
            engine.add_policy("default.rego".to_string(), default_policy)?;
        }
        engine.add_policy(
            "unrelated.rego".to_string(),
            "package unrelated\nfirst := second\nsecond := first".to_string(),
        )?;
        engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

        let entrypoint: Rc<str> = "data.framework.allow".into();
        let compiled = engine.compile_with_entrypoint(&entrypoint)?;
        let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
        assert_eq!(compiled.eval_with_input(input)?, Value::Bool(false));
        assert_eq!(
            engine.eval_rule(entrypoint.to_string())?,
            Value::Bool(false)
        );
        assert_eq!(
            engine.eval_rule("data.target.blocked".to_string())?,
            Value::Bool(true),
            "ordinary target rule must win regardless of file order"
        );
    }

    Ok(())
}

#[test]
fn dynamic_namespace_with_failure_restores_default_module_context() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        f(x) := x
        result := "primary" if { f(0) with f as data[input.namespace] } else := "fallback" if { true }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target-default.rego".to_string(),
        "package target\ndefault blocked := false".to_string(),
    )?;
    engine.add_policy(
        "target-true.rego".to_string(),
        "package target\nblocked := true".to_string(),
    )?;
    engine.add_policy(
        "target-false.rego".to_string(),
        "package target\nblocked := false".to_string(),
    )?;

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(
        compiled.eval_with_input(input.clone())?,
        Value::from("fallback")
    );

    engine.set_input(input);
    assert_eq!(
        engine.eval_rule(entrypoint.to_string())?,
        Value::from("fallback")
    );

    let followup = engine.eval_query("data.framework.f(7)".to_string(), false)?;
    assert_eq!(
        followup.result[0].expressions[0].value,
        Value::from(7),
        "a subsequent ordinary function call should remain usable on the same Engine"
    );

    Ok(())
}

#[test]
fn dynamic_namespace_default_applies_when_selected_ordinary_rule_is_undefined() -> Result<()> {
    for default_first in [true, false] {
        let mut engine = Engine::new();
        engine.add_policy(
            "framework.rego".to_string(),
            r#"
            package framework
            default allow := true
            allow := false if {
                cfg := data[input.namespace]
                cfg.blocked
            }
            "#
            .to_string(),
        )?;

        let default_policy = "package target\ndefault blocked := false".to_string();
        let ordinary_policy = "package target\nblocked := true if { input.enabled }".to_string();
        if default_first {
            engine.add_policy("default.rego".to_string(), default_policy)?;
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
        } else {
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
            engine.add_policy("default.rego".to_string(), default_policy)?;
        }
        engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

        let entrypoint: Rc<str> = "data.framework.allow".into();
        let compiled = engine.compile_with_entrypoint(&entrypoint)?;
        let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
        assert_eq!(compiled.eval_with_input(input)?, Value::Bool(true));
        assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::Bool(true));
        assert_eq!(
            engine.eval_rule("data.target.blocked".to_string())?,
            Value::Bool(false)
        );
    }

    Ok(())
}

#[test]
fn dynamic_namespace_ordinary_rule_without_default_stays_undefined() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        default allow := true
        allow := false if {
            cfg := data[input.namespace]
            cfg.blocked
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nblocked := true if { input.enabled }".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.allow".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, Value::Bool(true));
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::Bool(true));
    assert_eq!(
        engine.eval_rule("data.target.blocked".to_string())?,
        Value::Undefined
    );

    Ok(())
}

#[test]
fn nested_dynamic_data_lookup_does_not_prefetch_a_dotted_suffix_rule() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "dynamic.rego".to_string(),
        r#"
        package dynamic
        foo := {"bar": 7}
        bar := data.dynamic.value
        value := data.dynamic[input.first][input.second]
        "#
        .to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"first":"foo","second":"bar"}"#)?);

    assert_eq!(
        engine.eval_rule("data.dynamic.value".to_string())?,
        Value::from(7)
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_does_not_prefetch_a_trailing_sibling_rule() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nresult := data[input.namespace].value\nnested := data[input.namespace].nested"
            .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvalue := 7\nunrelated := data.framework.result".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested\nvalue := 11".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    assert_eq!(
        engine.eval_rule("data.framework.result".to_string())?,
        Value::from(7)
    );
    assert_eq!(
        engine.eval_rule("data.framework.nested".to_string())?,
        Value::from_json_str(r#"{"value":11}"#)?
    );
    Ok(())
}

#[test]
fn dynamic_namespace_nested_input_with_preserves_outer_data_override() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        outer := cfg if { cfg := inner with data.target as {"blocked": false} }
        inner := cfg if { cfg := data[input.namespace] with input as {"namespace": "target"} }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nblocked := true".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.outer".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"blocked":false}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    assert_eq!(
        engine.eval_rule("data.target.blocked".to_string())?,
        Value::Bool(true),
        "the data replacement must not persist after evaluation"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_materializes_a_trailing_subpackage_without_parent_siblings(
) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nconfig := data[input.namespace].nested".to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nunrelated := data.framework.config".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested\nvalue := 7".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.config".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"value":7}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_honors_with_replacement_of_selected_parent_data() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := cfg if {
            cfg := data[input.namespace] with data.target as {"blocked": false}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nblocked := true".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"blocked":false}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    assert_eq!(
        engine.eval_rule("data.target.blocked".to_string())?,
        Value::Bool(true),
        "the data replacement must not persist after evaluation"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_honors_with_data_root_replacement_and_restores_original_data(
) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := cfg if {
            cfg := data[input.namespace] with data as {"target": {"blocked": false}}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nblocked := true".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"blocked":false}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    assert_eq!(
        engine.eval_rule("data.target.blocked".to_string())?,
        Value::Bool(true),
        "the data-root replacement must not persist after evaluation"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_honors_with_data_root_replacement_without_materializing_modules(
) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := cfg if {
            cfg := data[input.namespace] with data as {}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvalue := 7".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, Value::Undefined);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::Undefined);
    assert_eq!(
        engine.eval_rule("data.target.value".to_string())?,
        Value::from(7),
        "the root replacement must be restored before ordinary evaluation"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_with_empty_parent_replacement_does_not_materialize_empty_child(
) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        config := cfg if {
            cfg := data[input.namespace].nested with data.target as {}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.config".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, Value::Undefined);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::Undefined);

    Ok(())
}

#[test]
fn dynamic_namespace_lookup_with_scalar_parent_replacement_does_not_materialize_child() -> Result<()>
{
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        config := cfg if {
            cfg := data[input.namespace].nested with data.target as 7
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested\nvalue := 7".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.config".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, Value::Undefined);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::Undefined);
    assert_eq!(
        engine.eval_rule("data.target.nested.value".to_string())?,
        Value::from(7),
        "the scalar replacement must be restored before ordinary evaluation"
    );

    Ok(())
}

#[test]
fn dynamic_namespace_prefetch_materializes_an_ordinary_empty_child_package() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        config := cfg.nested if {
            cfg := data[input.namespace]
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvalue := 7".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.config".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::new_object();
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);

    Ok(())
}

#[test]
fn dynamic_namespace_lookup_honors_with_parent_replacement_of_default_rule() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := cfg if {
            cfg := data[input.namespace] with data.target as {"blocked": false}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\ndefault blocked := true".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"blocked":false}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    assert_eq!(
        engine.eval_rule("data.target.blocked".to_string())?,
        Value::Bool(true),
        "the default rule must remain unchanged after evaluation"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_honors_with_nested_parent_replacement() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        config := cfg if {
            cfg := data[input.namespace].nested with data.target as {"nested": {"value": 7}}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nunrelated := data.framework.config".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested\nvalue := 11".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.config".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"value":7}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    assert_eq!(
        engine.eval_rule("data.target.nested.value".to_string())?,
        Value::from(11),
        "the nested package must remain unchanged after evaluation"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_honors_with_exact_leaf_replacement() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := blocked if {
            blocked := data[input.namespace].blocked with data.target.blocked as false
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nblocked := true\nvalue := 7".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, Value::Bool(false));
    assert_eq!(
        engine.eval_rule(entrypoint.to_string())?,
        Value::Bool(false)
    );
    assert_eq!(
        engine.eval_rule("data.target.blocked".to_string())?,
        Value::Bool(true)
    );
    assert_eq!(
        engine.eval_rule("data.target.value".to_string())?,
        Value::from(7)
    );
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_with_literal_dot_override_preserves_sibling_identity() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        result := config if {
            config := data.graph[input.namespace] with data.graph["a.b"] as {"value": 7}
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "literal.rego".to_string(),
        "package graph[\"a.b\"]\nvalue := 11".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package graph.a.b\nvalue := 13".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"a.b"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"a.b"}"#)?;
    let expected = Value::from_json_str(r#"{"value":7}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    assert_eq!(
        engine.eval_rule(r#"data.graph["a.b"].value"#.to_string())?,
        Value::from(11),
        "the literal-dot override must be restored"
    );
    assert_eq!(
        engine.eval_rule("data.graph.a.b.value".to_string())?,
        Value::from(13),
        "the dotted sibling must not be marked as part of the override"
    );
    Ok(())
}

#[test]
fn dynamic_namespace_prefetch_merges_initial_data_with_virtual_children() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_data(Value::from_json_str(r#"{"target":{"existing":1}}"#)?)?;
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nresult := data[input.namespace]".to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvirtual := 7".to_string(),
    )?;
    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);

    let entrypoint: Rc<str> = "data.framework.result".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"existing":1,"virtual":7}"#)?;
    assert_eq!(compiled.eval_with_input(input)?, expected);
    assert_eq!(engine.eval_rule(entrypoint.to_string())?, expected);
    Ok(())
}

#[test]
fn dynamic_namespace_package_prefetch_evaluates_only_the_selected_package() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_extension(
        "unrelated_failure".to_string(),
        0,
        Box::new(|_| Err(anyhow::anyhow!("unrelated module was evaluated"))),
    )?;
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        default allow := true
        allow := false if {
            cfg := data[input.namespace]
            cfg.blocked
        }
        config := data[input.namespace]
        literal_config := data.graph[input.namespace]
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nblocked := true".to_string(),
    )?;
    engine.add_policy(
        "unblocked.rego".to_string(),
        "package unblocked\nvalue := 7".to_string(),
    )?;
    engine.add_policy(
        "literal.rego".to_string(),
        "package graph[\"target.v1\"]\nblocked := true".to_string(),
    )?;
    engine.add_policy(
        "unrelated.rego".to_string(),
        "package unrelated\nfailure := unrelated_failure()".to_string(),
    )?;

    let entrypoint: Rc<str> = "data.framework.allow".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let cases = [
        (
            Value::from_json_str(r#"{"namespace":"target"}"#)?,
            Value::Bool(false),
        ),
        (Value::new_object(), Value::Bool(true)),
        (Value::Undefined, Value::Bool(true)),
        (
            Value::from_json_str(r#"{"namespace":"unblocked"}"#)?,
            Value::Bool(true),
        ),
        (
            Value::from_json_str(r#"{"namespace":"nonexistent"}"#)?,
            Value::Bool(true),
        ),
        (
            Value::from_json_str(r#"{"namespace":"target"}"#)?,
            Value::Bool(false),
        ),
    ];

    for (input, expected) in cases {
        engine.set_input(input.clone());
        assert_eq!(
            engine.eval_rule(entrypoint.to_string())?,
            expected,
            "interpreter result for input {input:?}"
        );
        assert_eq!(
            compiled.eval_with_input(input)?,
            expected,
            "compiled interpreter result"
        );
    }

    engine.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);
    assert_eq!(
        engine.eval_rule("data.framework.config".to_string())?,
        Value::from_json_str(r#"{"blocked":true}"#)?
    );

    engine.set_input(Value::from_json_str(r#"{"namespace":"target.v1"}"#)?);
    assert_eq!(
        engine.eval_rule("data.framework.literal_config".to_string())?,
        Value::from_json_str(r#"{"blocked":true}"#)?
    );

    engine.set_input(Value::from_json_str(r#"{"namespace":"nonexistent"}"#)?);
    assert_eq!(
        engine.eval_rule("data.framework.config".to_string())?,
        Value::Undefined
    );

    Ok(())
}

#[cfg(feature = "std")]
#[test]
fn failed_with_modifier_application_restores_document_before_engine_reuse() -> Result<()> {
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };
    use std::time::Duration;

    use regorus::utils::limits::ExecutionTimerConfig;

    let replacement_reached = Arc::new(AtomicBool::new(false));
    let extension_reached = Arc::clone(&replacement_reached);
    let mut engine = Engine::new();
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvalue := 42".to_string(),
    )?;
    engine.add_policy(
        "test.rego".to_string(),
        r#"
        package test
        result := value if {
            value := data.target.value with data.target as slow_replacement()
        }
        later := value if {
            value := data.target.value with input.flag as true
        }
        "#
        .to_string(),
    )?;
    engine.add_extension(
        "slow_replacement".to_string(),
        0,
        Box::new(move |_| {
            extension_reached.store(true, Ordering::SeqCst);
            std::thread::sleep(Duration::from_secs(2));
            Value::from_json_str(r#"{"value":99}"#)
        }),
    )?;

    assert_eq!(
        engine.eval_rule("data.test.later".to_string())?,
        Value::from(42),
        "prepare the engine before starting the timer"
    );

    engine.set_execution_timer_config(ExecutionTimerConfig {
        limit: Duration::from_secs(1),
        check_interval: std::num::NonZeroU32::new(1).unwrap(),
    });
    let error = engine
        .eval_rule("data.test.result".to_string())
        .unwrap_err();
    assert!(
        error.to_string().contains("execution exceeded time limit"),
        "expected the descendant scan timer to fail, got {error:#}"
    );
    assert!(
        replacement_reached.load(Ordering::SeqCst),
        "the replacement extension must run before the timer expires"
    );

    engine.clear_execution_timer_config();
    let later_result = engine.eval_rule("data.test.later".to_string());
    assert!(
        matches!(&later_result, Ok(value) if value == &Value::from(42)),
        "failed modifier application must preserve original virtual data; got {later_result:?}"
    );

    Ok(())
}

#[test]
fn rule_path_component_limit_preserves_engine_behavior() -> Result<()> {
    let package_path = (0..30)
        .map(|index| format!("p{index}"))
        .collect::<Vec<_>>()
        .join(".");
    let mut engine = Engine::new();
    engine.add_policy(
        "deep.rego".to_string(),
        format!("package {package_path}\nvalue := 7"),
    )?;
    let remaining_package_path = package_path
        .split('.')
        .skip(1)
        .collect::<Vec<_>>()
        .join(".");
    let at_limit = format!("data[\"p0\"].{remaining_package_path}.value");
    assert_eq!(
        package_path.split('.').count(),
        30,
        "the policy package contributes 30 components"
    );
    assert_eq!(
        engine.eval_rule(at_limit.clone())?,
        Value::from(7),
        "a 32-component entrypoint remains valid"
    );
    let compiled = engine.compile_with_entrypoint(&at_limit.clone().into())?;
    assert_eq!(
        compiled.eval_with_input(Value::Null)?,
        Value::from(7),
        "the compiled interpreter accepts a 32-component entrypoint"
    );
    assert_eq!(
        engine
            .eval_rule(format!("{at_limit}.extra"))
            .unwrap_err()
            .to_string(),
        "not a valid rule path"
    );

    Ok(())
}

#[test]
fn bracketed_entrypoints_match_dotted_paths_at_supported_depths() -> Result<()> {
    for (package_component_count, rule_component_count) in [(31, 1), (32, 1), (32, 32)] {
        let package_components = (0..package_component_count)
            .map(|index| format!("p{index}"))
            .collect::<Vec<_>>();
        let rule_components = (0..rule_component_count)
            .map(|index| format!("r{index}"))
            .collect::<Vec<_>>();
        let package_path = package_components.join(".");
        let rule_path = rule_components.join(".");
        let dotted_path = format!("data.{package_path}.{rule_path}");
        let mut bracketed_path = String::from("data");
        for component in package_components.iter().chain(&rule_components) {
            bracketed_path.push_str(&format!("[\"{component}\"]"));
        }

        let mut engine = Engine::new();
        engine.add_policy(
            "deep.rego".to_string(),
            format!("package {package_path}\n{rule_path} := 7"),
        )?;

        let dotted_entrypoint: Rc<str> = dotted_path.clone().into();
        let compiled = engine.compile_with_entrypoint(&dotted_entrypoint)?;
        assert_eq!(compiled.eval_with_input(Value::Null)?, Value::from(7));
        assert_eq!(
            engine.eval_rule(dotted_path.clone())?,
            Value::from(7),
            "dotted path with {package_component_count} package and {rule_component_count} rule components"
        );

        let bracketed_entrypoint: Rc<str> = bracketed_path.clone().into();
        let bracketed_compiled = engine.compile_with_entrypoint(&bracketed_entrypoint)?;
        assert_eq!(
            bracketed_compiled.eval_with_input(Value::Null)?,
            Value::from(7)
        );
        for _ in 0..2 {
            assert_eq!(
                engine.eval_rule(bracketed_path.clone())?,
                Value::from(7),
                "bracketed path with {package_component_count} package and {rule_component_count} rule components"
            );
        }
    }

    Ok(())
}

#[test]
fn engine_rejects_huge_dotted_and_bracketed_rule_paths() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "stable.rego".to_string(),
        "package stable\nvalue := true".to_string(),
    )?;
    let long_dotted = format!("data{}", ".a".repeat(300_000));
    let long_bracketed = format!("data{}", r#"["a"]"#.repeat(180_000));
    for path in [long_dotted, long_bracketed] {
        assert!(path.len() < 1024 * 1024);
        assert_eq!(
            engine.eval_rule(path).unwrap_err().to_string(),
            "not a valid rule path"
        );
        assert_eq!(
            engine.eval_rule("data.stable.value".to_string())?,
            Value::Bool(true),
            "engine remains usable after rejecting a huge rule path"
        );
    }

    Ok(())
}

#[test]
fn extension() -> Result<()> {
    fn repeat(mut params: Vec<Value>) -> Result<Value> {
        match params.remove(0) {
            Value::String(s) => {
                let s = s.as_ref().to_owned();
                Ok(Value::from(s.clone() + &s))
            }
            _ => bail!("param must be string"),
        }
    }
    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"package test
               x = repeat("hello")
             "#
        .to_string(),
    )?;

    // Raises error since repeat is not defined.
    assert!(engine.eval_query("data.test.x".to_string(), false).is_err());

    // Register extension.
    engine.add_extension("repeat".to_string(), 1, Box::new(repeat))?;

    // Adding extension twice is error.
    assert!(engine
        .add_extension(
            "repeat".to_string(),
            1,
            Box::new(|_| { Ok(Value::Undefined) })
        )
        .is_err());

    let r = engine.eval_query("data.test.x".to_string(), false)?;
    assert_eq!(
        r.result[0].expressions[0].value.as_string()?.as_ref(),
        "hellohello"
    );

    Ok(())
}

#[test]
fn extension_with_state() -> Result<()> {
    #[derive(Clone)]
    struct Gen {
        n: i64,
    }

    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"package test
               x = gen()
        "#
        .to_string(),
    )?;

    let mut g = Box::new(Gen { n: 5 });
    engine.add_extension(
        "gen".to_string(),
        0,
        Box::new(move |_: Vec<Value>| {
            let v = Value::from(g.n);
            g.n += 1;
            Ok(v)
        }),
    )?;

    // First eval.
    let r = engine.eval_query("data.test.x".to_string(), false)?;
    assert_eq!(r.result[0].expressions[0].value.as_i64()?, 5);

    // Second eval will produce a new value since for each query, the
    // internal evaluation state of the interpreter is cleared.
    // This might change in the future.
    let r = engine.eval_query("data.test.x".to_string(), false)?;
    assert_eq!(r.result[0].expressions[0].value.as_i64()?, 6);

    // Clone the engine.
    // This should also clone the stateful extension.
    let mut engine1 = engine.clone();

    // Both the engines should produce the same value.
    let r = engine.eval_query("data.test.x".to_string(), false)?;
    let r1 = engine1.eval_query("data.test.x".to_string(), false)?;
    assert_eq!(
        r.result[0].expressions[0].value,
        r1.result[0].expressions[0].value
    );

    assert_eq!(r.result[0].expressions[0].value.as_i64()?, 7);

    Ok(())
}

#[test]
fn fresh_engine_evaluates_inline_comprehension_outputs_without_entrypoint_compile() -> Result<()> {
    let policy = r#"
        package test
        deny := {"result": true, "reasons": [v | some v in input.values]} if {
            count(input.values) > 0
        }
    "#;
    let expected = Value::from_json_str(r#"{"result":true,"reasons":[false,"x",false]}"#)?;

    let mut nonempty = Engine::new();
    nonempty.set_input(Value::from_json_str(r#"{"values":[false,"x",false]}"#)?);
    nonempty.add_policy("test.rego".to_string(), policy.to_string())?;
    assert_eq!(nonempty.eval_rule("data.test.deny".to_string())?, expected);
    let query = nonempty.eval_query("data.test.deny".to_string(), false)?;
    assert_eq!(query.result.len(), 1);
    assert_eq!(query.result[0].expressions[0].value, expected);

    let mut empty = Engine::new();
    empty.set_input(Value::from_json_str(r#"{"values":[]}"#)?);
    empty.add_policy("test.rego".to_string(), policy.to_string())?;
    assert_eq!(
        empty.eval_rule("data.test.deny".to_string())?,
        Value::Undefined
    );
    let query = empty.eval_query("data.test.deny".to_string(), false)?;
    assert!(query.result.is_empty());

    let mut missing = Engine::new();
    missing.add_policy("test.rego".to_string(), policy.to_string())?;
    assert_eq!(
        missing.eval_rule("data.test.deny".to_string())?,
        Value::Undefined
    );
    let query = missing.eval_query("data.test.deny".to_string(), false)?;
    assert!(query.result.is_empty());

    Ok(())
}

#[test]
fn eval_rule_schedules_unification_nested_output_capture() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"
            package test
            result := a if {
                a := [[v | some v in vals] | true]
                vals = [1, 2]
            }
        "#
        .to_string(),
    )?;

    assert_eq!(
        engine.eval_rule("data.test.result".to_string())?,
        Value::from_json_str("[[1,2]]")?
    );
    Ok(())
}

#[test]
fn eval_rule_rejects_forward_assignment_nested_output_capture() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"
            package test
            result := a if {
                a := [[v | some v in vals] | true]
                vals := [1, 2]
            }
        "#
        .to_string(),
    )?;

    let error = engine
        .eval_rule("data.test.result".to_string())
        .expect_err("forward assignment should remain unsafe");
    assert!(error
        .to_string()
        .contains("use of undefined variable `vals`"));
    Ok(())
}

#[test]
#[cfg(feature = "azure_policy")]
#[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
fn get_policy_package_names() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy(
        "testPolicy1".to_string(),
        r#"package test["1.0.0"]
               
                deny if {
                    1 == 2
                }
        "#
        .to_string(),
    )?;
    assert_eq!(package, "data.test.1.0.0");

    engine.add_policy(
        "testPolicy2".to_string(),
        r#"package test.nested.name
                deny if {
                    1 == 2
                }
        "#
        .to_string(),
    )?;

    let package_names = engine.get_policy_package_names()?;

    assert_eq!(2, package_names.len());
    assert_eq!("test.1.0.0", package_names[0].package_name);
    assert_eq!("testPolicy1", package_names[0].source_file);

    assert_eq!("test.nested.name", package_names[1].package_name);
    assert_eq!("testPolicy2", package_names[1].source_file);
    Ok(())
}

#[test]
#[cfg(feature = "azure_policy")]
#[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
fn get_policy_parameters() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "testPolicy1".to_string(),
        r#"package test
                default parameters.a = 5
                default parameters.b = { asdf: 10}

                parameters.c = 10

                deny if {
                    parameter.a == parameter.b.asdf
                }
        "#
        .to_string(),
    )?;

    engine.add_policy(
        "testPolicy2".to_string(),
        r#"package test
                default parameters = {
                    a: 5,
                    b: { asdf: 10 }
                }

                parameters.c = 5

                deny if {
                    parameters.a == parameters.b.asdf
                }
        "#
        .to_string(),
    )?;

    let parameters = engine.get_policy_parameters()?;
    // let ast = engine.get_ast_as_json()?;
    // println!("ast: {}", ast);
    // let parameters = Value::from_json_str(&result)?;

    assert_eq!(2, parameters.len());

    let test_policy1_parameters = &parameters[0];
    assert_eq!(2, test_policy1_parameters.parameters.len());
    assert_eq!("a", test_policy1_parameters.parameters[0].name);
    assert_eq!("b", test_policy1_parameters.parameters[1].name);

    // We expect parameters to be defined separately, so the second policy does not have any parameters
    let test_policy2_parameters = &parameters[1];
    assert_eq!(0, test_policy2_parameters.parameters.len());

    assert_eq!(1, test_policy2_parameters.modifiers.len());
    assert_eq!("c", test_policy2_parameters.modifiers[0].name);

    Ok(())
}

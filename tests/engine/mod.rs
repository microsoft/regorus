// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};
use regorus::*;

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
fn namespace_literal_dot_package_metadata_is_unambiguous() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy(
        "namespace.rego".to_string(),
        r#"package graph.defUniqueName["1.0.0"]"#.to_string(),
    )?;

    assert_eq!(package, "data.graph.defUniqueName[\"1.0.0\"]");
    assert_eq!(
        engine.get_packages()?,
        vec!["data.graph.defUniqueName[\"1.0.0\"]"]
    );

    Ok(())
}

#[test]
fn namespace_escaped_literal_component_uses_json_path_escaping() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy(
        "escaped.rego".to_string(),
        r#"package graph["a\".b"]
           value := 1"#
            .to_string(),
    )?;

    assert_eq!(package, r#"data.graph["a\".b"]"#);
    assert_eq!(
        engine.eval_rule(r#"data.graph["a\".b"].value"#.to_string())?,
        Value::from(1)
    );

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

    assert_eq!(
        engine.eval_rule("data.framework.result".to_string())?,
        Value::from(7)
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
#[cfg(feature = "azure_policy")]
#[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
fn get_policy_package_names() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "testPolicy1".to_string(),
        r#"package test
               
                deny if {
                    1 == 2
                }
        "#
        .to_string(),
    )?;

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
    assert_eq!("test", package_names[0].package_name);
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

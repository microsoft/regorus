// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};
use regorus::*;

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
fn policy_package_override_is_used_for_evaluation() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy_with_package(
        "source.rego".to_string(),
        r#"package original.authz

            default allowed = false
            is_admin(user) := user == "admin"
            allowed if is_admin(input.user)
        "#
        .to_string(),
        "tenant.authz".to_string(),
    )?;

    assert_eq!("data.tenant.authz", package);
    assert_eq!(vec!["data.tenant.authz"], engine.get_packages()?);
    let source = engine.get_policies()?;
    assert_eq!("source.rego", source[0].get_path());
    assert!(source[0]
        .get_contents()
        .starts_with("package original.authz"));
    let sources_json = engine.get_policies_as_json()?;
    assert!(sources_json.contains("package original.authz"));
    assert!(!sources_json.contains("tenant.authz"));

    engine.set_input(Value::from_json_str(r#"{"user":"admin"}"#)?);
    let result = engine.eval_query("data.tenant.authz.allowed".to_string(), false)?;
    assert_eq!(Value::from(true), result.result[0].expressions[0].value);

    Ok(())
}

#[test]
fn policy_package_override_uses_limits_for_policy_source_not_synthetic_package() -> Result<()> {
    let mut engine = Engine::new();
    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: core::num::NonZeroU32::new(24)
            .ok_or_else(|| anyhow::anyhow!("invalid test limit"))?,
        max_file_bytes: core::num::NonZeroUsize::new(24)
            .ok_or_else(|| anyhow::anyhow!("invalid test limit"))?,
        max_lines: core::num::NonZeroUsize::new(20)
            .ok_or_else(|| anyhow::anyhow!("invalid test limit"))?,
    });

    let package = engine.add_policy_with_package(
        "source.rego".to_string(),
        "package a\nallow := true".to_string(),
        "tenant.authorization".to_string(),
    )?;

    assert_eq!("data.tenant.authorization", package);
    assert_eq!(
        Value::from(true),
        engine.eval_rule("data.tenant.authorization.allow".into())?
    );

    assert!(engine
        .add_policy_with_package(
            "over-limit.rego".to_string(),
            "package a\nallow := true\n\n".to_string(),
            "tenant.other".to_string(),
        )
        .is_err());
    assert_eq!(vec!["data.tenant.authorization"], engine.get_packages()?);

    Ok(())
}

#[test]
fn legacy_bracketed_package_segments_remain_evaluable() -> Result<()> {
    let mut engine = Engine::new();
    let package = engine.add_policy(
        "bracketed.rego".to_string(),
        "package team[\"authz\"]\nallow := true".to_string(),
    )?;

    assert_eq!("data.team.authz", package);
    assert_eq!(
        Value::from(true),
        engine.eval_rule("data.team.authz.allow".into())?
    );
    Ok(())
}

#[test]
fn invalid_package_overrides_leave_existing_engine_state_unchanged() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "original.rego".to_string(),
        "package original\ndefined := true".to_string(),
    )?;
    assert_eq!(
        Value::from(true),
        engine
            .eval_query("data.original.defined".to_string(), false)?
            .result[0]
            .expressions[0]
            .value
    );

    for invalid_package in [
        "",
        "data.tenant.authz",
        "tenant .authz",
        "tenant.authz # comment",
        "tenant.authz\nallow := true",
        "package tenant.authz",
        "tenant..authz",
        "tenant\0authz",
    ] {
        assert!(
            engine
                .add_policy_with_package(
                    "invalid.rego".to_string(),
                    "package invalid\nvalue := 1".to_string(),
                    invalid_package.to_string(),
                )
                .is_err(),
            "accepted malformed package {invalid_package:?}"
        );
    }

    assert!(engine
        .add_policy_with_package(
            "broken.rego".to_string(),
            "package broken\nvalue := {".to_string(),
            "tenant.authz".to_string(),
        )
        .is_err());

    assert_eq!(vec!["data.original"], engine.get_packages()?);
    assert_eq!(1, engine.get_policies()?.len());
    assert_eq!(
        Value::from(true),
        engine
            .eval_query("data.original.defined".to_string(), false)?
            .result[0]
            .expressions[0]
            .value
    );
    Ok(())
}

#[test]
fn adding_overridden_policy_after_evaluation_updates_only_that_engine() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "first.rego".to_string(),
        "package first\nvalue := 1".to_string(),
    )?;
    assert_eq!(
        Value::from(1),
        engine
            .eval_query("data.first.value".to_string(), false)?
            .result[0]
            .expressions[0]
            .value
    );
    let mut clone = engine.clone();

    engine.add_policy_with_package(
        "source.rego".to_string(),
        "package original\nanswer := 2".to_string(),
        "tenant.authz".to_string(),
    )?;

    assert_eq!(
        Value::from(2),
        engine
            .eval_query("data.tenant.authz.answer".to_string(), false)?
            .result[0]
            .expressions[0]
            .value
    );
    assert_eq!(
        vec!["data.first", "data.tenant.authz"],
        engine.get_packages()?
    );
    assert_eq!(vec!["data.first"], clone.get_packages()?);
    assert!(clone
        .eval_query("data.tenant.authz.answer".to_string(), false)?
        .result
        .is_empty());

    Ok(())
}

#[test]
fn modules_with_the_same_effective_package_merge_distinct_rules() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy_with_package(
        "first.rego".to_string(),
        "package first\none := 1".to_string(),
        "tenant.authz".to_string(),
    )?;
    engine.add_policy_with_package(
        "second.rego".to_string(),
        "package second\ntwo := 2".to_string(),
        "tenant.authz".to_string(),
    )?;

    assert_eq!(
        Value::from(1),
        engine.eval_rule("data.tenant.authz.one".into())?
    );
    assert_eq!(
        Value::from(2),
        engine.eval_rule("data.tenant.authz.two".into())?
    );
    Ok(())
}

#[test]
fn colliding_rules_in_overridden_packages_keep_existing_conflict_behavior() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy_with_package(
        "first.rego".to_string(),
        "package first\nvalue := 1".to_string(),
        "tenant.authz".to_string(),
    )?;
    engine.add_policy_with_package(
        "second.rego".to_string(),
        "package second\nvalue := 2".to_string(),
        "tenant.authz".to_string(),
    )?;

    let error = engine
        .eval_rule("data.tenant.authz.value".into())
        .expect_err("different complete-rule values must conflict");
    assert!(error
        .to_string()
        .contains("rule conflicts with rule at first.rego:2:1"));
    Ok(())
}

#[test]
fn absolute_references_and_imports_are_not_rewritten() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_data(Value::from_json_str(r#"{"original":{"base":100}}"#)?)?;
    engine.add_policy_with_package(
        "moved.rego".to_string(),
        "package original\nbase := 1\nabsolute := data.original.base".to_string(),
        "tenant.authz".to_string(),
    )?;
    engine.add_policy_with_package(
        "helpers.rego".to_string(),
        "package original.helpers\nvalue := 7".to_string(),
        "tenant.authz.helpers".to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        "package consumer\nimport data.original.helpers\nresult := helpers.value".to_string(),
    )?;

    assert_eq!(
        Value::from(100),
        engine.eval_rule("data.tenant.authz.absolute".into())?
    );
    assert_eq!(
        Value::Undefined,
        engine.eval_rule("data.consumer.result".into())?
    );
    Ok(())
}

#[test]
#[cfg(feature = "ast")]
fn ast_json_omits_unset_effective_package_for_legacy_output() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy("legacy.rego".to_string(), "package legacy".to_string())?;

    let ast = engine.get_ast_as_json()?;
    assert!(
        !ast.contains("\"effective_package\""),
        "legacy AST output should omit unset override metadata"
    );
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
fn get_policy_package_names_uses_effective_package() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy_with_package(
        "source.rego".to_string(),
        "package original\nallow := true".to_string(),
        "tenant.authz".to_string(),
    )?;

    let package_names = engine.get_policy_package_names()?;
    assert_eq!(1, package_names.len());
    assert_eq!("tenant.authz", package_names[0].package_name);
    assert_eq!("source.rego", package_names[0].source_file);
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

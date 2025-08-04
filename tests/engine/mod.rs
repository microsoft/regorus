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

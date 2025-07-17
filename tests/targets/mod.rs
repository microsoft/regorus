// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::*;

use anyhow::{anyhow, bail, Result};
use serde::{Deserialize, Serialize};
use test_generator::test_resources;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    data: Option<Value>,
    input: Option<Value>,
    modules: Vec<String>,
    note: String,
    rule: Option<String>,
    want_result: Option<Value>,
    skip: Option<bool>,
    want_error: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    // Load all targets
    let targets_dir = "tests/targets/targets";
    let entries = std::fs::read_dir(&targets_dir)
        .or_else(|e| bail!("failed to read targets directory {targets_dir}.\n{e}"))?;
    // Loop through each entry in the bundle folder.
    for entry in entries {
        let entry = entry.or_else(|e| bail!("failed to unwrap entry. {e}"))?;
        let path = entry.path();

        // Process only .json files.
        match (path.is_file(), path.extension()) {
            (true, Some(ext)) if ext == "json" => {}
            _ => continue,
        }

        let target_json = std::fs::read_to_string(&entry.path().display().to_string())
            .map_err(|e| anyhow!("could not read {}. {e}", path.display()))?;
        regorus::add_target(&target_json)
            .map_err(|e| anyhow!("Failed to add target {} {e}", path.display()))?;
    }

    std::eprintln!("running {file}");

    for case in test.cases {
        std::print!("case {} ", case.note);
        if case.skip == Some(true) {
            std::println!("skipped");
            continue;
        }

        let mut engine: Engine = Engine::new();
        engine.set_gather_prints(true);

        #[cfg(feature = "coverage")]
        engine.set_enable_coverage(true);

        for (idx, rego) in case.modules.iter().enumerate() {
            engine.add_policy(format!("rego_{idx}"), rego.clone())?;
        }

        if let Some(data) = case.data {
            engine.add_data(data.clone())?;
        }

        if let Some(input) = case.input {
            engine.set_input(input.clone());
        }

        if let Err(actual) = engine.validate() {
            match case.want_error {
                None => {
                    panic!("validate raise `{}` unexpectedly.", actual.to_string());
                }
                Some(expected) => {
                    if !actual.to_string().contains(&expected) {
                        panic!("`{actual}` does not contain `{expected}`");
                    }
                }
            }
        } else if let Some(rule) = &case.rule {
            let r = engine.eval_rule(rule.clone());
            match (case.want_result, case.want_error, r) {
                (Some(expected), _, Ok(actual)) => {
                    assert_eq!(expected, actual);
                }
                (_, Some(expected), Err(actual)) => {
                    if !actual.to_string().contains(&expected) {
                        panic!("`{actual}` does not contain `{expected}`");
                    }
                }
                (want_result, want_error, actual) => {
                    panic!(
                    "failure: want_result = `{want_result:?}` want_error = `{want_error:?}` actual={actual:?}",

                );
                }
            }
        }

        std::eprintln!("passed");
    }

    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    #[cfg(not(feature = "rego-extensions"))]
    if file.contains("rego-extensions") {
        return Ok(());
    }

    match yaml_test_impl(file) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{e}");
        }
    }
}

#[test_resources("tests/targets/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

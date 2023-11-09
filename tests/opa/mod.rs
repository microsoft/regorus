// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::*;

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::Result;
use walkdir::WalkDir;

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    data: Option<Value>,
    input: Option<Value>,
    modules: Option<Vec<String>>,
    note: String,
    query: String,
    sort_bindings: Option<bool>,
    want_result: Option<Value>,
    skip: Option<bool>,
    error: Option<String>,
    traces: Option<bool>,
    want_error: Option<String>,
    want_error_code: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn eval_test_case(case: &TestCase) -> Result<Value> {
    let mut engine = Engine::new();

    if let Some(data) = &case.data {
        engine.add_data(data.clone())?;
    }
    if let Some(input) = &case.input {
        engine.set_input(input.clone());
    }
    if let Some(modules) = &case.modules {
        for (idx, rego) in modules.iter().enumerate() {
            engine.add_policy(format!("rego{idx}.rego"), rego.clone())?;
        }
    }
    let query_results = engine.eval_query(case.query.clone(), true)?;

    let mut values = vec![];
    for qr in query_results.result {
        values.push(if !qr.bindings.is_empty_object() {
            qr.bindings.clone()
        } else if let Some(v) = qr.expressions.last() {
            v["value"].clone()
        } else {
            Value::Undefined
        });
    }
    let result = Value::from_array(values);
    // Make result json compatible. (E.g: avoid sets).
    Value::from_json_str(&result.to_string())
}

#[test]
fn run_opa_tests() -> Result<()> {
    let opa_tests_dir = match std::env::var("OPA_TESTS_DIR") {
        Ok(v) => v,
        _ => {
            println!("OPA_TESTS_DIR environment vairable not defined.");
            return Ok(());
        }
    };
    dbg!(&opa_tests_dir);
    let tests_path = Path::new(&opa_tests_dir);
    let mut status = BTreeMap::<String, (u32, u32)>::new();
    let mut n = 0;
    for entry in WalkDir::new(&opa_tests_dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path_str = entry.path().to_string_lossy().to_string();
        let path = Path::new(&path_str);
        if !path.is_file() || !path_str.ends_with(".yaml") {
            continue;
        }

        let path_dir = path.strip_prefix(tests_path)?.parent().unwrap();

        let path_dir_str = path_dir.to_string_lossy().to_string();
        let entry = status.entry(path_dir_str).or_insert((0, 0));

        let yaml_str = std::fs::read_to_string(&path_str)?;
        let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

        for case in &test.cases {
            print!("{} ...", case.note);
            match (eval_test_case(case), &case.want_result) {
                (Ok(actual), Some(expected)) if &actual == expected => {
                    println!("passed");
                    entry.0 += 1;
                }
                (Err(_), None) if case.want_error.is_some() => {
                    // Expected failure.
                    println!("passed");
                    entry.0 += 1;
                }
                _ => {
                    let path = Path::new("target/opa").join(path_dir);
                    std::fs::create_dir_all(path.clone())?;

                    if let Some(data) = &case.data {
                        std::fs::write(
                            path.join(format!("data{n}.json")),
                            data.to_json_str()?.as_bytes(),
                        )?;
                    };
                    if let Some(input) = &case.input {
                        std::fs::write(
                            path.join(format!("input{n}.json")),
                            input.to_json_str()?.as_bytes(),
                        )?;
                    };

                    if let Some(modules) = &case.modules {
                        if modules.len() == 1 {
                            std::fs::write(
                                path.join(format!("rego{n}.rego")),
                                modules[0].as_bytes(),
                            )?;
                        } else {
                            for (i, m) in modules.iter().enumerate() {
                                std::fs::write(
                                    path.join(format!("rego{n}_{i}.json")),
                                    m.as_bytes(),
                                )?;
                            }
                        }
                    }

                    println!("failed");
                    entry.1 += 1;
                    n += 1;
                    continue;
                }
            };
        }
    }

    println!("TESTSUITE STATUS");
    println!("    {:30}  {:4} {:4}", "FOLDER", "PASS", "FAIL");
    for (dir, (pass, fail)) in status {
        if fail == 0 {
            println!("\x1b[32m    {dir:40}: {pass:4} {fail:4}\x1b[0m");
        } else {
            println!("\x1b[31m    {dir:40}: {pass:4} {fail:4}\x1b[0m");
        }
    }

    Ok(())
}

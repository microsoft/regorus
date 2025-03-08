// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::collections::BTreeSet;

use regorus::*;

use anyhow::Result;
use test_generator::test_resources;

#[derive(serde::Deserialize)]
struct File {
    covered: BTreeSet<u32>,
    not_covered: BTreeSet<u32>,
}

#[derive(serde::Deserialize)]
struct TestCase {
    data: Option<Value>,
    input: Option<Value>,
    modules: Vec<String>,
    note: String,
    query: String,
    skip: Option<bool>,
    report: Vec<File>,
}

#[derive(serde::Deserialize)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    println!("running {file}");

    for case in test.cases.into_iter() {
        print!("case {} ", case.note);
        if case.skip == Some(true) {
            println!("skipped");
            continue;
        }

        let mut engine = Engine::new();
        engine.set_enable_coverage(true);
        engine.set_rego_v0(true);

        for (idx, rego) in case.modules.iter().enumerate() {
            engine.add_policy(format!("rego_{idx}"), rego.clone())?;
        }

        if let Some(data) = case.data {
            engine.add_data(data)?;
        }

        if let Some(input) = case.input {
            engine.set_input(input);
        }

        let _ = engine.eval_query(case.query.clone(), false)?;
        let report = engine.get_coverage_report()?;

        for (idx, file) in case.report.into_iter().enumerate() {
            assert_eq!(file.not_covered, report.files[idx].not_covered);
            assert_eq!(file.covered, report.files[idx].covered);
        }

        println!("passed");
    }

    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    match yaml_test_impl(file) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{}", e);
        }
    }
}

#[test_resources("tests/coverage/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

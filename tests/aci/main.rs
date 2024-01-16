// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use regorus::*;

use std::path::Path;
use std::time::Instant;

use anyhow::Result;
use clap::Parser;
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    note: String,
    data: Value,
    input: Value,
    modules: Vec<String>,
    query: String,
    want_result: Value,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn eval_test_case(dir: &Path, case: &TestCase) -> Result<Value> {
    let mut engine = Engine::new();

    engine.add_data(case.data.clone())?;
    engine.set_input(case.input.clone());

    for (idx, rego) in case.modules.iter().enumerate() {
        if rego.ends_with(".rego") {
            let path = dir.join(rego);
            let path = path.to_str().expect("not a valid path");
            engine.add_policy_from_file(path.to_string())?;
        } else {
            engine.add_policy(format!("rego{idx}.rego"), rego.clone())?;
        }
    }

    let query_results = engine.eval_query(case.query.clone(), true)?;

    let mut values = vec![];
    for qr in query_results.result {
        values.push(if !qr.bindings.as_object()?.is_empty() {
            qr.bindings.clone()
        } else if let Some(v) = qr.expressions.last() {
            v.value.clone()
        } else {
            Value::Undefined
        });
    }
    let result = Value::from(values);
    // Make result json compatible. (E.g: avoid sets).
    Value::from_json_str(&result.to_string())
}

fn run_aci_tests(dir: &Path) -> Result<()> {
    let mut nfailures = 0;
    for entry in WalkDir::new(dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if !path.to_string_lossy().ends_with(".yaml") {
            continue;
        }

        let yaml = std::fs::read(&path)?;
        let yaml = String::from_utf8_lossy(&yaml);
        let test: YamlTest = serde_yaml::from_str(&yaml)?;

        for case in &test.cases {
            print!("{:50}", case.note);
            let start = Instant::now();
            let results = eval_test_case(dir, case);
            let duration = start.elapsed();

            match results {
                Ok(actual) if actual == case.want_result => {
                    println!("passed    {:?}", duration);
                }
                Ok(actual) => {
                    println!(
                        "DIFF {}",
                        colored_diff::PrettyDifference {
                            expected: &serde_yaml::to_string(&case.want_result)?,
                            actual: &serde_yaml::to_string(&actual)?
                        }
                    );

                    nfailures += 1;
                }
                Err(e) => {
                    println!("failed    {:?}", duration);
                    println!("{e}");
                    nfailures += 1;
                }
            }
        }
    }
    assert!(nfailures == 0);

    Ok(())
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to ACI test suite.
    #[arg(long, short)]
    #[clap(default_value = "tests/aci")]
    test_dir: String,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    run_aci_tests(&Path::new(&cli.test_dir))
}

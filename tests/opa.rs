// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use regorus::*;

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

const OPA_REPO: &str = "https://github.com/open-policy-agent/opa";
const OPA_BRANCH: &str = "v0.58.0";

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

fn run_opa_tests(opa_tests_dir: String, folders: &[String]) -> Result<()> {
    println!("OPA TESTSUITE: {opa_tests_dir}");
    let tests_path = Path::new(&opa_tests_dir);
    let mut status = BTreeMap::<String, (u32, u32)>::new();
    let mut n = 0;
    let mut missing_functions = BTreeMap::new();
    for entry in WalkDir::new(&opa_tests_dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path_str = entry.path().to_string_lossy().to_string();
        if path_str == opa_tests_dir {
            continue;
        }
        let path = Path::new(&path_str);
        let path_dir = path.strip_prefix(tests_path)?.parent().unwrap();
        let path_dir_str = path_dir.to_string_lossy().to_string();

        if path.is_dir() {
            n = 0;
            continue;
        } else if !path.is_file() || !path_str.ends_with(".yaml") {
            continue;
        }

        let run_test = folders.is_empty() || folders.iter().any(|f| &path_dir_str == f);
        if !run_test {
            continue;
        }

        let entry = status.entry(path_dir_str).or_insert((0, 0));

        let yaml_str = std::fs::read_to_string(&path_str)?;
        let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

        for case in &test.cases {
            match (eval_test_case(case), &case.want_result) {
                (Ok(actual), Some(expected)) if &actual == expected => {
                    entry.0 += 1;
                }
                (Ok(actual), None)
                    if actual == Value::new_array()
                        && case.want_error.is_none()
                        && case.error.is_none() =>
                {
                    entry.0 += 1;
                }
                (Err(_), None) if case.want_error.is_some() => {
                    // Expected failure.
                    entry.0 += 1;
                }
                (r, _) => {
                    print!("\n{} failed.", case.note);
                    println!("{}", serde_yaml::to_string(&case)?);
                    match &r {
                        Ok(actual) => println!("GOT\n{}", serde_yaml::to_string(&actual)?),
                        Err(e) => println!("ERROR: {e}"),
                    }

                    if let Err(e) = r {
                        let msg = e.to_string();
                        let pat = "could not find function ";
                        if let Some(pos) = msg.find(pat) {
                            let fcn = &msg[pos + pat.len()..];
                            missing_functions
                                .entry(fcn.to_string())
                                .and_modify(|e| *e += 1)
                                .or_insert(1);
                        }
                    }
                    let path = Path::new("target/opa/failures").join(path_dir);
                    std::fs::create_dir_all(path.clone())?;

                    let mut cmd = "cargo run --example regorus eval".to_string();
                    if let Some(data) = &case.data {
                        let json_path = path.join(format!("data{n}.json"));
                        cmd += format!(" -d {}", json_path.display()).as_str();
                        std::fs::write(json_path, data.to_json_str()?.as_bytes())?;
                    };
                    if let Some(input) = &case.input {
                        let input_path = path.join(format!("data{n}.json"));
                        cmd += format!(" -i {}", input_path.display()).as_str();
                        std::fs::write(input_path, input.to_json_str()?.as_bytes())?;
                    };

                    if let Some(modules) = &case.modules {
                        if modules.len() == 1 {
                            let rego_path = path.join(format!("rego{n}.rego"));
                            cmd += format!(" -d {}", rego_path.display()).as_str();
                            std::fs::write(rego_path, modules[0].as_bytes())?;
                        } else {
                            for (i, m) in modules.iter().enumerate() {
                                let rego_path = path.join(format!("rego{n}_{i}.rego"));
                                cmd += format!(" -d {}", rego_path.display()).as_str();
                                std::fs::write(rego_path, m.as_bytes())?;
                            }
                        }
                    }

                    std::fs::write(path.join(format!("query{n}.text")), case.query.as_bytes())?;
                    cmd += format!(" \"{}\"", &case.query).as_str();

                    println!(" To debug, run:\n\x1b[31m{cmd}\x1b[0m");
                    entry.1 += 1;
                    n += 1;
                    continue;
                }
            };
        }
    }

    println!("\nOPA TESTSUITE STATUS");
    println!("    {:40}  {:4} {:4}", "FOLDER", "PASS", "FAIL");
    let (mut npass, mut nfail) = (0, 0);
    for (dir, (pass, fail)) in status {
        if fail == 0 {
            println!("\x1b[32m    {dir:40}: {pass:4} {fail:4}\x1b[0m");
        } else {
            println!("\x1b[31m    {dir:40}: {pass:4} {fail:4}\x1b[0m");
        }
        npass += pass;
        nfail += fail;
    }
    println!();

    if npass == 0 && nfail == 0 {
        bail!("no matching tests found.");
    } else if nfail == 0 {
        println!("\x1b[32m    {:40}: {npass:4} {nfail:4}\x1b[0m", "TOTAL");
    } else {
        println!("\x1b[31m    {:40}: {npass:4} {nfail:4}\x1b[0m", "TOTAL");
    }

    if !missing_functions.is_empty() {
        println!("\nMISSING FUNCTIONS");
        println!("    {:4}  {:40} {}", "", "FUNCTION", "FAILURES");
        let mut ncalls = 0;
        for (idx, (fcn, calls)) in missing_functions.iter().enumerate() {
            println!("\x1b[31m    {:4}: {fcn:40} {calls}\x1b[0m", idx + 1);
            ncalls += calls;
        }
        println!("\x1b[31m    {:4}  {:40} {ncalls}\x1b[0m", "", "TOTAL");
    }

    if nfail != 0 {
        bail!("OPA tests failed");
    }

    Ok(())
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to OPA test suite.
    #[arg(long, short)]
    test_suite_path: Option<String>,

    /// Specific test folder to run.
    folders: Vec<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    let opa_tests_dir = match cli.test_suite_path {
        Some(p) => p,
        None => {
            let branch_dir = format!("target/opa/branch/{OPA_BRANCH}");
            std::fs::create_dir_all(&branch_dir)?;
            if !std::path::Path::exists(Path::new(format!("{branch_dir}/.git").as_str())) {
                let output = match Command::new("git")
                    .arg("clone")
                    .arg(OPA_REPO)
                    .arg("--depth")
                    .arg("1")
                    .arg("--single-branch")
                    .arg("--branch")
                    .arg(OPA_BRANCH)
                    .arg(&branch_dir)
                    .output()
                {
                    Ok(o) => o,
                    Err(e) => {
                        bail!("failed to execute git clone. {e}")
                    }
                };
                println!("status: {}", output.status);
                io::stdout().write_all(&output.stdout).unwrap();
                io::stderr().write_all(&output.stderr).unwrap();
                if !output.status.success() {
                    bail!("failed to clone OPA repository");
                }
            }
            format!("{branch_dir}/test/cases/testdata")
        }
    };

    run_opa_tests(opa_tests_dir, &cli.folders)
}

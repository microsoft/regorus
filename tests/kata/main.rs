// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use regorus::*;

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Result};
use clap::Parser;
use walkdir::WalkDir;

fn normalize_printed_paths(mut prints: Vec<String>) -> Vec<String> {
    prints.iter_mut().for_each(|p| {
        *p = p
            .replace("\\", "/")
            .replace("//", "/")
            .replace("\r\n", "\n");
    });
    prints
}

fn run_kata_tests(
    tests_dir: &Path,
    name: &Option<String>,
    coverage: bool,
    generate: bool,
) -> Result<()> {
    let mut num_tests = 0;
    let mut num_queries = 0;
    let mut total_time_ns = 0;
    for entry in WalkDir::new(tests_dir)
        .max_depth(1) // Do not recurse
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if path == tests_dir || !path.is_dir() {
            continue;
        }

        // If specificed, only execute tests matching given name.
        if let Some(name) = name {
            if !path.ends_with(name) {
                continue;
            }
        }
        num_tests += 1;

        let policy_file = path.join("policy.rego");
        let inputs_file = path.join("inputs.txt");
        let outputs_file = path.join("outputs.json");
        let prints_file = path.join("prints.json");

        let mut engine = Engine::new();
        engine.set_rego_v0(true);
        engine.add_policy_from_file(&policy_file)?;
        engine.set_gather_prints(true);
        engine.set_strict_builtin_errors(false);

        #[cfg(feature = "coverage")]
        engine.set_enable_coverage(true);

        // Keep a copy of the engine.
        let engine_base = engine.clone();
        let mut results = if generate {
            vec![]
        } else {
            Value::from_json_file(&outputs_file)?
                .as_array()?
                .iter()
                .cloned()
                .rev()
                .collect()
        };

        let mut prints: Vec<Vec<String>> = if generate {
            vec![]
        } else {
            let prints_json = std::fs::read_to_string(&prints_file).map_err(|e| {
                anyhow::Error::msg(format!("could not read {}\n{e}", prints_file.display()))
            })?;

            serde_json::from_str::<Vec<Vec<String>>>(&prints_json)?
                .into_iter()
                .rev()
                .collect()
        };

        let inputs = std::fs::read_to_string(&inputs_file)?;
        for (lineno, line) in inputs.split('\n').enumerate() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            // Remove "ep":
            let line = line.replace("\"ep\":", "");
            // Remove trailing ,
            let line = &line[0..line.len() - 1];

            let request = Value::from_json_str(line)?;

            let rule = format!("data.agent_policy.{}", request[0].as_string()?.as_ref());
            let input = request[1].clone();

            // Evaluate using engine.
            engine.set_input(input.clone());
            let start = Instant::now();
            let r = engine.eval_rule(rule.clone())?;
            total_time_ns += start.elapsed().as_nanos();

            // Evaluate using fresh engine.
            let mut new_engine = engine_base.clone();
            new_engine.set_input(input);
            let start = Instant::now();
            let r_new = new_engine.eval_rule(rule)?;
            total_time_ns += start.elapsed().as_nanos();

            // Ensure that both evaluations produced the same result.
            assert_eq!(r, r_new);

            if generate {
                results.push(r);
                prints.push(normalize_printed_paths(engine.take_prints()?));
            } else {
                let expected = results.pop().unwrap();
                assert_eq!(r, expected, "{lineno} failed in {}", inputs_file.display());

                let p = normalize_printed_paths(engine.take_prints()?);
                assert_eq!(p, normalize_printed_paths(new_engine.take_prints()?));
                assert_eq!(p, normalize_printed_paths(prints.pop().unwrap()));
            }

            num_queries += 2;
        }

        if generate {
            std::fs::write(outputs_file, Value::from(results).to_json_str()?)?;
            std::fs::write(prints_file, serde_json::to_string_pretty(&prints)?)?;
        }

        if coverage {
            #[cfg(feature = "coverage")]
            {
                let report = engine.get_coverage_report()?;
                println!("{}", report.to_string_pretty()?);
            }
        }
    }

    if num_tests == 0 {
        bail!("no tests found");
    }

    let millis = total_time_ns as f64 / 1000_000.0;
    println!("executed {num_queries} queries in {millis:2} millis");
    println!("time per query is {:2} millis", millis / num_queries as f64);
    println!("kata tests passed");

    Ok(())
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to Kata test suite.
    #[arg(long, short)]
    #[clap(default_value = "tests/kata/data")]
    test_dir: String,

    /// Name of a specific test
    #[arg(long, short)]
    name: Option<String>,

    /// Display code coverage
    #[arg(long, short)]
    #[clap(default_value = "false")]
    coverage: bool,

    /// Generate outputs instead of testing.
    #[arg(long, short)]
    #[clap(default_value = "false")]
    generate: bool,
}

fn stateful_policy_test() -> Result<()> {
    // Create an engine for evaluating Rego policies.
    let mut engine = regorus::Engine::new();

    let policy = String::from(
        r#"
       package example

       default allow := false

       allow if {
         print("data.allowed_actions = ", data.allowed_actions)
         input.action in data.allowed_actions["user1"]
         print("This rule should be allowed")
       }
	"#,
    );

    // Add policy to the engine.
    engine.add_policy(String::from("policy.rego"), policy)?;

    // Evaluate first input. Expect to evaluate to false, since state is not set
    engine.set_input(regorus::Value::from_json_str(
        r#"{
      "action": "write"
    }"#,
    )?);

    let r = engine.eval_bool_query(String::from("data.example.allow"), false)?;
    println!("Received result: {:?}", r);
    assert_eq!(r, false);

    // Add data to engine. Set state
    engine.add_data(regorus::Value::from_json_str(
        r#"{
     "allowed_actions": {
        "user1" : ["read", "write"]
     }}"#,
    )?)?;

    // Evaluate second input. Expect to evaluate to true, since state has been set now
    engine.set_input(regorus::Value::from_json_str(
        r#"{
      "action": "write"
    }"#,
    )?);

    let r = engine.eval_bool_query(String::from("data.example.allow"), false)?;
    println!("Received result: {:?}", r);
    assert_eq!(
        r, true,
        "expect result to be true since rule evaluates to true after state has been updated, per rego logs"
    );

    Ok(())
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    run_kata_tests(
        &Path::new(&cli.test_dir),
        &cli.name,
        cli.coverage,
        cli.generate,
    )?;
    stateful_policy_test()
}

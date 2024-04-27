// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use regorus::*;

use std::path::Path;

use anyhow::Result;
use clap::Parser;
use walkdir::WalkDir;

fn run_kata_tests(tests_dir: &Path, generate: bool) -> Result<()> {
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

        let policy_file = path.join("policy.rego");
        let inputs_file = path.join("inputs.txt");
        let outputs_file = path.join("output.json");

        let mut engine = Engine::new();
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
            Value::from_json_str(&std::fs::read_to_string(&outputs_file)?)?
                .as_array()?
                .iter()
                .cloned()
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
            let r = engine.eval_rule(rule.clone())?;

            // Evaluate using fresh engine.
            let mut new_engine = engine_base.clone();
            new_engine.set_input(input);
            let r_new = new_engine.eval_rule(rule)?;

            // Ensure that both evaluations produced the same result.
            assert_eq!(r, r_new);

            if generate {
                results.push(r);
            } else {
                let expected = results.pop().unwrap();
                assert_eq!(r, expected, "{lineno} failed in {}", inputs_file.display());
            }
        }

        if generate {
            std::fs::write(outputs_file, Value::from(results).to_json_str()?)?;
        }
        #[cfg(feature = "coverage")]
        {
            let report = engine.get_coverage_report()?;
            println!("{}", report.to_colored_string()?);
        }
    }

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

    /// Generate outputs instead of testing.
    #[arg(long, short)]
    #[clap(default_value = "false")]
    generate: bool,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    run_kata_tests(&Path::new(&cli.test_dir), cli.generate)
}

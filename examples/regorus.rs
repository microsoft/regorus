// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Context, Result};
use clap::Parser;

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Policy or data files. Rego, json or yaml.
    #[arg(required(true), long, short, value_name = "policy.rego")]
    data: Vec<String>,

    /// Input file. json or yaml.
    #[arg(long, short, value_name = "input.rego")]
    input: Option<String>,

    // Query. Rego expression.
    #[arg(long, short)]
    query: Option<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let enable_tracing = false;

    // User specified data.
    let mut data = regorus::Value::new_object();

    // Read all policy files.
    let mut policies = vec![];
    for file in cli.data.iter() {
        let contents =
            std::fs::read_to_string(file).with_context(|| format!("Failed to read {file}"))?;

        if file.ends_with(".rego") {
            policies.push(contents);
        } else {
            let value: regorus::Value = if file.ends_with(".json") {
                serde_json::from_str(&contents)?
            } else if file.ends_with(".yaml") {
                serde_yaml::from_str(&contents)?
            } else {
                bail!("Unsupported data file `{file}`. Must be rego, json or yaml.")
            };

            if let Err(err) = data.merge(value) {
                bail!("Error processing {file}. {err}");
            }
        }
    }

    // Create source objects.
    let mut sources = vec![];
    for (idx, rego) in policies.iter().enumerate() {
        sources.push(regorus::Source {
            file: &cli.data[idx],
            contents: rego.as_str(),
            lines: rego.split('\n').collect(),
        });
    }

    // Parse the policy files.
    let mut modules = vec![];
    for source in &sources {
        let mut parser = regorus::Parser::new(source)?;
        modules.push(parser.parse()?);
    }

    // Analyze the modules and determine how statements must be schedules.
    let analyzer = regorus::Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    // Create interpreter object.
    let modules_ref: Vec<&regorus::Module> = modules.iter().collect();
    let mut interpreter = regorus::Interpreter::new(modules_ref)?;

    // Prepare for evalution.
    interpreter.prepare_for_eval(Some(&schedule), &Some(data))?;

    // Evaluate all the modules.
    interpreter.eval(&None, &None, false, Some(&schedule))?;

    // Fetch query string. If none specified, use "data".
    let query = match &cli.query {
        Some(query) => query,
        _ => "data",
    };

    // Parse the query.
    let query_source = regorus::Source {
        file: "<query.rego>",
        contents: query,
        lines: query.split('\n').collect(),
    };
    let query_span = regorus::Span {
        source: &query_source,
        line: 1,
        col: 1,
        start: 0,
        end: query.len() as u16,
    };
    let mut parser = regorus::Parser::new(&query_source)?;
    let query_node = parser.parse_query(query_span, "")?;
    let stmt_order = regorus::Analyzer::new().analyze_query_snippet(&modules, &query_node)?;

    let results = interpreter.eval_user_query(&query_node, &stmt_order, enable_tracing)?;
    println!("eval results:\n{}", serde_json::to_string_pretty(&results)?);

    Ok(())
}

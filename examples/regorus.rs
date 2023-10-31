// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Context, Result};
use clap::{Parser, Subcommand};

fn rego_eval(
    files: &[String],
    input: Option<String>,
    query: Option<String>,
    enable_tracing: bool,
) -> Result<()> {
    // User specified data.
    let mut data = regorus::Value::new_object();

    // Read all policy files.
    let mut policies = vec![];
    for file in files.iter() {
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
            file: &files[idx],
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

    // Parse input file.
    let input = if let Some(file) = input {
        let input_contents = std::fs::read_to_string(file.clone())
            .with_context(|| format!("Failed to read {file}"))?;

        Some(if file.ends_with(".json") {
            serde_json::from_str(&input_contents)?
        } else if file.ends_with(".yaml") {
            serde_yaml::from_str(&input_contents)?
        } else {
            bail!("invalid input file {file}");
        })
    } else {
        None
    };

    // Analyze the modules and determine how statements must be schedules.
    let analyzer = regorus::Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    // Create interpreter object.
    let modules_ref: Vec<&regorus::Module> = modules.iter().collect();
    let mut interpreter = regorus::Interpreter::new(modules_ref)?;

    // Prepare for evalution.
    interpreter.prepare_for_eval(Some(&schedule), &Some(data.clone()))?;

    // Evaluate all the modules.
    interpreter.eval(&Some(data), &input, false, Some(&schedule))?;

    // Fetch query string. If none specified, use "data".
    let query = match &query {
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

fn rego_lex(file: String, verbose: bool) -> Result<()> {
    let contents =
        std::fs::read_to_string(file.clone()).with_context(|| format!("Failed to read {file}"))?;

    // Create source.
    let source = regorus::Source {
        file: file.as_str(),
        contents: contents.as_str(),
        lines: contents.split('\n').collect(),
    };

    // Create lexer.
    let mut lexer = regorus::Lexer::new(&source);

    // Read tokens until EOF.
    loop {
        let token = lexer.next_token()?;
        if token.0 == regorus::TokenKind::Eof {
            break;
        }

        if verbose {
            // Print each token's line and mark with with ^.
            println!("{}", token.1.message("", ""));
        }

        // Print the token.
        println!("{token:?}");
    }
    Ok(())
}

fn rego_parse(file: String) -> Result<()> {
    let contents =
        std::fs::read_to_string(file.clone()).with_context(|| format!("Failed to read {file}"))?;

    // Create source.
    let source = regorus::Source {
        file: file.as_str(),
        contents: contents.as_str(),
        lines: contents.split('\n').collect(),
    };

    // Create a parser and parse the source.
    let mut parser = regorus::Parser::new(&source)?;
    let ast = parser.parse()?;
    println!("{ast:#?}");

    Ok(())
}

#[derive(Subcommand)]
enum RegorusCommand {
    /// Evaluate a Rego Query.
    Eval {
        /// Policy or data files. Rego, json or yaml.
        #[arg(
            required(true),
            long,
            short,
            value_name = "policy.rego|data.json|data.yaml"
        )]
        data: Vec<String>,

        /// Input file. json or yaml.
        #[arg(long, short, value_name = "input.rego")]
        input: Option<String>,

        /// Query. Rego query block.
        query: Option<String>,

        /// Enable tracing.
        #[arg(long, short)]
        trace: bool,
    },

    /// Tokenize a Rego policy.
    Lex {
        /// Rego policy file.
        file: String,

        /// Verbose output.
        #[arg(long, short)]
        verbose: bool,
    },

    /// Parse q Rego policy.
    Parse {
        /// Rego policy file.
        file: String,
    },
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: RegorusCommand,
}

fn main() -> Result<()> {
    // Parse and dispatch command.
    let cli = Cli::parse();
    match cli.command {
        RegorusCommand::Eval {
            data,
            input,
            query,
            trace,
        } => rego_eval(&data, input, query, trace),
        RegorusCommand::Lex { file, verbose } => rego_lex(file, verbose),
        RegorusCommand::Parse { file } => rego_parse(file),
    }
}

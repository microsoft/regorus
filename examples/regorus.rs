// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};

fn rego_eval(
    bundles: &[String],
    files: &[String],
    input: Option<String>,
    query: String,
    enable_tracing: bool,
    non_strict: bool,
    #[cfg(feature = "coverage")] coverage: bool,
) -> Result<()> {
    // Create engine.
    let mut engine = regorus::Engine::new();

    engine.set_strict_builtin_errors(!non_strict);

    #[cfg(feature = "coverage")]
    engine.set_enable_coverage(coverage);

    // Load files from given bundles.
    for dir in bundles.iter() {
        let entries =
            std::fs::read_dir(dir).or_else(|e| bail!("failed to read bundle {dir}.\n{e}"))?;
        // Loop through each entry in the bundle folder.
        for entry in entries {
            let entry = entry.or_else(|e| bail!("failed to unwrap entry. {e}"))?;
            let path = entry.path();

            // Process only .rego files.
            match (path.is_file(), path.extension()) {
                (true, Some(ext)) if ext == "rego" => {}
                _ => continue,
            }

            engine.add_policy_from_file(entry.path())?;
        }
    }

    // Load given files.
    for file in files.iter() {
        if file.ends_with(".rego") {
            // Read policy file.
            engine.add_policy_from_file(file)?;
        } else {
            // Read data file.
            let data = if file.ends_with(".json") {
                regorus::Value::from_json_file(file)?
            } else if file.ends_with(".yaml") {
                regorus::Value::from_yaml_file(file)?
            } else {
                bail!("Unsupported data file `{file}`. Must be rego, json or yaml.")
            };

            // Merge given data.
            engine.add_data(data)?;
        }
    }

    if let Some(file) = input {
        let input = if file.ends_with(".json") {
            regorus::Value::from_json_file(&file)?
        } else if file.ends_with(".yaml") {
            regorus::Value::from_yaml_file(&file)?
        } else {
            bail!("Unsupported input file `{file}`. Must be json or yaml.")
        };
        engine.set_input(input);
    }

    // Evaluate query.
    let results = engine.eval_query(query, enable_tracing)?;

    println!("{}", serde_json::to_string_pretty(&results)?);

    #[cfg(feature = "coverage")]
    if coverage {
        let report = engine.get_coverage_report()?;
        println!("{}", report.to_colored_string()?);
    }

    Ok(())
}

fn rego_lex(file: String, verbose: bool) -> Result<()> {
    use regorus::unstable::*;

    // Create source.
    let source = Source::from_file(file)?;

    // Create lexer.
    let mut lexer = Lexer::new(&source);

    // Read tokens until EOF.
    loop {
        let token = lexer.next_token()?;
        if token.0 == TokenKind::Eof {
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
    use regorus::unstable::*;

    // Create source.
    let source = Source::from_file(file)?;

    // Create a parser and parse the source.
    let mut parser = Parser::new(&source)?;
    let ast = parser.parse()?;
    println!("{ast:#?}");

    Ok(())
}

#[derive(clap::Subcommand)]
enum RegorusCommand {
    /// Evaluate a Rego Query.
    Eval {
        /// Directories containing Rego files.
        #[arg(long, short, value_name = "bundle")]
        bundles: Vec<String>,

        /// Policy or data files. Rego, json or yaml.
        #[arg(long, short, value_name = "policy.rego|data.json|data.yaml")]
        data: Vec<String>,

        /// Input file. json or yaml.
        #[arg(long, short, value_name = "input.rego")]
        input: Option<String>,

        /// Query. Rego query block.
        query: String,

        /// Enable tracing.
        #[arg(long, short)]
        trace: bool,

        /// Perform non-strict evaluation. (default behavior of OPA).
        #[arg(long, short)]
        non_strict: bool,

        /// Display coverage information
        #[cfg(feature = "coverage")]
        #[arg(long, short)]
        coverage: bool,
    },

    /// Tokenize a Rego policy.
    Lex {
        /// Rego policy file.
        file: String,

        /// Verbose output.
        #[arg(long, short)]
        verbose: bool,
    },

    /// Parse a Rego policy.
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
    use clap::Parser;

    // Parse and dispatch command.
    let cli = Cli::parse();
    match cli.command {
        RegorusCommand::Eval {
            bundles,
            data,
            input,
            query,
            trace,
            non_strict,
            #[cfg(feature = "coverage")]
            coverage,
        } => rego_eval(
            &bundles,
            &data,
            input,
            query,
            trace,
            non_strict,
            #[cfg(feature = "coverage")]
            coverage,
        ),
        RegorusCommand::Lex { file, verbose } => rego_lex(file, verbose),
        RegorusCommand::Parse { file } => rego_parse(file),
    }
}

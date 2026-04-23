// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, bail, Result};

#[cfg(feature = "azure_policy")]
mod azure_policy;

#[cfg(feature = "explanations")]
#[derive(clap::ValueEnum, Clone, Copy, Debug, Eq, PartialEq)]
enum WhyScopeArg {
    AllEmissions,
    RuleSummary,
}

#[cfg(feature = "explanations")]
#[derive(clap::ValueEnum, Clone, Copy, Debug, Eq, PartialEq)]
enum WhyDetailArg {
    Compact,
    Standard,
    Full,
}

#[cfg(feature = "explanations")]
#[derive(clap::ValueEnum, Clone, Copy, Debug, Eq, PartialEq)]
enum EvalModeArg {
    Causality,
    Partial,
}

#[cfg(feature = "explanations")]
#[allow(clippy::too_many_arguments)]
fn build_explanation_settings(
    why_detail: Option<WhyDetailArg>,
    why_scope: Option<WhyScopeArg>,
    why_emission: Option<usize>,
    why_emission_value: Option<String>,
    why_full_values: bool,
    why_all_conditions: bool,
    assume_unknown_input: bool,
    eval_mode: Option<EvalModeArg>,
    unknowns: Option<String>,
) -> Result<regorus::evaluation_trace::ExplanationSettings> {
    let detail = why_detail.map_or_else(
        || {
            if why_full_values || why_all_conditions {
                regorus::evaluation_trace::ExplanationDetail::Full
            } else {
                regorus::evaluation_trace::ExplanationDetail::Standard
            }
        },
        |detail| match detail {
            WhyDetailArg::Compact => regorus::evaluation_trace::ExplanationDetail::Compact,
            WhyDetailArg::Standard => regorus::evaluation_trace::ExplanationDetail::Standard,
            WhyDetailArg::Full => regorus::evaluation_trace::ExplanationDetail::Full,
        },
    );

    let emission_value = why_emission_value.map(|raw| {
        regorus::Value::from_json_str(&raw).unwrap_or_else(|_| regorus::Value::from(raw))
    });

    let scope = if why_emission.is_some() || emission_value.is_some() {
        regorus::evaluation_trace::ExplanationScope::SingleEmission
    } else {
        why_scope.map_or(
            regorus::evaluation_trace::ExplanationScope::AllEmissions,
            |scope| match scope {
                WhyScopeArg::AllEmissions => {
                    regorus::evaluation_trace::ExplanationScope::AllEmissions
                }
                WhyScopeArg::RuleSummary => {
                    regorus::evaluation_trace::ExplanationScope::RuleSummary
                }
            },
        )
    };

    let value_mode =
        if why_full_values || detail == regorus::evaluation_trace::ExplanationDetail::Full {
            regorus::evaluation_trace::ValueMode::Full
        } else {
            regorus::evaluation_trace::ValueMode::Redacted
        };

    let condition_mode =
        if why_all_conditions || detail == regorus::evaluation_trace::ExplanationDetail::Full {
            regorus::evaluation_trace::ConditionMode::AllContributing
        } else {
            regorus::evaluation_trace::ConditionMode::PrimaryOnly
        };

    let eval_mode_setting = match eval_mode {
        Some(EvalModeArg::Partial) => regorus::evaluation_trace::EvaluationMode::PartialEval,
        _ => regorus::evaluation_trace::EvaluationMode::Causality,
    };

    let unknowns_list = match unknowns {
        Some(s) => s.split(',').map(|p| p.trim().to_string()).collect(),
        None => vec!["input".into()],
    };

    Ok(regorus::evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode,
        condition_mode,
        scope,
        detail,
        emission_index: why_emission,
        emission_value,
        assume_unknown_input,
        eval_mode: eval_mode_setting,
        unknowns: unknowns_list,
    })
}

#[allow(dead_code)]
fn read_file(path: &String) -> Result<String> {
    std::fs::read_to_string(path).map_err(|_| anyhow!("could not read {path}"))
}

#[allow(unused_variables)]
fn read_value_from_yaml_file(path: &String) -> Result<regorus::Value> {
    #[cfg(feature = "yaml")]
    return regorus::Value::from_yaml_file(path);

    #[cfg(not(feature = "yaml"))]
    bail!("regorus has not been built with yaml support");
}

fn read_value_from_json_file(path: &String) -> Result<regorus::Value> {
    #[cfg(feature = "std")]
    return regorus::Value::from_json_file(path);

    #[cfg(not(feature = "std"))]
    regorus::Value::from_json_str(&read_file(path)?)
}

fn add_policy_from_file(engine: &mut regorus::Engine, path: String) -> Result<String> {
    #[cfg(feature = "std")]
    return engine.add_policy_from_file(path);

    #[cfg(not(feature = "std"))]
    engine.add_policy(path.clone(), read_file(&path)?)
}

#[allow(clippy::too_many_arguments)]
fn rego_eval(
    bundles: &[String],
    files: &[String],
    input: Option<String>,
    query: String,
    engine: EvalEngine,
    enable_tracing: bool,
    non_strict: bool,
    #[cfg(feature = "explanations")] why: bool,
    #[cfg(feature = "explanations")] why_scope: Option<WhyScopeArg>,
    #[cfg(feature = "explanations")] why_detail: Option<WhyDetailArg>,
    #[cfg(feature = "explanations")] why_emission: Option<usize>,
    #[cfg(feature = "explanations")] why_emission_value: Option<String>,
    #[cfg(feature = "explanations")] why_full_values: bool,
    #[cfg(feature = "explanations")] why_all_conditions: bool,
    #[cfg(feature = "explanations")] assume_unknown_input: bool,
    #[cfg(feature = "explanations")] eval_mode: Option<EvalModeArg>,
    #[cfg(feature = "explanations")] unknowns: Option<String>,
    #[cfg(feature = "coverage")] coverage: bool,
    v0: bool,
) -> Result<()> {
    #[cfg(feature = "explanations")]
    let why_enabled = why;

    #[cfg(feature = "explanations")]
    let is_pe_mode = matches!(eval_mode, Some(EvalModeArg::Partial));

    // Create engine.
    let mut policy_engine = regorus::Engine::new();

    policy_engine.set_strict_builtin_errors(!non_strict);

    #[cfg(feature = "coverage")]
    policy_engine.set_enable_coverage(coverage);

    policy_engine.set_rego_v0(v0);

    #[cfg(feature = "explanations")]
    if why_enabled {
        policy_engine.set_explanation_settings(build_explanation_settings(
            why_detail,
            why_scope,
            why_emission,
            why_emission_value.clone(),
            why_full_values,
            why_all_conditions,
            assume_unknown_input,
            eval_mode,
            unknowns.clone(),
        )?);
    }

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

            let _package =
                add_policy_from_file(&mut policy_engine, entry.path().display().to_string())?;
        }
    }

    // Load given files.
    for file in files.iter() {
        if file.ends_with(".rego") {
            // Read policy file.
            let _package = add_policy_from_file(&mut policy_engine, file.clone())?;
        } else {
            // Read data file.
            let data = if file.ends_with(".json") {
                read_value_from_json_file(file)?
            } else if file.ends_with(".yaml") {
                read_value_from_yaml_file(file)?
            } else {
                bail!("Unsupported data file `{file}`. Must be rego, json or yaml.");
            };

            // Merge given data.
            policy_engine.add_data(data)?;
        }
    }

    let input_value = if let Some(file) = input.as_ref() {
        let input = if file.ends_with(".json") {
            read_value_from_json_file(file)?
        } else if file.ends_with(".yaml") {
            read_value_from_yaml_file(file)?
        } else {
            bail!("Unsupported input file `{file}`. Must be json or yaml.")
        };
        Some(input)
    } else {
        None
    };

    if let Some(input) = input_value.clone() {
        policy_engine.set_input(input);
    }

    let results = match engine {
        EvalEngine::Interpreter => {
            // Note: The `eval_query` function is used below since it produces output
            // in the same format as OPA. It also allows evaluating arbitrary statements
            // as queries.
            //
            // Most applications will want to use `eval_rule` instead.
            // It is faster since it does not have to parse the query string.
            // It also returns the value of the rule directly and thus is easier
            // to use.
            policy_engine.eval_query(query.clone(), enable_tracing)?
        }
        EvalEngine::Rvm => {
            #[cfg(not(feature = "rvm"))]
            {
                bail!("the example was built without the `rvm` feature");
            }

            #[cfg(feature = "rvm")]
            {
                if enable_tracing {
                    bail!("trace output is not supported when --engine rvm is selected");
                }

                #[cfg(feature = "coverage")]
                if coverage {
                    bail!("coverage is not supported when --engine rvm is selected");
                }

                let entrypoint: regorus::Rc<str> = query.clone().into();
                let compiled = policy_engine.compile_with_entrypoint(&entrypoint)?;
                let program = regorus::languages::rego::compiler::Compiler::compile_from_policy(
                    &compiled,
                    &[entrypoint.as_ref()],
                )?;

                let mut vm = regorus::rvm::RegoVM::new_with_policy(compiled);
                vm.load_program(program);
                vm.set_strict_builtin_errors(!non_strict);

                #[cfg(feature = "explanations")]
                if why_enabled {
                    vm.set_explanation_settings(build_explanation_settings(
                        why_detail,
                        why_scope,
                        why_emission,
                        why_emission_value.clone(),
                        why_full_values,
                        why_all_conditions,
                        assume_unknown_input,
                        eval_mode,
                        unknowns.clone(),
                    )?);
                }

                if let Some(input) = input_value {
                    vm.set_input(input);
                }

                let value = vm.execute_entry_point_by_name(entrypoint.as_ref())?;

                #[cfg(feature = "explanations")]
                let _rvm_report = if why_enabled {
                    let report = if is_pe_mode {
                        vm.take_partial_eval_result(value.clone())
                            .map_err(|e| anyhow!("{e}"))?
                    } else {
                        vm.take_causality_report(value.clone())
                            .map_err(|e| anyhow!("{e}"))?
                    };
                    Some(report)
                } else {
                    None
                };

                #[cfg(not(feature = "explanations"))]
                let _rvm_report: Option<String> = None;

                let results = single_value_query_results(query.clone(), value);

                println!("{}", serde_json::to_string_pretty(&results)?);

                #[cfg(feature = "explanations")]
                if why_enabled {
                    if let Some(report) = _rvm_report {
                        eprintln!("\n--- Causality Report ---");
                        println!("{report}");
                    }
                }

                #[cfg(feature = "coverage")]
                if coverage {
                    let report = policy_engine.get_coverage_report()?;
                    println!("{}", report.to_string_pretty()?);
                }

                return Ok(());
            }
        }
    };

    println!("{}", serde_json::to_string_pretty(&results)?);

    #[cfg(feature = "explanations")]
    if why_enabled {
        let report = policy_engine.take_causality_report()?;
        eprintln!("\n--- Causality Report ---");
        println!("{report}");
    }

    #[cfg(feature = "coverage")]
    if coverage {
        let report = policy_engine.get_coverage_report()?;
        println!("{}", report.to_string_pretty()?);
    }

    Ok(())
}

fn rego_lex(file: String, verbose: bool) -> Result<()> {
    use regorus::unstable::*;

    // Create source.
    #[cfg(feature = "std")]
    let source = Source::from_file(file)?;

    #[cfg(not(feature = "std"))]
    let source = Source::from_contents(file.clone(), read_file(&file)?)?;

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

fn rego_parse(file: String, v0: bool) -> Result<()> {
    use regorus::unstable::*;

    // Create source.
    #[cfg(feature = "std")]
    let source = Source::from_file(file)?;

    #[cfg(not(feature = "std"))]
    let source = Source::from_contents(file.clone(), read_file(&file)?)?;

    // Create a parser and parse the source.
    let mut parser = Parser::new(&source)?;

    if !v0 {
        parser.enable_rego_v1()?;
    }

    let ast = parser.parse()?;
    println!("{ast:#?}");

    Ok(())
}

#[allow(unused_variables)]
fn rego_ast(file: String) -> Result<()> {
    #[cfg(feature = "ast")]
    {
        // Create engine.
        let mut engine = regorus::Engine::new();

        // Create source.
        #[cfg(feature = "std")]
        engine.add_policy_from_file(file)?;

        #[cfg(not(feature = "std"))]
        engine.add_policy(file.clone(), read_file(&file)?)?;

        let ast = engine.get_ast_as_json()?;

        println!("{ast}");
        Ok(())
    }

    #[cfg(not(feature = "ast"))]
    {
        bail!("`ast` feature must be enabled");
    }
}

#[derive(clap::Subcommand)]
enum RegorusCommand {
    /// Parse a Rego policy and dump AST.
    Ast {
        /// Rego policy file.
        file: String,
    },

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

        /// Evaluation backend.
        #[arg(long, default_value = "interpreter")]
        engine: EvalEngine,

        /// Enable tracing.
        #[arg(long, short)]
        trace: bool,

        /// Perform non-strict evaluation. (default behavior of OPA).
        #[arg(long, short)]
        non_strict: bool,

        /// Capture and print the causality report for the query.
        #[cfg(feature = "explanations")]
        #[arg(long = "why")]
        why: bool,

        /// Limit the causality report to a specific scope.
        #[cfg(feature = "explanations")]
        #[arg(long = "why-scope", value_enum, requires = "why")]
        why_scope: Option<WhyScopeArg>,

        /// Control the amount of explanation detail.
        #[cfg(feature = "explanations")]
        #[arg(long = "why-detail", value_enum, requires = "why")]
        why_detail: Option<WhyDetailArg>,

        /// Explain only the selected emitted result by 0-based index.
        #[cfg(feature = "explanations")]
        #[arg(
            long = "why-emission",
            requires = "why",
            conflicts_with = "why_emission_value"
        )]
        why_emission: Option<usize>,

        /// Explain only the emitted result whose value exactly matches this JSON literal or string.
        #[cfg(feature = "explanations")]
        #[arg(
            long = "why-emission-value",
            requires = "why",
            conflicts_with = "why_emission"
        )]
        why_emission_value: Option<String>,

        /// Preserve secret-looking values in the causality report.
        #[cfg(feature = "explanations")]
        #[arg(long = "why-full-values", requires = "why")]
        why_full_values: bool,

        /// Include all contributing conditions, not just the primary one.
        #[cfg(feature = "explanations")]
        #[arg(long = "why-all-conditions")]
        why_all_conditions: bool,

        /// Assume unknown input fields exist (treat as assumptions).
        #[cfg(feature = "explanations")]
        #[arg(long = "assume-unknown-input")]
        assume_unknown_input: bool,

        /// Evaluation mode: causality (default) or partial evaluation.
        #[cfg(feature = "explanations")]
        #[arg(long = "eval-mode", value_enum, requires = "why")]
        eval_mode: Option<EvalModeArg>,

        /// Comma-separated list of unknown path prefixes for partial evaluation.
        /// Default: "input". Example: --unknowns "input.document,input.action"
        #[cfg(feature = "explanations")]
        #[arg(long = "unknowns")]
        unknowns: Option<String>,

        /// Display coverage information
        #[cfg(feature = "coverage")]
        #[arg(long, short)]
        coverage: bool,

        /// Turn on Rego language v0.
        #[arg(long)]
        v0: bool,
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

        /// Turn on Rego language v0.
        #[arg(long)]
        v0: bool,
    },

    /// Evaluate an Azure Policy definition against a resource.
    #[cfg(feature = "azure_policy")]
    AzurePolicyEval {
        /// Azure Policy definition JSON file.
        #[arg(long)]
        policy_definition: String,

        /// ARM resource JSON file to evaluate.
        #[arg(long)]
        resource: String,

        /// Aliases JSON file (provider aliases).
        #[arg(long)]
        aliases: String,

        /// Policy parameters as a JSON string.
        #[arg(long)]
        parameters: Option<String>,

        /// API version for alias path selection.
        #[arg(long)]
        api_version: Option<String>,
    },

    /// List aliases from an alias registry file.
    #[cfg(feature = "azure_policy")]
    AzurePolicyAliases {
        /// Aliases JSON file (provider aliases).
        #[arg(long)]
        aliases: String,

        /// Filter aliases by resource type prefix.
        #[arg(long)]
        resource_type: Option<String>,
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
            engine,
            trace,
            non_strict,
            #[cfg(feature = "explanations")]
            why,
            #[cfg(feature = "explanations")]
            why_scope,
            #[cfg(feature = "explanations")]
            why_detail,
            #[cfg(feature = "explanations")]
            why_emission,
            #[cfg(feature = "explanations")]
            why_emission_value,
            #[cfg(feature = "explanations")]
            why_full_values,
            #[cfg(feature = "explanations")]
            why_all_conditions,
            #[cfg(feature = "explanations")]
            assume_unknown_input,
            #[cfg(feature = "explanations")]
            eval_mode,
            #[cfg(feature = "explanations")]
            unknowns,
            #[cfg(feature = "coverage")]
            coverage,
            v0,
        } => rego_eval(
            &bundles,
            &data,
            input,
            query,
            engine,
            trace,
            non_strict,
            #[cfg(feature = "explanations")]
            why,
            #[cfg(feature = "explanations")]
            why_scope,
            #[cfg(feature = "explanations")]
            why_detail,
            #[cfg(feature = "explanations")]
            why_emission,
            #[cfg(feature = "explanations")]
            why_emission_value,
            #[cfg(feature = "explanations")]
            why_full_values,
            #[cfg(feature = "explanations")]
            why_all_conditions,
            #[cfg(feature = "explanations")]
            assume_unknown_input,
            #[cfg(feature = "explanations")]
            eval_mode,
            #[cfg(feature = "explanations")]
            unknowns,
            #[cfg(feature = "coverage")]
            coverage,
            v0,
        ),
        RegorusCommand::Lex { file, verbose } => rego_lex(file, verbose),
        RegorusCommand::Parse { file, v0 } => rego_parse(file, v0),
        RegorusCommand::Ast { file } => rego_ast(file),
        #[cfg(feature = "azure_policy")]
        RegorusCommand::AzurePolicyEval {
            policy_definition,
            resource,
            aliases,
            parameters,
            api_version,
        } => azure_policy::azure_policy_eval(
            policy_definition,
            resource,
            aliases,
            parameters,
            api_version,
        ),
        #[cfg(feature = "azure_policy")]
        RegorusCommand::AzurePolicyAliases {
            aliases,
            resource_type,
        } => azure_policy::azure_policy_aliases(aliases, resource_type),
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::std_instead_of_core,
    clippy::semicolon_if_nothing_returned,
    clippy::pattern_type_mismatch,
    clippy::as_conversions
)] // scheduler analyzer tests rely on asserts/unwraps and std conveniences

use crate::*;
use crate::{ast::*, lexer::*, parser::*, scheduler::*};
use anyhow::{anyhow, bail, Result};
use serde::{Deserialize, Serialize};
use test_generator::test_resources;

use std::collections::BTreeSet;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Scope {
    pub locals: BTreeSet<String>,
    pub unscoped: BTreeSet<String>,
    pub inputs: BTreeSet<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    modules: Vec<String>,
    note: String,
    scopes: Vec<Scope>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn to_string_set<'a, I>(itr: I) -> BTreeSet<String>
where
    I: std::iter::Iterator<Item = &'a SourceStr>,
{
    itr.map(|s| s.to_string()).collect()
}

fn analyze_file(regos: &[String], expected_scopes: &[Scope]) -> Result<()> {
    let mut sources = vec![];
    let mut modules = vec![];
    for (idx, _) in regos.iter().enumerate() {
        sources.push(Source::from_contents(
            format!("rego_{idx}"),
            regos[idx].clone(),
        )?);
    }

    for source in &sources {
        let mut parser = Parser::new(source)?;
        modules.push(Ref::new(parser.parse()?));
    }

    let analyzer = Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    // Collect all queries from modules to create the mapping
    let mut all_queries = Vec::new();
    for (module_idx, module) in modules.iter().enumerate() {
        for rule in &module.policy {
            if let Rule::Spec { bodies, .. } = rule.as_ref() {
                for body in bodies {
                    all_queries.push((module_idx as u32, body.query.qidx, body.query.clone()));
                }
            }
        }
    }

    let mut scopes = Vec::new();
    for (module_idx, qidx, query) in all_queries.iter() {
        // Find the corresponding query schedule
        if let Some(query_schedule) = schedule
            .queries
            .get_checked(*module_idx, *qidx)
            .map_err(|err| anyhow!("schedule out of bounds: {err}"))?
        {
            scopes.push((query.clone(), &query_schedule.scope));
        }
    }

    scopes.sort_by(|a, b| a.0.span.line.cmp(&b.0.span.line));
    for (idx, (_, scope)) in scopes.iter().enumerate() {
        if idx > expected_scopes.len() {
            bail!("extra scope generated.")
        }
        assert_eq!(
            to_string_set(scope.locals.keys()),
            expected_scopes[idx].locals
        );
        assert_eq!(
            to_string_set(scope.unscoped.iter()),
            expected_scopes[idx].unscoped
        );
        assert_eq!(
            to_string_set(scope.inputs.iter()),
            expected_scopes[idx].inputs
        );
        std::println!("scope {idx} matched.")
    }

    Ok(())
}

fn yaml_test_impl(file: &str) -> Result<()> {
    std::println!("\nrunning {file}");

    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    for case in &test.cases {
        std::print!("\ncase {} ", case.note);
        analyze_file(&case.modules, &case.scopes)?;
        std::println!("passed");
    }

    std::println!("{} cases passed.", test.cases.len());
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

#[test_resources("tests/scheduler/analyzer/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

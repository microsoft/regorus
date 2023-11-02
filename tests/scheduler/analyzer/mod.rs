// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};
use regorus::scheduler::*;
use regorus::*;
use serde::{Deserialize, Serialize};
use test_generator::test_resources;

use std::collections::BTreeSet;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Scope {
    pub locals: BTreeSet<String>,
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

fn to_string_set(s: &BTreeSet<&str>) -> BTreeSet<String> {
    s.iter().map(|s| s.to_string()).collect()
}

fn analyze_file(regos: &[String], expected_scopes: &[Scope]) -> Result<()> {
    let mut files = vec![];
    let mut sources = vec![];
    let mut modules = vec![];
    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        sources.push(Source {
            file,
            contents,
            lines: contents.split('\n').collect(),
        });
    }

    for source in &sources {
        let mut parser = Parser::new(source)?;
        modules.push(parser.parse()?);
    }
    let modules_ref: Vec<&Module> = modules.iter().collect();

    let analyzer = Analyzer::new();
    let schedule = analyzer.analyze(&modules_ref)?;
    let mut scopes: Vec<(&Query, &regorus::Scope)> = schedule
        .scopes
        .iter()
        .map(|(r, s)| (r.inner(), s))
        .collect();
    scopes.sort_by(|a, b| a.0.span.line.cmp(&b.0.span.line));
    for (idx, (_, scope)) in scopes.iter().enumerate() {
        if idx > expected_scopes.len() {
            bail!("extra scope generated.")
        }
        assert_eq!(to_string_set(&scope.locals), expected_scopes[idx].locals);
        assert_eq!(to_string_set(&scope.inputs), expected_scopes[idx].inputs);
        println!("scope {idx} matched.")
    }

    Ok(())
}

fn yaml_test_impl(file: &str) -> Result<()> {
    println!("\nrunning {file}");

    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    for case in &test.cases {
        print!("\ncase {} ", case.note);
        analyze_file(&case.modules, &case.scopes)?;
        println!("passed");
    }

    println!("{} cases passed.", test.cases.len());
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

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::{ast::*, lexer::*, parser::*, scheduler::*};
use anyhow::{bail, Result};
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
    let mut scopes: Vec<(Ref<Query>, &crate::scheduler::Scope)> = schedule
        .scopes
        .iter()
        .map(|(r, s)| (r.clone(), s))
        .collect();
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

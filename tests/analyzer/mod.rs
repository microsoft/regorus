// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use std::env;

use anyhow::{bail, Result};
use regorus::analyzer::*;
use regorus::*;

#[test]
#[ignore = "intended for use by scripts/rego-analyze"]
fn one_file() -> Result<()> {
    env_logger::init();

    let mut file = String::default();
    for a in env::args() {
        if a.ends_with(".rego") {
            file = a;
        }
    }

    if file.is_empty() {
        bail!("missing <policy.rego>");
    }

    let contents = std::fs::read_to_string(&file)?;

    let source = Source {
        file: file.as_str(),
        contents: contents.as_str(),
        lines: contents.split('\n').collect(),
    };
    let mut parser = Parser::new(&source)?;
    let tree = parser.parse()?;

    let mut analyzer = Analyzer::new();
    analyzer.analyze_modules(&[&tree])?;

    Ok(())
}

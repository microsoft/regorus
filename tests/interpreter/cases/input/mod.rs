// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use crate::interpreter::*;
use anyhow::Result;

#[test]
fn basic() -> Result<()> {
    let rego = r#"
    package test
        
    x[a] {
      a = y
    }

    y[a] {
      a = input.x + 5
    }
"#;

    let input = ValueOrVec::Many(vec![
        Value::from_json_str(r#"{"x": 1}"#)?,
        Value::from_json_str(r#"{"x": 6}"#)?,
    ]);

    let expected = [
        Value::from_json_str(
            r#" {
        "y": {"set!": [6]},
        "x": {"set!": [{"set!":[6]}]}
}"#,
        )?,
        Value::from_json_str(
            r#" {
        "y": {"set!": [11]},
        "x": {"set!": [{"set!":[11]}]}
}"#,
        )?,
    ];

    check_output(
        &eval_file_first_rule(&[rego.to_owned()], None, Some(input), "data.test", false)?,
        &expected,
    )
}

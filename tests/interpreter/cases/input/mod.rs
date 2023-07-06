// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(test)]

use crate::interpreter::*;

#[test]
fn basic_second_input() -> Result<()> {
    let rego = r#"
    package test

    x[a] {
        a = input.x + 5
    }
"#;

    let expected = Value::from_json_str(
        r#" {
            "test": {
                "x": {
                    "set!":[8, 15]
                }
            }
}"#,
    )?;

    let input1 = Value::from_json_str(
        r#" {
            "x": 3
}"#,
    )?;

    let input2 = Value::from_json_str(
        r#" {
            "x": 10
}"#,
    )?;

    assert_match(
        eval_file_additional_input(
            &[rego.to_owned()],
            None,
            Some(input1),
            Some(input2),
            "data.test",
            false,
        )?,
        expected,
    );
    Ok(())
}

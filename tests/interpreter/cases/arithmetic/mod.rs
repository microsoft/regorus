// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use crate::interpreter::*;
use anyhow::Result;

#[test]
fn basic() -> Result<()> {
    let rego = r#"
    package test

    add {
      1 + 2 == 3
    }

    sub {
      5 - 1 == 4
    }

    mul {
      3 * 4 == 12
    }

    # Lock down float operation.
    div {
      21 / 5 == 4.2
    }
"#;

    let expected = vec![Value::from_json_str(
        r#" {
    "add" : true,
    "sub" : true,
    "mul" : true,
    "div" : true
}"#,
    )?];

    assert_eq!(
        eval_file(&[rego.to_owned()], None, None, "data.test", false)?,
        expected
    );
    Ok(())
}

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

    eq1 { 1 == 1.0 }
    eq2 { 1 == 1.00 }
    neq1 { 1 != 1.0001 }

    sum { 0.1 + 0.2 == 0.3 }
    diff { 0.3 - 0.2 == 0.1 }
    product { 0.1 * 0.2 == 0.02 }
    quotient { 0.3 / 0.1 == 3.0 }

    lt { 1 < 1.0001 }
    le { 1 <= 1.0 }
    gt { 1.0001 > 1 }
    ge { 1.0 >= 1 }
    neg_lt { -1 < 0 }
    neg_le { -1 <= -1 }

    div1 { 1 / 2 == 0.5 }
    div2 { 5 / 2 == 2.5 }

    neg1 { -1 == -1 }
    neg2 { -1 + 2 == 1 }
    neg3 { -(2 + 3) == -5 }
    neg4 { 1 - -1 == 2 }

    big1 { 1000000000000000000000 + 1 == 1000000000000000000001 }
    big2 { 2 * 1000000000000000000000 == 2000000000000000000000 }
    big3 { 2 / 1e18 == 2e-18 }
"#;

    let expected = vec![Value::from_json_str(
        r#" {
    "add" : true,
    "sub" : true,
    "mul" : true,
    "div" : true,
    "eq1": true,
    "eq2": true,
    "neq1": true,
    "sum": true,
    "diff": true,
    "product": true,
    "quotient": true,
    "lt": true,
    "le": true,
    "gt": true,
    "ge": true,
    "neg_lt": true,
    "neg_le": true,
    "div1": true,
    "div2": true,
    "neg1": true,
    "neg2": true,
    "neg3": true,
    "neg4": true,
    "big1": true,
    "big2": true,
    "big3": true
}"#,
    )?];

    assert_eq!(
        eval_file(&[rego.to_owned()], None, None, "data.test", false)?,
        expected
    );
    Ok(())
}

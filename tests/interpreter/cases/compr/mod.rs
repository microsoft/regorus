// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(test)]

use crate::interpreter::*;

#[test]
fn basic_array() -> Result<()> {
    let rego = r#"
    package test

    array = [1, 2, 3]

    array_compr_0 = [ x | x = 1 ]

    array_compr_1 = [ array | true ]

    array_compr_2 = [ x | x = array[_] ]

    array_compr_3 = [ x | x = array[_]; x != 2 ]

    # This produces 3 values
    array_compr_4 = [ 1 | [1, 2, 3][_] ]

    # This produces 6 values.
    array_compr_5 = [ 1 | [1, 2, 3][_]; {1, 2}[_] ]

    # This also produces 6 values.
    array_compr_6 = [ 1 | [1, 2, 3][_]; {"a":1, "b":2}[_] ]

    # This produces 3 values.
    array_compr_7 = [ 1 | [1, 2, 3][_]; [1, 2][_] >= 2 ]
"#;

    let expected = [Value::from_json_str(
        r#" {
            "array": [1, 2, 3],
            "array_compr_0": [1],
            "array_compr_1": [[1, 2, 3]],
            "array_compr_2": [1, 2, 3],
            "array_compr_3": [1, 3],
            "array_compr_4": [1, 1, 1],
            "array_compr_5": [1, 1, 1, 1, 1, 1],
            "array_compr_6": [1, 1, 1, 1, 1, 1],
            "array_compr_7": [1, 1, 1]
}"#,
    )?];

    check_output(
        &eval_file(&[rego.to_owned()], None, None, "data.test", false)?,
        &expected,
    )
}

#[test]
fn basic_set() -> Result<()> {
    let rego = r#"
    package test

    set = { 1,  "string", 1, [2, 3, 4], 567, false, 1 }

    set_compr_0 = { x | x = 1 }

    set_compr_1 = { set | true }

    set_compr_2 = { x | x = set[_] }

    set_compr_3 = { x | x = set[_]; x != [2, 3, 4] }

    # This produces 1 value
    set_compr_4 = { 1 | [1, 2, 3][_] }

    # This produces 4 values.
    set_compr_5 = { (a+b) | a=[1, 2, 3][_]; b={1, 2}[_] }

    # This also produces 2 values.
    set_compr_6 = { a | [1, 2, 3][_]; a={"a":1, "b":2}[_] }

    # This produces 3 values.
    set_compr_7 = { a | a = [1, 2, 3][_]; [1, 2][_] >= 2 }
"#;

    let expected = [Value::from_json_str(
        r#" {
            "set": {
                "set!": [1, "string", [2, 3, 4], 567, false]
            },
            "set_compr_0": {
                "set!": [1]
            },
           "set_compr_1":  {
                "set!" : [{
                    "set!": [1, "string", [2, 3, 4], 567, false]
                }]
            },
            "set_compr_2":  {
                "set!": [1, "string", [2, 3, 4], 567, false]
            },
            "set_compr_3":  {
                "set!": [1, "string", 567, false]
            },
            "set_compr_4":  {
                "set!": [1]
            },
            "set_compr_5":  {
                "set!": [2, 3, 4, 5]
            },
            "set_compr_6":  {
                "set!": [1, 2]
            },
            "set_compr_7":  {
                "set!": [1, 2, 3]
            }
 }"#,
    )?];

    check_output(
        &eval_file(&[rego.to_owned()], None, None, "data.test", false)?,
        &expected,
    )
}

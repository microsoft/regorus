// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(test)]

use crate::interpreter::*;

#[test]
fn basic() -> Result<()> {
    let rego = r#"
    package test

    array = [1, 2, 3]

    nested_array = [1, [2, 3, 4], 5, 6]

    object = { "key0": "value0" }

    key = "key"

    object_var = { key: array }

    local_0 = x {
        x = 10
    }

    local_1 = x {
        some x
        x = "test_local"
    }

    set = {1, 2, 3}
"#;

    let expected = [Value::from_json_str(
        r#" {
    "array": [1, 2, 3],
    "nested_array": [1, [2, 3, 4], 5, 6],
    "object": { "key0": "value0" },
    "key": "key",
    "object_var": { "key": [1, 2, 3] },
    "set" : {
       "set!" : [3, 2, 1]
     },
     "local_0": 10,
     "local_1": "test_local"
}"#,
    )?];

    check_output(
        &eval_file(&[rego.to_owned()], None, None, "data.test", false)?,
        &expected,
    )
}

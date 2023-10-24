// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use crate::interpreter::*;

#[test]
fn basic() -> Result<()> {
    let rego = r#"
    package test

    import future.keywords.in

    array = [1, 2, 3]

    in_array_key_value {
        0, 1 in array
    }

    in_array_key_value_negative {
        0, 2 in array
    }

    some_decl_array_key_value {
        some 0, 1 in array
    }

    some_decl_array_key_value_negative {
        some 0, 2 in array
    }

    some_decl_array_value {
        some 1 in array
    }

    some_decl_array_value_negative {
        some 4 in array
    }

    in_array_value {
        1 in array
    }

    in_array_value_negative {
        4 in array
    }

    object = { "number": 1, "array": [2, 3], "string": "test", "bool": true }

    in_object_key_value {
        "number", 1 in object
    }

    in_object_key_value_negative {
        "non-exist", 1 in object
    }

    some_decl_object_key_value {
        some "number", 1 in object
    }

    some_decl_object_key_value_negative {
        some "non-exist", 1 in object
    }

    in_object_value {
        [2, 3] in object
    }

    in_object_value_negative {
        false in object
    }

    some_decl_object_value {
        some [2, 3] in object
    }

    some_decl_object_value_negative {
        some false in object
    }

    set = { "string", [2, 3, 4], 567, false }

    in_set_value {
        "string" in set
    }

    some_decl_set_value {
        some "string" in set
    }

    in_set_value_negative {
        "non-exist" in set
    }

    some_decl_set_value_negative {
        some "non-exist" in set
    }
"#;

    let expected = [Value::from_json_str(
        r#" {
            "array": [1, 2, 3],
            "in_array_key_value": true,
            "some_decl_array_key_value": true,
            "in_array_value": true,
            "some_decl_array_value": true,
            "object": { "number": 1, "array": [2, 3], "string": "test", "bool": true},
            "in_object_key_value": true,
            "some_decl_object_key_value": true,
            "in_object_value": true,
            "some_decl_object_value": true,
            "set": {
                "set!": ["string", [2, 3, 4], 567, false]
            },
            "in_set_value": true,
            "some_decl_set_value": true
}"#,
    )?];

    check_output(
        &eval_file(&[rego.to_owned()], None, None, "data.test", false)?,
        &expected,
    )
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::builtins;
use regorus::Value;

// Lockdown calls that cannot happen via rego.
#[test]
fn type_name_undefined() {
    assert_eq!(builtins::types::get_type(&Value::Undefined), "undefined");
}

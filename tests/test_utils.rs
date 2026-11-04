// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(any(feature = "test-utils", all(feature = "yaml", feature = "std")))]

use anyhow::Result;
use regorus::test_utils::{
    check_output, match_values, process_value, value_or_vec_to_vec, ValueOrVec,
};
use regorus::Value;

#[test]
fn comparisons_preserve_undefined() -> Result<()> {
    match_values(&Value::Undefined, &Value::Undefined)?;
    for expected in [Value::Null, Value::Bool(false), Value::from("<undefined>")] {
        let error = match_values(&Value::Undefined, &expected).expect_err("values differ");
        let message = error.to_string();
        assert!(message.contains("expected:"));
        assert!(message.contains("computed:"));
    }
    Ok(())
}

#[test]
fn fixture_encodings_support_sets_and_non_string_keys() -> Result<()> {
    let encoded = Value::from_json_str(r#"{"set!":[1,2]}"#)?;
    let set = process_value(&encoded)?;
    assert_eq!(set.as_set()?.len(), 2);
    assert!(set.as_set()?.contains(&Value::from(1)));
    check_output(&[set], &[encoded])?;

    let encoded = Value::from_json_str(r##"{"object!":[{"key":1,"value":"#undefined"}]}"##)?;
    let object = process_value(&encoded)?;
    assert_eq!(
        object.as_object()?.get(&Value::from(1)),
        Some(&Value::Undefined)
    );
    check_output(&[object], &[encoded])?;
    Ok(())
}

#[test]
fn many_results_round_trip_without_yaml() -> Result<()> {
    let results = ValueOrVec::Many(vec![Value::Bool(true), Value::Bool(false)]);
    let json = serde_json::to_string(&results)?;
    assert_eq!(json, r#"{"many!":[true,false]}"#);
    let decoded: ValueOrVec = serde_json::from_str(&json)?;
    assert_eq!(
        value_or_vec_to_vec(decoded),
        vec![Value::Bool(true), Value::Bool(false)]
    );
    let error = check_output(&[], &[Value::Null]).expect_err("result counts differ");
    assert!(error.to_string().contains("number of computed results"));
    Ok(())
}

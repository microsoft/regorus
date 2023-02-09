// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use anyhow::Result;
use rego_rs::*;

#[test]
fn non_string_key() -> Result<()> {
    let mut obj = Value::new_object();

    obj.as_object_mut()?.insert(Value::Null, Value::Null);
    obj.as_object_mut()?.insert(Value::Bool(false), Value::Null);
    obj.as_object_mut()?
        .insert(Value::from_f64(std::f64::consts::PI), Value::Null);
    obj.as_object_mut()?.insert(
        Value::from_array(vec![
            Value::Bool(true),
            Value::Null,
            Value::from_f64(std::f64::consts::PI),
        ]),
        Value::Null,
    );

    let mut set = Value::new_set();
    set.as_set_mut()?.insert(Value::Bool(true));
    set.as_set_mut()?.insert(Value::Bool(false));
    set.as_set_mut()?.insert(Value::Bool(true));
    set.as_set_mut()?
        .insert(Value::from_f64(std::f64::consts::PI));
    obj.as_object_mut()?.insert(set, Value::Null);

    obj.as_object_mut()?.insert(Value::Undefined, Value::Null);

    let key_obj = obj.clone();
    obj.as_object_mut()?.insert(key_obj, Value::Null);

    let json = serde_json::to_string_pretty(&obj)?;
    println!("{}", json);

    let expected = r#"{
  "null": null,
  "false": null,
  "3.141592653589793": null,
  "[true,null,3.141592653589793]": null,
  "{\"null\":null,\"false\":null,\"3.141592653589793\":null,\"[true,null,3.141592653589793]\":null,\"[false,true,3.141592653589793]\":null,\"\\\"<undefined>\\\"\":null}": null,
  "[false,true,3.141592653589793]": null,
  "\"<undefined>\"": null
}"#;

    assert_eq!(json, expected);

    Ok(())
}

#[test]
fn serialize_number() -> Result<()> {
    // Check that integer values are serialized without fractional part
    assert_eq!(serde_json::to_string_pretty(&Value::from_f64(1.0))?, "1");
    assert_eq!(serde_json::to_string_pretty(&Value::from_f64(-1.0))?, "-1");

    // Ensure that fractional parts are also serialized.
    assert_eq!(serde_json::to_string_pretty(&Value::from_f64(1.1))?, "1.1");
    assert_eq!(
        serde_json::to_string_pretty(&Value::from_f64(-1.1))?,
        "-1.1"
    );

    Ok(())
}

#[test]
fn display_number() {
    use ordered_float::OrderedFloat;
    let n = Number(OrderedFloat(123456f64));
    assert_eq!(format!("{}", &n), "123456");
}

#[test]
fn serialize_string() -> Result<()> {
    assert_eq!(
        Value::String("Hello, World\n".to_owned()).to_json_str()?,
        "\"Hello, World\\n\""
    );
    Ok(())
}

#[test]
fn constructors() -> Result<()> {
    assert_eq!(Value::new_object(), Value::from_json_str("{}")?);
    assert!(Value::new_set().as_set()?.is_empty());
    Ok(())
}

#[test]
fn value_as_index() -> Result<()> {
    let idx = Value::from_f64(2.0);

    let mut item = Value::new_array();
    item.as_array_mut()?.push(Value::from_f64(3.0));
    item.as_array_mut()?.push(Value::from_f64(4.0));
    item.as_array_mut()?.push(Value::from_f64(5.0));

    // Check case of item present.
    assert_eq!(&Value::from_json_str("[1, 2, [3, 4, 5]]")?[&idx], &item);

    // Check case of item not present.
    let idx = Value::from_f64(5.0);
    assert_eq!(
        &Value::from_json_str("[1, 2, [3, 4, 5]]")?[&idx],
        &Value::Undefined
    );

    // Check case of non indexable item.
    assert_eq!(&Value::Undefined[&idx], &Value::Undefined);
    assert_eq!(&Value::Null[&idx], &Value::Undefined);
    assert_eq!(&Value::Bool(true)[&idx], &Value::Undefined);
    assert_eq!(&Value::String("Hello".to_owned())[&idx], &Value::Undefined);
    assert_eq!(&Value::new_set()[&idx], &Value::Undefined);

    Ok(())
}

#[test]
fn string_as_index() -> Result<()> {
    let obj = Value::from_json_str(r#"{ "a" : 5, "b" : 6 }"#)?;
    assert_eq!(&obj["a"], &Value::from_f64(5.0));
    assert_eq!(&obj[&"b".to_owned()], &Value::from_f64(6.0));
    Ok(())
}

#[test]
fn usize_as_index() -> Result<()> {
    assert_eq!(
        &Value::from_json_str("[1, 2, 3]")?[0],
        &Value::from_f64(1.0)
    );
    assert_eq!(&Value::from_json_str("[1, 2, 3]")?[5], &Value::Undefined);
    Ok(())
}

#[test]
fn api() -> Result<()> {
    assert!(&Value::from_json_str("{}")?.as_object()?.is_empty());
    let mut v = Value::new_object();
    v.as_object_mut()?
        .insert(Value::String("a".to_owned()), Value::from_f64(3.145));
    assert_eq!(v["a"], Value::from_f64(3.145));
    assert_eq!(v.as_object()?.len(), 1);

    // Null
    assert!(Value::Null.is_null());

    let v = Value::new_set();
    assert_eq!(v.as_set()?.len(), 0);

    // Check invalid api calls.
    assert!(matches!(Value::Undefined.as_object(), Err(_)));
    assert!(matches!(Value::Undefined.as_object_mut(), Err(_)));

    assert!(matches!(Value::Null.as_set(), Err(_)));
    assert!(matches!(Value::Null.as_set_mut(), Err(_)));

    assert!(matches!(Value::String("anc".to_owned()).as_array(), Err(_)));
    assert!(matches!(
        Value::String("anc".to_owned()).as_array_mut(),
        Err(_)
    ));

    assert!(matches!(Value::new_object().as_number(), Err(_)));
    assert!(matches!(Value::new_object().as_number_mut(), Err(_)));

    assert!(matches!(Value::from_f64(5.6).as_bool(), Err(_)));
    assert!(matches!(Value::from_f64(5.6).as_bool_mut(), Err(_)));
    Ok(())
}

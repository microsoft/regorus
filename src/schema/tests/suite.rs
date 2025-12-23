// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::shadow_unrelated,
    clippy::semicolon_if_nothing_returned,
    clippy::pattern_type_mismatch,
    clippy::assertions_on_result_states,
    clippy::as_conversions
)] // schema suite tests panic/unwrap to assert specific error shapes

use super::super::*;
use crate::{format, vec};
use serde_json::json;

#[test]
fn test_deserialize_any() {
    let schema = json!({
        "type": "any",
        "description": "any type",
        "default": 42
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Any {
            description,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("any type"));
            assert_eq!(default, &Some(Value::from(42)));
        }
        _ => panic!("Expected Type::Any"),
    }
}

#[test]
fn test_deserialize_integer_all_fields() {
    let schema = json!({
        "type": "integer",
        "description": "an integer",
        "minimum": 1,
        "maximum": 10,
        "default": 5
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("an integer"));
            assert_eq!(minimum, &Some(1));
            assert_eq!(maximum, &Some(10));
            assert_eq!(default, &Some(Value::from(5)));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_no_minimum() {
    let schema = json!({
        "type": "integer",
        "description": "no min",
        "maximum": 100,
        "default": 50
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("no min"));
            assert_eq!(minimum, &None);
            assert_eq!(maximum, &Some(100));
            assert_eq!(default, &Some(Value::from(50)));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_no_maximum() {
    let schema = json!({
        "type": "integer",
        "description": "no max",
        "minimum": -10,
        "default": 0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("no max"));
            assert_eq!(minimum, &Some(-10));
            assert_eq!(maximum, &None);
            assert_eq!(default, &Some(Value::from(0)));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_only_required() {
    let schema = json!({
        "type": "integer"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description, &None);
            assert_eq!(minimum, &None);
            assert_eq!(maximum, &None);
            assert_eq!(default, &None);
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_minimum_equals_maximum() {
    let schema = json!({
        "type": "integer",
        "minimum": 5,
        "maximum": 5
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(5));
            assert_eq!(maximum, &Some(5));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_negative_minimum_and_maximum() {
    let schema = json!({
        "type": "integer",
        "minimum": -100,
        "maximum": -1
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(-100));
            assert_eq!(maximum, &Some(-1));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_zero_minimum() {
    let schema = json!({
        "type": "integer",
        "minimum": 0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(0));
            assert_eq!(maximum, &None);
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_large_values() {
    let schema = json!({
        "type": "integer",
        "minimum": i64::MIN,
        "maximum": i64::MAX
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(i64::MIN));
            assert_eq!(maximum, &Some(i64::MAX));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_integer_invalid_minimum_type() {
    let schema = json!({
        "type": "integer",
        "minimum": "not_an_integer"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_integer_invalid_maximum_type() {
    let schema = json!({
        "type": "integer",
        "maximum": [1, 2, 3]
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_integer_minimum_greater_than_maximum() {
    let schema = json!({
        "type": "integer",
        "minimum": 10,
        "maximum": 5
    });
    // This will not error at deserialization, but you may want to add validation logic elsewhere.
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Integer {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(10));
            assert_eq!(maximum, &Some(5));
        }
        _ => panic!("Expected Type::Integer"),
    }
}

#[test]
fn test_deserialize_number_all_fields() {
    let schema = json!({
        "type": "number",
        "description": "a number",
        "minimum": 1.5,
        "maximum": 10.5,
        "default": 5.5
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("a number"));
            assert_eq!(minimum, &Some(1.5));
            assert_eq!(maximum, &Some(10.5));
            assert_eq!(default, &Some(Value::from(5.5)));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_no_minimum() {
    let schema = json!({
        "type": "number",
        "description": "no min",
        "maximum": 100.0,
        "default": 50.0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("no min"));
            assert_eq!(minimum, &None);
            assert_eq!(maximum, &Some(100.0));
            assert_eq!(default, &Some(Value::from(50.0)));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_no_maximum() {
    let schema = json!({
        "type": "number",
        "description": "no max",
        "minimum": -10.0,
        "default": 0.0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("no max"));
            assert_eq!(minimum, &Some(-10.0));
            assert_eq!(maximum, &None);
            assert_eq!(default, &Some(Value::from(0.0)));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_only_required() {
    let schema = json!({
        "type": "number"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            description,
            minimum,
            maximum,
            default,
        } => {
            assert_eq!(description, &None);
            assert_eq!(minimum, &None);
            assert_eq!(maximum, &None);
            assert_eq!(default, &None);
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_minimum_equals_maximum() {
    let schema = json!({
        "type": "number",
        "minimum": 5.5,
        "maximum": 5.5
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(5.5));
            assert_eq!(maximum, &Some(5.5));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_negative_minimum_and_maximum() {
    let schema = json!({
        "type": "number",
        "minimum": -100.25,
        "maximum": -1.75
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(-100.25));
            assert_eq!(maximum, &Some(-1.75));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_zero_minimum() {
    let schema = json!({
        "type": "number",
        "minimum": 0.0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(0.0));
            assert_eq!(maximum, &None);
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_large_values() {
    let schema = json!({
        "type": "number",
        "minimum": f64::MIN,
        "maximum": f64::MAX
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(f64::MIN));
            assert_eq!(maximum, &Some(f64::MAX));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_number_invalid_minimum_type() {
    let schema = json!({
        "type": "number",
        "minimum": "not_a_number"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_number_invalid_maximum_type() {
    let schema = json!({
        "type": "number",
        "maximum": [1, 2, 3]
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_number_minimum_greater_than_maximum() {
    let schema = json!({
        "type": "number",
        "minimum": 10.0,
        "maximum": 5.0
    });
    // This will not error at deserialization, but you may want to add validation logic elsewhere.
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Number {
            minimum, maximum, ..
        } => {
            assert_eq!(minimum, &Some(10.0));
            assert_eq!(maximum, &Some(5.0));
        }
        _ => panic!("Expected Type::Number"),
    }
}

#[test]
fn test_deserialize_boolean_all_fields() {
    let schema = json!({
        "type": "boolean",
        "description": "a boolean",
        "default": true
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Boolean {
            description,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("a boolean"));
            assert_eq!(default, &Some(Value::from(true)));
        }
        _ => panic!("Expected Type::Boolean"),
    }
}

#[test]
fn test_deserialize_boolean_no_description() {
    let schema = json!({
        "type": "boolean",
        "default": false
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Boolean {
            description,
            default,
        } => {
            assert_eq!(description, &None);
            assert_eq!(default, &Some(Value::from(false)));
        }
        _ => panic!("Expected Type::Boolean"),
    }
}

#[test]
fn test_deserialize_boolean_no_default() {
    let schema = json!({
        "type": "boolean",
        "description": "no default"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Boolean {
            description,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("no default"));
            assert_eq!(default, &None);
        }
        _ => panic!("Expected Type::Boolean"),
    }
}

#[test]
fn test_deserialize_boolean_only_required() {
    let schema = json!({
        "type": "boolean"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Boolean {
            description,
            default,
        } => {
            assert_eq!(description, &None);
            assert_eq!(default, &None);
        }
        _ => panic!("Expected Type::Boolean"),
    }
}

#[test]
fn test_deserialize_null_all_fields() {
    let schema = json!({
        "type": "null",
        "description": "a null"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Null { description } => {
            assert_eq!(description.as_deref(), Some("a null"));
        }
        _ => panic!("Expected Type::Null"),
    }
}

#[test]
fn test_deserialize_null_no_description() {
    let schema = json!({
        "type": "null"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Null { description } => {
            assert_eq!(description, &None);
        }
        _ => panic!("Expected Type::Null"),
    }
}

#[test]
fn test_deserialize_string_all_fields() {
    let schema = json!({
        "type": "string",
        "description": "a string",
        "minLength": 2,
        "maxLength": 10,
        "pattern": "^abc",
        "default": "abc"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String {
            description,
            min_length,
            max_length,
            pattern,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("a string"));
            assert_eq!(min_length, &Some(2));
            assert_eq!(max_length, &Some(10));
            assert_eq!(pattern.as_deref(), Some("^abc"));
            assert_eq!(default, &Some(Value::from("abc")));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_no_min_max_pattern() {
    let schema = json!({
        "type": "string",
        "description": "no min/max/pattern",
        "default": "foo"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String {
            description,
            min_length,
            max_length,
            pattern,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("no min/max/pattern"));
            assert_eq!(min_length, &None);
            assert_eq!(max_length, &None);
            assert_eq!(pattern, &None);
            assert_eq!(default, &Some(Value::from("foo")));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_only_required() {
    let schema = json!({
        "type": "string"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String {
            description,
            min_length,
            max_length,
            pattern,
            default,
        } => {
            assert_eq!(description, &None);
            assert_eq!(min_length, &None);
            assert_eq!(max_length, &None);
            assert_eq!(pattern, &None);
            assert_eq!(default, &None);
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_min_equals_max() {
    let schema = json!({
        "type": "string",
        "minLength": 5,
        "maxLength": 5
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String {
            min_length,
            max_length,
            ..
        } => {
            assert_eq!(min_length, &Some(5));
            assert_eq!(max_length, &Some(5));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_zero_min_length() {
    let schema = json!({
        "type": "string",
        "minLength": 0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String { min_length, .. } => {
            assert_eq!(min_length, &Some(0));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_invalid_min_length_type() {
    let schema = json!({
        "type": "string",
        "minLength": "not_a_number"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_string_invalid_max_length_type() {
    let schema = json!({
        "type": "string",
        "maxLength": [1, 2, 3]
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_string_empty_pattern() {
    let schema = json!({
        "type": "string",
        "pattern": ""
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String { pattern, .. } => {
            assert_eq!(pattern.as_deref(), Some(""));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_unicode_pattern() {
    let schema = json!({
        "type": "string",
        "pattern": "^[\\u4e00-\\u9fa5]+$"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String { pattern, .. } => {
            assert_eq!(pattern.as_deref(), Some("^[\\u4e00-\\u9fa5]+$"));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_large_min_max_length() {
    let schema = json!({
        "type": "string",
        "minLength": usize::MAX,
        "maxLength": usize::MAX
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::String {
            min_length,
            max_length,
            ..
        } => {
            assert_eq!(min_length, &Some(usize::MAX));
            assert_eq!(max_length, &Some(usize::MAX));
        }
        _ => panic!("Expected Type::String"),
    }
}

#[test]
fn test_deserialize_string_invalid_pattern_type() {
    let schema = json!({
        "type": "string",
        "pattern": 123
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_array_only_required() {
    let schema = json!({
        "type": "array",
        "items": { "type": "integer" }
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            description,
            items,
            min_items,
            max_items,
            default,
        } => {
            assert_eq!(description, &None);
            assert_eq!(min_items, &None);
            assert_eq!(max_items, &None);
            assert_eq!(default, &None);
            // Assert items fields individually
            match items.as_type() {
                Type::Integer {
                    description,
                    minimum,
                    maximum,
                    default,
                } => {
                    assert_eq!(description, &None);
                    assert_eq!(minimum, &None);
                    assert_eq!(maximum, &None);
                    assert_eq!(default, &None);
                }
                _ => panic!("Expected items to be Type::Integer"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_min_equals_max() {
    let schema = json!({
        "type": "array",
        "items": { "type": "boolean" },
        "minItems": 3,
        "maxItems": 3
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(3));
            assert_eq!(max_items, &Some(3));
            match items.as_type() {
                Type::Boolean {
                    description,
                    default,
                } => {
                    assert_eq!(description, &None);
                    assert_eq!(default, &None);
                }
                _ => panic!("Expected items to be Type::Boolean"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_zero_min_items() {
    let schema = json!({
        "type": "array",
        "items": { "type": "null" },
        "minItems": 0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items, items, ..
        } => {
            assert_eq!(min_items, &Some(0));
            match items.as_type() {
                Type::Null { description } => {
                    assert_eq!(description, &None);
                }
                _ => panic!("Expected items to be Type::Null"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_min_greater_than_max() {
    let schema = json!({
        "type": "array",
        "items": { "type": "string" },
        "minItems": 10,
        "maxItems": 5
    });
    // This will not error at deserialization, but you may want to add validation logic elsewhere.
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(10));
            assert_eq!(max_items, &Some(5));
            match items.as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected items to be Type::String"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_large_min_max() {
    let schema = json!({
        "type": "array",
        "items": { "type": "number" },
        "minItems": usize::MAX,
        "maxItems": usize::MAX
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(usize::MAX));
            assert_eq!(max_items, &Some(usize::MAX));
            match items.as_type() {
                Type::Number { .. } => {}
                _ => panic!("Expected items to be Type::Number"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_invalid_min_items_type() {
    let schema = json!({
        "type": "array",
        "items": { "type": "string" },
        "minItems": "not_a_number"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_array_invalid_max_items_type() {
    let schema = json!({
        "type": "array",
        "items": { "type": "string" },
        "maxItems": [1, 2, 3]
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_array_invalid_items_type() {
    let schema = json!({
        "type": "array",
        "items": 123
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_array_items_with_fields() {
    let schema = json!({
        "type": "array",
        "items": {
            "type": "string",
            "description": "inner string",
            "minLength": 1,
            "maxLength": 8,
            "pattern": "foo",
            "default": "bar"
        },
        "minItems": 1,
        "maxItems": 2,
        "description": "outer array",
        "default": ["bar"]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            description,
            items,
            min_items,
            max_items,
            default,
        } => {
            assert_eq!(description.as_deref(), Some("outer array"));
            assert_eq!(min_items, &Some(1));
            assert_eq!(max_items, &Some(2));
            assert_eq!(
                default,
                &Some(Value::Array(Rc::new(vec![Value::from("bar")])))
            );
            match items.as_type() {
                Type::String {
                    description,
                    min_length,
                    max_length,
                    pattern,
                    default,
                } => {
                    assert_eq!(description.as_deref(), Some("inner string"));
                    assert_eq!(min_length, &Some(1));
                    assert_eq!(max_length, &Some(8));
                    assert_eq!(pattern.as_deref(), Some("foo"));
                    assert_eq!(default, &Some(Value::from("bar")));
                }
                _ => panic!("Expected items to be Type::String"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_min_items_none_max_items_some() {
    let schema = json!({
        "type": "array",
        "items": { "type": "string" },
        "maxItems": 7
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &None);
            assert_eq!(max_items, &Some(7));
            match items.as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected items to be Type::String"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_min_items_some_max_items_none() {
    let schema = json!({
        "type": "array",
        "items": { "type": "boolean" },
        "minItems": 2
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(2));
            assert_eq!(max_items, &None);
            match items.as_type() {
                Type::Boolean { .. } => {}
                _ => panic!("Expected items to be Type::Boolean"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_min_items_zero_max_items_zero() {
    let schema = json!({
        "type": "array",
        "items": { "type": "null" },
        "minItems": 0,
        "maxItems": 0
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(0));
            assert_eq!(max_items, &Some(0));
            match items.as_type() {
                Type::Null { .. } => {}
                _ => panic!("Expected items to be Type::Null"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_min_items_greater_than_max_items() {
    let schema = json!({
        "type": "array",
        "items": { "type": "number" },
        "minItems": 5,
        "maxItems": 2
    });
    // This is a corner case: minItems > maxItems, should not error at deserialization.
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(5));
            assert_eq!(max_items, &Some(2));
            match items.as_type() {
                Type::Number { .. } => {}
                _ => panic!("Expected items to be Type::Number"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_array_items_with_nested_array() {
    let schema = json!({
        "type": "array",
        "items": {
            "type": "array",
            "items": { "type": "integer" },
            "minItems": 1,
            "maxItems": 2
        },
        "minItems": 2,
        "maxItems": 3
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Array {
            min_items,
            max_items,
            items,
            ..
        } => {
            assert_eq!(min_items, &Some(2));
            assert_eq!(max_items, &Some(3));
            match items.as_type() {
                Type::Array {
                    min_items: inner_min,
                    max_items: inner_max,
                    items: inner_items,
                    ..
                } => {
                    assert_eq!(inner_min, &Some(1));
                    assert_eq!(inner_max, &Some(2));
                    match inner_items.as_type() {
                        Type::Integer { .. } => {}
                        _ => panic!("Expected nested items to be Type::Integer"),
                    }
                }
                _ => panic!("Expected items to be Type::Array"),
            }
        }
        _ => panic!("Expected Type::Array"),
    }
}

#[test]
fn test_deserialize_object_all_fields() {
    let schema = json!({
        "type": "object",
        "description": "an object",
        "properties": {
            "foo": { "type": "string" },
            "bar": { "type": "integer" }
        },
        "required": ["foo"],
        "additionalProperties": { "type": "boolean" },
        "name": "MyObject",
        "default": { "foo": "abc", "bar": 42 }
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            description,
            properties,
            required,
            additional_properties,
            name,
            default,
            discriminated_subobject,
        } => {
            assert_eq!(description.as_deref(), Some("an object"));
            assert_eq!(name.as_deref(), Some("MyObject"));
            assert_eq!(
                default,
                &Some(Value::Object(Rc::new(
                    [
                        ("foo".into(), Value::from("abc")),
                        ("bar".into(), Value::from(42))
                    ]
                    .iter()
                    .cloned()
                    .collect()
                )))
            );
            // properties
            assert_eq!(properties.len(), 2);
            match properties.get("foo").unwrap().as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected foo to be Type::String"),
            }
            match properties.get("bar").unwrap().as_type() {
                Type::Integer { .. } => {}
                _ => panic!("Expected bar to be Type::Integer"),
            }
            // required
            let req = required.as_ref().expect("required should be present");
            assert_eq!(req.len(), 1);
            assert_eq!(req[0].as_ref(), "foo");
            // additional_properties
            match additional_properties.as_ref().unwrap().as_type() {
                Type::Boolean { .. } => {}
                _ => panic!("Expected additionalProperties to be Type::Boolean"),
            }
            // discriminated_subobject
            assert!(discriminated_subobject.is_none());
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_only_required() {
    let schema = json!({
        "type": "object",
        "properties": {}
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            description,
            properties,
            required,
            additional_properties,
            name,
            default,
            discriminated_subobject,
        } => {
            assert_eq!(description, &None);
            assert_eq!(properties.len(), 0);
            assert!(required.is_none());
            assert!(matches!(
                additional_properties.as_ref().unwrap().as_type(),
                Type::Any { .. }
            ));
            assert!(name.is_none());
            assert!(default.is_none());
            assert!(discriminated_subobject.is_none());
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_with_required_and_additional_properties() {
    let schema = json!({
        "type": "object",
        "properties": {
            "x": { "type": "number" }
        },
        "required": ["x"],
        "additionalProperties": { "type": "string" }
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            properties,
            required,
            additional_properties,
            ..
        } => {
            assert_eq!(properties.len(), 1);
            match properties.get("x").unwrap().as_type() {
                Type::Number { .. } => {}
                _ => panic!("Expected x to be Type::Number"),
            }
            let req = required.as_ref().expect("required should be present");
            assert_eq!(req.len(), 1);
            assert_eq!(req[0].as_ref(), "x");
            match additional_properties.as_ref().unwrap().as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected additionalProperties to be Type::String"),
            }
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_with_discriminated_subobject() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "allOf": [
            {
                "if": { "properties": { "kind": { "const": "foo" } } },
                "then": {
                    "properties": { "foo": { "type": "string" } },
                    "required": ["foo"]
                }
            },
            {
                "if": { "properties": { "kind": { "const": "bar" } } },
                "then": {
                    "properties": { "bar": { "type": "integer" } },
                    "required": ["bar"]
                }
            }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            discriminated_subobject,
            ..
        } => {
            let dso = discriminated_subobject
                .as_ref()
                .expect("should have discriminated_subobject");
            assert_eq!(dso.discriminator.as_ref(), "kind");
            assert_eq!(dso.variants.len(), 2);
            let foo_variant = dso.variants.get("foo").expect("foo variant");
            assert!(foo_variant.properties.contains_key("foo"));
            let bar_variant = dso.variants.get("bar").expect("bar variant");
            assert!(bar_variant.properties.contains_key("bar"));
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_invalid_properties_type() {
    let schema = json!({
        "type": "object",
        "properties": 123
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_object_invalid_required_type() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "required": "not_an_array"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_object_invalid_additional_properties_type() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "additionalProperties": 123
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_object_empty_properties_and_required() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "required": []
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert_eq!(properties.len(), 0);
            let req = required.as_ref().expect("required should be present");
            assert!(req.is_empty());
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_required_not_in_properties() {
    let schema = json!({
        "type": "object",
        "properties": { "x": { "type": "string" } },
        "required": ["y"]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert_eq!(properties.len(), 1);
            let req = required.as_ref().expect("required should be present");
            assert_eq!(req.len(), 1);
            assert_eq!(req[0].as_ref(), "y");
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_additional_properties_none() {
    let schema = json!({
        "type": "object",
        "properties": { "foo": { "type": "string" } }
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            additional_properties,
            ..
        } => {
            // When no additionalProperties field is specified, the default behavior
            // is to allow additional properties of any type
            match additional_properties.as_ref().unwrap().as_type() {
                Type::Any { .. } => {}
                _ => panic!("Expected additionalProperties to default to Type::Any"),
            }
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_additional_properties_false() {
    let schema = json!({
        "type": "object",
        "properties": { "foo": { "type": "string" } },
        "additionalProperties": false
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            additional_properties,
            ..
        } => {
            // When additionalProperties is false, no additional properties are allowed
            assert!(
                additional_properties.is_none(),
                "Expected additionalProperties to be None when set to false"
            );
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_additional_properties_true() {
    let schema = json!({
        "type": "object",
        "properties": { "foo": { "type": "string" } },
        "additionalProperties": true
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            additional_properties,
            ..
        } => {
            // When additionalProperties is true, additional properties of any type are allowed
            match additional_properties.as_ref().unwrap().as_type() {
                Type::Any { .. } => {}
                _ => panic!("Expected additionalProperties to be Type::Any when set to true"),
            }
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_name_field_only() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "name": "OnlyName"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object { name, .. } => {
            assert_eq!(name.as_deref(), Some("OnlyName"));
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_default_empty_object() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "default": {}
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object { default, .. } => {
            assert_eq!(default, &Some(Value::Object(Rc::new(BTreeMap::new()))));
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_with_empty_discriminated_subobject() {
    let schema = json!({
        "type": "object",
        "properties": {},
        "allOf": []
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_object_nested_2_levels() {
    let schema = json!({
        "type": "object",
        "properties": {
            "level1": {
                "type": "object",
                "properties": {
                    "level2": { "type": "string" }
                }
            }
        }
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object { properties, .. } => {
            let level1 = properties.get("level1").expect("level1 property");
            match level1.as_type() {
                Type::Object {
                    properties: props2, ..
                } => {
                    let level2 = props2.get("level2").expect("level2 property");
                    match level2.as_type() {
                        Type::String { .. } => {}
                        _ => panic!("Expected level2 to be Type::String"),
                    }
                }
                _ => panic!("Expected level1 to be Type::Object"),
            }
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_object_nested_3_levels() {
    let schema = json!({
        "type": "object",
        "properties": {
            "a": {
                "type": "object",
                "properties": {
                    "b": {
                        "type": "object",
                        "properties": {
                            "c": { "type": "integer" }
                        }
                    }
                }
            }
        }
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object { properties, .. } => {
            let a = properties.get("a").expect("a property");
            match a.as_type() {
                Type::Object {
                    properties: props_b,
                    ..
                } => {
                    let b = props_b.get("b").expect("b property");
                    match b.as_type() {
                        Type::Object {
                            properties: props_c,
                            ..
                        } => {
                            let c = props_c.get("c").expect("c property");
                            match c.as_type() {
                                Type::Integer { .. } => {}
                                _ => panic!("Expected c to be Type::Integer"),
                            }
                        }
                        _ => panic!("Expected b to be Type::Object"),
                    }
                }
                _ => panic!("Expected a to be Type::Object"),
            }
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_deserialize_enum_all_fields() {
    let schema = json!({
        "enum": ["foo", "bar", 42, true, null],
        "description": "an enum"
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum {
            description,
            values,
        } => {
            assert_eq!(description.as_deref(), Some("an enum"));
            assert_eq!(values.len(), 5);
            assert_eq!(values[0], Value::from("foo"));
            assert_eq!(values[1], Value::from("bar"));
            assert_eq!(values[2], Value::from(42));
            assert_eq!(values[3], Value::from(true));
            assert_eq!(values[4], Value::Null);
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_only_required() {
    let schema = json!({
        "enum": ["a", "b"]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum {
            description,
            values,
        } => {
            assert_eq!(description, &None);
            assert_eq!(values.len(), 2);
            assert_eq!(values[0], Value::from("a"));
            assert_eq!(values[1], Value::from("b"));
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_empty_values() {
    let schema = json!({
        "enum": [],
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => {
            assert!(values.is_empty());
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_single_value() {
    let schema = json!({
        "enum": [123]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => {
            assert_eq!(values.len(), 1);
            assert_eq!(values[0], Value::from(123));
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_mixed_types() {
    let schema = json!({
        "enum": ["x", 1, false, null, {"foo": "bar"}, [1,2,3]]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => {
            assert_eq!(values.len(), 6);
            assert_eq!(values[0], Value::from("x"));
            assert_eq!(values[1], Value::from(1));
            assert_eq!(values[2], Value::from(false));
            assert_eq!(values[3], Value::Null);
            // Object and array types
            match &values[4] {
                Value::Object(obj) => {
                    assert_eq!(obj.get(&Value::from("foo")), Some(&Value::from("bar")))
                }
                _ => panic!("Expected object in enum values"),
            }
            match &values[5] {
                Value::Array(arr) => {
                    assert_eq!(arr.len(), 3);
                    assert_eq!(arr[0], Value::from(1));
                    assert_eq!(arr[1], Value::from(2));
                    assert_eq!(arr[2], Value::from(3));
                }
                _ => panic!("Expected array in enum values"),
            }
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_invalid_values_type() {
    let schema = json!({
        "enum": "not_an_array"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_enum_with_duplicate_values() {
    let schema = json!({
        "enum": ["dup", "dup", 1, 1, null, null]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => {
            assert_eq!(values.len(), 6);
            assert_eq!(values[0], Value::from("dup"));
            assert_eq!(values[1], Value::from("dup"));
            assert_eq!(values[2], Value::from(1));
            assert_eq!(values[3], Value::from(1));
            assert_eq!(values[4], Value::Null);
            assert_eq!(values[5], Value::Null);
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_all_values_null() {
    let schema = json!({
        "enum": [null, null, null]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => {
            assert_eq!(values.len(), 3);
            assert!(values.iter().all(|v| *v == Value::Null));
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_large_number_of_values() {
    let values: Vec<_> = (0..1000).map(Value::from).collect();
    let schema = json!({
        "enum": values
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => {
            assert_eq!(values.len(), 1000);
            assert_eq!(values[0], Value::from(0));
            assert_eq!(values[999], Value::from(999));
        }
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_values_with_object_non_string_keys() {
    // JSON keys are always strings, but serde_json will parse them as such.
    let schema = json!({
        "enum": [
            { "1": "one", "true": "bool" }
        ]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => match &values[0] {
            Value::Object(obj) => {
                assert_eq!(obj[&Value::from("1")], Value::from("one"));
                assert_eq!(obj[&Value::from("true")], Value::from("bool"));
            }
            _ => panic!("Expected object in enum values"),
        },
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_enum_values_with_deeply_nested_structures() {
    let schema = json!({
        "enum": [
            {
                "a": [
                    { "b": [1, 2, { "c": null }] }
                ]
            }
        ]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Enum { values, .. } => match &values[0] {
            Value::Object(obj) => {
                let a = &obj[&Value::from("a")];
                match a {
                    Value::Array(arr) => match &arr[0] {
                        Value::Object(inner) => {
                            let b = &inner[&Value::from("b")];
                            match b {
                                Value::Array(barr) => {
                                    assert_eq!(barr[0], Value::from(1));
                                    assert_eq!(barr[1], Value::from(2));
                                    match &barr[2] {
                                        Value::Object(cobj) => {
                                            assert_eq!(cobj[&Value::from("c")], Value::Null);
                                        }
                                        _ => panic!("Expected object for 'c'"),
                                    }
                                }
                                _ => panic!("Expected array for 'b'"),
                            }
                        }
                        _ => panic!("Expected object in 'a' array"),
                    },
                    _ => panic!("Expected array for 'a'"),
                }
            }
            _ => panic!("Expected object in enum values"),
        },
        _ => panic!("Expected Type::Enum"),
    }
}

#[test]
fn test_deserialize_const_all_fields() {
    let schema = json!({
        "const": 42,
        "description": "a constant",
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { description, value } => {
            assert_eq!(description.as_deref(), Some("a constant"));
            assert_eq!(value, &Value::from(42));
        }
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_only_required() {
    let schema = json!({
        "const": "foo"
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { description, value } => {
            assert_eq!(description, &None);
            assert_eq!(value, &Value::from("foo"));
        }
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_value_null() {
    let schema = json!({
        "const": null
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { value, .. } => {
            assert_eq!(value, &Value::Null);
        }
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_value_object() {
    let schema = json!({
        "const": { "foo": "bar", "baz": 1 }
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { value, .. } => match value {
            Value::Object(ref obj) => {
                assert_eq!(obj[&Value::from("foo")], Value::from("bar"));
                assert_eq!(obj[&Value::from("baz")], Value::from(1));
            }
            _ => panic!("Expected object for const value"),
        },
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_value_array() {
    let schema = json!({
        "const": [1, 2, 3]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { value, .. } => match value {
            Value::Array(ref arr) => {
                assert_eq!(arr.len(), 3);
                assert_eq!(arr[0], Value::from(1));
                assert_eq!(arr[1], Value::from(2));
                assert_eq!(arr[2], Value::from(3));
            }
            _ => panic!("Expected array for const value"),
        },
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_value_boolean() {
    let schema = json!({
        "const": true
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { value, .. } => {
            assert_eq!(value, &Value::from(true));
        }
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_value_deeply_nested() {
    let schema = json!({
        "const": {
            "a": [1, { "b": [null, false] }]
        }
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Const { value, .. } => match value {
            Value::Object(ref obj) => {
                let a = &obj[&Value::from("a")];
                match a {
                    Value::Array(arr) => {
                        assert_eq!(arr[0], Value::from(1));
                        match &arr[1] {
                            Value::Object(inner) => {
                                let b = &inner[&Value::from("b")];
                                match b {
                                    Value::Array(barr) => {
                                        assert_eq!(barr[0], Value::Null);
                                        assert_eq!(barr[1], Value::from(false));
                                    }
                                    _ => panic!("Expected array for 'b'"),
                                }
                            }
                            _ => panic!("Expected object in 'a' array"),
                        }
                    }
                    _ => panic!("Expected array for 'a'"),
                }
            }
            _ => panic!("Expected object for const value"),
        },
        _ => panic!("Expected Type::Const"),
    }
}

#[test]
fn test_deserialize_const_invalid_missing_value() {
    let schema = json!({
        "type": "const"
    });
    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_basic() {
    let schema = json!({
        "anyOf": [
            { "type": "string" },
            { "type": "integer" }
        ]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 2);
            match variants[0].as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected first variant to be Type::String"),
            }
            match variants[1].as_type() {
                Type::Integer { .. } => {}
                _ => panic!("Expected second variant to be Type::Integer"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_single_variant() {
    let schema = json!({
        "anyOf": [
            { "type": "string" }
        ]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 1);
            match variants[0].as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected variant to be Type::String"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_empty() {
    let schema = json!({
        "anyOf": []
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert!(variants.is_empty());
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_mixed_types() {
    let schema = json!({
        "anyOf": [
            { "type": "string" },
            { "type": "integer" },
            { "type": "array", "items": { "type": "boolean" } },
            { "type": "object", "properties": { "foo": { "type": "null" } } }
        ]
    });
    let s: Schema = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 4);
            match variants[0].as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected variant 0 to be Type::String"),
            }
            match variants[1].as_type() {
                Type::Integer { .. } => {}
                _ => panic!("Expected variant 1 to be Type::Integer"),
            }
            match variants[2].as_type() {
                Type::Array { items, .. } => match items.as_type() {
                    Type::Boolean { .. } => {}
                    _ => panic!("Expected array items to be Type::Boolean"),
                },
                _ => panic!("Expected variant 2 to be Type::Array"),
            }
            match variants[3].as_type() {
                Type::Object { properties, .. } => {
                    assert!(properties.contains_key("foo"));
                }
                _ => panic!("Expected variant 3 to be Type::Object"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_invalid_variants_type() {
    let schema = json!({
        "anyOf": "not_an_array"
    });
    let result: Result<Schema, _> = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_missing_anyof() {
    let schema = json!({});
    let result: Result<Schema, _> = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_with_invalid_variant() {
    let schema = json!({
        "anyOf": [
            { "type": "string" },
            123
        ]
    });
    let result: Result<Schema, _> = Schema::from_serde_json_value(schema);
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_deeply_nested() {
    let schema = json!({
        "anyOf": [
            {
                "anyOf": [
                    { "type": "string" },
                    { "type": "integer" }
                ]
            },
            { "type": "boolean" }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 2);
            match variants[0].as_type() {
                Type::AnyOf(inner) => {
                    assert_eq!(inner.len(), 2);
                    match inner[0].as_type() {
                        Type::String { .. } => {}
                        _ => panic!("Expected inner variant 0 to be Type::String"),
                    }
                    match inner[1].as_type() {
                        Type::Integer { .. } => {}
                        _ => panic!("Expected inner variant 1 to be Type::Integer"),
                    }
                }
                _ => panic!("Expected first variant to be Type::AnyOf"),
            }
            match variants[1].as_type() {
                Type::Boolean { .. } => {}
                _ => panic!("Expected second variant to be Type::Boolean"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_all_null() {
    let schema = json!({
        "anyOf": [null, null, null]
    });
    let result = Schema::from_serde_json_value(schema);
    // Should error: null is not a valid schema
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_with_duplicates() {
    let schema = json!({
        "anyOf": [
            { "type": "string" },
            { "type": "string" },
            { "type": "integer" },
            { "type": "integer" }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 4);
            match variants[0].as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected variant 0 to be Type::String"),
            }
            match variants[1].as_type() {
                Type::String { .. } => {}
                _ => panic!("Expected variant 1 to be Type::String"),
            }
            match variants[2].as_type() {
                Type::Integer { .. } => {}
                _ => panic!("Expected variant 2 to be Type::Integer"),
            }
            match variants[3].as_type() {
                Type::Integer { .. } => {}
                _ => panic!("Expected variant 3 to be Type::Integer"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_large_number_of_variants() {
    let variants: Vec<_> = (0..100)
        .map(|i| json!({ "type": "integer", "default": i }))
        .collect();
    let schema = json!({
        "anyOf": variants
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 100);
            for (i, v) in variants.iter().enumerate() {
                match v.as_type() {
                    Type::Integer { default, .. } => {
                        assert_eq!(default, &Some(Value::from(i as i64)));
                    }
                    _ => panic!("Expected all variants to be Type::Integer"),
                }
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_deeply_nested_multiple_levels() {
    let schema = json!({
        "anyOf": [
            {
                "anyOf": [
                    {
                        "anyOf": [
                            { "type": "string" }
                        ]
                    }
                ]
            }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(outer) => {
            assert_eq!(outer.len(), 1);
            match outer[0].as_type() {
                Type::AnyOf(middle) => {
                    assert_eq!(middle.len(), 1);
                    match middle[0].as_type() {
                        Type::AnyOf(inner) => {
                            assert_eq!(inner.len(), 1);
                            match inner[0].as_type() {
                                Type::String { .. } => {}
                                _ => panic!("Expected innermost to be Type::String"),
                            }
                        }
                        _ => panic!("Expected middle to be Type::AnyOf"),
                    }
                }
                _ => panic!("Expected outer to be Type::AnyOf"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_empty_object_variant() {
    let schema = json!({
        "anyOf": [
            {}
        ]
    });
    let result = Schema::from_serde_json_value(schema);
    // Should error: empty object is not a valid schema
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_with_invalid_schema_in_list() {
    let schema = json!({
        "anyOf": [
            { "type": "string" },
            { "foo": "bar" }
        ]
    });
    let result = Schema::from_serde_json_value(schema);
    // Should error: { "foo": "bar" } is not a valid schema
    assert!(result.is_err());
}

#[test]
fn test_deserialize_anyof_all_same_variant() {
    let schema = json!({
        "anyOf": [
            { "type": "boolean" },
            { "type": "boolean" },
            { "type": "boolean" }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 3);
            for v in variants.iter() {
                match v.as_type() {
                    Type::Boolean { .. } => {}
                    _ => panic!("Expected all variants to be Type::Boolean"),
                }
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_nested_types() {
    let schema = json!({
        "anyOf": [
            { "type": "string", "minLength": 2 },
            { "type": "integer", "minimum": 0 },
            {
                "type": "array",
                "items": { "type": "boolean" },
                "minItems": 1
            },
            {
                "type": "object",
                "properties": {
                    "foo": { "type": "string" },
                    "bar": { "type": "number" }
                },
                "required": ["foo"]
            }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 4);
            match &variants[0].as_type() {
                Type::String { min_length, .. } => assert_eq!(min_length, &Some(2)),
                _ => panic!("Expected first variant to be Type::String"),
            }
            match &variants[1].as_type() {
                Type::Integer { minimum, .. } => assert_eq!(minimum, &Some(0)),
                _ => panic!("Expected second variant to be Type::Integer"),
            }
            match &variants[2].as_type() {
                Type::Array {
                    items, min_items, ..
                } => {
                    assert_eq!(min_items, &Some(1));
                    match items.as_type() {
                        Type::Boolean { .. } => {}
                        _ => panic!("Expected array items to be Type::Boolean"),
                    }
                }
                _ => panic!("Expected third variant to be Type::Array"),
            }
            match &variants[3].as_type() {
                Type::Object {
                    properties,
                    required,
                    ..
                } => {
                    assert!(properties.contains_key("foo"));
                    assert!(properties.contains_key("bar"));
                    let req = required.as_ref().expect("required should be present");
                    assert_eq!(req[0].as_ref(), "foo");
                }
                _ => panic!("Expected fourth variant to be Type::Object"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_deeply_nested_anyof() {
    let schema = json!({
        "anyOf": [
            {
                "anyOf": [
                    { "type": "string" },
                    { "type": "null" }
                ]
            },
            { "type": "integer" }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 2);
            match &variants[0].as_type() {
                Type::AnyOf(inner_variants) => {
                    assert_eq!(inner_variants.len(), 2);
                    match inner_variants[0].as_type() {
                        Type::String { .. } => {}
                        _ => panic!("Expected inner variant 0 to be Type::String"),
                    }
                    match inner_variants[1].as_type() {
                        Type::Null { .. } => {}
                        _ => panic!("Expected inner variant 1 to be Type::Null"),
                    }
                }
                _ => panic!("Expected first variant to be Type::AnyOf"),
            }
            match &variants[1].as_type() {
                Type::Integer { .. } => {}
                _ => panic!("Expected second variant to be Type::Integer"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_enum_and_const() {
    let schema = json!({
        "anyOf": [
            {
                "enum": ["a", "b", "c"]
            },
            {
                "const": 42
            }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 2);
            match &variants[0].as_type() {
                Type::Enum { values, .. } => {
                    assert_eq!(
                        values.as_ref(),
                        &vec![Value::from("a"), Value::from("b"), Value::from("c")]
                    );
                }
                _ => panic!("Expected first variant to be Type::Enum"),
            }
            match &variants[1].as_type() {
                Type::Const { value, .. } => {
                    assert_eq!(value, &Value::from(42));
                }
                _ => panic!("Expected second variant to be Type::Const"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_complex_nesting() {
    let schema = json!({
        "anyOf": [
            {
                "type": "object",
                "properties": {
                    "x": {
                        "anyOf": [
                            { "type": "string" },
                            { "type": "integer" }
                        ]
                    }
                }
            },
            {
                "type": "array",
                "items": {
                    "anyOf": [
                        { "type": "boolean" },
                        { "type": "null" }
                    ]
                }
            }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 2);
            match &variants[0].as_type() {
                Type::Object { properties, .. } => {
                    let x = properties.get("x").expect("x property");
                    match x.as_type() {
                        Type::AnyOf(inner) => {
                            assert_eq!(inner.len(), 2);
                            match inner[0].as_type() {
                                Type::String { .. } => {}
                                _ => panic!("Expected x.anyOf[0] to be Type::String"),
                            }
                            match inner[1].as_type() {
                                Type::Integer { .. } => {}
                                _ => panic!("Expected x.anyOf[1] to be Type::Integer"),
                            }
                        }
                        _ => panic!("Expected x to be Type::AnyOf"),
                    }
                }
                _ => panic!("Expected first variant to be Type::Object"),
            }
            match &variants[1].as_type() {
                Type::Array { items, .. } => match items.as_type() {
                    Type::AnyOf(inner) => {
                        assert_eq!(inner.len(), 2);
                        match inner[0].as_type() {
                            Type::Boolean { .. } => {}
                            _ => panic!("Expected items.anyOf[0] to be Type::Boolean"),
                        }
                        match inner[1].as_type() {
                            Type::Null { .. } => {}
                            _ => panic!("Expected items.anyOf[1] to be Type::Null"),
                        }
                    }
                    _ => panic!("Expected items to be Type::AnyOf"),
                },
                _ => panic!("Expected second variant to be Type::Array"),
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_duplicate_and_null_variants() {
    let schema = json!({
        "anyOf": [
            { "type": "null" },
            { "type": "null" },
            { "type": "string" },
            { "type": "string" }
        ]
    });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 4);
            assert!(matches!(variants[0].as_type(), Type::Null { .. }));
            assert!(matches!(variants[1].as_type(), Type::Null { .. }));
            assert!(matches!(variants[2].as_type(), Type::String { .. }));
            assert!(matches!(variants[3].as_type(), Type::String { .. }));
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_anyof_with_large_number_of_variants() {
    let variants: Vec<_> = (0..100)
        .map(|i| json!({ "type": "integer", "minimum": i }))
        .collect();
    let schema = json!({ "anyOf": variants });
    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::AnyOf(variants) => {
            assert_eq!(variants.len(), 100);
            for (i, v) in variants.iter().enumerate() {
                match v.as_type() {
                    Type::Integer { minimum, .. } => assert_eq!(minimum, &Some(i as i64)),
                    _ => panic!("Expected variant {} to be Type::Integer", i),
                }
            }
        }
        _ => panic!("Expected Type::AnyOf"),
    }
}

#[test]
fn test_deserialize_object_with_mixed_discriminators_error() {
    // This test verifies that using different discriminator fields in the same
    // discriminated subobject results in an error
    let schema = json!({
        "type": "object",
        "peekoo": 1,
        "properties": {
            "name": { "type": "string" }
        },
        "allOf": [
            {
                "if": {
                    "properties": {
                        "type": { "const": "user" }
                    }
                },
                "then": {
                    "properties": {
                        "email": { "type": "string" }
                    },
                    "required": ["email"]
                }
            },
            {
                "if": {
                    "properties": {
                        "kind": { "const": "admin" }  // Different discriminator field
                    }
                },
                "then": {
                    "properties": {
                        "permissions": {
                            "type": "array",
                            "items": { "type": "string" }
                        }
                    },
                    "required": ["permissions"]
                }
            }
        ]
    });

    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());

    // Verify the error message mentions single discriminator requirement
    let error_msg = format!("{}", result.unwrap_err());
    assert!(error_msg.contains("single discriminator"));
}

#[test]
fn test_deserialize_object_with_multiple_discriminator_properties_error() {
    // This test verifies that having multiple properties in a discriminator specification
    // results in an error
    let schema = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" }
        },
        "allOf": [
            {
                "if": {
                    "properties": {
                        "type": { "const": "user" },
                        "category": { "const": "external" }  // Multiple discriminator properties
                    }
                },
                "then": {
                    "properties": {
                        "email": { "type": "string" }
                    }
                }
            }
        ]
    });

    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());

    // Verify the error message mentions exactly one property requirement
    let error_msg = format!("{}", result.unwrap_err());
    assert!(error_msg.contains("exactly one property"));
}

#[test]
fn test_deserialize_object_with_no_discriminator_properties_error() {
    // This test verifies that having no properties in a discriminator specification
    // results in an error
    let schema = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" }
        },
        "allOf": [
            {
                "if": {
                    "properties": {}  // No discriminator properties
                },
                "then": {
                    "properties": {
                        "email": { "type": "string" }
                    }
                }
            }
        ]
    });

    let result = Schema::from_serde_json_value(schema);
    assert!(result.is_err());

    // Verify the error message mentions exactly one property requirement
    let error_msg = format!("{}", result.unwrap_err());
    assert!(error_msg.contains("exactly one property"));
}

#[test]
fn test_deserialize_object_with_consistent_discriminator_success() {
    // This test verifies that using the same discriminator field consistently works
    let schema = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" },
            "entityType": { "type": "string" }
        },
        "required": ["name", "entityType"],
        "allOf": [
            {
                "if": {
                    "properties": {
                        "entityType": { "const": "user" }
                    }
                },
                "then": {
                    "properties": {
                        "email": { "type": "string" },
                        "lastLogin": { "type": "string" }
                    },
                    "required": ["email"]
                }
            },
            {
                "if": {
                    "properties": {
                        "entityType": { "const": "group" }
                    }
                },
                "then": {
                    "properties": {
                        "members": {
                            "type": "array",
                            "items": { "type": "string" }
                        },
                        "permissions": {
                            "type": "array",
                            "items": { "type": "string" }
                        }
                    },
                    "required": ["members"]
                }
            },
            {
                "if": {
                    "properties": {
                        "entityType": { "const": "service" }
                    }
                },
                "then": {
                    "properties": {
                        "endpoint": { "type": "string" },
                        "healthCheck": { "type": "string" },
                        "version": { "type": "string" }
                    },
                    "required": ["endpoint", "version"]
                }
            }
        ]
    });

    let s = Schema::from_serde_json_value(schema).unwrap();
    match s.as_type() {
        Type::Object {
            discriminated_subobject,
            properties,
            required,
            ..
        } => {
            // Verify base properties
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("entityType"));

            let req = required.as_ref().expect("required should be present");
            assert!(req.contains(&"name".into()));
            assert!(req.contains(&"entityType".into()));

            // Verify discriminated subobject
            let dso = discriminated_subobject
                .as_ref()
                .expect("should have discriminated_subobject");
            assert_eq!(dso.discriminator.as_ref(), "entityType");
            assert_eq!(dso.variants.len(), 3);

            // Verify user variant
            let user_variant = dso.variants.get("user").expect("user variant");
            assert!(user_variant.properties.contains_key("email"));
            assert!(user_variant.properties.contains_key("lastLogin"));
            let user_req = user_variant.required.as_ref().expect("user required");
            assert!(user_req.contains(&"email".into()));

            // Verify group variant
            let group_variant = dso.variants.get("group").expect("group variant");
            assert!(group_variant.properties.contains_key("members"));
            assert!(group_variant.properties.contains_key("permissions"));
            let group_req = group_variant.required.as_ref().expect("group required");
            assert!(group_req.contains(&"members".into()));

            // Verify service variant
            let service_variant = dso.variants.get("service").expect("service variant");
            assert!(service_variant.properties.contains_key("endpoint"));
            assert!(service_variant.properties.contains_key("healthCheck"));
            assert!(service_variant.properties.contains_key("version"));
            let service_req = service_variant.required.as_ref().expect("service required");
            assert!(service_req.contains(&"endpoint".into()));
            assert!(service_req.contains(&"version".into()));
        }
        _ => panic!("Expected Type::Object"),
    }
}

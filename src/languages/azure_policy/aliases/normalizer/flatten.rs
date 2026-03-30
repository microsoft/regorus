// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Value normalization helpers: recursive key lowercasing, sub-resource array
//! flattening, and element merging.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{make_array, make_value, new_map, obj_contains, obj_insert, val_str};

/// Lowercase all keys of a JSON object (shallow — values are untouched).
/// Non-object values are returned as-is.
pub fn lowercase_object_keys(value: &Value) -> Value {
    match value {
        Value::Object(obj) => {
            let mut result = new_map();
            for (k, v) in obj.iter() {
                if let Some(s) = val_str(k) {
                    obj_insert(&mut result, &s.to_ascii_lowercase(), v.clone());
                }
            }
            make_value(result)
        }
        _ => value.clone(),
    }
}

/// Recursively normalize a value, flattening sub-resource array elements.
pub fn normalize_value(
    value: &Value,
    field_path: &str,
    sub_arrays: Option<&BTreeSet<String>>,
) -> Value {
    match value {
        Value::Array(arr) => {
            let items: Vec<Value> = if is_sub_resource_array(field_path, sub_arrays) {
                arr.iter()
                    .map(|elem| flatten_element(elem, field_path, sub_arrays))
                    .collect()
            } else {
                arr.iter()
                    .map(|elem| normalize_value(elem, field_path, sub_arrays))
                    .collect()
            };
            make_array(items)
        }
        Value::Object(obj) => {
            let mut result = new_map();
            for (k, v) in obj.iter() {
                let key_s = match val_str(k) {
                    Some(s) => s,
                    None => continue,
                };
                let child_path = alloc::format!("{}.{}", field_path, key_s);
                obj_insert(
                    &mut result,
                    &key_s.to_ascii_lowercase(),
                    normalize_value(v, &child_path, sub_arrays),
                );
            }
            make_value(result)
        }
        _ => value.clone(),
    }
}

/// Flatten a sub-resource array element by merging its `properties` into
/// the element root.
pub fn flatten_element(
    element: &Value,
    array_path: &str,
    sub_arrays: Option<&BTreeSet<String>>,
) -> Value {
    let obj = match element.as_object() {
        Ok(o) => o,
        Err(_) => return element.clone(),
    };

    let mut result = new_map();

    // Copy non-`properties` fields from the element envelope (keys lowercased).
    for (key, val) in obj.iter() {
        let key_s = match val_str(key) {
            Some(s) => s,
            None => continue,
        };
        if key_s.eq_ignore_ascii_case("properties") {
            continue;
        }
        let child_path = alloc::format!("{}.{}", array_path, key_s);
        obj_insert(
            &mut result,
            &key_s.to_ascii_lowercase(),
            normalize_value(val, &child_path, sub_arrays),
        );
    }

    // Merge `properties` into the element (keys lowercased).
    let props_val = obj
        .iter()
        .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case("properties")))
        .map(|(_, v)| v);
    if let Some(Value::Object(props)) = props_val {
        for (key, val) in props.iter() {
            let key_s = match val_str(key) {
                Some(s) => s,
                None => continue,
            };
            let lc_key = key_s.to_ascii_lowercase();
            if obj_contains(&result, &lc_key) {
                continue;
            }
            let child_path = alloc::format!("{}.{}", array_path, key_s);
            obj_insert(
                &mut result,
                &lc_key,
                normalize_value(val, &child_path, sub_arrays),
            );
        }
    }

    make_value(result)
}

/// Check if a field path corresponds to a sub-resource array.
fn is_sub_resource_array(field_path: &str, sub_arrays: Option<&BTreeSet<String>>) -> bool {
    sub_arrays.is_some_and(|set| set.contains(&field_path.to_ascii_lowercase()))
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sub-resource array re-wrapping during denormalization.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{make_value, new_map, obj_insert, val_str, ObjMap};
use super::super::types::ResolvedEntry;
use super::helpers::find_key_ci;

/// Sub-resource array element envelope fields that remain at the element root.
const ELEMENT_ENVELOPE_FIELDS: &[&str] = &["name", "type", "id", "etag"];

/// Re-wrap sub-resource array elements by moving non-envelope fields back
/// under each element's `properties` object.
pub fn rewrap_sub_resource_arrays(
    properties: &mut ObjMap,
    sub_arrays: &BTreeSet<String>,
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
) {
    let mut sorted: Vec<&String> = sub_arrays.iter().collect();
    sorted.sort_by(|a, b| {
        let depth_a = a.chars().filter(|&c| c == '.').count();
        let depth_b = b.chars().filter(|&c| c == '.').count();
        depth_b.cmp(&depth_a)
    });

    for sub_array_path in sorted {
        let envelope_fields = classify_envelope_fields(sub_array_path, entries, api_version);
        let parts: Vec<&str> = sub_array_path.split('.').collect();

        if parts.len() == 1 {
            if let Some(key) = parts.first().and_then(|p| find_key_ci(properties, p)) {
                if let Some(Value::Array(arr)) = properties.get_mut(key.as_ref()) {
                    let inner = crate::Rc::make_mut(arr);
                    for elem in inner.iter_mut() {
                        *elem = rewrap_element(elem, &envelope_fields);
                    }
                }
            }
        } else if let Some((&array_name, parent_parts)) = parts.split_last() {
            rewrap_nested_array(properties, parent_parts, array_name, &envelope_fields);
        }
    }
}

/// Determine which element-level fields are envelope fields for a given
/// sub-resource array.
fn classify_envelope_fields(
    sub_array_path: &str,
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
) -> BTreeSet<String> {
    let mut envelope = BTreeSet::new();
    for &f in ELEMENT_ENVELOPE_FIELDS {
        envelope.insert(f.to_ascii_lowercase());
    }

    let wildcard_prefix: String = {
        let parts: Vec<&str> = sub_array_path.split('.').collect();
        let mut prefix = String::new();
        for (i, part) in parts.iter().enumerate() {
            if i > 0 {
                prefix.push_str("[*].");
            }
            prefix.push_str(&part.to_ascii_lowercase());
        }
        prefix.push_str("[*].");
        prefix
    };

    for (lc_key, entry) in entries {
        if !lc_key.starts_with(&wildcard_prefix) {
            continue;
        }
        let field = &lc_key[wildcard_prefix.len()..];
        let first_segment = field.split('.').next().unwrap_or(field);

        let arm_path = entry.select_path(api_version);
        let arm_after_last_wildcard = arm_path.rsplit("[*].").next().unwrap_or("");

        if !arm_after_last_wildcard.starts_with("properties.") {
            envelope.insert(first_segment.to_ascii_lowercase());
        }
    }

    envelope
}

/// Recursively navigate nested arrays and re-wrap elements of the innermost
/// sub-resource array.
fn rewrap_nested_array(
    obj: &mut ObjMap,
    parent_parts: &[&str],
    array_name: &str,
    envelope_fields: &BTreeSet<String>,
) {
    if parent_parts.is_empty() {
        return;
    }

    let parent_key = match parent_parts.first().and_then(|&p| find_key_ci(obj, p)) {
        Some(k) => k,
        None => return,
    };

    let parent_arr = match obj.get_mut(parent_key.as_ref()) {
        Some(Value::Array(arr)) => crate::Rc::make_mut(arr),
        _ => return,
    };

    for element in parent_arr.iter_mut() {
        if let Value::Object(obj_rc) = element {
            let inner_btree = crate::Rc::make_mut(obj_rc);

            if parent_parts.len() > 1 {
                rewrap_nested_array_in_btree(
                    inner_btree,
                    parent_parts.get(1..).unwrap_or_default(),
                    array_name,
                    envelope_fields,
                );
            } else if let Some(arr_key) = find_key_ci_btree(inner_btree, array_name) {
                if let Some(Value::Array(arr)) = inner_btree.get_mut(&arr_key) {
                    let inner = crate::Rc::make_mut(arr);
                    for inner_elem in inner.iter_mut() {
                        *inner_elem = rewrap_element(inner_elem, envelope_fields);
                    }
                }
            }
        }
    }
}

/// BTreeMap-native recursion for nested sub-resource array re-wrapping,
/// avoiding ObjMap round-trips on each array element.
fn rewrap_nested_array_in_btree(
    btree: &mut alloc::collections::BTreeMap<Value, Value>,
    parent_parts: &[&str],
    array_name: &str,
    envelope_fields: &BTreeSet<String>,
) {
    if parent_parts.is_empty() {
        return;
    }

    let parent_key = match parent_parts
        .first()
        .and_then(|&p| find_key_ci_btree(btree, p))
    {
        Some(k) => k,
        None => return,
    };

    let parent_arr = match btree.get_mut(&parent_key) {
        Some(Value::Array(arr)) => crate::Rc::make_mut(arr),
        _ => return,
    };

    for element in parent_arr.iter_mut() {
        if let Value::Object(obj_rc) = element {
            let inner_btree = crate::Rc::make_mut(obj_rc);

            if parent_parts.len() > 1 {
                rewrap_nested_array_in_btree(
                    inner_btree,
                    parent_parts.get(1..).unwrap_or_default(),
                    array_name,
                    envelope_fields,
                );
            } else if let Some(arr_key) = find_key_ci_btree(inner_btree, array_name) {
                if let Some(Value::Array(arr)) = inner_btree.get_mut(&arr_key) {
                    let inner = crate::Rc::make_mut(arr);
                    for inner_elem in inner.iter_mut() {
                        *inner_elem = rewrap_element(inner_elem, envelope_fields);
                    }
                }
            }
        }
    }
}

/// Find a key in a BTreeMap using case-insensitive comparison.
fn find_key_ci_btree(
    btree: &alloc::collections::BTreeMap<Value, Value>,
    key: &str,
) -> Option<Value> {
    btree
        .keys()
        .find(|k| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(key)))
        .cloned()
}

/// Re-wrap a single sub-resource array element by moving non-envelope
/// fields back under a `properties` object.
fn rewrap_element(element: &Value, envelope_fields: &BTreeSet<String>) -> Value {
    let obj = match element.as_object() {
        Ok(o) => o,
        Err(_) => return element.clone(),
    };

    let mut envelope = new_map();
    let mut props = new_map();

    for (key, val) in obj.iter() {
        let key_s = match val_str(key) {
            Some(s) => s,
            None => continue,
        };
        if envelope_fields.contains(&key_s.to_ascii_lowercase()) {
            obj_insert(&mut envelope, key_s, val.clone());
        } else {
            obj_insert(&mut props, key_s, val.clone());
        }
    }

    if !props.is_empty() {
        obj_insert(&mut envelope, "properties", make_value(props));
    }

    make_value(envelope)
}

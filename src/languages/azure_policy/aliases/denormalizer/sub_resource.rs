// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sub-resource array re-wrapping during denormalization.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{
    for_each_array_object_in_path_ci, make_value, new_map, obj_get_mut_ci, obj_insert, val_str,
    ObjMap,
};
use super::super::types::{PrecomputedSubResourceRewrap, ResolvedEntry};

/// Sub-resource array element envelope fields that remain at the element root.
const ELEMENT_ENVELOPE_FIELDS: &[&str] = &["name", "type", "id", "etag"];

/// Precompute sub-resource array rewrap operations for a specific API version.
pub fn precompute_sub_resource_rewraps(
    sub_arrays: &BTreeSet<String>,
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
) -> Vec<PrecomputedSubResourceRewrap> {
    let mut sorted: Vec<&String> = sub_arrays.iter().collect();
    sorted.sort_by(|a, b| {
        let depth_a = a.chars().filter(|&c| c == '.').count();
        let depth_b = b.chars().filter(|&c| c == '.').count();
        depth_b.cmp(&depth_a)
    });

    sorted
        .into_iter()
        .filter_map(|sub_array_path| {
            let envelope_fields = classify_envelope_fields(sub_array_path, entries, api_version);
            let parts: Vec<&str> = sub_array_path.split('.').collect();
            let (&array_name, parent_parts) = parts.split_last()?;
            Some(PrecomputedSubResourceRewrap {
                parent_path: parent_parts
                    .iter()
                    .map(|part| String::from(*part))
                    .collect(),
                array_name: String::from(array_name),
                envelope_fields,
            })
        })
        .collect()
}

/// Re-wrap sub-resource array elements by moving non-envelope fields back
/// under each element's `properties` object.
pub fn rewrap_precomputed_sub_resource_arrays(
    properties: &mut ObjMap,
    ops: &[PrecomputedSubResourceRewrap],
) {
    for op in ops {
        for_each_array_object_in_path_ci(properties, &op.parent_path, &mut |parent| {
            if let Some(Value::Array(arr)) = obj_get_mut_ci(parent, &op.array_name) {
                let inner = crate::Rc::make_mut(arr);
                for elem in inner.iter_mut() {
                    *elem = rewrap_element(elem, &op.envelope_fields);
                }
            }
        });
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

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sub-resource array re-wrapping during denormalization.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::Value;

use super::super::obj_map::{make_value, new_map, obj_insert, val_str, ObjMap};
use super::super::path;
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

    if sorted.is_empty() {
        return;
    }
    // Parse once per call; only wildcard aliases can address array elements.
    let parsed: Vec<(path::Path, path::Path)> = entries
        .values()
        .filter(|entry| entry.is_wildcard)
        .filter_map(|entry| {
            Some((
                path::parse(&entry.short_name)?,
                path::parse(entry.select_path(api_version))?,
            ))
        })
        .collect();

    for sub_array_path in sorted {
        let envelope_fields = classify_envelope_fields(sub_array_path, &parsed);
        let keys: Vec<&str> = sub_array_path.split('.').collect();
        let Some((first, rest)) = keys.split_first() else {
            continue;
        };
        if let Some(key) = find_key_ci(properties, first) {
            if let Some(value) = properties.get_mut(key.as_ref()) {
                rewrap_at(value, rest, &envelope_fields);
            }
        }
    }
}

/// Determine which element-level fields are envelope fields for a given
/// sub-resource array, from parsed `(short name, ARM path)` pairs. Entries
/// whose short name or selected ARM path does not parse are excluded.
fn classify_envelope_fields(
    sub_array_path: &str,
    parsed: &[(path::Path, path::Path)],
) -> BTreeSet<String> {
    let mut envelope = BTreeSet::new();
    for &f in ELEMENT_ENVELOPE_FIELDS {
        envelope.insert(f.to_ascii_lowercase());
    }

    let array_keys: Vec<&str> = sub_array_path.split('.').collect();
    for (short, arm_path) in parsed {
        let parts = short.parts();
        let Some(level) = array_level(&array_keys, &parts) else {
            continue;
        };
        let Some(path::Segment::Key(first_segment)) =
            parts.get(level).and_then(|part| part.segments.first())
        else {
            continue;
        };
        // Classify by the ARM part at this array's element level, not by the
        // deepest part of a nested field. The array is flattened, so a quoted
        // `['properties']` there is the same wrapper.
        let wrapped = arm_path
            .parts()
            .get(level)
            .is_some_and(path::Part::has_flattened_wrapper);

        if !wrapped {
            envelope.insert(first_segment.to_ascii_lowercase());
        }
    }

    envelope
}

/// Number of leading short-name parts whose keys spell `array_keys`, i.e.
/// the part index of the array's elements; `None` if the alias is outside
/// the array. A part may hold several keys (`a.b[*]`).
fn array_level(array_keys: &[&str], parts: &[path::Part<'_>]) -> Option<usize> {
    let mut remaining = array_keys;
    for (level, part) in parts.iter().enumerate() {
        if remaining.is_empty() {
            return Some(level);
        }
        for segment in part.segments {
            let path::Segment::Key(key) = segment else {
                return None;
            };
            let (name, rest) = remaining.split_first()?;
            if !key.eq_ignore_ascii_case(name) {
                return None;
            }
            remaining = rest;
        }
    }
    None
}

/// Follow `keys` from `value` and re-wrap the elements of the array there.
/// Like the normalizer's path tracking, arrays along the way are walked
/// element by element and objects by key, so a name such as `a.b.c` matches
/// `a.b[*].c[*]` and `a[*].b[*].c[*]` alike.
fn rewrap_at(value: &mut Value, keys: &[&str], envelope_fields: &BTreeSet<String>) {
    match value {
        Value::Array(arr) => {
            let inner = crate::Rc::make_mut(arr);
            for elem in inner.iter_mut() {
                if keys.is_empty() {
                    *elem = rewrap_element(elem, envelope_fields);
                } else {
                    rewrap_at(elem, keys, envelope_fields);
                }
            }
        }
        Value::Object(obj) => {
            let Some((first, rest)) = keys.split_first() else {
                return;
            };
            let obj = crate::Rc::make_mut(obj);
            if let Some(key) = find_key_ci_btree(obj, first) {
                if let Some(child) = obj.get_mut(&key) {
                    rewrap_at(child, rest, envelope_fields);
                }
            }
        }
        _ => {}
    }
}

/// Find a key in a BTreeMap using case-insensitive comparison.
fn find_key_ci_btree(btree: &Object, key: &str) -> Option<Value> {
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

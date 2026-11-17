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

/// The keys leading to a sub-resource array and its envelope fields.
type Target<'a> = (Vec<&'a str>, BTreeSet<String>);

/// Re-wrap sub-resource array elements by moving non-envelope fields back
/// under each element's `properties` object. `written` holds the plain
/// aliases phase 2b wrote; `is_data_plane` says where phase 2a put
/// non-aliased keys.
pub fn rewrap_sub_resource_arrays(
    result: &mut ObjMap,
    properties: &mut ObjMap,
    sub_arrays: &BTreeSet<String>,
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    written: &BTreeSet<String>,
    is_data_plane: bool,
) {
    if sub_arrays.is_empty() {
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

    // Several short names can resolve to the same array (two plain aliases
    // with one ARM path). Wrap each array once, keeping a field at the
    // element root if any of its names leaves it there.
    let mut targets: BTreeMap<(bool, Vec<String>), Target<'_>> = BTreeMap::new();
    for sub_array_path in sub_arrays {
        let envelope_fields = classify_envelope_fields(sub_array_path, &parsed);
        let (at_root, keys) =
            written_keys(sub_array_path, entries, api_version, written, is_data_plane);
        let id = keys.iter().map(|key| key.to_ascii_lowercase()).collect();
        targets
            .entry((at_root, id))
            .or_insert_with(|| (keys, BTreeSet::new()))
            .1
            .extend(envelope_fields);
    }

    // Deepest first, so an outer array is wrapped after the arrays inside it.
    let mut sorted: Vec<_> = targets.into_iter().collect();
    sorted.sort_by_key(|((_, id), _)| core::cmp::Reverse(id.len()));

    for ((at_root, _), (keys, envelope_fields)) in sorted {
        let Some((first, rest)) = keys.split_first() else {
            continue;
        };
        let map = if at_root {
            &mut *result
        } else {
            &mut *properties
        };
        if let Some(key) = find_key_ci(map, first) {
            if let Some(value) = map.get_mut(key.as_ref()) {
                rewrap_at(value, rest, &envelope_fields);
            }
        }
    }
}

/// Where a sub-resource array sits in the denormalized output: `true` for
/// the ARM root rather than `properties`, plus the keys leading to it. When
/// phase 2b wrote a plain alias for the first key, the array is under that
/// alias's ARM path (`x` -> `properties.items` puts `x.y` at `items.y`);
/// otherwise phase 2a wrote the key as is.
fn written_keys<'a>(
    sub_array_path: &'a str,
    entries: &'a BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    written: &BTreeSet<String>,
    is_data_plane: bool,
) -> (bool, Vec<&'a str>) {
    let keys: Vec<&str> = sub_array_path.split('.').collect();
    let Some((first, rest)) = keys.split_first() else {
        return (is_data_plane, keys);
    };
    match alias_location(first, entries, api_version, written) {
        Some((at_root, mut arm)) => {
            arm.extend(rest.iter().copied());
            (at_root, arm)
        }
        None => (is_data_plane, keys),
    }
}

/// Where phase 2b wrote the plain alias `key`: `true` for the ARM root
/// rather than `properties`, plus its ARM keys. `None` if it wrote nothing
/// for `key`.
fn alias_location<'a>(
    key: &str,
    entries: &'a BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    written: &BTreeSet<String>,
) -> Option<(bool, Vec<&'a str>)> {
    if !written.contains(key) {
        return None;
    }
    let arm = entries.get(key)?.select_path(api_version);
    let (at_root, arm) = arm
        .strip_prefix("properties.")
        .map_or((true, arm), |inner| (false, inner));
    Some((at_root, arm.split('.').collect()))
}

/// Point an element remap's array chain at where phase 2b wrote its outer
/// array: `true` for the ARM root rather than `properties`, plus the chain
/// with its first key replaced by the alias's ARM keys. `None` if phase 2b
/// did not write the first key.
pub fn redirect_chain(
    chain: &[Vec<String>],
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    written: &BTreeSet<String>,
) -> Option<(bool, Vec<Vec<String>>)> {
    let (outer, inner) = chain.split_first()?;
    let (first, rest) = outer.split_first()?;
    let (at_root, arm) = alias_location(first, entries, api_version, written)?;
    let redirected = arm
        .into_iter()
        .map(String::from)
        .chain(rest.iter().cloned())
        .collect();
    Some((
        at_root,
        core::iter::once(redirected)
            .chain(inner.iter().cloned())
            .collect(),
    ))
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
    // ARM names of the element's root fields, and of the fields under its
    // `properties` wrapper.
    let mut unwrapped = BTreeSet::new();
    let mut wrapped = BTreeSet::new();
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
        let arm_parts = arm_path.parts();
        let arm_part = arm_parts.get(level);
        if let Some(part) = arm_part.filter(|part| part.has_flattened_wrapper()) {
            if let Some(path::Segment::Key(key)) = part.segments.get(1) {
                wrapped.insert(key.to_ascii_lowercase());
            }
            continue;
        }
        // Phase 2d gives the field its ARM name when it finds the array, and
        // leaves the short name when it does not.
        envelope.insert(first_segment.to_ascii_lowercase());
        if let Some(path::Segment::Key(key)) = arm_part.and_then(|part| part.segments.first()) {
            unwrapped.insert(key.to_ascii_lowercase());
        }
    }
    // A name that is also a wrapped field's ARM name stays wrapped, as it was
    // before phase 2d gave fields their ARM names.
    envelope.extend(unwrapped.difference(&wrapped).cloned());

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

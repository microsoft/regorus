// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Lightweight string-keyed map used during normalization/denormalization.
//!
//! Internally uses `hashbrown::HashMap<Rc<str>, Value>` for O(1) lookups,
//! then converts to `Value::Object` (a `BTreeMap<Value, Value>`) only at
//! the output boundary via [`make_value`].

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use hashbrown::HashMap;

use crate::Rc;
use crate::Value;

/// A string-keyed map of JSON values.
///
/// All normalizer / denormalizer code works with this type internally.
/// Convert to [`Value::Object`] via [`make_value`] when producing output.
pub type ObjMap = HashMap<Rc<str>, Value>;

/// Create an empty [`ObjMap`].
pub fn new_map() -> ObjMap {
    ObjMap::new()
}

/// Look up a value by string key.
pub fn obj_get<'a>(map: &'a ObjMap, key: &str) -> Option<&'a Value> {
    map.get(key)
}

/// Look up a mutable value reference by string key.
pub fn obj_get_mut<'a>(map: &'a mut ObjMap, key: &str) -> Option<&'a mut Value> {
    map.get_mut(key)
}

/// Insert a key-value pair.
pub fn obj_insert(map: &mut ObjMap, key: &str, val: Value) {
    map.insert(Rc::from(key), val);
}

/// Check whether a key exists.
pub fn obj_contains(map: &ObjMap, key: &str) -> bool {
    map.contains_key(key)
}

/// Remove a key, returning its value if present.
pub fn obj_remove(map: &mut ObjMap, key: &str) -> Option<Value> {
    map.remove(key)
}

/// Convert an [`ObjMap`] into a [`Value::Object`].
///
/// Keys are converted from `Rc<str>` to `Value::String` and inserted into
/// a `BTreeMap` to match the `Value::Object` representation.
pub fn make_value(map: ObjMap) -> Value {
    use alloc::collections::BTreeMap;
    let mut btree = BTreeMap::new();
    for (k, v) in map {
        btree.insert(Value::String(k), v);
    }
    Value::Object(Rc::new(btree))
}

/// Convert a `Vec<Value>` into a `Value::Array`.
pub fn make_array(items: Vec<Value>) -> Value {
    Value::Array(Rc::new(items))
}

/// Extract a `&str` from a `Value::String`.
pub fn val_str(v: &Value) -> Option<&str> {
    match v {
        Value::String(s) => Some(s.as_ref()),
        _ => None,
    }
}

/// Extract the `type` field value from a resource JSON object.
///
/// Performs a case-insensitive key lookup so both `"type"` and `"Type"` work.
pub fn extract_type_field(resource: &Value) -> Option<&str> {
    resource.as_object().ok().and_then(|obj| {
        obj.iter()
            .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case("type")))
            .and_then(|(_, v)| val_str(v))
    })
}

/// Convert a `Value::Object` (BTreeMap<Value, Value>) into an [`ObjMap`].
///
/// Non-string keys are silently skipped.
#[allow(dead_code)]
pub fn value_to_obj_map(value: &Value) -> Option<ObjMap> {
    let btree = value.as_object().ok()?;
    let mut map = ObjMap::with_capacity(btree.len());
    for (k, v) in btree.iter() {
        if let Value::String(s) = k {
            map.insert(Rc::clone(s), v.clone());
        }
    }
    Some(map)
}

/// Set a value at a dot-separated path in an [`ObjMap`], creating
/// intermediate `Value::Object` nodes as needed.  All keys are lowercased.
pub fn set_nested_lowercased(result: &mut ObjMap, path: &str, value: Value) {
    let segments: Vec<&str> = path.split('.').collect();
    if segments.is_empty() {
        return;
    }
    if segments.len() == 1 {
        if let Some(&seg) = segments.first() {
            obj_insert(result, &seg.to_ascii_lowercase(), value);
        }
        return;
    }
    // Build the nested structure from inside-out.
    set_nested_inner(result, &segments, value, true);
}

/// Set a value at a dot-separated path in an [`ObjMap`], creating
/// intermediate `Value::Object` nodes as needed.  Keys preserve their casing.
pub fn set_nested_verbatim(result: &mut ObjMap, path: &str, value: Value) {
    let segments: Vec<&str> = path.split('.').collect();
    if segments.is_empty() {
        return;
    }
    if segments.len() == 1 {
        if let Some(&seg) = segments.first() {
            obj_insert(result, seg, value);
        }
        return;
    }
    set_nested_inner(result, &segments, value, false);
}

/// Core implementation of nested-set.  Navigates the first N-1 segments,
/// creating intermediate objects, then inserts the value at the last segment.
fn set_nested_inner(obj: &mut ObjMap, segments: &[&str], value: Value, lowercase: bool) {
    let Some(&first) = segments.first() else {
        return;
    };

    if segments.len() == 1 {
        let key = if lowercase {
            first.to_ascii_lowercase()
        } else {
            first.to_string()
        };
        obj_insert(obj, &key, value);
        return;
    }

    let seg = if lowercase {
        first.to_ascii_lowercase()
    } else {
        first.to_string()
    };

    // Ensure an intermediate object exists at `seg`.
    if !obj_contains(obj, &seg) {
        obj_insert(obj, &seg, make_value(new_map()));
    }

    // Descend directly into the BTreeMap, avoiding ObjMap round-trip.
    if let Some(Value::Object(inner_rc)) = obj_get_mut(obj, &seg) {
        let inner_btree = Rc::make_mut(inner_rc);
        set_nested_in_btree(
            inner_btree,
            segments.get(1..).unwrap_or_default(),
            value,
            lowercase,
        );
    }
}

/// Set a value at a path directly in a `BTreeMap<Value, Value>`, creating
/// intermediate `Value::Object` nodes as needed.
///
/// This avoids the `btree_to_obj_map` / `obj_map_to_btree` round-trip that
/// would clone every sibling entry at each nesting level.
pub fn set_nested_in_btree(
    btree: &mut alloc::collections::BTreeMap<Value, Value>,
    segments: &[&str],
    value: Value,
    lowercase: bool,
) {
    let Some(&first) = segments.first() else {
        return;
    };

    let key_str: String = if lowercase {
        first.to_ascii_lowercase()
    } else {
        first.to_string()
    };
    let key_val = Value::String(Rc::from(key_str.as_str()));

    if segments.len() == 1 {
        btree.insert(key_val, value);
        return;
    }

    // Ensure an intermediate object exists.
    if !btree.contains_key(&key_val) {
        btree.insert(key_val.clone(), make_value(new_map()));
    }

    if let Some(Value::Object(inner_rc)) = btree.get_mut(&key_val) {
        let inner = Rc::make_mut(inner_rc);
        set_nested_in_btree(
            inner,
            segments.get(1..).unwrap_or_default(),
            value,
            lowercase,
        );
    }
}

/// Fields that exist at the ARM resource root (not under `properties`).
///
/// These are the standard ARM resource envelope fields as defined by the
/// Azure Resource Manager resource model.  They are preserved at the
/// resource root during normalization and denormalization.
pub const ROOT_FIELDS: &[&str] = &[
    "name",
    "type",
    "location",
    "kind",
    "id",
    "tags",
    "identity",
    "sku",
    "plan",
    "zones",
    "managedBy",
    "etag",
    "apiVersion",
    "fullName",
    "systemData",
    "extendedLocation",
];

/// Check whether an alias short name collides with a reserved ARM root field
/// and needs a collision-safe key.
pub fn is_root_field_collision(short_name: &str, default_path: &str) -> bool {
    ROOT_FIELDS
        .iter()
        .any(|f| f.eq_ignore_ascii_case(short_name))
        && default_path.to_ascii_lowercase().starts_with("properties.")
}

/// Return a collision-safe key for an alias whose short name collides with a
/// root ARM field.  The key is `_p_` + the lowercased short name.
pub fn collision_safe_key(short_name: &str) -> String {
    alloc::format!("_p_{}", short_name.to_ascii_lowercase())
}

// ─── Element-level field removal ────────────────────────────────────────────
//
// Shared by both normalizer (stale source cleanup after remap) and
// denormalizer (cleanup after reverse remap).

/// Remove a (possibly dot-separated) field from each element of a (possibly
/// nested) array, navigating via the given `array_chain`.
pub fn remove_element_field(obj: &mut ObjMap, array_chain: &[Vec<String>], field: &str) {
    remove_field_at_depth(obj, array_chain, 0, field);
}

fn remove_field_at_depth(obj: &mut ObjMap, array_chain: &[Vec<String>], depth: usize, field: &str) {
    let Some(nav) = array_chain.get(depth) else {
        let segments: Vec<&str> = field.split('.').collect();
        if segments.len() == 1 {
            if let Some(&seg) = segments.first() {
                obj_remove(obj, seg);
            }
        } else if segments.len() > 1 {
            remove_at_dotted_path(obj, &segments);
        }
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    let arr_val = if nav.len() == 1 {
        match obj_get_mut(obj, first) {
            Some(v) => v,
            None => return,
        }
    } else {
        let mut cur: &mut Value = match obj_get_mut(obj, first) {
            Some(v) => v,
            None => return,
        };
        for segment in nav.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match inner.get_mut(&Value::from(segment.as_str())) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        cur
    };

    if let Value::Array(elements) = arr_val {
        let inner = Rc::make_mut(elements);
        for elem in inner.iter_mut() {
            if let Value::Object(obj_rc) = elem {
                let inner_btree = Rc::make_mut(obj_rc);
                remove_field_at_depth_in_btree(
                    inner_btree,
                    array_chain,
                    depth.saturating_add(1),
                    field,
                );
            }
        }
    }
}

/// BTreeMap-native recursion for element-level field removal.
fn remove_field_at_depth_in_btree(
    btree: &mut alloc::collections::BTreeMap<Value, Value>,
    array_chain: &[Vec<String>],
    depth: usize,
    field: &str,
) {
    let Some(nav) = array_chain.get(depth) else {
        let segments: Vec<&str> = field.split('.').collect();
        if segments.len() == 1 {
            if let Some(&seg) = segments.first() {
                btree.remove(&Value::from(seg));
            }
        } else if segments.len() > 1 {
            remove_at_dotted_path_in_btree(btree, &segments);
        }
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    let key_val = Value::from(first);
    let arr_val = if nav.len() == 1 {
        match btree.get_mut(&key_val) {
            Some(v) => v,
            None => return,
        }
    } else {
        let mut cur: &mut Value = match btree.get_mut(&key_val) {
            Some(v) => v,
            None => return,
        };
        for segment in nav.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match inner.get_mut(&Value::from(segment.as_str())) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        cur
    };

    if let Value::Array(elements) = arr_val {
        let inner = Rc::make_mut(elements);
        for elem in inner.iter_mut() {
            if let Value::Object(obj_rc) = elem {
                let inner_btree = Rc::make_mut(obj_rc);
                remove_field_at_depth_in_btree(
                    inner_btree,
                    array_chain,
                    depth.saturating_add(1),
                    field,
                );
            }
        }
    }
}

/// Remove the leaf segment at a dotted path directly in a BTreeMap.
fn remove_at_dotted_path_in_btree(
    btree: &mut alloc::collections::BTreeMap<Value, Value>,
    segments: &[&str],
) {
    let Some((&leaf, parent_segs)) = segments.split_last() else {
        return;
    };
    if parent_segs.is_empty() {
        btree.remove(&Value::from(leaf));
        return;
    }

    let Some(&first) = parent_segs.first() else {
        return;
    };
    let first_key = Value::from(first);
    let parent_val = match btree.get_mut(&first_key) {
        Some(v) => v,
        None => return,
    };

    if parent_segs.len() == 1 {
        if let Value::Object(inner_rc) = parent_val {
            let inner_btree = Rc::make_mut(inner_rc);
            inner_btree.remove(&Value::from(leaf));
        }
    } else {
        let mut cur = parent_val;
        for &seg in parent_segs.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match inner.get_mut(&Value::from(seg)) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        if let Value::Object(inner_rc) = cur {
            let inner_btree = Rc::make_mut(inner_rc);
            inner_btree.remove(&Value::from(leaf));
        }
    }
}

/// Remove the leaf segment at a dot-separated path from an ObjMap.
fn remove_at_dotted_path(obj: &mut ObjMap, segments: &[&str]) {
    let Some((&leaf, parent_segs)) = segments.split_last() else {
        return;
    };
    if parent_segs.is_empty() {
        obj_remove(obj, leaf);
        return;
    }

    let Some(&first) = parent_segs.first() else {
        return;
    };
    let parent_val = match obj_get_mut(obj, first) {
        Some(v) => v,
        None => return,
    };

    if parent_segs.len() == 1 {
        if let Value::Object(inner_rc) = parent_val {
            let inner_btree = Rc::make_mut(inner_rc);
            inner_btree.remove(&Value::from(leaf));
        }
    } else {
        let mut cur = parent_val;
        for &seg in parent_segs.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match inner.get_mut(&Value::from(seg)) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        if let Value::Object(inner_rc) = cur {
            let inner_btree = Rc::make_mut(inner_rc);
            inner_btree.remove(&Value::from(leaf));
        }
    }
}

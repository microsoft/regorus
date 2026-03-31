// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Lightweight string-keyed map used during normalization/denormalization.
//!
//! Uses `BTreeMap<Value, Value>` throughout — the same representation as
//! `Value::Object` — so there is no conversion step at output boundaries.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use crate::Rc;
use crate::Value;

/// A string-keyed map of JSON values.
///
/// This is the same type used inside `Value::Object`, so wrapping into a
/// `Value` is a zero-conversion `Value::Object(Rc::new(map))` call.
pub type ObjMap = BTreeMap<Value, Value>;

/// Create an empty [`ObjMap`].
pub const fn new_map() -> ObjMap {
    ObjMap::new()
}

/// Look up a value by string key.
pub fn obj_get<'a>(map: &'a ObjMap, key: &str) -> Option<&'a Value> {
    map.get(&Value::from(key))
}

/// Look up a value by case-insensitive string key.
pub fn obj_get_ci<'a>(map: &'a ObjMap, key: &str) -> Option<&'a Value> {
    let found = find_key_ci(map, key)?;
    map.get(&found)
}

/// Look up a value by exact key first, then fall back to case-insensitive lookup.
pub fn obj_get_exact_or_ci<'a>(map: &'a ObjMap, key: &str) -> Option<&'a Value> {
    obj_get(map, key).or_else(|| obj_get_ci(map, key))
}

/// Look up a mutable value reference by string key.
pub fn obj_get_mut<'a>(map: &'a mut ObjMap, key: &str) -> Option<&'a mut Value> {
    map.get_mut(&Value::from(key))
}

/// Insert a key-value pair.
pub fn obj_insert(map: &mut ObjMap, key: &str, val: Value) {
    map.insert(Value::String(Rc::from(key)), val);
}

/// Check whether a key exists.
pub fn obj_contains(map: &ObjMap, key: &str) -> bool {
    map.contains_key(&Value::from(key))
}

/// Remove a key, returning its value if present.
pub fn obj_remove(map: &mut ObjMap, key: &str) -> Option<Value> {
    map.remove(&Value::from(key))
}

/// Wrap an [`ObjMap`] into a [`Value::Object`].
pub fn make_value(map: ObjMap) -> Value {
    Value::Object(Rc::new(map))
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

/// Find a key in an ObjMap using case-insensitive comparison, returning
/// the key as found in the map.
pub fn find_key_ci(map: &ObjMap, key: &str) -> Option<Value> {
    map.keys()
        .find(|k| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(key)))
        .cloned()
}

/// Look up a mutable value reference by case-insensitive string key.
pub fn obj_get_mut_ci<'a>(map: &'a mut ObjMap, key: &str) -> Option<&'a mut Value> {
    let found = find_key_ci(map, key)?;
    map.get_mut(&found)
}

/// Read a value at a dot-separated path from an ObjMap.
pub fn get_path<'a>(obj: &'a ObjMap, segments: &[&str]) -> Option<&'a Value> {
    let (first, rest) = segments.split_first()?;
    let value = obj_get(obj, first)?;
    if rest.is_empty() {
        return Some(value);
    }

    let inner = value.as_object().ok()?;
    get_path(inner, rest)
}

/// Read a value at a dot-separated path using exact key lookup first and
/// case-insensitive fallback for each path segment.
pub fn get_path_exact_or_ci<'a>(obj: &'a ObjMap, segments: &[String]) -> Option<&'a Value> {
    let (first, rest) = segments.split_first()?;
    let value = obj_get_exact_or_ci(obj, first)?;
    if rest.is_empty() {
        return Some(value);
    }

    let inner = value.as_object().ok()?;
    get_path_exact_or_ci(inner, rest)
}

/// Read a value from a `Value` object using pre-tokenized path segments.
pub fn get_value_path_segments<'a>(value: &'a Value, segments: &[String]) -> Option<&'a Value> {
    let mut current = value;
    for segment in segments {
        current = current
            .as_object()
            .ok()?
            .get(&Value::from(segment.as_str()))?;
    }
    Some(current)
}

/// Navigate to a nested value using pre-tokenized `String` segments.
pub fn get_path_mut_owned<'a>(obj: &'a mut ObjMap, segments: &[String]) -> Option<&'a mut Value> {
    let (first, rest) = segments.split_first()?;
    let value = obj_get_mut(obj, first)?;
    if rest.is_empty() {
        return Some(value);
    }
    let inner = value.as_object_mut().ok()?;
    get_path_mut_owned(inner, rest)
}

/// Case-insensitive variant of [`get_path_mut_owned`].
fn get_path_mut_owned_ci<'a>(obj: &'a mut ObjMap, segments: &[String]) -> Option<&'a mut Value> {
    let (first, rest) = segments.split_first()?;
    let value = obj_get_mut_ci(obj, first)?;
    if rest.is_empty() {
        return Some(value);
    }
    let inner = value.as_object_mut().ok()?;
    get_path_mut_owned_ci(inner, rest)
}

/// Visit each object element located by a nested exact-case array chain.
///
/// Each entry in `array_chain` is a path from the current object to an array.
/// When the chain is exhausted, `visit` is called with the current object.
pub fn for_each_array_object_in_chain(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    visit: &mut dyn FnMut(&mut ObjMap),
) {
    for_each_array_object_in_chain_at_depth(obj, array_chain, 0, visit);
}

fn for_each_array_object_in_chain_at_depth(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    depth: usize,
    visit: &mut dyn FnMut(&mut ObjMap),
) {
    let Some(nav) = array_chain.get(depth) else {
        visit(obj);
        return;
    };

    let Some(arr_val) = get_path_mut_owned(obj, nav) else {
        return;
    };

    let Value::Array(elements) = arr_val else {
        return;
    };

    for element in Rc::make_mut(elements).iter_mut() {
        if let Value::Object(obj_rc) = element {
            let inner = Rc::make_mut(obj_rc);
            for_each_array_object_in_chain_at_depth(
                inner,
                array_chain,
                depth.saturating_add(1),
                visit,
            );
        }
    }
}

/// Case-insensitive variant of [`for_each_array_object_in_chain`].
pub fn for_each_array_object_in_chain_ci(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    visit: &mut dyn FnMut(&mut ObjMap),
) {
    for_each_array_object_in_chain_ci_at_depth(obj, array_chain, 0, visit);
}

fn for_each_array_object_in_chain_ci_at_depth(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    depth: usize,
    visit: &mut dyn FnMut(&mut ObjMap),
) {
    let Some(nav) = array_chain.get(depth) else {
        visit(obj);
        return;
    };

    let Some(arr_val) = get_path_mut_owned_ci(obj, nav) else {
        return;
    };

    let Value::Array(elements) = arr_val else {
        return;
    };

    for element in Rc::make_mut(elements).iter_mut() {
        if let Value::Object(obj_rc) = element {
            let inner = Rc::make_mut(obj_rc);
            for_each_array_object_in_chain_ci_at_depth(
                inner,
                array_chain,
                depth.saturating_add(1),
                visit,
            );
        }
    }
}

/// Visit each object element located by a case-insensitive chain of array names.
///
/// Each segment in `array_path` names an array under the current object. The
/// visitor is called with each object element found at the end of that chain,
/// or with the current object when the chain is empty.
pub fn for_each_array_object_in_path_ci(
    obj: &mut ObjMap,
    array_path: &[String],
    visit: &mut dyn FnMut(&mut ObjMap),
) {
    let Some((first, rest)) = array_path.split_first() else {
        visit(obj);
        return;
    };

    let Some(arr_val) = obj_get_mut_ci(obj, first) else {
        return;
    };

    let Value::Array(elements) = arr_val else {
        return;
    };

    for element in Rc::make_mut(elements).iter_mut() {
        if let Value::Object(obj_rc) = element {
            let inner = Rc::make_mut(obj_rc);
            for_each_array_object_in_path_ci(inner, rest, visit);
        }
    }
}

/// Set a value at a dot-separated path, creating intermediate
/// `Value::Object` nodes as needed.
///
/// When `lowercase` is true, all path segments are lowercased.
/// When false, segments preserve their original casing.
pub fn set_nested(result: &mut ObjMap, path: &str, value: Value, lowercase: bool) {
    let segments: Vec<&str> = path.split('.').collect();
    if segments.is_empty() {
        return;
    }
    if segments.len() == 1 {
        if let Some(&seg) = segments.first() {
            let key = if lowercase {
                seg.to_ascii_lowercase()
            } else {
                seg.to_string()
            };
            obj_insert(result, &key, value);
        }
        return;
    }
    set_nested_inner(result, &segments, value, lowercase);
}

/// Core implementation of nested-set.
fn set_nested_inner(obj: &mut ObjMap, segments: &[&str], value: Value, lowercase: bool) {
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
        obj.insert(key_val, value);
        return;
    }

    // Ensure an intermediate object exists at `key_val`.
    if !obj.contains_key(&key_val) {
        obj.insert(key_val.clone(), make_value(new_map()));
    }

    if let Some(Value::Object(inner_rc)) = obj.get_mut(&key_val) {
        let inner = Rc::make_mut(inner_rc);
        set_nested_inner(
            inner,
            segments.get(1..).unwrap_or_default(),
            value,
            lowercase,
        );
    }
}

/// Fields that exist at the ARM resource root (not under `properties`).
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

// Element-level field removal, shared by normalizer and denormalizer.

/// Remove a (possibly dot-separated) field from each element of a (possibly
/// nested) array, navigating via the given `array_chain`.
pub fn remove_element_field(obj: &mut ObjMap, array_chain: &[Vec<String>], field: &str) {
    for_each_array_object_in_chain(obj, array_chain, &mut |element| {
        let segments: Vec<&str> = field.split('.').collect();
        if segments.len() == 1 {
            if let Some(&seg) = segments.first() {
                element.remove(&Value::from(seg));
            }
        } else if segments.len() > 1 {
            remove_at_dotted_path(element, &segments);
        }
    });
}

/// Case-insensitive variant of [`remove_element_field`].
pub fn remove_element_field_ci(obj: &mut ObjMap, array_chain: &[Vec<String>], field: &str) {
    for_each_array_object_in_chain_ci(obj, array_chain, &mut |element| {
        let segments: Vec<&str> = field.split('.').collect();
        if segments.len() == 1 {
            if let Some(&seg) = segments.first() {
                if let Some(key) = find_key_ci(element, seg) {
                    element.remove(&key);
                }
            }
        } else if segments.len() > 1 {
            remove_at_dotted_path_ci(element, &segments);
        }
    });
}

/// Remove the leaf segment at a dotted path.
fn remove_at_dotted_path(obj: &mut ObjMap, segments: &[&str]) {
    let Some((&leaf, parent_segs)) = segments.split_last() else {
        return;
    };
    if parent_segs.is_empty() {
        obj.remove(&Value::from(leaf));
        return;
    }

    let Some(&first) = parent_segs.first() else {
        return;
    };
    let first_key = Value::from(first);
    let parent_val = match obj.get_mut(&first_key) {
        Some(v) => v,
        None => return,
    };

    if parent_segs.len() == 1 {
        if let Value::Object(inner_rc) = parent_val {
            let inner = Rc::make_mut(inner_rc);
            inner.remove(&Value::from(leaf));
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
            let inner = Rc::make_mut(inner_rc);
            inner.remove(&Value::from(leaf));
        }
    }
}

/// Case-insensitive variant of [`remove_at_dotted_path`].
fn remove_at_dotted_path_ci(obj: &mut ObjMap, segments: &[&str]) {
    let Some((&leaf, parent_segs)) = segments.split_last() else {
        return;
    };
    if parent_segs.is_empty() {
        if let Some(key) = find_key_ci(obj, leaf) {
            obj.remove(&key);
        }
        return;
    }

    let Some(&first) = parent_segs.first() else {
        return;
    };
    let parent_val = match obj_get_mut_ci(obj, first) {
        Some(v) => v,
        None => return,
    };

    if parent_segs.len() == 1 {
        if let Value::Object(inner_rc) = parent_val {
            let inner = Rc::make_mut(inner_rc);
            if let Some(key) = find_key_ci(inner, leaf) {
                inner.remove(&key);
            }
        }
    } else {
        let mut cur = parent_val;
        for &seg in parent_segs.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match obj_get_mut_ci(inner, seg) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        if let Value::Object(inner_rc) = cur {
            let inner = Rc::make_mut(inner_rc);
            if let Some(key) = find_key_ci(inner, leaf) {
                inner.remove(&key);
            }
        }
    }
}

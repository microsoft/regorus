// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Element-level field remapping for array aliases with versioned paths.

use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{
    obj_get, obj_get_mut, obj_insert, set_nested_in_btree, set_nested_lowercased,
    set_nested_verbatim, ObjMap,
};
use super::super::types::PrecomputedRemap;

/// Describes a field remapping inside each element of a (possibly nested) array.
pub struct ElementRemap {
    /// Chain of array navigations for nested `[*]` levels.
    pub(crate) array_chain: Vec<Vec<String>>,
    /// Dot-separated path to read within the innermost array element.
    pub(crate) source_field: String,
    /// Dot-separated path to write within the innermost array element.
    pub(crate) target_field: String,
}

/// Apply an element-level field remap to each element of an array (or nested
/// array chain).
///
/// When `lowercase` is `true` (normalizer), target path segments are
/// lowercased.  When `false` (denormalizer), they are written verbatim
/// so that restored casing is preserved.
pub fn apply_element_remap(result: &mut ObjMap, remap: &ElementRemap, lowercase: bool) {
    apply_remap_at_depth(
        result,
        &remap.array_chain,
        0,
        &remap.source_field,
        &remap.target_field,
        lowercase,
    );
}

/// Apply a precomputed element remap (from [`PrecomputedRemap`]) without
/// any per-call string splitting or allocation.
pub fn apply_element_remap_precomputed(result: &mut ObjMap, remap: &PrecomputedRemap) {
    apply_remap_at_depth(
        result,
        &remap.array_chain,
        0,
        &remap.source_field,
        &remap.target_field,
        true,
    );
}

/// Recursively navigate nested arrays via `array_chain` and apply a field
/// remap in each innermost element.
fn apply_remap_at_depth(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    depth: usize,
    source_field: &str,
    target_field: &str,
    lowercase: bool,
) {
    let Some(nav) = array_chain.get(depth) else {
        remap_deep_field(obj, source_field, target_field, lowercase);
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    // Navigate through intermediate segments to reach the array value.
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
        let inner = crate::Rc::make_mut(elements);
        for elem in inner.iter_mut() {
            if let Value::Object(obj_rc) = elem {
                let inner_btree = crate::Rc::make_mut(obj_rc);
                remap_at_depth_in_btree(
                    inner_btree,
                    array_chain,
                    depth.saturating_add(1),
                    source_field,
                    target_field,
                    lowercase,
                );
            }
        }
    }
}

/// BTreeMap-native recursion for element-level remap, avoiding ObjMap
/// round-trips on each array element.
fn remap_at_depth_in_btree(
    btree: &mut alloc::collections::BTreeMap<Value, Value>,
    array_chain: &[Vec<String>],
    depth: usize,
    source_field: &str,
    target_field: &str,
    lowercase: bool,
) {
    let Some(nav) = array_chain.get(depth) else {
        remap_deep_field_in_btree(btree, source_field, target_field, lowercase);
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
        let inner = crate::Rc::make_mut(elements);
        for elem in inner.iter_mut() {
            if let Value::Object(obj_rc) = elem {
                let inner_btree = crate::Rc::make_mut(obj_rc);
                remap_at_depth_in_btree(
                    inner_btree,
                    array_chain,
                    depth.saturating_add(1),
                    source_field,
                    target_field,
                    lowercase,
                );
            }
        }
    }
}

/// Remap a value between dotted paths directly in a BTreeMap.
fn remap_deep_field_in_btree(
    btree: &mut alloc::collections::BTreeMap<Value, Value>,
    source: &str,
    target: &str,
    lowercase: bool,
) {
    let val = match read_dotted_path_btree(btree, source) {
        Some(v) => v,
        None => return,
    };

    let segments: Vec<&str> = target.split('.').collect();
    if segments.is_empty() {
        return;
    }
    if segments.len() == 1 {
        if let Some(seg) = segments.first() {
            btree.insert(Value::String(crate::Rc::from(*seg)), val);
        }
        return;
    }
    set_nested_in_btree(btree, &segments, val, lowercase);
}

/// Read a value at a dotted path from a BTreeMap.
fn read_dotted_path_btree(
    btree: &alloc::collections::BTreeMap<Value, Value>,
    path: &str,
) -> Option<Value> {
    let segments: Vec<&str> = path.split('.').collect();
    let first = segments.first()?;
    let mut cur: &Value = btree.get(&Value::from(*first))?;
    for &seg in segments.iter().skip(1) {
        cur = cur.as_object().ok()?.get(&Value::from(seg))?;
    }
    Some(cur.clone())
}

/// Remap a value from one (possibly nested) dot-separated path to another
/// in an ObjMap.  Used only at the top level when `depth >= array_chain.len()`.
fn remap_deep_field(obj: &mut ObjMap, source: &str, target: &str, lowercase: bool) {
    let val = match read_dotted_path(obj, source) {
        Some(v) => v,
        None => return,
    };

    let segments: Vec<&str> = target.split('.').collect();
    if segments.is_empty() {
        return;
    }
    if segments.len() == 1 {
        if let Some(seg) = segments.first() {
            obj_insert(obj, seg, val);
        }
        return;
    }
    if lowercase {
        set_nested_lowercased(obj, target, val);
    } else {
        set_nested_verbatim(obj, target, val);
    }
}

/// Read a value at a dot-separated path from an ObjMap.
fn read_dotted_path(obj: &ObjMap, path: &str) -> Option<Value> {
    let segments: Vec<&str> = path.split('.').collect();
    let first = segments.first()?;
    let mut cur: &Value = obj_get(obj, first)?;
    for &seg in segments.iter().skip(1) {
        cur = cur.as_object().ok()?.get(&Value::from(seg))?;
    }
    Some(cur.clone())
}

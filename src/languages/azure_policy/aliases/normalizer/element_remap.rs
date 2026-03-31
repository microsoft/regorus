// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Element-level field remapping for array aliases with versioned paths.

use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{for_each_array_object_in_chain, get_path, set_nested, ObjMap};
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
    for_each_array_object_in_chain(result, &remap.array_chain, &mut |element| {
        remap_deep_field(element, &remap.source_field, &remap.target_field, lowercase);
    });
}

/// Apply a precomputed element remap (from [`PrecomputedRemap`]) without
/// any per-call string splitting or allocation.
pub fn apply_element_remap_precomputed(result: &mut ObjMap, remap: &PrecomputedRemap) {
    for_each_array_object_in_chain(result, &remap.array_chain, &mut |element| {
        remap_deep_field(element, &remap.source_field, &remap.target_field, true);
    });
}

/// Remap a value from one (possibly nested) dot-separated path to another.
fn remap_deep_field(obj: &mut ObjMap, source: &str, target: &str, lowercase: bool) {
    let val = match read_dotted_path(obj, source) {
        Some(v) => v,
        None => return,
    };

    set_nested(obj, target, val, lowercase);
}

/// Read a value at a dot-separated path from an ObjMap.
fn read_dotted_path(obj: &ObjMap, path: &str) -> Option<Value> {
    let segments: Vec<&str> = path.split('.').collect();
    get_path(obj, &segments).cloned()
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Element-level field remapping for array aliases with versioned paths.

use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{
    for_each_array_object_in_chain, for_each_array_object_in_chain_ci, get_path,
    get_path_exact_or_ci, set_nested, ObjMap,
};
use super::super::types::PrecomputedRemap;

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

/// Apply a reverse (denormalization) element-level field remap using
/// case-insensitive lookups for both array chain traversal and source field
/// reads.  This is necessary because Phase 2a restores key casing before
/// Phase 2d runs, so the lowercased chain/source segments would miss with
/// exact-case lookups.
pub fn apply_element_remap_reverse(
    result: &mut ObjMap,
    array_chain: &[Vec<String>],
    source_segments: &[String],
    target: &str,
) {
    for_each_array_object_in_chain_ci(result, array_chain, &mut |element| {
        let val = match get_path_exact_or_ci(element, source_segments) {
            Some(v) => v.clone(),
            None => return,
        };
        set_nested(element, target, val, false);
    });
}

/// Read a value at a dot-separated path from an ObjMap.
fn read_dotted_path(obj: &ObjMap, path: &str) -> Option<Value> {
    let segments: Vec<&str> = path.split('.').collect();
    get_path(obj, &segments).cloned()
}

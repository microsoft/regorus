// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Small helper functions used by the denormalizer.

use crate::Rc;

use super::super::obj_map::ObjMap;

/// Find a key in an ObjMap using case-insensitive comparison.
pub fn find_key_ci(obj: &ObjMap, key: &str) -> Option<Rc<str>> {
    obj.keys().find(|k| k.eq_ignore_ascii_case(key)).cloned()
}

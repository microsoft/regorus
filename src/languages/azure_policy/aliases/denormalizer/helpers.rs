// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Small helper functions used by the denormalizer.

use crate::Rc;

use super::super::obj_map::{obj_key_ci, ObjMap};

/// Find a key in an ObjMap: `key` itself, else the smallest key that
/// differs only in ASCII case, so the choice does not depend on map order.
pub fn find_key_ci(obj: &ObjMap, key: &str) -> Option<Rc<str>> {
    obj_key_ci(obj, key)
}

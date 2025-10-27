// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::Rc;

use core::hash::BuildHasherDefault;

use hashbrown::HashSet;
use rustc_hash::FxHasher;

type KeySet = HashSet<Rc<str>, BuildHasherDefault<FxHasher>>;

/// Arena-local string cache that interns keys within a single parse or evaluation.
pub struct KeyArena {
    entries: KeySet,
}

impl KeyArena {
    /// Create an empty arena.
    pub fn new() -> Self {
        Self {
            entries: KeySet::default(),
        }
    }

    /// Intern a borrowed key.
    pub fn intern(&mut self, key: &str) -> Rc<str> {
        if let Some(existing) = self.entries.get(key) {
            existing.clone()
        } else {
            let shared: Rc<str> = Rc::from(key);
            self.entries.insert(shared.clone());
            shared
        }
    }

    /// Intern an owned Rc<str> value.
    pub fn intern_owned(&mut self, key: Rc<str>) -> Rc<str> {
        if let Some(existing) = self.entries.get(key.as_ref()) {
            existing.clone()
        } else {
            self.entries.insert(key.clone());
            key
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Value;
    use alloc::string::{String, ToString};
    use std::collections::btree_map::Entry;
    use std::collections::BTreeMap;

    fn assert_key_rcs_reused(value: &Value) {
        fn walk(value: &Value, seen: &mut BTreeMap<String, Rc<str>>) {
            match value {
                Value::Object(map) => {
                    for (key, val) in map.iter() {
                        if let Value::String(rc) = key {
                            let key_text = rc.as_ref().to_string();
                            let entry = seen.entry(key_text);
                            match entry {
                                Entry::Vacant(slot) => {
                                    slot.insert(rc.clone());
                                }
                                Entry::Occupied(slot) => {
                                    assert!(
                                        Rc::ptr_eq(slot.get(), rc),
                                        "key `{}` was not interned",
                                        rc.as_ref()
                                    );
                                }
                            }
                        }
                        walk(val, seen);
                    }
                }
                Value::Array(arr) => {
                    for element in arr.iter() {
                        walk(element, seen);
                    }
                }
                _ => {}
            }
        }

        let mut seen = BTreeMap::new();
        walk(value, &mut seen);
    }

    #[test]
    fn deserialization_reuses_object_keys() {
        let json = r#"
        [
            {
                "foo": {
                    "bar": 1,
                    "values": [
                        {"p": {"foo": 1}},
                        {"p": {"foo": 2}}
                    ]
                },
                "bar": {
                    "foo": {"baz": 3}
                }
            },
            {
                "foo": {
                    "bar": 4,
                    "values": [
                        {"p": {"foo": 3}},
                        {"q": {"foo": 4}}
                    ]
                },
                "values": [
                    {"foo": {"bar": 5}}
                ]
            }
        ]
        "#;

        let value = Value::from_json_str(json).expect("json parse");
        assert_key_rcs_reused(&value);
    }
}

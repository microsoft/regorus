// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

pub const MAX_DEPTH: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
#[error("operation exceeds supported nesting limit {0}")]
pub struct DepthExceeded(pub usize);

pub fn descend(remaining: usize) -> Result<usize, DepthExceeded> {
    remaining.checked_sub(1).ok_or(DepthExceeded(MAX_DEPTH))
}

#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum DepthCheckError {
    #[error(transparent)]
    Depth(#[from] DepthExceeded),
    #[error(transparent)]
    Limit(#[from] crate::LimitError),
}

#[cfg(any(feature = "jsonpatch", feature = "jsonschema"))]
impl DepthCheckError {
    pub fn into_anyhow(self) -> anyhow::Error {
        match self {
            Self::Depth(error) => error.into(),
            Self::Limit(error) => error.into(),
        }
    }
}

#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum ContainerId {
    Array(*const crate::value::Array),
    Set(*const crate::value::Set),
    Object(*const crate::value::Object),
}

#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
enum Children<'a> {
    Array(crate::value::ArrayIter<'a>),
    Set(crate::value::SetIter<'a>),
    Object(crate::value::Iter<'a>, Option<&'a crate::Value>),
}

#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
impl<'a> Iterator for Children<'a> {
    type Item = &'a crate::Value;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Array(values) => values.next(),
            Self::Set(values) => values.next(),
            Self::Object(values, pending_value) => pending_value.take().or_else(|| {
                values.next().map(|(key, value)| {
                    *pending_value = Some(value);
                    key
                })
            }),
        }
    }
}

#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
enum Frame<'a> {
    Value(&'a crate::Value, usize),
    Container {
        identity: ContainerId,
        children: Children<'a>,
        remaining: usize,
        height: usize,
    },
}

// Count empty containers, keys and set members. Cache subtree heights by allocation
// identity, not Value hashing/ordering: shared descendants must not be expanded again.
#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
pub fn check_value(value: &crate::Value, remaining: usize) -> Result<(), DepthCheckError> {
    check_value_impl(value, remaining, &mut || {})
}

#[cfg(any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema"))]
fn check_value_impl(
    value: &crate::Value,
    limit: usize,
    visit: &mut impl FnMut(),
) -> Result<(), DepthCheckError> {
    use crate::Value;

    let mut pending = alloc::vec::Vec::new();
    let mut heights = alloc::collections::BTreeMap::new();
    let mut height = 0_usize;
    let mut current = Some(Frame::Value(value, limit));
    while let Some(frame) = current.take().or_else(|| pending.pop()) {
        crate::utils::limits::check_memory_limit_if_needed()?;
        match frame {
            Frame::Value(value, remaining) => {
                visit();
                height = 0;
                let (identity, children) = match value {
                    Value::Array(values) => (
                        ContainerId::Array(crate::Rc::as_ptr(values)),
                        Children::Array(values.iter()),
                    ),
                    Value::Set(values) => (
                        ContainerId::Set(crate::Rc::as_ptr(values)),
                        Children::Set(values.iter()),
                    ),
                    Value::Object(values) => (
                        ContainerId::Object(crate::Rc::as_ptr(values)),
                        Children::Object(values.iter_sorted(), None),
                    ),
                    _ => continue,
                };
                if let Some(&known_height) = heights.get(&identity) {
                    if known_height > remaining {
                        return Err(DepthExceeded(limit).into());
                    }
                    height = known_height;
                } else {
                    current = Some(Frame::Container {
                        identity,
                        children,
                        remaining: remaining.checked_sub(1).ok_or(DepthExceeded(limit))?,
                        height: 1,
                    });
                }
            }
            Frame::Container {
                identity,
                mut children,
                remaining,
                height: maximum,
            } => {
                let maximum = maximum.max(height.checked_add(1).ok_or(DepthExceeded(limit))?);
                if let Some(child) = children.next() {
                    pending.push(Frame::Container {
                        identity,
                        children,
                        remaining,
                        height: maximum,
                    });
                    current = Some(Frame::Value(child, remaining));
                } else {
                    heights.insert(identity, maximum);
                    height = maximum;
                }
            }
        }
    }
    crate::utils::limits::check_memory_limit_if_needed()?;
    Ok(())
}

#[cfg(all(
    test,
    any(feature = "rvm", feature = "jsonpatch", feature = "jsonschema")
))]
mod tests {
    use super::*;
    use crate::Value;
    use alloc::collections::{BTreeMap, BTreeSet};
    use alloc::vec;

    fn nested(depth: usize) -> Value {
        (0..depth).fold(Value::Null, |value, _| Value::from(vec![value]))
    }

    #[test]
    fn shared_dag_visits_each_allocation_once() {
        for depth in [8, 16, 24, 32] {
            let value = (0..depth).fold(Value::Null, |value, _| {
                Value::from(vec![value.clone(), value])
            });
            let mut visits = 0_usize;
            assert_eq!(
                check_value_impl(&value, depth, &mut || visits = visits.saturating_add(1)),
                Ok(())
            );
            assert_eq!(visits, depth.saturating_mul(2).saturating_add(1));
        }
    }

    #[test]
    fn shared_objects_and_sets_use_allocation_identity() {
        for shared in [
            Value::from(BTreeMap::from([(Value::from("k"), nested(1))])),
            Value::from(BTreeSet::from([nested(1)])),
        ] {
            let value = Value::from(vec![shared.clone(), shared]);
            let mut visits = 0_usize;
            assert_eq!(
                check_value_impl(&value, 3, &mut || visits = visits.saturating_add(1)),
                Ok(())
            );
            assert!(visits <= 6);
        }
    }

    #[test]
    fn cached_heights_obey_each_path_budget() {
        let shared = nested(2);
        for children in [
            vec![shared.clone(), Value::from(vec![shared.clone()])],
            vec![Value::from(vec![shared.clone()]), shared.clone()],
        ] {
            let value = Value::from(children);
            assert_eq!(check_value(&value, 4), Ok(()));
            assert_eq!(
                check_value(&value, 3),
                Err(DepthCheckError::Depth(DepthExceeded(3)))
            );
        }
    }

    #[test]
    fn empty_containers_keys_and_members_count() {
        for value in [Value::new_array(), Value::new_set(), Value::new_object()] {
            assert_eq!(check_value(&value, 1), Ok(()));
            assert_eq!(
                check_value(&value, 0),
                Err(DepthCheckError::Depth(DepthExceeded(0)))
            );
        }
        for value in [
            Value::from(BTreeMap::from([(nested(2), Value::Null)])),
            Value::from(BTreeSet::from([nested(2)])),
        ] {
            assert_eq!(check_value(&value, 3), Ok(()));
            assert_eq!(
                check_value(&value, 2),
                Err(DepthCheckError::Depth(DepthExceeded(2)))
            );
        }
    }
}

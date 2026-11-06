// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

pub const MAX_DEPTH: usize = 32;

#[derive(Debug, thiserror::Error)]
#[error("operation exceeds supported nesting limit {0}")]
pub struct DepthExceeded(pub usize);

pub fn descend(remaining: usize) -> Result<usize, DepthExceeded> {
    remaining.checked_sub(1).ok_or(DepthExceeded(MAX_DEPTH))
}

#[cfg(any(
    feature = "rvm",
    feature = "jsonpatch",
    feature = "jsonschema",
    feature = "yaml"
))]
enum Frame<'a> {
    Value(&'a crate::Value, usize),
    Array(crate::value::ArrayIter<'a>, usize),
    Set(crate::value::SetIter<'a>, usize),
    Object(crate::value::Iter<'a>, usize),
}

// Count containers, including empty containers, object keys and set members.
// Iterator continuations keep scratch storage proportional to the active path.
#[cfg(any(
    feature = "rvm",
    feature = "jsonpatch",
    feature = "jsonschema",
    feature = "yaml"
))]
pub fn check_value(value: &crate::Value, remaining: usize) -> Result<(), DepthExceeded> {
    check_value_impl(value, remaining).map_err(|_| DepthExceeded(remaining))
}

#[cfg(any(
    feature = "rvm",
    feature = "jsonpatch",
    feature = "jsonschema",
    feature = "yaml"
))]
fn check_value_impl(value: &crate::Value, remaining: usize) -> Result<(), DepthExceeded> {
    use crate::Value;
    let mut pending = alloc::vec::Vec::new();
    let mut current = Some(Frame::Value(value, remaining));
    while let Some(frame) = current.take().or_else(|| pending.pop()) {
        match frame {
            Frame::Value(value, remaining) => {
                current = match value {
                    Value::Array(values) => Some(Frame::Array(values.iter(), descend(remaining)?)),
                    Value::Set(values) => Some(Frame::Set(values.iter(), descend(remaining)?)),
                    Value::Object(values) => {
                        Some(Frame::Object(values.iter_sorted(), descend(remaining)?))
                    }
                    _ => None,
                };
            }
            Frame::Array(mut values, remaining) => {
                if let Some(value) = values.next() {
                    pending.push(Frame::Array(values, remaining));
                    current = Some(Frame::Value(value, remaining));
                }
            }
            Frame::Set(mut values, remaining) => {
                if let Some(value) = values.next() {
                    pending.push(Frame::Set(values, remaining));
                    current = Some(Frame::Value(value, remaining));
                }
            }
            Frame::Object(mut values, remaining) => {
                if let Some((key, value)) = values.next() {
                    pending.push(Frame::Object(values, remaining));
                    pending.push(Frame::Value(value, remaining));
                    current = Some(Frame::Value(key, remaining));
                }
            }
        }
    }
    Ok(())
}

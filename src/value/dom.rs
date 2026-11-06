// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::{Object, Value};
use alloc::{boxed::Box, vec, vec::Vec};

pub(super) enum Dom {
    Json(serde_json::Value),
    #[cfg(feature = "yaml")]
    Yaml(yaml_serde::Value),
}

type Items = Box<dyn Iterator<Item = Dom>>;
type Entries = Box<dyn Iterator<Item = (Dom, Dom)>>;

enum Frame {
    Value(Dom),
    Array(Items, Vec<Value>, bool),
    Map(Entries, Object),
    Key(Entries, Object, Dom),
    Entry(Entries, Object, Value),
}

pub(super) fn convert(value: Dom) -> Value {
    let mut pending = vec![Frame::Value(value)];
    let mut result = Value::Undefined;
    let mut valid = true;
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Value(Dom::Json(value)) => match value {
                serde_json::Value::Null => result = Value::Null,
                serde_json::Value::Bool(value) => result = Value::Bool(value),
                serde_json::Value::String(value) => result = Value::from(value),
                serde_json::Value::Number(value) => {
                    result = number(
                        serde_json::from_value::<Value>(serde_json::Value::Number(value)),
                        &mut valid,
                    );
                }
                serde_json::Value::Array(values) => pending.push(Frame::Array(
                    Box::new(values.into_iter().map(Dom::Json)),
                    Vec::new(),
                    false,
                )),
                serde_json::Value::Object(values) => pending.push(Frame::Map(
                    Box::new(values.into_iter().map(|(key, value)| {
                        (Dom::Json(serde_json::Value::String(key)), Dom::Json(value))
                    })),
                    Object::new(),
                )),
            },
            #[cfg(feature = "yaml")]
            Frame::Value(Dom::Yaml(value)) => match value {
                yaml_serde::Value::Null => result = Value::Null,
                yaml_serde::Value::Bool(value) => result = Value::Bool(value),
                yaml_serde::Value::String(value) => result = Value::from(value),
                yaml_serde::Value::Number(value) => {
                    result = number(
                        yaml_serde::from_value::<Value>(yaml_serde::Value::Number(value)),
                        &mut valid,
                    );
                }
                yaml_serde::Value::Sequence(values) => pending.push(Frame::Array(
                    Box::new(values.into_iter().map(Dom::Yaml)),
                    Vec::new(),
                    false,
                )),
                yaml_serde::Value::Mapping(values) => pending.push(Frame::Map(
                    Box::new(
                        values
                            .into_iter()
                            .map(|(key, value)| (Dom::Yaml(key), Dom::Yaml(value))),
                    ),
                    Object::new(),
                )),
                yaml_serde::Value::Tagged(value) => {
                    valid = false;
                    pending.push(Frame::Value(Dom::Yaml(value.value)));
                }
            },
            Frame::Array(mut values, mut output, have_child) => {
                if have_child {
                    output.push(core::mem::replace(&mut result, Value::Undefined));
                }
                if let Some(value) = values.next() {
                    pending.push(Frame::Array(values, output, true));
                    pending.push(Frame::Value(value));
                } else {
                    result = Value::from(output);
                }
            }
            Frame::Map(mut values, output) => {
                if let Some((key, value)) = values.next() {
                    pending.push(Frame::Key(values, output, value));
                    pending.push(Frame::Value(key));
                } else {
                    result = output.into_value();
                }
            }
            Frame::Key(values, output, value) => {
                let key = core::mem::replace(&mut result, Value::Undefined);
                pending.push(Frame::Entry(values, output, key));
                pending.push(Frame::Value(value));
            }
            Frame::Entry(values, mut output, key) => {
                output.insert(key, core::mem::replace(&mut result, Value::Undefined));
                pending.push(Frame::Map(values, output));
            }
        }
    }
    if valid {
        result
    } else {
        Value::Undefined
    }
}

fn number<E>(value: Result<Value, E>, valid: &mut bool) -> Value {
    match value {
        Ok(value) => value,
        Err(_) => {
            *valid = false;
            Value::Undefined
        }
    }
}

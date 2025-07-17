// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use serde::{Deserialize, Deserializer, Serialize};

use crate::*;
use alloc::collections::BTreeMap;
use anyhow::{bail, Result};

#[derive(Deserialize, Serialize, Debug, Eq, PartialEq, Ord, PartialOrd, Clone)]
#[serde(rename_all = "camelCase")]
pub enum SimpleType {
    Array,
    Boolean,
    Integer,
    Null,
    Number,
    Object,
    String,

    // Types that exist only in Rego
    Set,
    Undefined,
}

#[derive(Deserialize, Serialize, Debug, Eq, PartialEq, Ord, PartialOrd)]
#[serde(rename_all = "camelCase")]
pub enum Constraint {
    Id(String),
    Schema(String),
    Ref(String),

    //Comment(String),
    //Title(String),
    //Description(String),
    //ReadOnly(String),
    //WriteOnly(String),
    MultipleOf(Value),
    Maximum(Value),
    ExclusiveMaximum(Value),
    Minimum(Value),
    ExclusiveMininum(Value),
    MaxLength(Value),
    MinLength(Value),
    Pattern(String),
    AdditionalItem(Rc<Schema>),
    Items(Items),
    MaxItems(u32),
    MinItems(u32),
    UniqueItems(bool),
    Contains(Schema),
    MaxProperties(u32),
    MinProperties(u32),
    Required(Vec<String>),
    AdditionalProperties(Schema),
    Definitions(Rc<BTreeMap<String, Schema>>),
    Properties(Rc<BTreeMap<String, Schema>>),
    PatternProperties(Rc<BTreeMap<String, Schema>>),
    PropertyNames(Schema),
    Const(Value),
    Enum(Rc<Vec<Value>>),

    // Since this is the most important and common constraint, we inline it in
    // Schema directly.
    // Type(SimpleType)
    Format(String),

    // contentMediaType
    // contentEncoding
    // if
    // then
    // else
    AllOf(Rc<Vec<Schema>>),
    AnyOf(Rc<Vec<Schema>>),
    OneOf(Rc<Vec<Schema>>),
    Not(Rc<Schema>),
}

#[derive(Deserialize, Serialize, Debug, Eq, PartialEq, Ord, PartialOrd)]
#[serde(untagged)]
pub enum Items {
    Schema(Rc<Schema>),
    Array(Vec<Rc<Schema>>),
}

#[derive(Deserialize, Serialize, Debug, Eq, PartialEq, Ord, PartialOrd, Clone)]
#[serde(rename_all = "camelCase")]
#[serde(untagged)]
pub enum Type {
    One(SimpleType),
    Array(Rc<Vec<SimpleType>>),
}

#[derive(Serialize, Debug, Clone, Default, Eq, PartialEq, Ord, PartialOrd)]
#[serde(rename_all = "camelCase")]
pub struct Schema {
    #[serde(rename = "type")]
    pub type_: Option<Type>,

    pub constraints: Rc<Vec<Constraint>>,

    pub extra: Rc<BTreeMap<String, Value>>,
}

impl<'de> Deserialize<'de> for Schema {
    fn deserialize<D>(deserializer: D) -> Result<Schema, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Use a helper to read constraints.
        #[derive(Deserialize)]
        #[serde(rename = "camelCase")]
        struct S {
            #[serde(rename = "$id")]
            id: Option<String>,
            #[serde(rename = "$schema")]
            schema: Option<String>,
            #[serde(rename = "$ref")]
            ref_: Option<String>,

            //#[serde(rename="$comment")]
            //comment: Option<String>,

            //title: Option<String>,
            //description: Option<String>,
            //read_only: Option<String>,
            //write_only: Option<String>,
            multiple_of: Option<Value>,
            maximum: Option<Value>,
            exclusive_maximum: Option<Value>,
            minimum: Option<Value>,
            exclusive_mininum: Option<Value>,
            max_length: Option<Value>,
            min_length: Option<Value>,
            pattern: Option<String>,
            additional_item: Option<Schema>,
            items: Option<Items>,
            max_items: Option<u32>,
            min_items: Option<u32>,
            unique_items: Option<bool>,
            contains: Option<Schema>,
            max_properties: Option<u32>,
            min_properties: Option<u32>,
            required: Option<Vec<String>>,
            additional_properties: Option<Schema>,
            definitions: Option<Rc<BTreeMap<String, Schema>>>,
            properties: Option<Rc<BTreeMap<String, Schema>>>,
            pattern_properties: Option<Rc<BTreeMap<String, Schema>>>,
            property_names: Option<Schema>,

            #[serde(rename = "const")]
            const_: Option<Value>,
            #[serde(rename = "enum")]
            enum_: Option<Rc<Vec<Value>>>,

            #[serde(rename = "type")]
            type_: Option<Type>,

            format: Option<String>,

            all_of: Option<Rc<Vec<Schema>>>,
            any_of: Option<Rc<Vec<Schema>>>,
            one_of: Option<Rc<Vec<Schema>>>,
            not: Option<Schema>,

            #[serde(flatten)]
            extra: BTreeMap<String, Value>,
        }

        let s: S = S::deserialize(deserializer)?;
        let mut constraints = Vec::default();

        if let Some(v) = s.id {
            constraints.push(Constraint::Id(v));
        }

        if let Some(v) = s.schema {
            constraints.push(Constraint::Schema(v))
        }

        if let Some(v) = s.ref_ {
            constraints.push(Constraint::Ref(v));
        }

        if let Some(v) = s.multiple_of {
            constraints.push(Constraint::MultipleOf(v));
        }

        if let Some(v) = s.maximum {
            constraints.push(Constraint::Maximum(v));
        }

        if let Some(v) = s.exclusive_maximum {
            constraints.push(Constraint::ExclusiveMaximum(v));
        }

        if let Some(v) = s.minimum {
            constraints.push(Constraint::Minimum(v));
        }

        if let Some(v) = s.exclusive_mininum {
            constraints.push(Constraint::ExclusiveMininum(v));
        }

        if let Some(v) = s.max_length {
            constraints.push(Constraint::MaxLength(v));
        }

        if let Some(v) = s.min_length {
            constraints.push(Constraint::MinLength(v));
        }

        if let Some(v) = s.pattern {
            constraints.push(Constraint::Pattern(v));
        }

        if let Some(v) = s.additional_item {
            constraints.push(Constraint::AdditionalItem(Rc::new(v)));
        }

        if let Some(v) = s.items {
            constraints.push(Constraint::Items(v));
        }

        if let Some(v) = s.max_items {
            constraints.push(Constraint::MaxItems(v));
        }

        if let Some(v) = s.min_items {
            constraints.push(Constraint::MinItems(v));
        }

        if let Some(v) = s.unique_items {
            constraints.push(Constraint::UniqueItems(v));
        }

        if let Some(v) = s.contains {
            constraints.push(Constraint::Contains(v));
        }

        if let Some(v) = s.max_properties {
            constraints.push(Constraint::MaxProperties(v));
        }

        if let Some(v) = s.min_properties {
            constraints.push(Constraint::MinProperties(v));
        }

        if let Some(v) = s.required {
            constraints.push(Constraint::Required(v));
        }

        if let Some(v) = s.additional_properties {
            constraints.push(Constraint::AdditionalProperties(v));
        }

        if let Some(v) = s.definitions {
            constraints.push(Constraint::Definitions(v));
        }

        if let Some(v) = s.properties {
            constraints.push(Constraint::Properties(v));
        }

        if let Some(v) = s.pattern_properties {
            constraints.push(Constraint::PatternProperties(v));
        }

        if let Some(v) = s.property_names {
            constraints.push(Constraint::PropertyNames(v));
        }

        if let Some(v) = s.const_ {
            constraints.push(Constraint::Const(v));
        }

        if let Some(v) = s.enum_ {
            constraints.push(Constraint::Enum(v));
        }

        if let Some(v) = s.format {
            constraints.push(Constraint::Format(v));
        }

        if let Some(v) = s.all_of {
            constraints.push(Constraint::AllOf(v));
        }

        if let Some(v) = s.any_of {
            constraints.push(Constraint::AnyOf(v));
        }

        if let Some(v) = s.one_of {
            constraints.push(Constraint::OneOf(v));
        }

        if let Some(v) = s.not {
            constraints.push(Constraint::Not(Rc::new(v)));
        }

        let schema = Schema {
            type_: s.type_,
            constraints: Rc::new(constraints),
            extra: Rc::new(s.extra),
        };

        Ok(schema)
    }
}

impl Schema {
    pub fn get_property(&self, name: &str) -> Result<Schema> {
        for c in self.constraints.iter() {
            if let Constraint::Properties(props) = c {
                match props.get(name) {
                    Some(s) => return Ok(s.clone()),
                    _ => {
                        bail!("Invalid key `{name}`. Valid keys are {:?}", props.keys())
                    }
                }
            }
        }
        bail!("cannot index into a non-object")
    }
}

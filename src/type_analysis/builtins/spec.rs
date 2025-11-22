// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::TryFrom;
use core::fmt;

use crate::schema::Type;
use crate::type_analysis::model::{
    HybridType, StructuralObjectShape, StructuralType, TypeDescriptor,
};

use super::catalog::{BuiltinConfig, PurityConfig, TemplateConfig};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinPurity {
    Pure,
    Impure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinTypeTemplate {
    Any,
    Boolean,
    Number,
    Integer,
    String,
    Null,
    ArrayAny,
    SetAny,
    ObjectAny,
    SameAsArgument(u8),
    CollectionElement(u8),
}

fn descriptor_from_template(template: BuiltinTypeTemplate, args: &[HybridType]) -> TypeDescriptor {
    match template {
        BuiltinTypeTemplate::Any => TypeDescriptor::structural(StructuralType::Any),
        BuiltinTypeTemplate::Boolean => TypeDescriptor::structural(StructuralType::Boolean),
        BuiltinTypeTemplate::Number => TypeDescriptor::structural(StructuralType::Number),
        BuiltinTypeTemplate::Integer => TypeDescriptor::structural(StructuralType::Integer),
        BuiltinTypeTemplate::String => TypeDescriptor::structural(StructuralType::String),
        BuiltinTypeTemplate::Null => TypeDescriptor::structural(StructuralType::Null),
        BuiltinTypeTemplate::ArrayAny => {
            TypeDescriptor::structural(StructuralType::Array(Box::new(StructuralType::Any)))
        }
        BuiltinTypeTemplate::SetAny => {
            TypeDescriptor::structural(StructuralType::Set(Box::new(StructuralType::Any)))
        }
        BuiltinTypeTemplate::ObjectAny => {
            TypeDescriptor::structural(StructuralType::Object(StructuralObjectShape::new()))
        }
        BuiltinTypeTemplate::SameAsArgument(idx) => args
            .get(idx as usize)
            .map(|arg| arg.fact.descriptor.clone())
            .unwrap_or_else(|| TypeDescriptor::structural(StructuralType::Any)),
        BuiltinTypeTemplate::CollectionElement(idx) => args
            .get(idx as usize)
            .map(collection_element_descriptor)
            .unwrap_or_else(|| TypeDescriptor::structural(StructuralType::Any)),
    }
}

fn collection_element_descriptor(arg: &HybridType) -> TypeDescriptor {
    match &arg.fact.descriptor {
        TypeDescriptor::Structural(structural) => match structural {
            StructuralType::Array(inner) | StructuralType::Set(inner) => {
                TypeDescriptor::structural((**inner).clone())
            }
            _ => TypeDescriptor::structural(StructuralType::Any),
        },
        TypeDescriptor::Schema(schema) => match schema.as_type() {
            Type::Array { items, .. } | Type::Set { items, .. } => {
                TypeDescriptor::schema(items.clone())
            }
            _ => TypeDescriptor::structural(StructuralType::Any),
        },
    }
}

#[derive(Clone, Debug)]
pub struct BuiltinSpec {
    purity: BuiltinPurity,
    return_template: BuiltinTypeTemplate,
    params: Option<Box<[BuiltinTypeTemplate]>>,
    param_count: u8,
    must_cache: bool,
}

impl BuiltinSpec {
    fn from_parts(
        purity: BuiltinPurity,
        return_template: BuiltinTypeTemplate,
        params: Option<Box<[BuiltinTypeTemplate]>>,
        param_count: u8,
        must_cache: bool,
    ) -> Self {
        BuiltinSpec {
            purity,
            return_template,
            params,
            param_count,
            must_cache,
        }
    }

    pub(super) fn from_config(name: &str, cfg: &BuiltinConfig) -> Result<Self, BuiltinTableError> {
        let params_vec: Vec<BuiltinTypeTemplate> = cfg
            .params
            .iter()
            .copied()
            .map(TemplateConfig::as_template)
            .collect();

        let param_len = params_vec.len();
        let param_count =
            u8::try_from(param_len).map_err(|_| BuiltinTableError::TooManyParameters {
                builtin: name.to_owned(),
                count: param_len,
            })?;

        let params = Some(params_vec.into_boxed_slice());
        let purity = cfg.purity.unwrap_or(PurityConfig::Pure).into_purity();

        let spec = BuiltinSpec::from_parts(
            purity,
            cfg.return_template.as_template(),
            params,
            param_count,
            cfg.cache,
        );

        spec.validate_template_indices(name)?;
        Ok(spec)
    }

    fn validate_template_indices(&self, name: &str) -> Result<(), BuiltinTableError> {
        let param_total = self.param_count as usize;

        match self.return_template {
            BuiltinTypeTemplate::SameAsArgument(idx)
            | BuiltinTypeTemplate::CollectionElement(idx)
                if idx as usize >= param_total =>
            {
                return Err(BuiltinTableError::InvalidTemplate {
                    builtin: name.to_owned(),
                    detail: format!(
                        "return template references argument {idx} but only {param_total} parameters defined",
                    ),
                });
            }
            _ => {}
        }

        if let Some(params) = &self.params {
            for (position, template) in params.iter().enumerate() {
                match template {
                    BuiltinTypeTemplate::SameAsArgument(idx)
                    | BuiltinTypeTemplate::CollectionElement(idx)
                        if *idx as usize >= param_total =>
                    {
                        return Err(BuiltinTableError::InvalidTemplate {
                            builtin: name.to_owned(),
                            detail: format!(
                                "parameter template at index {position} references argument {idx} but only {param_total} parameters defined",
                            ),
                        });
                    }
                    _ => {}
                }
            }
        }

        Ok(())
    }

    pub const fn fallback(param_count: u8) -> Self {
        BuiltinSpec {
            purity: BuiltinPurity::Impure,
            return_template: BuiltinTypeTemplate::Any,
            params: None,
            param_count,
            must_cache: false,
        }
    }

    pub fn return_descriptor(&self, args: &[HybridType]) -> TypeDescriptor {
        descriptor_from_template(self.return_template, args)
    }

    pub fn params(&self) -> Option<&[BuiltinTypeTemplate]> {
        self.params.as_deref()
    }

    pub fn param_count(&self) -> u8 {
        self.param_count
    }

    pub fn is_pure(&self) -> bool {
        matches!(self.purity, BuiltinPurity::Pure)
    }

    pub fn must_cache(&self) -> bool {
        self.must_cache
    }
}

#[derive(Debug)]
pub enum BuiltinTableError {
    Parse(serde_json::Error),
    DuplicateBuiltin(String),
    UnknownFeature(String),
    TooManyParameters { builtin: String, count: usize },
    InvalidTemplate { builtin: String, detail: String },
}

impl fmt::Display for BuiltinTableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuiltinTableError::Parse(err) => write!(f, "failed to parse builtin table: {err}"),
            BuiltinTableError::DuplicateBuiltin(name) => {
                write!(f, "duplicate builtin entry `{name}` in table")
            }
            BuiltinTableError::UnknownFeature(feature) => {
                write!(f, "unknown feature `{feature}` referenced in builtin table")
            }
            BuiltinTableError::TooManyParameters { builtin, count } => write!(
                f,
                "builtin `{builtin}` declares {count} parameters which exceeds supported limit"
            ),
            BuiltinTableError::InvalidTemplate { builtin, detail } => {
                write!(f, "builtin `{builtin}` has invalid template: {detail}")
            }
        }
    }
}

impl From<serde_json::Error> for BuiltinTableError {
    fn from(err: serde_json::Error) -> Self {
        BuiltinTableError::Parse(err)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for BuiltinTableError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            BuiltinTableError::Parse(err) => Some(err),
            _ => None,
        }
    }
}

pub fn return_descriptor(template: BuiltinTypeTemplate, args: &[HybridType]) -> TypeDescriptor {
    descriptor_from_template(template, args)
}

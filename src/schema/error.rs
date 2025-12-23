// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::use_debug, clippy::pattern_type_mismatch)]

use crate::*;

type String = Rc<str>;

/// Validation errors that can occur when validating a Value against a Schema.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    /// Value type does not match the expected schema type.
    TypeMismatch {
        expected: String,
        actual: String,
        path: String,
    },
    /// Numeric value is outside the allowed range.
    OutOfRange {
        value: String,
        min: Option<String>,
        max: Option<String>,
        path: String,
    },
    /// String length constraint violation.
    LengthConstraint {
        actual_length: usize,
        min_length: Option<usize>,
        max_length: Option<usize>,
        path: String,
    },
    /// String does not match required pattern.
    PatternMismatch {
        value: String,
        pattern: String,
        path: String,
    },
    /// Array size constraint violation.
    ArraySizeConstraint {
        actual_size: usize,
        min_items: Option<usize>,
        max_items: Option<usize>,
        path: String,
    },
    /// Required object property is missing.
    MissingRequiredProperty { property: String, path: String },
    /// Object property failed validation.
    PropertyValidationFailed {
        property: String,
        path: String,
        error: Box<ValidationError>,
    },
    /// Additional properties are not allowed.
    AdditionalPropertiesNotAllowed { property: String, path: String },
    /// Value is not in the allowed enum values.
    NotInEnum {
        value: String,
        allowed_values: Vec<String>,
        path: String,
    },
    /// Value does not match the required constant.
    ConstMismatch {
        expected: String,
        actual: String,
        path: String,
    },
    /// Value does not match any schema in a union (anyOf).
    NoUnionMatch {
        path: String,
        errors: Vec<ValidationError>,
    },
    /// Invalid regex pattern in schema.
    InvalidPattern { pattern: String, error: String },
    /// Array item validation failed.
    ArrayItemValidationFailed {
        index: usize,
        path: String,
        error: Box<ValidationError>,
    },
    /// Object key is not a string.
    NonStringKey { key_type: String, path: String },
    /// Missing discriminator field in discriminated subobject.
    MissingDiscriminator { discriminator: String, path: String },
    /// Unknown discriminator value in discriminated subobject.
    UnknownDiscriminatorValue {
        discriminator: String,
        value: String,
        allowed_values: Vec<String>,
        path: String,
    },
    /// Discriminated subobject validation failed.
    DiscriminatedSubobjectValidationFailed {
        discriminator: String,
        value: String,
        path: String,
        error: Box<ValidationError>,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::TypeMismatch {
                expected,
                actual,
                path,
            } => {
                write!(
                    f,
                    "Type mismatch at '{path}': expected {expected}, got {actual}"
                )
            }
            ValidationError::OutOfRange {
                value,
                min,
                max,
                path,
            } => {
                let range_desc = match (min, max) {
                    (Some(min), Some(max)) => format!("between {min} and {max}"),
                    (Some(min), None) => format!("at least {min}"),
                    (None, Some(max)) => format!("at most {max}"),
                    (None, None) => "within valid range".to_string(),
                };
                write!(
                    f,
                    "Value {value} at '{path}' is out of range: must be {range_desc}"
                )
            }
            ValidationError::LengthConstraint {
                actual_length,
                min_length,
                max_length,
                path,
            } => {
                let constraint_desc = match (min_length, max_length) {
                    (Some(min), Some(max)) => format!("between {min} and {max} characters"),
                    (Some(min), None) => format!("at least {min} characters"),
                    (None, Some(max)) => format!("at most {max} characters"),
                    (None, None) => "within valid length".to_string(),
                };
                write!(
                    f,
                    "String length {actual_length} at '{path}' violates constraint: must be {constraint_desc}"
                )
            }
            ValidationError::PatternMismatch {
                value,
                pattern,
                path,
            } => {
                write!(
                    f,
                    "String '{value}' at '{path}' does not match pattern '{pattern}'"
                )
            }
            ValidationError::ArraySizeConstraint {
                actual_size,
                min_items,
                max_items,
                path,
            } => {
                let constraint_desc = match (min_items, max_items) {
                    (Some(min), Some(max)) => format!("between {min} and {max} items"),
                    (Some(min), None) => format!("at least {min} items"),
                    (None, Some(max)) => format!("at most {max} items"),
                    (None, None) => "within valid size".to_string(),
                };
                write!(
                    f,
                    "Array size {actual_size} at '{path}' violates constraint: must have {constraint_desc}"
                )
            }
            ValidationError::MissingRequiredProperty { property, path } => {
                write!(f, "Missing required property '{property}' at '{path}'")
            }
            ValidationError::PropertyValidationFailed {
                property,
                path,
                error,
            } => {
                write!(
                    f,
                    "Property '{property}' at '{path}' failed validation: {error}"
                )
            }
            ValidationError::AdditionalPropertiesNotAllowed { property, path } => {
                write!(
                    f,
                    "Additional property '{property}' not allowed at '{path}'"
                )
            }
            ValidationError::NotInEnum {
                value,
                allowed_values,
                path,
            } => {
                let values_json = serde_json::to_string(&allowed_values)
                    .unwrap_or_else(|_| format!("{allowed_values:?}"));

                write!(
                    f,
                    "Value '{value}' at '{path}' is not in allowed enum values: {values_json}",
                )
            }
            ValidationError::ConstMismatch {
                expected,
                actual,
                path,
            } => {
                write!(
                    f,
                    "Constant mismatch at '{path}': expected '{expected}', got '{actual}'"
                )
            }
            ValidationError::NoUnionMatch { path, errors } => {
                write!(
                    f,
                    "Value at '{path}' does not match any schema in union. Errors: {errors:?}"
                )
            }
            ValidationError::InvalidPattern { pattern, error } => {
                write!(f, "Invalid regex pattern '{pattern}': {error}")
            }
            ValidationError::ArrayItemValidationFailed { index, path, error } => {
                write!(
                    f,
                    "Array item {index} at '{path}' failed validation: {error}"
                )
            }
            ValidationError::NonStringKey { key_type, path } => {
                write!(
                    f,
                    "Object key at '{path}' must be a string, but found {key_type}"
                )
            }
            ValidationError::MissingDiscriminator {
                discriminator,
                path,
            } => {
                write!(
                    f,
                    "Missing discriminator field '{discriminator}' at '{path}'"
                )
            }
            ValidationError::UnknownDiscriminatorValue {
                discriminator,
                value,
                allowed_values,
                path,
            } => {
                let values_json: Vec<serde_json::Value> = allowed_values
                    .iter()
                    .map(|v| serde_json::Value::String(v.to_string()))
                    .collect();
                write!(
                    f,
                    "Unknown discriminator value '{value}' for field '{discriminator}' at '{path}'. Allowed values: {}",
                    serde_json::to_string(&values_json).unwrap_or_else(|_| format!("{values_json:?}"))
                )
            }
            ValidationError::DiscriminatedSubobjectValidationFailed {
                discriminator,
                value,
                path,
                error,
            } => {
                write!(
                    f,
                    "Discriminated subobject validation failed for discriminator '{discriminator}' with value '{value}' at '{path}': {error}"
                )
            }
        }
    }
}

impl core::error::Error for ValidationError {}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(missing_debug_implementations)] // validator is zero-sized marker
#![allow(dead_code)]
#![allow(clippy::pattern_type_mismatch, clippy::needless_continue)]

use crate::{
    schema::{error::ValidationError, Schema, Type},
    *,
};
use alloc::collections::BTreeMap;
use regex::Regex;

type String = Rc<str>;

/// Validator for checking if a Value conforms to a Schema.
pub struct SchemaValidator;

impl SchemaValidator {
    /// Validates a Value against a Schema.
    ///
    /// # Arguments
    /// * `value` - The Value to validate
    /// * `schema` - The Schema to validate against
    ///
    /// # Returns
    /// * `Ok(())` if the value conforms to the schema
    /// * `Err(ValidationError)` if validation fails
    ///
    /// # Example
    /// ```rust
    /// use regorus::schema::{Schema, validate::SchemaValidator};
    /// use regorus::Value;
    /// use serde_json::json;
    ///
    /// let schema_json = json!({
    ///     "type": "string",
    ///     "minLength": 1,
    ///     "maxLength": 10
    /// });
    /// let schema = Schema::from_serde_json_value(schema_json).unwrap();
    /// let value = Value::from("hello");
    ///
    /// let result = SchemaValidator::validate(&value, &schema);
    /// assert!(result.is_ok());
    /// ```
    pub fn validate(value: &Value, schema: &Schema) -> Result<(), ValidationError> {
        Self::validate_with_path(value, schema, "")
    }

    /// Internal validation function that tracks the current path for error reporting.
    fn validate_with_path(
        value: &Value,
        schema: &Schema,
        path: &str,
    ) -> Result<(), ValidationError> {
        match schema.as_type() {
            Type::Any { .. } => {
                // Any type accepts all values
                Ok(())
            }
            Type::Integer {
                minimum, maximum, ..
            } => Self::validate_integer(value, *minimum, *maximum, path),
            Type::Number {
                minimum, maximum, ..
            } => Self::validate_number(value, *minimum, *maximum, path),
            Type::Boolean { .. } => Self::validate_boolean(value, path),
            Type::Null { .. } => Self::validate_null(value, path),
            Type::String {
                min_length,
                max_length,
                pattern,
                ..
            } => Self::validate_string(value, *min_length, *max_length, pattern.as_ref(), path),
            Type::Array {
                items,
                min_items,
                max_items,
                ..
            } => Self::validate_array(value, items, *min_items, *max_items, path),
            Type::Object {
                properties,
                required,
                additional_properties,
                discriminated_subobject,
                ..
            } => Self::validate_object(
                value,
                properties,
                required.as_ref().map(|r| &**r),
                additional_properties.as_ref(),
                discriminated_subobject.as_ref().map(|d| &**d),
                path,
            ),
            Type::AnyOf(schemas) => Self::validate_any_of(value, schemas, path),
            Type::Const {
                value: const_value, ..
            } => Self::validate_const(value, const_value, path),
            Type::Enum { values, .. } => Self::validate_enum(value, values, path),
            Type::Set { items, .. } => Self::validate_set(value, items, path),
        }
    }

    fn validate_integer(
        value: &Value,
        minimum: Option<i64>,
        maximum: Option<i64>,
        path: &str,
    ) -> Result<(), ValidationError> {
        match value {
            Value::Number(num) => {
                if let Some(int_val) = num.as_i64() {
                    if let Some(min) = minimum {
                        if int_val < min {
                            return Err(ValidationError::OutOfRange {
                                value: int_val.to_string().into(),
                                min: Some(min.to_string().into()),
                                max: maximum.map(|m| m.to_string().into()),
                                path: path.to_string().into(),
                            });
                        }
                    }
                    if let Some(max) = maximum {
                        if int_val > max {
                            return Err(ValidationError::OutOfRange {
                                value: int_val.to_string().into(),
                                min: minimum.map(|m| m.to_string().into()),
                                max: Some(max.to_string().into()),
                                path: path.into(),
                            });
                        }
                    }
                    Ok(())
                } else {
                    Err(ValidationError::TypeMismatch {
                        expected: "integer".into(),
                        actual: "non-integer number".into(),
                        path: path.into(),
                    })
                }
            }
            _ => Err(ValidationError::TypeMismatch {
                expected: "integer".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_number(
        value: &Value,
        minimum: Option<f64>,
        maximum: Option<f64>,
        path: &str,
    ) -> Result<(), ValidationError> {
        match value {
            Value::Number(num) => {
                if let Some(float_val) = num.as_f64() {
                    if let Some(min) = minimum {
                        if float_val < min {
                            return Err(ValidationError::OutOfRange {
                                value: float_val.to_string().into(),
                                min: Some(min.to_string().into()),
                                max: maximum.map(|m| m.to_string().into()),
                                path: path.into(),
                            });
                        }
                    }
                    if let Some(max) = maximum {
                        if float_val > max {
                            return Err(ValidationError::OutOfRange {
                                value: float_val.to_string().into(),
                                min: minimum.map(|m| m.to_string().into()),
                                max: Some(max.to_string().into()),
                                path: path.to_string().into(),
                            });
                        }
                    }
                    Ok(())
                } else {
                    Err(ValidationError::TypeMismatch {
                        expected: "number".into(),
                        actual: "non-numeric value".into(),
                        path: path.into(),
                    })
                }
            }
            _ => Err(ValidationError::TypeMismatch {
                expected: "number".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_boolean(value: &Value, path: &str) -> Result<(), ValidationError> {
        match value {
            Value::Bool(_) => Ok(()),
            _ => Err(ValidationError::TypeMismatch {
                expected: "boolean".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_null(value: &Value, path: &str) -> Result<(), ValidationError> {
        match value {
            Value::Null => Ok(()),
            _ => Err(ValidationError::TypeMismatch {
                expected: "null".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_string(
        value: &Value,
        min_length: Option<usize>,
        max_length: Option<usize>,
        pattern: Option<&String>,
        path: &str,
    ) -> Result<(), ValidationError> {
        match value {
            Value::String(string_value) => {
                let str_len = string_value.len();

                // Check length constraints
                if let Some(min) = min_length {
                    if str_len < min {
                        return Err(ValidationError::LengthConstraint {
                            actual_length: str_len,
                            min_length: Some(min),
                            max_length,
                            path: path.into(),
                        });
                    }
                }
                if let Some(max) = max_length {
                    if str_len > max {
                        return Err(ValidationError::LengthConstraint {
                            actual_length: str_len,
                            min_length,
                            max_length: Some(max),
                            path: path.into(),
                        });
                    }
                }

                // Check pattern constraint
                if let Some(pattern_str) = pattern {
                    let regex =
                        Regex::new(pattern_str).map_err(|e| ValidationError::InvalidPattern {
                            pattern: pattern_str.as_ref().into(),
                            error: e.to_string().into(),
                        })?;

                    if !regex.is_match(string_value) {
                        return Err(ValidationError::PatternMismatch {
                            value: string_value.to_string().into(),
                            pattern: pattern_str.clone(),
                            path: path.into(),
                        });
                    }
                }

                Ok(())
            }
            _ => Err(ValidationError::TypeMismatch {
                expected: "string".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_array(
        value: &Value,
        items_schema: &Schema,
        min_items: Option<usize>,
        max_items: Option<usize>,
        path: &str,
    ) -> Result<(), ValidationError> {
        match value {
            Value::Array(array_value) => {
                let arr_len = array_value.len();

                // Check size constraints
                if let Some(min) = min_items {
                    if arr_len < min {
                        return Err(ValidationError::ArraySizeConstraint {
                            actual_size: arr_len,
                            min_items: Some(min),
                            max_items,
                            path: path.into(),
                        });
                    }
                }
                if let Some(max) = max_items {
                    if arr_len > max {
                        return Err(ValidationError::ArraySizeConstraint {
                            actual_size: arr_len,
                            min_items,
                            max_items: Some(max),
                            path: path.into(),
                        });
                    }
                }

                // Validate each item
                for (index, item) in array_value.iter().enumerate() {
                    Self::validate_with_path(
                        item,
                        items_schema,
                        &if path.is_empty() {
                            format!("[{index}]")
                        } else {
                            format!("{path}[{index}]")
                        },
                    )
                    .map_err(|e| {
                        ValidationError::ArrayItemValidationFailed {
                            index,
                            path: path.into(),
                            error: Box::new(e),
                        }
                    })?;
                }

                Ok(())
            }
            _ => Err(ValidationError::TypeMismatch {
                expected: "array".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_object(
        value: &Value,
        properties: &BTreeMap<String, Schema>,
        required: Option<&Vec<String>>,
        additional_properties: Option<&Schema>,
        discriminated_subobject: Option<&crate::schema::DiscriminatedSubobject>,
        path: &str,
    ) -> Result<(), ValidationError> {
        match value {
            Value::Object(object_value) => {
                // Check required properties
                if let Some(required_props) = required {
                    for required_prop in required_props.iter() {
                        if !object_value.contains_key(&Value::String(required_prop.clone())) {
                            return Err(ValidationError::MissingRequiredProperty {
                                property: required_prop.clone(),
                                path: path.into(),
                            });
                        }
                    }
                }

                // Handle discriminated subobjects (allOf with if/then)
                // Validates against the appropriate variant schema based on discriminator field value
                if let Some(discriminated_subobject) = discriminated_subobject {
                    Self::validate_discriminated_subobject_with_base(
                        object_value,
                        discriminated_subobject,
                        properties,
                        additional_properties,
                        path,
                    )?;
                } else {
                    // Only validate regular object properties if no discriminated subobject exists
                    // Validate each property
                    for (prop_name, prop_value) in object_value.iter() {
                        // First, ensure the property key is a string
                        let prop_name_str = match prop_name {
                            Value::String(string_key) => string_key,
                            _ => {
                                return Err(ValidationError::NonStringKey {
                                    key_type: Self::value_type_name(prop_name),
                                    path: path.into(),
                                });
                            }
                        };

                        // Create property path lazily using a closure
                        let make_prop_path = || {
                            if path.is_empty() {
                                format!("[{prop_name_str}]")
                            } else {
                                format!("{path}.{prop_name_str}")
                            }
                        };

                        if let Some(prop_schema) = properties.get(prop_name_str) {
                            // Property is defined in schema, validate against it
                            Self::validate_with_path(prop_value, prop_schema, &make_prop_path())
                                .map_err(|e| ValidationError::PropertyValidationFailed {
                                    property: prop_name_str.clone(),
                                    path: path.into(),
                                    error: Box::new(e),
                                })?;
                        } else if let Some(additional_schema) = additional_properties {
                            // Property is not defined but additional properties are allowed
                            Self::validate_with_path(
                                prop_value,
                                additional_schema,
                                &make_prop_path(),
                            )
                            .map_err(|e| {
                                ValidationError::PropertyValidationFailed {
                                    property: prop_name_str.clone(),
                                    path: path.into(),
                                    error: Box::new(e),
                                }
                            })?;
                        } else {
                            // Property is not defined and additional properties are not allowed
                            return Err(ValidationError::AdditionalPropertiesNotAllowed {
                                property: prop_name_str.clone(),
                                path: path.into(),
                            });
                        }
                    }
                }

                Ok(())
            }
            _ => Err(ValidationError::TypeMismatch {
                expected: "object".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_any_of(
        value: &Value,
        schemas: &Vec<Schema>,
        path: &str,
    ) -> Result<(), ValidationError> {
        let mut errors = Vec::new();

        for schema in schemas {
            match Self::validate_with_path(value, schema, path) {
                Ok(()) => return Ok(()), // If any schema matches, validation succeeds
                Err(e) => errors.push(e),
            }
        }

        // If no schema matched, return error with all validation attempts
        Err(ValidationError::NoUnionMatch {
            path: path.into(),
            errors,
        })
    }

    fn validate_const(
        value: &Value,
        const_value: &Value,
        path: &str,
    ) -> Result<(), ValidationError> {
        if value == const_value {
            Ok(())
        } else {
            let expected_json =
                serde_json::to_string(const_value).unwrap_or_else(|_| format!("{const_value:?}"));
            let actual_json = serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}"));

            Err(ValidationError::ConstMismatch {
                expected: expected_json.into(),
                actual: actual_json.into(),
                path: path.into(),
            })
        }
    }

    fn validate_enum(
        value: &Value,
        allowed_values: &[Value],
        path: &str,
    ) -> Result<(), ValidationError> {
        if allowed_values.contains(value) {
            Ok(())
        } else {
            // Convert Value to JSON string, fallback to debug format if JSON serialization fails
            let value_json = serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}"));

            let allowed_json: Vec<String> = allowed_values
                .iter()
                .map(|v| {
                    serde_json::to_string(v)
                        .unwrap_or_else(|_| format!("{v:?}"))
                        .into()
                })
                .collect();

            Err(ValidationError::NotInEnum {
                value: value_json.into(),
                allowed_values: allowed_json,
                path: path.into(),
            })
        }
    }

    fn validate_set(
        value: &Value,
        items_schema: &Schema,
        path: &str,
    ) -> Result<(), ValidationError> {
        match value {
            Value::Set(set_value) => {
                // Validate each item in the set
                for (index, item) in set_value.iter().enumerate() {
                    Self::validate_with_path(
                        item,
                        items_schema,
                        &if path.is_empty() {
                            format!("{{{index}}}]")
                        } else {
                            format!("{path}{{{index}}}]")
                        },
                    )?;
                }
                Ok(())
            }
            _ => Err(ValidationError::TypeMismatch {
                expected: "set".into(),
                actual: Self::value_type_name(value),
                path: path.into(),
            }),
        }
    }

    fn validate_discriminated_subobject_with_base(
        object_value: &BTreeMap<Value, Value>,
        discriminated_subobject: &crate::schema::DiscriminatedSubobject,
        base_properties: &BTreeMap<String, Schema>,
        base_additional_properties: Option<&Schema>,
        path: &str,
    ) -> Result<(), ValidationError> {
        let discriminator_field = &discriminated_subobject.discriminator;
        let discriminator_key = Value::String(discriminator_field.clone());

        // Find the discriminator field value in the object
        let discriminator_value = object_value.get(&discriminator_key).ok_or_else(|| {
            ValidationError::MissingDiscriminator {
                discriminator: discriminator_field.clone(),
                path: path.into(),
            }
        })?;

        // Extract the string value from the discriminator field
        let discriminator_str = match discriminator_value {
            Value::String(string_value) => string_value.as_ref(),
            _ => {
                return Err(ValidationError::TypeMismatch {
                    expected: "string".into(),
                    actual: Self::value_type_name(discriminator_value),
                    path: format!("{path}.{discriminator_field}").into(),
                });
            }
        };

        // Find the corresponding variant schema
        let variant_schema = discriminated_subobject
            .variants
            .get(discriminator_str)
            .ok_or_else(|| ValidationError::UnknownDiscriminatorValue {
                discriminator: discriminator_field.clone(),
                value: discriminator_str.into(),
                allowed_values: discriminated_subobject.variants.keys().cloned().collect(),
                path: path.into(),
            })?;

        // Validate all properties against the appropriate schemas
        for (prop_name, prop_value) in object_value.iter() {
            // First, ensure the property key is a string
            let prop_name_str = match prop_name {
                Value::String(string_key) => string_key,
                _ => {
                    return Err(ValidationError::NonStringKey {
                        key_type: Self::value_type_name(prop_name),
                        path: path.into(),
                    });
                }
            };

            // Create property path lazily using a closure
            let make_prop_path = || {
                if path.is_empty() {
                    format!("[{prop_name_str}]")
                } else {
                    format!("{path}.{prop_name_str}")
                }
            };

            // Check if this property is defined in the variant schema first
            if variant_schema.properties.get(prop_name_str).is_some() {
                // Validate later in subobject.
                continue;
            }

            // Check if this property is defined in the base schema properties
            if let Some(prop_schema) = base_properties.get(prop_name_str) {
                // Property is defined in base schema, validate against it
                Self::validate_with_path(prop_value, prop_schema, &make_prop_path()).map_err(
                    |e| ValidationError::PropertyValidationFailed {
                        property: prop_name_str.clone(),
                        path: path.into(),
                        error: Box::new(e),
                    },
                )?;
                continue;
            }

            // Check if additional properties are allowed in the variant
            if variant_schema.additional_properties.is_some() {
                // Property is not defined but additional properties are allowed in variant.
                // Validate later.
                continue;
            } else if let Some(base_additional) = base_additional_properties {
                // Check if additional properties are allowed in the base schema
                Self::validate_with_path(prop_value, base_additional, &make_prop_path()).map_err(
                    |e| ValidationError::PropertyValidationFailed {
                        property: prop_name_str.clone(),
                        path: path.into(),
                        error: Box::new(e),
                    },
                )?;
            } else {
                // Property is not defined and additional properties are not allowed
                return Err(ValidationError::AdditionalPropertiesNotAllowed {
                    property: prop_name_str.clone(),
                    path: path.into(),
                });
            }
        }

        // Validate the object against the variant schema for required properties
        Self::validate_subobject(object_value, variant_schema, path).map_err(|e| {
            ValidationError::DiscriminatedSubobjectValidationFailed {
                discriminator: discriminator_field.clone(),
                value: discriminator_str.into(),
                path: path.into(),
                error: Box::new(e),
            }
        })
    }

    fn validate_subobject(
        object_value: &BTreeMap<Value, Value>,
        subobject: &crate::schema::Subobject,
        path: &str,
    ) -> Result<(), ValidationError> {
        // Check required properties from the subobject
        if let Some(required_props) = &subobject.required {
            for required_prop in required_props.iter() {
                if !object_value.contains_key(&Value::String(required_prop.clone())) {
                    return Err(ValidationError::MissingRequiredProperty {
                        property: required_prop.clone(),
                        path: path.into(),
                    });
                }
            }
        }

        // Validate each property in the subobject
        for (prop_name, prop_schema) in subobject.properties.iter() {
            let prop_key = Value::String(prop_name.clone());
            if let Some(prop_value) = object_value.get(&prop_key) {
                Self::validate_with_path(
                    prop_value,
                    prop_schema,
                    &if path.is_empty() {
                        format!("[{prop_name}]")
                    } else {
                        format!("{path}.{prop_name}")
                    },
                )
                .map_err(|e| ValidationError::PropertyValidationFailed {
                    property: prop_name.clone(),
                    path: path.into(),
                    error: Box::new(e),
                })?;
            }
        }

        // Handle additional properties if specified
        if let Some(additional_schema) = &subobject.additional_properties {
            for (prop_name, prop_value) in object_value.iter() {
                if let Value::String(prop_name_str) = prop_name {
                    if !subobject.properties.contains_key(prop_name_str) {
                        Self::validate_with_path(
                            prop_value,
                            additional_schema,
                            &if path.is_empty() {
                                format!("[{prop_name_str}]")
                            } else {
                                format!("{path}.{prop_name_str}")
                            },
                        )
                        .map_err(|e| {
                            ValidationError::PropertyValidationFailed {
                                property: prop_name_str.clone(),
                                path: path.into(),
                                error: Box::new(e),
                            }
                        })?;
                    }
                }
            }
        }

        Ok(())
    }
    fn value_type_name(value: &Value) -> String {
        match value {
            Value::Null => "null".into(),
            Value::Bool(_) => "boolean".into(),
            Value::Number(_) => "number".into(),
            Value::String(_) => "string".into(),
            Value::Array(_) => "array".into(),
            Value::Set(_) => "set".into(),
            Value::Object(_) => "object".into(),
            Value::Undefined => "undefined".into(),
        }
    }
}

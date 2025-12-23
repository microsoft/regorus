// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

/// There are two type systems of interest:
///     1. JSON Schema used by Azure Policy for some of its metadata.
///     2. Bicep's type system generated from Azure API swagger files.
///        https://github.com/Azure/bicep-types/blob/main/src/Bicep.Types/ConcreteTypes
///
/// JSON Schema is standardized and well documented, with good tooling support.
/// JSON Schema is quite flexible. The following schema:
/// {
///   "allOf": [
///     {
///       "properties": {
///         "name": {"type": "string" }
///       },
///       "required": ["name"]
///     },
///     {
///       "properties": {
///         "age": {"type": "integer" }
///       },
///       "required": ["age"]
///     },
///     {
///       "minLength": 5
///     }
///   ]
/// }
///
/// expresses the constraint that if a value happens to be an object, then it must have a string field `name`,
/// and also an integer field 'age'. If it happens to be a string, it must have a minimum length of 5.
/// There are also different ways to express the same contraint.
///
/// Such flexibility is not needed for our use cases as shown by Bicep's type system which only allows a subset of
/// the constraints expressible in JSON Schema yet represents Azure Resources. Note that Bicep's type system models
/// some JSON schema concepts such as `oneOf` differently.
///
/// For Regorus' type system, we will use a subset of JSON Schema that is needed to support Azure Policy.
/// This subset is initially derived from the Bicep type system, but has a few other JSON Schema concepts like
/// `enum`, `const` that are needed for Azure Policy. Additional JSON Schema features will be supported as needed.
/// This approach is consistent with Azure Policy's use of JSON Schema for metadata.
/// We can also potentially reuse the type schemas  (https://github.com/Azure/bicep-types-az)
/// that the Bicep team generates from Azure API swagger files, using a custom deserializer to convert them to our type system.
///
/// Here is the mapping between Bicep's type system and JSON Schema:
///
/// AnyType
/// Bicep:      { "$type": "AnyType" }
/// JSON Schema: {}
///
/// BooleanType
/// Bicep:      { "$type": "BooleanType" }
/// JSON Schema: { "type": "boolean" }
///
/// NullType
/// Bicep:      { "$type": "NullType" }
/// JSON Schema: { "type": "null" }
///
/// IntegerType
/// Bicep:      { "$type": "IntegerType", "minValue": X, "maxValue": Y }
/// JSON Schema: { "type": "integer", "minimum": X, "maximum": Y }
///
/// NumberType (no Bicep equivalent)
/// Bicep:      No equivalent
/// JSON Schema: { "type": "number", "minimum": X, "maximum": Y }
///
/// StringType
/// Bicep:      {
///               "$type": "StringType",
///               "minLength": X,
///               "maxLength": Y,
//               "pattern": "..."
///             }
/// JSON Schema: {
///               "type": "string",
///               "minLength": X,
///               "maxLength": Y,
///               "pattern": "..."
///             }
///
/// Integer Constant (no Bicep equivalent)
/// Bicep:      No equivalent
/// JSON Schema: { "const": 5 }
///
/// UnionType
/// Bicep:      { "$type": "UnionType", "elements": [...] }
/// JSON Schema: { "enum": [...] } or { "anyOf": [...] }
///
/// Enum with inline values (no Bicep equivalent)
/// Bicep:      No equivalent
/// JSON Schema: { "enum": [8, 10] }
///
/// ObjectType
/// Bicep:      {
///               "$type": "ObjectType",
///               "name": "Test.Rp1/testType1",
///               "properties": {
///                 "id": {
///                   "type": { "$ref": "#/2" },
///                   "flags": 10,
///                   "description": "The resource id"
///                 }
///               },
///               "additionalProperties": { "$ref": "#/3" }
///             }
/// JSON Schema: {
///               "type": "object",
///               "properties": {
///                 "id": {
///                   "type": "integer",
///                   "description": "The resource id"
///                 }
///               },
///               "required": ["id"],
///               "additionalProperties": { "type": "boolean" }
///             }
///
/// DiscriminatedObjectType
/// Bicep:      {
///               "$type": "DiscriminatedObjectType",
///               "name": "Microsoft.Security/settings",
///               "discriminator": "kind",
///               "baseProperties": {
///                 "name": {
///                   "type": { "$ref": "#/5" },
///                   "flags": 9,
///                   "description": "The resource name"
///                 }
///               },
///               "elements": {
///                 "ASubObject": { "$ref": "#/9" },
///                 "BSubObject": { "$ref": "#/13" }
///               }
///             }
/// JSON Schema: {
///               "type": "object",
///               "properties": {
///                 "name": {
///                   "type": "string",
///                   "description": "The resource name"
///                 },
///                 "kind": {
///                   "description": "The kind of the resource",
///                   "enum": ["ASubObject", "BSubObject"]
///                 }
///               },
///               "allOf": [
///                 {
///                   "if": {
///                     "properties": {
///                       "kind": { "const": "ASubObject" }
///                     }
///                   },
///                   "then": {
///                     "properties": {
///                       "apropertyA": {
///                         "type": "string",
///                         "description": "Property A of ASubObject"
///                       }
///                     },
///                     "required": ["apropertyA"]
///                   }
///                 },
///                 {
///                   "if": {
///                     "properties": {
///                       "kind": { "const": "BSubObject" }
///                     }
///                   },
///                   "then": {
///                     "properties": {
///                       "bpropertyB": {
///                         "type": "string",
///                         "description": "Property B of BSubObject"
///                       }
///                     },
///                     "required": ["bpropertyB"]
///                   }
///                 }
///               ]
///             }
///
/// The type system is implemented with the following principles:
///     - Types are immutable and can be shared safely across threads, allowing parallel schema validation using the same type.
///     - Any unsupported JSON Schema feature should raise an error during type creation. Otherwise, the user will not know whether
///       parts of their schema are ignored or not.
///     - Leverage serde as much as possible for serialization and deserialization, avoiding custom serialization logic.
///
/// We use a Rust enum to represent the type system, with each variant representing a different type. In each variant,
/// we list the properties that are relevant to that type, using `Option<T>` for properties that are not required.
/// `deny_unknown_fields` is used to ensure that any unsupported fields in the JSON Schema will raise an error during deserialization.
/// Some properties like `description` are duplicated in each variant, since `deny_unknown_fields` cannot be used with `#[serde(flatten)]`
/// which would have allowed us to refactor the common properties into a single struct to avoid duplication.
use alloc::collections::BTreeMap;
use serde::{Deserialize, Deserializer};

use crate::{format, Box, Rc, Value, Vec};

type String = Rc<str>;

pub mod error;
mod meta;
pub mod validate;

/// A schema represents a type definition that can be used for validation.
///
/// `Schema` is a lightweight wrapper around a [`Type`] that provides reference counting
/// for efficient sharing and cloning. It serves as the primary interface for working
/// with type definitions in the Regorus type system.
///
/// # Usage
///
/// Schemas are typically created by deserializing from JSON Schema format:
///
/// ```rust
/// use serde_json::json;
///
/// // Create a schema from JSON
/// let schema_json = json!({
///     "type": "object",
///     "properties": {
///         "name": { "type": "string" },
///         "age": { "type": "integer", "minimum": 0 }
///     },
///     "required": ["name"]
/// });
///
/// let schema: Schema = serde_json::from_value(schema_json).unwrap();
/// ```
///
/// # Supported Schema Features
///
/// The schema system supports a subset of JSON Schema features needed for Azure Policy
/// and other use cases:
///
/// - **Basic types**: `any`, `null`, `boolean`, `integer`, `number`, `string`
/// - **Complex types**: `array`, `set`, `object`
/// - **Value constraints**: `enum`, `const`
/// - **Composition**: `anyOf` for union types
/// - **String constraints**: `minLength`, `maxLength`, `pattern`
/// - **Numeric constraints**: `minimum`, `maximum`
/// - **Array constraints**: `minItems`, `maxItems`
/// - **Object features**: `properties`, `required`, `additionalProperties`
/// - **Discriminated unions**: via `allOf` with conditional schemas
/// # Thread Safety
///
/// While `Schema` itself is not `Send` or `Sync` due to the use of `Rc`, it can be
/// safely shared within a single thread and cloned efficiently. For multi-threaded
/// scenarios, consider wrapping in `Arc` if needed.
///
/// # Examples
///
/// ## Simple String Schema
/// ```rust
/// let schema = json!({ "type": "string", "minLength": 1 });
/// let parsed: Schema = serde_json::from_value(schema).unwrap();
/// ```
///
/// ## Complex Object Schema
/// ```rust
/// let schema = json!({
///     "type": "object",
///     "properties": {
///         "users": {
///             "type": "array",
///             "items": {
///                 "type": "object",
///                 "properties": {
///                     "id": { "type": "integer" },
///                     "email": { "type": "string", "pattern": "^[^@]+@[^@]+$" }
///                 },
///                 "required": ["id", "email"]
///             }
///         }
///     }
/// });
/// let parsed: Schema = serde_json::from_value(schema).unwrap();
/// ```
///
/// ## Union Types with anyOf
/// ```rust
/// let schema = json!({
///     "anyOf": [
///         { "type": "string" },
///         { "type": "integer", "minimum": 0 }
///     ]
/// });
/// let parsed: Schema = serde_json::from_value(schema).unwrap();
/// ```
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Schema {
    t: Rc<Type>,
}

#[allow(dead_code)]
impl Schema {
    fn new(t: Type) -> Self {
        Schema { t: Rc::new(t) }
    }

    /// Returns a reference to the underlying type definition.
    pub fn as_type(&self) -> &Type {
        &self.t
    }

    /// Parse a JSON Schema document into a `Schema` instance.
    /// Provides better error messages than `serde_json::from_value`.
    pub fn from_serde_json_value(
        schema: serde_json::Value,
    ) -> Result<Self, Box<dyn core::error::Error + Send + Sync>> {
        let meta_schema_validation_result = meta::validate_schema_detailed(&schema);
        let schema = serde_json::from_value::<Schema>(schema)
            .map_err(|e| format!("Failed to parse schema: {e}"))?;
        if let Err(errors) = meta_schema_validation_result {
            return Err(format!("Schema validation failed: {}", errors.join("\n")).into());
        }

        Ok(schema)
    }

    /// Parse a JSON Schema document from a string into a `Schema` instance.
    /// Provides better error messages than `serde_json::from_str`.
    pub fn from_json_str(s: &str) -> Result<Self, Box<dyn core::error::Error + Send + Sync>> {
        let value: serde_json::Value =
            serde_json::from_str(s).map_err(|e| format!("Failed to parse schema: {e}"))?;
        Self::from_serde_json_value(value)
    }

    /// Validates a `Value` against this schema.
    ///
    /// Returns `Ok(())` if the value conforms to the schema, or a `ValidationError`
    /// with detailed error information if validation fails.
    ///
    /// # Example
    /// ```rust
    /// use regorus::schema::Schema;
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
    /// assert!(schema.validate(&value).is_ok());
    /// ```
    pub fn validate(&self, value: &Value) -> Result<(), error::ValidationError> {
        validate::SchemaValidator::validate(value, self)
    }
}

impl<'de> Deserialize<'de> for Schema {
    /// Deserializes a JSON Schema into a `Schema` instance.
    ///
    /// This method handles the deserialization of JSON Schema documents into Regorus'
    /// internal type system. It supports two main formats:
    ///
    /// 1. **Regular typed schemas** - Standard JSON Schema with a `type` field
    /// 2. **Union schemas** - Schemas using `anyOf` to represent union types
    ///
    /// # Supported JSON Schema Formats
    ///
    /// ## Regular Type Schemas
    ///
    /// Standard JSON Schema documents with a `type` field are deserialized directly:
    ///
    /// ```json
    /// {
    ///   "type": "string",
    ///   "minLength": 1,
    ///   "maxLength": 100
    /// }
    /// ```
    ///
    /// ```json
    /// {
    ///   "type": "object",
    ///   "properties": {
    ///     "name": { "type": "string" },
    ///     "age": { "type": "integer", "minimum": 0 }
    ///   },
    ///   "required": ["name"]
    /// }
    /// ```
    ///
    /// ## Union Type Schemas with anyOf
    ///
    /// Schemas using `anyOf` are converted to `Type::AnyOf` variants:
    ///
    /// ```json
    /// {
    ///   "anyOf": [
    ///     { "type": "string" },
    ///     { "type": "integer", "minimum": 0 },
    ///     { "type": "null" }
    ///   ]
    /// }
    /// ```
    ///
    /// # Error Handling
    ///
    /// This method will return a deserialization error if:
    ///
    /// - The JSON contains unknown/unsupported fields (due to `deny_unknown_fields`)
    /// - The JSON structure doesn't match any supported schema format
    /// - Individual type definitions within the schema are invalid
    /// - Required fields are missing (e.g., `type` field for regular schemas)
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let v: serde_json::Value = Deserialize::deserialize(deserializer)?;
        if v.get("anyOf").is_some() {
            #[derive(Deserialize)]
            #[serde(deny_unknown_fields)]
            #[serde(rename_all = "camelCase")]
            struct AnyOf {
                #[serde(rename = "anyOf")]
                variants: Rc<Vec<Schema>>,
            }
            let any_of: AnyOf = Deserialize::deserialize(v)
                .map_err(|e| serde::de::Error::custom(format!("{e}")))?;
            return Ok(Schema::new(Type::AnyOf(any_of.variants)));
        }

        if v.get("const").is_some() {
            #[derive(Deserialize)]
            #[serde(deny_unknown_fields)]
            #[serde(rename_all = "camelCase")]
            struct Const {
                #[serde(rename = "const")]
                value: Value,
                description: Option<String>,
            }
            let const_schema: Const = Deserialize::deserialize(v)
                .map_err(|e| serde::de::Error::custom(format!("{e}")))?;
            return Ok(Schema::new(Type::Const {
                description: const_schema.description,
                value: const_schema.value,
            }));
        }
        if v.get("enum").is_some() {
            #[derive(Deserialize)]
            #[serde(deny_unknown_fields)]
            #[serde(rename_all = "camelCase")]
            struct Enum {
                #[serde(rename = "enum")]
                values: Rc<Vec<Value>>,
                description: Option<String>,
            }
            let enum_schema: Enum = Deserialize::deserialize(v)
                .map_err(|e| serde::de::Error::custom(format!("{e}")))?;
            return Ok(Schema::new(Type::Enum {
                description: enum_schema.description,
                values: enum_schema.values,
            }));
        }

        let t: Type =
            Deserialize::deserialize(v).map_err(|e| serde::de::Error::custom(format!("{e}")))?;
        Ok(Schema::new(t))
    }
}

#[derive(Debug, Clone, Deserialize)]
// Use `type` when deserializing to discriminate between different types.
#[serde(tag = "type")]
// match JSON Schema casing.
#[serde(rename_all = "camelCase")]
// Raise error if unsupported fields are encountered.
#[serde(deny_unknown_fields)]
#[allow(dead_code)]
pub enum Type {
    /// Represents a type that can accept any JSON value.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "any",
    ///   "description": "Accepts any JSON value",
    ///   "default": "fallback_value"
    /// }
    /// ```
    Any {
        description: Option<String>,
        default: Option<Value>,
    },

    /// Represents a 64-bit signed integer type with optional range constraints.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "integer",
    ///   "description": "A whole number",
    ///   "minimum": 0,
    ///   "maximum": 100,
    ///   "default": 50
    /// }
    /// ```
    Integer {
        description: Option<String>,
        // In Bicep's type system, this is called minValue.
        minimum: Option<i64>,
        // In Bicep's type system, this is called maxValue.
        maximum: Option<i64>,
        default: Option<Value>,
    },

    /// Represents a 64-bit floating-point number type with optional range constraints.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "number",
    ///   "description": "A numeric value",
    ///   "minimum": 0.0,
    ///   "maximum": 1.0,
    ///   "default": 0.5
    /// }
    /// ```
    Number {
        description: Option<String>,
        minimum: Option<f64>,
        maximum: Option<f64>,
        default: Option<Value>,
    },

    /// Represents a boolean type that accepts `true` or `false` values.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "boolean",
    ///   "description": "A true/false value",
    ///   "default": false
    /// }
    /// ```
    Boolean {
        description: Option<String>,
        default: Option<Value>,
    },

    /// Represents the null type that only accepts JSON `null` values.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "null",
    ///   "description": "A null value"
    /// }
    /// ```
    Null { description: Option<String> },

    /// Represents a string type with optional length and pattern constraints.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "string",
    ///   "description": "Email address",
    ///   "minLength": 1,
    ///   "maxLength": 100,
    ///   "pattern": "^[^@]+@[^@]+\\.[^@]+$",
    /// }
    /// ```
    #[serde(rename_all = "camelCase")]
    String {
        description: Option<String>,
        min_length: Option<usize>,
        max_length: Option<usize>,
        pattern: Option<String>,
        default: Option<Value>,
    },

    /// Represents an array type with a specified item type and optional size constraints.
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "array",
    ///   "description": "A list of items",
    ///   "items": { "type": "string" },
    ///   "minItems": 1,
    ///   "maxItems": 10,
    ///   "default": ["item1", "item2"]
    /// }
    /// ```
    #[serde(rename_all = "camelCase")]
    Array {
        description: Option<String>,
        items: Schema,
        // In Bicep's type system, this is called minLength.
        min_items: Option<usize>,
        // In Bicep's type system, this is called maxLength.
        max_items: Option<usize>,
        default: Option<Value>,
    },

    /// Represents an object type with defined properties and optional constraints.
    ///
    /// The `Object` type accepts JSON objects with specified properties, required fields,
    /// and optional additional properties schema. It can also support discriminated
    /// unions through the `allOf` mechanism.
    ///
    /// # Examples
    ///
    /// ## Basic Object
    /// ```json
    /// {
    ///   "type": "object",
    ///   "properties": {
    ///     "name": { "type": "string" },
    ///     "age": { "type": "integer" }
    ///   },
    ///   "required": ["name"]
    /// }
    /// ```
    ///
    /// ## Object with Additional Properties
    /// ```json
    /// {
    ///   "type": "object",
    ///   "properties": {
    ///     "core_field": { "type": "string" }
    ///   },
    ///   "additionalProperties": { "type": "any" },
    ///   "description": "Extensible configuration object"
    /// }
    /// ```
    ///
    /// ## Discriminated Subobjects (Polymorphic Types)
    ///
    /// Discriminated subobjects allow modeling polymorphic types where the structure
    /// depends on a discriminator field value. This is useful for representing different
    /// types of resources, messages, or configurations that share common base properties
    /// but have type-specific additional properties.
    ///
    /// ```json
    /// {
    ///   "type": "object",
    ///   "description": "Azure resource definition",
    ///   "properties": {
    ///     "name": {
    ///       "type": "string",
    ///       "description": "Resource name"
    ///     },
    ///     "location": {
    ///       "type": "string",
    ///       "description": "Azure region"
    ///     },
    ///     "type": {
    ///       "type": "string",
    ///       "description": "Resource type discriminator"
    ///     }
    ///   },
    ///   "required": ["name", "location", "type"],
    ///   "allOf": [
    ///     {
    ///       "if": {
    ///         "properties": {
    ///           "type": { "const": "Microsoft.Compute/virtualMachines" }
    ///         }
    ///       },
    ///       "then": {
    ///         "properties": {
    ///           "vmSize": {
    ///             "type": "string",
    ///             "description": "Virtual machine size"
    ///           },
    ///           "osType": {
    ///             "type": "enum",
    ///             "values": ["Windows", "Linux"]
    ///           },
    ///           "imageReference": {
    ///             "type": "object",
    ///             "properties": {
    ///               "publisher": { "type": "string" },
    ///               "offer": { "type": "string" },
    ///               "sku": { "type": "string" }
    ///             },
    ///             "required": ["publisher", "offer", "sku"]
    ///           }
    ///         },
    ///         "required": ["vmSize", "osType", "imageReference"]
    ///       }
    ///     },
    ///     {
    ///       "if": {
    ///         "properties": {
    ///           "type": { "const": "Microsoft.Storage/storageAccounts" }
    ///         }
    ///       },
    ///       "then": {
    ///         "properties": {
    ///           "accountType": {
    ///             "type": "enum",
    ///             "values": ["Standard_LRS", "Standard_GRS", "Premium_LRS"]
    ///           },
    ///           "encryption": {
    ///             "type": "object",
    ///             "properties": {
    ///               "services": {
    ///                 "type": "object",
    ///                 "properties": {
    ///                   "blob": { "type": "boolean" },
    ///                   "file": { "type": "boolean" }
    ///                 }
    ///               }
    ///             }
    ///           }
    ///         },
    ///         "required": ["accountType"]
    ///       }
    ///     },
    ///     {
    ///       "if": {
    ///         "properties": {
    ///           "type": { "const": "Microsoft.Network/virtualNetworks" }
    ///         }
    ///       },
    ///       "then": {
    ///         "properties": {
    ///           "addressSpace": {
    ///             "type": "object",
    ///             "properties": {
    ///               "addressPrefixes": {
    ///                 "type": "array",
    ///                 "items": { "type": "string" },
    ///                 "minItems": 1
    ///               }
    ///             },
    ///             "required": ["addressPrefixes"]
    ///           },
    ///           "subnets": {
    ///             "type": "array",
    ///             "items": {
    ///               "type": "object",
    ///               "properties": {
    ///                 "name": { "type": "string" },
    ///                 "addressPrefix": { "type": "string" }
    ///               },
    ///               "required": ["name", "addressPrefix"]
    ///             }
    ///           }
    ///         },
    ///         "required": ["addressSpace"]
    ///       }
    ///     }
    ///   ]
    /// }
    /// ```
    ///
    /// ## Discriminated Subobject Structure
    ///
    /// When using discriminated subobjects:
    ///
    /// 1. **Base Properties**: Common properties shared by all variants (defined in the main `properties`)
    /// 2. **Discriminator Field**: A property that determines which variant applies (e.g., `"kind"` field)
    /// 3. **Variant-Specific Properties**: Additional properties that only apply to specific discriminator values
    /// 4. **Conditional Schema**: Each `allOf` entry uses `if`/`then` to conditionally apply variant-specific schemas
    ///
    /// ## Message Type Example
    ///
    /// ```json
    /// {
    ///   "type": "object",
    ///   "description": "Polymorphic message types",
    ///   "properties": {
    ///     "id": { "type": "string" },
    ///     "timestamp": { "type": "integer" },
    ///     "messageType": { "type": "string" }
    ///   },
    ///   "required": ["id", "timestamp", "messageType"],
    ///   "allOf": [
    ///     {
    ///       "if": {
    ///         "properties": {
    ///           "messageType": { "const": "text" }
    ///         }
    ///       },
    ///       "then": {
    ///         "properties": {
    ///           "content": { "type": "string", "minLength": 1 },
    ///           "formatting": {
    ///             "type": "enum",
    ///             "values": ["plain", "markdown", "html"]
    ///           }
    ///         },
    ///         "required": ["content"]
    ///       }
    ///     },
    ///     {
    ///       "if": {
    ///         "properties": {
    ///           "messageType": { "const": "image" }
    ///         }
    ///       },
    ///       "then": {
    ///         "properties": {
    ///           "imageUrl": { "type": "string" },
    ///           "altText": { "type": "string" },
    ///           "width": { "type": "integer", "minimum": 1 },
    ///           "height": { "type": "integer", "minimum": 1 }
    ///         },
    ///         "required": ["imageUrl"]
    ///       }
    ///     },
    ///     {
    ///       "if": {
    ///         "properties": {
    ///           "messageType": { "const": "file" }
    ///         }
    ///       },
    ///       "then": {
    ///         "properties": {
    ///           "filename": { "type": "string" },
    ///           "fileSize": { "type": "integer", "minimum": 0 },
    ///           "mimeType": { "type": "string" },
    ///           "downloadUrl": { "type": "string" }
    ///         },
    ///         "required": ["filename", "fileSize", "downloadUrl"]
    ///       }
    ///     }
    ///   ]
    /// }
    /// ```
    ///
    /// This structure ensures that:
    /// - All messages have `id`, `timestamp`, and `messageType` fields
    /// - Text messages additionally require `content` and may have `formatting`
    /// - Image messages require `imageUrl` and may specify dimensions
    #[serde(rename_all = "camelCase")]
    Object {
        description: Option<String>,
        #[serde(default)]
        properties: Rc<BTreeMap<String, Schema>>,
        #[serde(default)]
        required: Option<Rc<Vec<String>>>,
        #[serde(default = "additional_properties_default")]
        #[serde(deserialize_with = "additional_properties_deserialize")]
        additional_properties: Option<Schema>,

        // This is a required property in Bicep's type system. There is not direct equivalent in JSON Schema.
        // However, JSON Schema simply allows any schema to have a `name` property.
        name: Option<String>,

        default: Option<Value>,

        #[serde(rename = "allOf")]
        discriminated_subobject: Option<Rc<DiscriminatedSubobject>>,
        // Bicep property attributes like `readOnly`, `writeOnly` are not needed in Regorus' type system.
    },

    /// Represents a union type that accepts values matching any of the specified schemas.
    ///
    /// The `AnyOf` type creates a union where a value is valid if it matches at least
    /// one of the provided schemas. This is useful for optional types, alternative
    /// formats, or polymorphic data structures.
    ///
    /// # JSON Schema Format
    ///
    /// ```json
    /// {
    ///   "anyOf": [
    ///     { "type": "string" },
    ///     { "type": "integer", "minimum": 0 },
    ///     { "type": "null" }
    ///   ]
    /// }
    /// ```
    ///
    /// AnyOf deserialization is handled by the `Schema` deserializer.
    /// This is because, unlike other variant which can be distingished by the `type` field,
    /// `anyOf` does not have a `type` field. Instead, it is a top-level field that contains an array of schemas.
    #[serde(skip)]
    AnyOf(Rc<Vec<Schema>>),

    /// Represents a constant type that accepts only a single specific value.
    ///
    /// The `Const` type accepts only the exact value specified. This is useful for
    /// literal values, discriminator fields, or when only one specific value is valid.
    ///
    /// # Example
    ///
    /// ```json
    /// {
    ///   "type": "const",
    ///   "description": "A single constant value",
    ///   "value": "specific_value"
    /// }
    /// ```
    #[serde(skip)]
    Const {
        description: Option<String>,
        value: Value,
    },

    /// Represents an enumeration type with a fixed set of allowed values.
    ///
    /// The `Enum` type accepts only values that are explicitly listed in the values array.
    /// Values can be of any JSON type (strings, numbers, booleans, objects, arrays, null).
    ///
    /// # Example
    /// ```json
    /// {
    ///   "type": "enum",
    ///   "description": "A predefined set of values",
    ///   "values": ["value1", "value2", 42, true, null]
    /// }
    /// ```
    #[serde(skip)]
    Enum {
        description: Option<String>,
        values: Rc<Vec<Value>>,
    },

    /// Specific to Rego. Needed for representing type of expressions involving sets.
    #[serde(skip)]
    Set {
        description: Option<String>,
        items: Schema,
        default: Option<Value>,
    },
}

// By default any additional properties are allowed.
fn additional_properties_default() -> Option<Schema> {
    // Default is to allow additional properties of any type.
    Some(Schema::new(Type::Any {
        description: None,
        default: None,
    }))
}

fn additional_properties_deserialize<'de, D>(deserializer: D) -> Result<Option<Schema>, D::Error>
where
    D: Deserializer<'de>,
{
    let value = serde_json::Value::deserialize(deserializer)?;
    if let Some(b) = value.as_bool() {
        if b {
            // If additionalProperties is true, it means any type is allowed.
            return Ok(Some(Schema::new(Type::Any {
                description: None,
                default: None,
            })));
        } else {
            // If additionalProperties is false, no additional properties are allowed.
            return Ok(None);
        }
    }

    let schema: Schema = Deserialize::deserialize(value.clone())
        .map_err(|e| serde::de::Error::custom(format!("{e}")))?;
    Ok(Some(schema))
}

// A subobject is just like an object, but it cannot have a `discriminated_subobject` property.
#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct Subobject {
    pub description: Option<String>,
    pub properties: Rc<BTreeMap<String, Schema>>,
    pub required: Option<Rc<Vec<String>>>,
    #[serde(default = "additional_properties_default")]
    #[serde(deserialize_with = "additional_properties_deserialize")]
    pub additional_properties: Option<Schema>,
    // This is a required property in Bicep's type system. There is not direct equivalent in JSON Schema.
    // However, JSON Schema simply allows any schema to have a `name` property.
    pub name: Option<String>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct DiscriminatedSubobject {
    pub discriminator: String,
    pub variants: Rc<BTreeMap<String, Subobject>>,
}

mod discriminated_subobject {
    use super::*;

    #[derive(Debug, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct DiscriminatorValue {
        #[serde(rename = "const")]
        pub value: String,
    }

    #[derive(Debug, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct DiscriminatorValueSpecification {
        pub properties: BTreeMap<String, DiscriminatorValue>,
    }

    #[derive(Debug, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct IfThen {
        #[serde(rename = "if")]
        pub discriminator_spec: DiscriminatorValueSpecification,
        #[serde(rename = "then")]
        pub subobject: Subobject,
    }
}

impl<'de> Deserialize<'de> for DiscriminatedSubobject {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let ifthens: Vec<discriminated_subobject::IfThen> = Deserialize::deserialize(deserializer)?;
        if ifthens.is_empty() {
            return Err(serde::de::Error::custom(
                "DiscriminatedSubobject must have at least one variant",
            ));
        }
        let mut discriminator = None;
        let mut variants = BTreeMap::new();
        for variant in ifthens.into_iter() {
            if variant.discriminator_spec.properties.len() != 1 {
                return Err(serde::de::Error::custom(
                    "DiscriminatedSubobject discriminator must have exactly one property",
                ));
            }
            if let Some((d, v)) = variant.discriminator_spec.properties.into_iter().next() {
                if let Some(discriminator) = &discriminator {
                    if d != *discriminator {
                        return Err(serde::de::Error::custom(
                            "DiscriminatedSubobject must have a single discriminator property",
                        ));
                    }
                } else {
                    discriminator = Some(d.clone());
                }
                variants.insert(v.value, variant.subobject);
            } else {
                return Err(serde::de::Error::custom(
                    "DiscriminatedSubobject discriminator must have exactly one property",
                ));
            }
        }

        Ok(DiscriminatedSubobject {
            discriminator: discriminator.ok_or_else(|| {
                serde::de::Error::custom(
                    "DiscriminatedSubobject must have a discriminator property",
                )
            })?,
            variants: Rc::new(variants),
        })
    }
}

#[cfg(test)]
mod tests {
    mod azure;
    mod suite;
    mod validate {
        mod effect;
        mod resource;
    }
}

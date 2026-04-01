// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Span-annotated AST types for Azure Policy rule conditions.
//!
//! AST nodes carry [`Span`] information pointing back into the original JSON
//! source, enabling precise error messages during compilation and validation.
//!
//! The type hierarchy mirrors the Azure Policy JSON structure:
//! - [`PolicyDefinition`] — full policy definition wrapper
//! - [`PolicyRule`] — top-level `{ "if": constraint, "then": { "effect": ... } }`
//! - [`Constraint`] — logical combinators (`allOf`, `anyOf`, `not`) or leaf [`Condition`]
//! - [`Condition`] — `{ lhs, operator, rhs }` triple
//! - [`FieldNode`] / [`FieldKind`] — field reference classification
//! - [`Expr`] — ARM template expression (`"[concat(...)]"`)
//! - [`CountNode`] — `count` with optional `where` clause

mod value;

pub use value::*;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

pub use crate::lexer::Span;

// ============================================================================
// Top-level
// ============================================================================

/// A parsed Azure Policy rule.
///
/// Represents the `policyRule` object:
/// ```json
/// {
///   "if": { /* constraint */ },
///   "then": { "effect": "deny" }
/// }
/// ```
#[derive(Clone, Debug)]
pub struct PolicyRule {
    /// Span covering the entire `policyRule` JSON object.
    pub span: Span,
    /// The `"if"` condition.
    pub condition: Constraint,
    /// The `"then"` block containing the effect.
    pub then_block: ThenBlock,
}

/// The `"then"` block of a policy rule.
#[derive(Clone, Debug)]
pub struct ThenBlock {
    /// Span covering the `"then"` JSON object.
    pub span: Span,
    /// The effect (e.g., "deny", "audit", "modify").
    pub effect: EffectNode,
    /// Optional details block (for modify/append/deployIfNotExists effects).
    pub details: Option<JsonValue>,
    /// Parsed `existenceCondition` from `details` (for auditIfNotExists /
    /// deployIfNotExists). This is extracted from the `details` JSON and
    /// parsed as a `Constraint` (same grammar as `policyRule.if`).
    pub existence_condition: Option<Constraint>,
}

/// The `"effect"` value in the then block.
#[derive(Clone, Debug)]
pub struct EffectNode {
    /// Span of the effect value string.
    pub span: Span,
    /// The effect kind.
    pub kind: EffectKind,
    /// The original effect text as written (preserves casing).
    pub raw: String,
}

/// Known Azure Policy effect types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectKind {
    Deny,
    Audit,
    Append,
    AuditIfNotExists,
    DeployIfNotExists,
    Disabled,
    Modify,
    DenyAction,
    Manual,
    /// An effect value that wasn't recognized (may be a parameterized expression).
    /// Use [`EffectNode::raw`] to get the original text.
    Other,
}

// ============================================================================
// Constraints
// ============================================================================

/// A logical or leaf constraint node.
///
/// Maps directly to the Azure Policy JSON structure:
/// - `{ "allOf": [...] }` → `AllOf`
/// - `{ "anyOf": [...] }` → `AnyOf`
/// - `{ "not": {...} }` → `Not`
/// - `{ "field": "...", "equals": "..." }` → `Condition`
#[derive(Clone, Debug)]
pub enum Constraint {
    AllOf {
        /// Span covering the entire JSON object `{ "allOf": [...] }`.
        span: Span,
        /// The child constraints.
        constraints: Vec<Constraint>,
    },
    AnyOf {
        /// Span covering the entire JSON object `{ "anyOf": [...] }`.
        span: Span,
        /// The child constraints.
        constraints: Vec<Constraint>,
    },
    Not {
        /// Span covering the entire JSON object `{ "not": {...} }`.
        span: Span,
        /// The negated constraint.
        constraint: Box<Constraint>,
    },
    /// A leaf condition (field/value/count + operator + rhs).
    Condition(Box<Condition>),
}

// ============================================================================
// Conditions
// ============================================================================

/// A leaf condition: `{ lhs, operator, rhs }`.
///
/// Example: `{ "field": "type", "equals": "Microsoft.Compute/virtualMachines" }`
#[derive(Clone, Debug)]
pub struct Condition {
    /// Span covering the entire condition JSON object.
    pub span: Span,
    /// The left-hand operand (field, value, or count).
    pub lhs: Lhs,
    /// The operator (equals, contains, etc.) with its span.
    pub operator: OperatorNode,
    /// The right-hand value or expression.
    pub rhs: ValueOrExpr,
}

/// The left-hand side of a condition.
#[derive(Clone, Debug)]
pub enum Lhs {
    /// `"field": "..."` — a resource field reference.
    Field(FieldNode),
    /// `"value": ...` — a literal value or expression.
    Value {
        /// Span of the `"value"` key.
        key_span: Span,
        /// The value or expression.
        value: ValueOrExpr,
    },
    /// `"count": { ... }` — a count expression.
    Count(CountNode),
}

// ============================================================================
// Fields
// ============================================================================

/// A field reference with its source span.
#[derive(Clone, Debug)]
pub struct FieldNode {
    /// Span of the field string value in the JSON.
    pub span: Span,
    /// The classified field kind.
    pub kind: FieldKind,
}

/// Classification of a `"field"` string value.
///
/// Built-in fields are mapped to specific variants; everything else is either
/// an alias or an ARM template expression.
#[derive(Clone, Debug)]
pub enum FieldKind {
    /// `"type"`
    Type,
    /// `"id"`
    Id,
    /// `"kind"`
    Kind,
    /// `"name"`
    Name,
    /// `"location"`
    Location,
    /// `"fullName"`
    FullName,
    /// `"tags"` (the entire tags object)
    Tags,
    /// `"identity.type"`
    IdentityType,
    /// `"identity.<subpath>"` — any identity sub-field other than `type`
    /// (e.g., `"identity.userAssignedIdentities"`, `"identity.principalId"`).
    IdentityField(String),
    /// `"apiVersion"`
    ApiVersion,
    /// `"tags.tagName"` or `"tags['tagName']"`
    Tag(String),
    /// An alias string (e.g., `"Microsoft.Compute/virtualMachines/imagePublisher"`)
    Alias(String),
    /// An ARM template expression (e.g., `"[concat('Microsoft.Network/', ...)]"`)
    Expr(Expr),
}

// ============================================================================
// Operators
// ============================================================================

/// An operator node with span information.
#[derive(Clone, Debug)]
pub struct OperatorNode {
    /// Span of the operator key string in the JSON (e.g., the `"equals"` key).
    pub span: Span,
    /// The operator kind.
    pub kind: OperatorKind,
}

/// The 19 Azure Policy condition operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatorKind {
    Contains,
    ContainsKey,
    Equals,
    Greater,
    GreaterOrEquals,
    Exists,
    In,
    Less,
    LessOrEquals,
    Like,
    Match,
    MatchInsensitively,
    NotContains,
    NotContainsKey,
    NotEquals,
    NotIn,
    NotLike,
    NotMatch,
    NotMatchInsensitively,
}

// ============================================================================
// Policy Definition (full envelope)
// ============================================================================

/// A fully parsed Azure Policy definition.
///
/// Wraps the `properties` section of a policy definition JSON:
/// ```json
/// {
///   "properties": {
///     "displayName": "...",
///     "description": "...",
///     "mode": "All",
///     "parameters": { ... },
///     "policyRule": { "if": ..., "then": ... }
///   }
/// }
/// ```
///
/// Fields that we don't parse into typed members are stored in `extra`.
#[derive(Clone, Debug)]
pub struct PolicyDefinition {
    /// Span covering the entire definition JSON object.
    pub span: Span,

    /// Optional `displayName`.
    pub display_name: Option<String>,

    /// Optional `description`.
    pub description: Option<String>,

    /// Optional `mode` (e.g., `"All"`, `"Indexed"`, `"Microsoft.KeyVault.Data"`).
    pub mode: Option<String>,

    /// Optional `metadata` (kept as raw JSON).
    pub metadata: Option<JsonValue>,

    /// Parameter definitions as an ordered list; lookups should match `ParameterDefinition::name`.
    pub parameters: Vec<ParameterDefinition>,

    /// The parsed `policyRule`.
    pub policy_rule: PolicyRule,

    /// Any other top-level fields not handled above (e.g., `id`, `name`, `type`, `policyType`).
    pub extra: Vec<ObjectEntry>,
}

/// A single parameter definition within `properties.parameters`.
///
/// ```json
/// "paramName": {
///   "type": "String",
///   "defaultValue": "...",
///   "allowedValues": [...],
///   "metadata": { "displayName": "...", "description": "..." }
/// }
/// ```
#[derive(Clone, Debug)]
pub struct ParameterDefinition {
    /// Span covering this parameter's JSON object.
    pub span: Span,

    /// The parameter name (the key in the `parameters` object).
    pub name: String,

    /// Span of the parameter name key.
    pub name_span: Span,

    /// The `type` field (e.g., `"String"`, `"Integer"`, `"Boolean"`, `"Array"`, `"Object"`).
    pub param_type: Option<String>,

    /// Optional default value.
    pub default_value: Option<JsonValue>,

    /// Optional list of allowed values.
    pub allowed_values: Option<Vec<JsonValue>>,

    /// Optional metadata (kept as raw JSON).
    pub metadata: Option<JsonValue>,

    /// Any extra fields not handled above.
    pub extra: Vec<ObjectEntry>,
}

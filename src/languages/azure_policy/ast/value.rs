// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! JSON value types, ARM template expressions, and count nodes.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

use crate::lexer::Span;

use super::{Constraint, FieldNode};

// ============================================================================
// Values and Expressions
// ============================================================================

/// A value that may be a literal JSON value or an ARM template expression.
///
/// Strings of the form `"[expr]"` are parsed as expressions; everything else
/// remains a plain JSON value.
#[derive(Clone, Debug)]
pub enum ValueOrExpr {
    /// A plain JSON value.
    Value(JsonValue),
    /// An ARM template expression parsed from a `"[...]"` string.
    Expr {
        /// Span of the entire string (including the `[` and `]`).
        span: Span,
        /// The raw string content (between the quotes, including `[` and `]`).
        raw: String,
        /// The parsed expression AST.
        expr: Expr,
    },
}

/// A JSON value with span information.
///
/// This is our own representation (not `serde_json::Value`) because we need
/// exact source spans for every token.
#[derive(Clone, Debug)]
pub enum JsonValue {
    /// JSON `null`.
    Null(Span),
    /// JSON boolean.
    Bool(Span, bool),
    /// JSON number (stored as raw string for lossless round-trip).
    Number(Span, String),
    /// JSON string.
    Str(Span, String),
    /// JSON array.
    Array(Span, Vec<JsonValue>),
    /// JSON object.
    Object(Span, Vec<ObjectEntry>),
}

/// A key-value entry in a JSON object.
#[derive(Clone, Debug)]
pub struct ObjectEntry {
    /// Span of the key string.
    pub key_span: Span,
    /// The key text.
    pub key: String,
    /// The value.
    pub value: JsonValue,
}

impl JsonValue {
    /// Returns the span of this JSON value.
    pub const fn span(&self) -> &Span {
        match *self {
            Self::Null(ref s)
            | Self::Bool(ref s, _)
            | Self::Number(ref s, _)
            | Self::Str(ref s, _)
            | Self::Array(ref s, _)
            | Self::Object(ref s, _) => s,
        }
    }
}

// ============================================================================
// ARM Template Expressions
// ============================================================================

/// An ARM template expression AST node.
///
/// Represents expressions inside `"[...]"` strings, following the grammar:
/// ```text
/// expr ::= IDENT
///        | NUMBER
///        | STRING
///        | BOOL
///        | expr '.' IDENT
///        | expr '(' args ')'
///        | expr '[' expr ']'
/// ```
#[derive(Clone, Debug)]
pub enum Expr {
    /// A literal value (number, string, or bool).
    Literal { span: Span, value: ExprLiteral },
    /// An identifier (e.g., function name or parameter reference).
    Ident { span: Span, name: String },
    /// A function call: `func(arg1, arg2, ...)`.
    Call {
        span: Span,
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    /// A dot access: `expr.field`.
    Dot {
        span: Span,
        object: Box<Expr>,
        field_span: Span,
        field: String,
    },
    /// An index access: `expr[index]`.
    Index {
        span: Span,
        object: Box<Expr>,
        index: Box<Expr>,
    },
}

impl Expr {
    /// Returns a reference to this expression's span.
    pub const fn span(&self) -> &Span {
        match *self {
            Self::Literal { ref span, .. }
            | Self::Ident { ref span, .. }
            | Self::Call { ref span, .. }
            | Self::Dot { ref span, .. }
            | Self::Index { ref span, .. } => span,
        }
    }
}

/// A literal value inside an ARM template expression.
#[derive(Clone, Debug, PartialEq)]
pub enum ExprLiteral {
    /// Numeric value (raw string).
    Number(String),
    /// String value.
    String(String),
    /// Boolean value (from string `"true"`/`"false"` in expression context).
    Bool(bool),
}

// ============================================================================
// Count
// ============================================================================

/// A `"count"` expression node.
///
/// Two forms:
/// - **Field count**: `{ "count": { "field": "alias[*]", "where": {...} } }`
/// - **Value count**: `{ "count": { "value": [...], "name": "x", "where": {...} } }`
#[derive(Clone, Debug)]
pub enum CountNode {
    /// Count over an alias array field.
    Field {
        /// Span covering the `"count"` value object.
        span: Span,
        /// The field being counted (must be an alias or template expression).
        field: FieldNode,
        /// Optional filter constraint.
        where_: Option<Box<Constraint>>,
    },
    /// Count over an inline value.
    Value {
        /// Span covering the `"count"` value object.
        span: Span,
        /// The JSON value or expression being counted (typically an array).
        value: ValueOrExpr,
        /// Optional iteration variable name.
        name: Option<NameNode>,
        /// Optional filter constraint.
        where_: Option<Box<Constraint>>,
    },
}

/// A `"name"` entry in a count-value block.
#[derive(Clone, Debug)]
pub struct NameNode {
    /// Span of the name string value.
    pub span: Span,
    /// The name text.
    pub name: String,
}

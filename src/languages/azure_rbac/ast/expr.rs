#![allow(clippy::missing_const_for_fn)]
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};

use super::literals::{
    BooleanLiteral, DateTimeLiteral, NullLiteral, NumberLiteral, StringLiteral, TimeLiteral,
};
use super::operators::{ArrayOperator, ConditionOperator};
use super::references::AttributeReference;
use super::span::EmptySpan;

/// ABAC condition expression
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConditionExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub raw_expression: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expression: Option<ConditionExpr>,
}

impl ConditionExpression {
    pub fn new(span: EmptySpan, expression: String) -> Self {
        Self {
            span,
            raw_expression: expression,
            expression: None,
        }
    }

    pub fn with_parsed(span: EmptySpan, raw_expression: String, parsed: ConditionExpr) -> Self {
        Self {
            span,
            raw_expression,
            expression: Some(parsed),
        }
    }
}

/// Condition expression node
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ConditionExpr {
    Logical(LogicalExpression),
    Unary(UnaryExpression),
    Binary(BinaryExpression),
    FunctionCall(FunctionCallExpression),
    AttributeReference(AttributeReference),
    ArrayExpression(ArrayExpression),
    Identifier(IdentifierExpression),
    VariableReference(VariableReference),
    PropertyAccess(PropertyAccessExpression),
    StringLiteral(StringLiteral),
    NumberLiteral(NumberLiteral),
    BooleanLiteral(BooleanLiteral),
    NullLiteral(NullLiteral),
    DateTimeLiteral(DateTimeLiteral),
    TimeLiteral(TimeLiteral),
    SetLiteral(SetLiteral),
    ListLiteral(ListLiteral),
}

/// Logical (AND/OR) expression
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LogicalExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub operator: LogicalOperator,
    pub left: Box<ConditionExpr>,
    pub right: Box<ConditionExpr>,
}

/// Logical operator kinds
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum LogicalOperator {
    And,
    Or,
}

/// Unary expression (e.g., NOT)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct UnaryExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub operator: UnaryOperator,
    pub operand: Box<ConditionExpr>,
}

/// Unary operator kinds
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnaryOperator {
    Not,
    Exists,
    NotExists,
}

/// Binary expression with an operator and two operands
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub operator: ConditionOperator,
    pub left: Box<ConditionExpr>,
    pub right: Box<ConditionExpr>,
}

/// Function call expression (e.g. ToLower(expr))
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionCallExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub function: String,
    pub arguments: Vec<ConditionExpr>,
}

/// Array expression with quantifiers (e.g. ANY tag : ...)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ArrayExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub operator: ArrayOperator,
    pub array: Box<ConditionExpr>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub variable: Option<String>,
    pub condition: Box<ConditionExpr>,
}

/// Set literal value (e.g. {'a', 'b'})
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SetLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub elements: Vec<ConditionExpr>,
}

/// List literal value (e.g. ['start', 'end'])
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ListLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub elements: Vec<ConditionExpr>,
}

/// Identifier expression (unqualified name)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct IdentifierExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub name: String,
}

/// Variable reference (e.g. loop variable in ANY clauses)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VariableReference {
    #[serde(skip)]
    pub span: EmptySpan,
    pub name: String,
}

/// Property access expression (e.g. tag.key)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PropertyAccessExpression {
    #[serde(skip)]
    pub span: EmptySpan,
    pub object: Box<ConditionExpr>,
    pub property: String,
}

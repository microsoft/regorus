// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure RBAC condition expression interpreter.
//!
//! This module evaluates parsed condition expressions against an
//! [`EvaluationContext`] without compiling to RVM instructions.

mod access;
mod attributes;
mod error;
mod eval;
mod literals;
mod quantifiers;

#[cfg(test)]
mod tests;

pub use error::ConditionEvalError;

use crate::languages::azure_rbac::ast::{ConditionExpr, ConditionExpression, EvaluationContext};
use crate::value::Value;
use eval::Evaluator;

/// Dynamic interpreter for Azure RBAC conditions.
#[derive(Debug, Clone)]
pub struct ConditionInterpreter<'a> {
    context: &'a EvaluationContext,
}

impl<'a> ConditionInterpreter<'a> {
    /// Create a new interpreter bound to a context.
    pub const fn new(context: &'a EvaluationContext) -> Self {
        Self { context }
    }

    /// Parse and evaluate a condition string.
    pub fn evaluate_str(&self, condition: &str) -> Result<bool, ConditionEvalError> {
        let mut evaluator = Evaluator::new(self.context);
        evaluator.evaluate_str(condition)
    }

    /// Evaluate a parsed condition expression.
    pub fn evaluate_condition_expression(
        &self,
        condition: &ConditionExpression,
    ) -> Result<bool, ConditionEvalError> {
        let mut evaluator = Evaluator::new(self.context);
        evaluator.evaluate_condition_expression(condition)
    }

    /// Evaluate a condition AST and return a boolean result.
    pub fn evaluate_bool(&self, expr: &ConditionExpr) -> Result<bool, ConditionEvalError> {
        let mut evaluator = Evaluator::new(self.context);
        evaluator.evaluate_bool(expr)
    }

    /// Evaluate a condition AST and return a value.
    pub fn evaluate_value(&self, expr: &ConditionExpr) -> Result<Value, ConditionEvalError> {
        let mut evaluator = Evaluator::new(self.context);
        evaluator.evaluate_value(expr)
    }
}

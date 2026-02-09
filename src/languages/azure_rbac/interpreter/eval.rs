// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use crate::languages::azure_rbac::ast::EvaluationContext;
use crate::languages::azure_rbac::ast::{
    BinaryExpression, ConditionExpr, ConditionExpression, FunctionCallExpression,
    LogicalExpression, LogicalOperator, UnaryExpression, UnaryOperator,
};
use crate::languages::azure_rbac::builtins::{
    DefaultRbacBuiltinEvaluator, RbacBuiltin, RbacBuiltinContext,
};
use crate::languages::azure_rbac::parser::parse_condition_expression;
use crate::value::Value;

use super::error::ConditionEvalError;

pub(super) struct Evaluator<'a> {
    pub(super) context: &'a EvaluationContext,
    variables: Vec<VariableBinding>,
}

struct VariableBinding {
    name: String,
    value: Value,
}

impl<'a> Evaluator<'a> {
    pub(super) const fn new(context: &'a EvaluationContext) -> Self {
        Self {
            context,
            variables: Vec::new(),
        }
    }

    pub(super) fn evaluate_str(&mut self, condition: &str) -> Result<bool, ConditionEvalError> {
        let parsed = parse_condition_expression(condition)
            .map_err(|err| ConditionEvalError::new(err.to_string()))?;
        self.evaluate_condition_expression(&parsed)
    }

    pub(super) fn evaluate_condition_expression(
        &mut self,
        condition: &ConditionExpression,
    ) -> Result<bool, ConditionEvalError> {
        let expr = condition
            .expression
            .as_ref()
            .ok_or_else(|| ConditionEvalError::new("Condition expression not parsed"))?;
        self.evaluate_bool(expr)
    }

    pub(super) fn evaluate_bool(
        &mut self,
        expr: &ConditionExpr,
    ) -> Result<bool, ConditionEvalError> {
        let value = self.evaluate_value(expr)?;
        match value {
            Value::Bool(b) => Ok(b),
            Value::Undefined => Ok(false),
            _ => Err(ConditionEvalError::new(
                "Condition did not evaluate to boolean",
            )),
        }
    }

    pub(super) fn evaluate_value(
        &mut self,
        expr: &ConditionExpr,
    ) -> Result<Value, ConditionEvalError> {
        match *expr {
            ConditionExpr::Logical(ref logical) => self.eval_logical(logical),
            ConditionExpr::Unary(ref unary) => self.eval_unary(unary),
            ConditionExpr::Binary(ref binary) => self.eval_binary(binary),
            ConditionExpr::FunctionCall(ref call) => self.eval_function(call),
            ConditionExpr::AttributeReference(ref attr) => self.eval_attribute_reference(attr),
            ConditionExpr::ArrayExpression(ref array) => self.eval_array_expression(array),
            ConditionExpr::Identifier(ref identifier) => Ok(self.eval_identifier(identifier)),
            ConditionExpr::VariableReference(ref variable) => {
                self.eval_variable_reference(variable)
            }
            ConditionExpr::PropertyAccess(ref access) => self.eval_property_access(access),
            ConditionExpr::StringLiteral(ref lit) => Ok(Value::String(lit.value.as_str().into())),
            ConditionExpr::NumberLiteral(ref lit) => {
                let num = lit.raw.parse::<f64>().map_err(|_| {
                    ConditionEvalError::new(format!("Invalid numeric literal: {}", lit.raw))
                })?;
                Ok(Value::from(num))
            }
            ConditionExpr::BooleanLiteral(ref lit) => Ok(Value::Bool(lit.value)),
            ConditionExpr::NullLiteral(_) => Ok(Value::Null),
            ConditionExpr::DateTimeLiteral(ref lit) => Ok(Value::String(lit.value.as_str().into())),
            ConditionExpr::TimeLiteral(ref lit) => Ok(Value::String(lit.value.as_str().into())),
            ConditionExpr::SetLiteral(ref set) => self.eval_set_literal(set),
            ConditionExpr::ListLiteral(ref list) => self.eval_list_literal(&list.elements),
        }
    }

    fn eval_logical(&mut self, expr: &LogicalExpression) -> Result<Value, ConditionEvalError> {
        let left = self.evaluate_bool(&expr.left)?;
        match expr.operator {
            LogicalOperator::And => {
                if !left {
                    return Ok(Value::Bool(false));
                }
                let right = self.evaluate_bool(&expr.right)?;
                Ok(Value::Bool(left && right))
            }
            LogicalOperator::Or => {
                if left {
                    return Ok(Value::Bool(true));
                }
                let right = self.evaluate_bool(&expr.right)?;
                Ok(Value::Bool(left || right))
            }
        }
    }

    fn eval_unary(&mut self, expr: &UnaryExpression) -> Result<Value, ConditionEvalError> {
        match expr.operator {
            UnaryOperator::Not => {
                let value = self.evaluate_bool(&expr.operand)?;
                Ok(Value::Bool(!value))
            }
            UnaryOperator::Exists => {
                let value = self.evaluate_value(&expr.operand)?;
                Ok(Value::Bool(!matches!(value, Value::Undefined)))
            }
            UnaryOperator::NotExists => {
                let value = self.evaluate_value(&expr.operand)?;
                Ok(Value::Bool(matches!(value, Value::Undefined)))
            }
        }
    }

    fn eval_binary(&mut self, expr: &BinaryExpression) -> Result<Value, ConditionEvalError> {
        let left = self.evaluate_value(&expr.left)?;
        let right = self.evaluate_value(&expr.right)?;
        let builtin = expr.operator;

        let evaluator = DefaultRbacBuiltinEvaluator::new();
        let ctx = RbacBuiltinContext::new(self.context);
        let args = [left, right];
        evaluator
            .eval(builtin, &args, &ctx)
            .map_err(|err| ConditionEvalError::new(err.to_string()))
    }

    fn eval_function(
        &mut self,
        call: &FunctionCallExpression,
    ) -> Result<Value, ConditionEvalError> {
        let mut args = Vec::with_capacity(call.arguments.len());
        for arg in &call.arguments {
            args.push(self.evaluate_value(arg)?);
        }
        let builtin = RbacBuiltin::parse(call.function.as_str()).ok_or_else(|| {
            ConditionEvalError::new(format!("Unsupported function: {}", call.function))
        })?;
        let evaluator = DefaultRbacBuiltinEvaluator::new();
        let ctx = RbacBuiltinContext::new(self.context);
        evaluator
            .eval(builtin, &args, &ctx)
            .map_err(|err| ConditionEvalError::new(err.to_string()))
    }

    pub(super) fn push_variable(&mut self, name: &str, value: Value) {
        self.variables.push(VariableBinding {
            name: name.to_string(),
            value,
        });
    }

    pub(super) fn pop_variable(&mut self) {
        let _ = self.variables.pop();
    }

    pub(super) fn lookup_variable(&self, name: &str) -> Option<Value> {
        self.variables
            .iter()
            .rev()
            .find(|binding| binding.name == name)
            .map(|binding| binding.value.clone())
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::vec::Vec;

use crate::languages::azure_rbac::ast::ArrayExpression;
use crate::value::Value;

use super::error::ConditionEvalError;
use super::eval::Evaluator;

impl<'a> Evaluator<'a> {
    pub(super) fn eval_array_expression(
        &mut self,
        array: &ArrayExpression,
    ) -> Result<Value, ConditionEvalError> {
        let collection = self.evaluate_value(&array.array)?;
        let values: Vec<&Value> = match collection {
            Value::Array(ref list) => list.iter().collect(),
            Value::Set(ref set) => set.iter().collect(),
            Value::Undefined => return Ok(Value::Bool(false)),
            _ => {
                return Err(ConditionEvalError::new(
                    "Array expression expects a list or set",
                ))
            }
        };

        let is_any = array.operator.name.eq_ignore_ascii_case("ANY");
        let is_all = array.operator.name.eq_ignore_ascii_case("ALL");
        if !is_any && !is_all {
            return Err(ConditionEvalError::new(format!(
                "Unsupported array operator: {}",
                array.operator.name
            )));
        }

        let variable = array.variable.as_deref();
        if is_any {
            for value in &values {
                let matched = self.eval_array_condition(variable, value, &array.condition)?;
                if matched {
                    return Ok(Value::Bool(true));
                }
            }
            return Ok(Value::Bool(false));
        }

        let mut saw_value = false;
        for value in &values {
            saw_value = true;
            let matched = self.eval_array_condition(variable, value, &array.condition)?;
            if !matched {
                return Ok(Value::Bool(false));
            }
        }

        Ok(Value::Bool(!saw_value || is_all))
    }

    fn eval_array_condition(
        &mut self,
        variable: Option<&str>,
        value: &Value,
        condition: &crate::languages::azure_rbac::ast::ConditionExpr,
    ) -> Result<bool, ConditionEvalError> {
        if let Some(name) = variable {
            self.push_variable(name, value.clone());
            let result = self.evaluate_bool(condition);
            self.pop_variable();
            result
        } else {
            self.evaluate_bool(condition)
        }
    }
}

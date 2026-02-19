// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::languages::azure_rbac::ast::{PropertyAccessExpression, VariableReference};
use crate::value::Value;

use super::error::ConditionEvalError;
use super::eval::Evaluator;

impl<'a> Evaluator<'a> {
    pub(super) fn eval_variable_reference(
        &self,
        variable: &VariableReference,
    ) -> Result<Value, ConditionEvalError> {
        Ok(self
            .lookup_variable(variable.name.as_str())
            .unwrap_or(Value::Undefined))
    }

    pub(super) fn eval_property_access(
        &mut self,
        access: &PropertyAccessExpression,
    ) -> Result<Value, ConditionEvalError> {
        let object = self.evaluate_value(&access.object)?;
        match object {
            Value::Object(map) => Ok(map
                .get(&Value::String(access.property.as_str().into()))
                .cloned()
                .unwrap_or(Value::Undefined)),
            _ => Ok(Value::Undefined),
        }
    }
}

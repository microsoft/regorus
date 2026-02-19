// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use crate::languages::azure_rbac::ast::{ConditionExpr, IdentifierExpression, SetLiteral};
use crate::value::Value;

use super::error::ConditionEvalError;
use super::eval::Evaluator;

impl<'a> Evaluator<'a> {
    pub(super) fn eval_set_literal(
        &mut self,
        set: &SetLiteral,
    ) -> Result<Value, ConditionEvalError> {
        let mut values = BTreeSet::new();
        for elem in &set.elements {
            let value = self.evaluate_value(elem)?;
            values.insert(value);
        }
        Ok(Value::from(values))
    }

    pub(super) fn eval_list_literal(
        &mut self,
        elements: &[ConditionExpr],
    ) -> Result<Value, ConditionEvalError> {
        let mut values = Vec::with_capacity(elements.len());
        for elem in elements {
            values.push(self.evaluate_value(elem)?);
        }
        Ok(Value::from(values))
    }

    pub(super) fn eval_identifier(&self, identifier: &IdentifierExpression) -> Value {
        match identifier.name.as_str() {
            "operationName" => self
                .context
                .action
                .clone()
                .map(|s: String| Value::String(s.into()))
                .unwrap_or(Value::Undefined),
            "subOperationName" => self
                .context
                .suboperation
                .clone()
                .map(|s: String| Value::String(s.into()))
                .unwrap_or(Value::Undefined),
            "action" => self
                .context
                .request
                .action
                .clone()
                .map(|s: String| Value::String(s.into()))
                .unwrap_or(Value::Undefined),
            "dataAction" => self
                .context
                .request
                .data_action
                .clone()
                .map(|s: String| Value::String(s.into()))
                .unwrap_or(Value::Undefined),
            "principalId" => Value::String(self.context.principal.id.as_str().into()),
            "resourceId" => Value::String(self.context.resource.id.as_str().into()),
            "resourceScope" => Value::String(self.context.resource.scope.as_str().into()),
            "resourceType" => Value::String(self.context.resource.resource_type.as_str().into()),
            _ => Value::Undefined,
        }
    }
}

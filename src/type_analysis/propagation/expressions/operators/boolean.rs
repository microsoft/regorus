// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{BoolOp, Expr, Ref};
use crate::lexer::Span;
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::derived_from_pair;
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_bool_expr(
        &self,
        module_idx: u32,
        span: &Span,
        op: &BoolOp,
        lhs: &Ref<Expr>,
        rhs: &Ref<Expr>,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let lhs_fact = self.infer_expr(module_idx, lhs, bindings, result, rule_analysis);
        let rhs_fact = self.infer_expr(module_idx, rhs, bindings, result, rule_analysis);

        self.check_equality_diagnostic(module_idx, span, op, &lhs_fact, &rhs_fact, result);

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Boolean),
            TypeProvenance::Propagated,
        );

        if let (Some(left), Some(right)) = (
            lhs_fact.fact.constant.as_value(),
            rhs_fact.fact.constant.as_value(),
        ) {
            let result_value = if *left == Value::Undefined || *right == Value::Undefined {
                Some(Value::Undefined)
            } else {
                match op {
                    BoolOp::Eq => Some(Value::from(left == right)),
                    BoolOp::Ne => Some(Value::from(left != right)),
                    BoolOp::Lt => left
                        .partial_cmp(right)
                        .map(|ord| Value::from(ord == core::cmp::Ordering::Less)),
                    BoolOp::Gt => left
                        .partial_cmp(right)
                        .map(|ord| Value::from(ord == core::cmp::Ordering::Greater)),
                    BoolOp::Le => left
                        .partial_cmp(right)
                        .map(|ord| Value::from(ord != core::cmp::Ordering::Greater)),
                    BoolOp::Ge => left
                        .partial_cmp(right)
                        .map(|ord| Value::from(ord != core::cmp::Ordering::Less)),
                }
            };

            if let Some(value) = result_value {
                fact = fact.with_constant(ConstantValue::known(value));
            }
        }

        if !lhs_fact.fact.origins.is_empty() || !rhs_fact.fact.origins.is_empty() {
            fact = fact.with_origins(derived_from_pair(
                &lhs_fact.fact.origins,
                &rhs_fact.fact.origins,
            ));
        }

        fact
    }
}

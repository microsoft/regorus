// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::mark_origins_derived;
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

impl TypeAnalyzer {
    pub(crate) fn infer_unary_expr(
        &self,
        module_idx: u32,
        expr: &Ref<Expr>,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let operand = self.infer_expr(module_idx, expr, bindings, result, rule_analysis);

        if let Some(value) = operand.fact.constant.as_value() {
            if let Ok(number) = value.as_number() {
                if let Ok(negated_number) = crate::number::Number::from(0i64).sub(number) {
                    let structural_type = if negated_number.is_integer() {
                        StructuralType::Integer
                    } else {
                        StructuralType::Number
                    };

                    return TypeFact::new(
                        TypeDescriptor::Structural(structural_type),
                        TypeProvenance::Literal,
                    )
                    .with_constant(ConstantValue::known(Value::from(negated_number)));
                }
            }
        }

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Number),
            TypeProvenance::Propagated,
        );

        if !operand.fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&operand.fact.origins));
        }

        fact
    }
}

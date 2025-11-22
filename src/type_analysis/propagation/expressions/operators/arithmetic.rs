// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec;

use crate::ast::{ArithOp, Expr, Ref};
use crate::lexer::Span;
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, HybridType, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact,
    TypeProvenance,
};
use crate::type_analysis::propagation::facts::{derived_from_pair, schema_array_items};
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_arith_expr(
        &self,
        module_idx: u32,
        span: &Span,
        op: &ArithOp,
        lhs: &Ref<Expr>,
        rhs: &Ref<Expr>,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let lhs_fact = self.infer_expr(module_idx, lhs, bindings, result, rule_analysis);
        let rhs_fact = self.infer_expr(module_idx, rhs, bindings, result, rule_analysis);

        self.check_arithmetic_diagnostic(module_idx, span, op, &lhs_fact, &rhs_fact, result);

        let lhs_def_integer = Self::hybrid_is_definitely_integer(&lhs_fact);
        let rhs_def_integer = Self::hybrid_is_definitely_integer(&rhs_fact);

        let (lhs_element, lhs_provenance, lhs_is_set) = match &lhs_fact.fact.descriptor {
            TypeDescriptor::Schema(schema) => {
                if let Some((item_schema, _)) = schema_array_items(schema) {
                    (
                        StructuralType::from_schema(&item_schema),
                        lhs_fact.fact.provenance.clone(),
                        true,
                    )
                } else {
                    (StructuralType::Any, TypeProvenance::Propagated, false)
                }
            }
            TypeDescriptor::Structural(StructuralType::Set(element)) => (
                element.as_ref().clone(),
                lhs_fact.fact.provenance.clone(),
                true,
            ),
            _ => (StructuralType::Any, TypeProvenance::Propagated, false),
        };

        let (_rhs_element, rhs_is_set) = match &rhs_fact.fact.descriptor {
            TypeDescriptor::Schema(schema) => {
                if let Some((item_schema, _)) = schema_array_items(schema) {
                    (StructuralType::from_schema(&item_schema), true)
                } else {
                    (StructuralType::Any, false)
                }
            }
            TypeDescriptor::Structural(StructuralType::Set(element)) => {
                (element.as_ref().clone(), true)
            }
            _ => (StructuralType::Any, false),
        };

        if matches!(op, ArithOp::Sub) {
            let lhs_numeric = matches!(&lhs_fact.fact.descriptor,
                TypeDescriptor::Structural(st) if Self::is_numeric_type(st));
            let rhs_numeric = matches!(&rhs_fact.fact.descriptor,
                TypeDescriptor::Structural(st) if Self::is_numeric_type(st));

            if lhs_is_set && rhs_is_set {
                let mut fact = TypeFact::new(
                    TypeDescriptor::Structural(StructuralType::Set(Box::new(lhs_element.clone()))),
                    lhs_provenance.clone(),
                );

                if !lhs_fact.fact.origins.is_empty() || !rhs_fact.fact.origins.is_empty() {
                    fact = fact.with_origins(derived_from_pair(
                        &lhs_fact.fact.origins,
                        &rhs_fact.fact.origins,
                    ));
                }

                if let (ConstantValue::Known(lhs_val), ConstantValue::Known(rhs_val)) =
                    (&lhs_fact.fact.constant, &rhs_fact.fact.constant)
                {
                    if lhs_val == &Value::Undefined || rhs_val == &Value::Undefined {
                        fact = fact.with_constant(ConstantValue::unknown());
                        fact.descriptor = TypeDescriptor::Structural(StructuralType::Unknown);
                    } else if let (Ok(lhs_set), Ok(rhs_set)) = (lhs_val.as_set(), rhs_val.as_set())
                    {
                        let diff_set: BTreeSet<Value> = lhs_set
                            .iter()
                            .filter(|item| !rhs_set.contains(item))
                            .cloned()
                            .collect();
                        fact = fact.with_constant(ConstantValue::known(Value::from(diff_set)));
                    }
                }

                return fact;
            }

            if lhs_numeric && rhs_numeric {
                let result_numeric_type = if lhs_def_integer && rhs_def_integer {
                    StructuralType::Integer
                } else {
                    StructuralType::Number
                };

                let mut fact = TypeFact::new(
                    TypeDescriptor::Structural(result_numeric_type.clone()),
                    TypeProvenance::Propagated,
                );

                if !lhs_fact.fact.origins.is_empty() || !rhs_fact.fact.origins.is_empty() {
                    fact = fact.with_origins(derived_from_pair(
                        &lhs_fact.fact.origins,
                        &rhs_fact.fact.origins,
                    ));
                }

                // Perform constant folding for numeric subtraction
                if let (ConstantValue::Known(lhs_val), ConstantValue::Known(rhs_val)) =
                    (&lhs_fact.fact.constant, &rhs_fact.fact.constant)
                {
                    if *lhs_val == Value::Undefined || *rhs_val == Value::Undefined {
                        fact = fact.with_constant(ConstantValue::unknown());
                        fact.descriptor = TypeDescriptor::Structural(StructuralType::Unknown);
                    } else if let (Ok(lhs_num), Ok(rhs_num)) =
                        (lhs_val.as_number(), rhs_val.as_number())
                    {
                        if let Ok(result) = lhs_num.sub(rhs_num) {
                            let structural_type = if result.is_integer() {
                                StructuralType::Integer
                            } else {
                                StructuralType::Number
                            };

                            fact = TypeFact::new(
                                TypeDescriptor::Structural(structural_type),
                                TypeProvenance::Propagated,
                            )
                            .with_constant(ConstantValue::known(Value::from(result)));

                            if !lhs_fact.fact.origins.is_empty()
                                || !rhs_fact.fact.origins.is_empty()
                            {
                                fact = fact.with_origins(derived_from_pair(
                                    &lhs_fact.fact.origins,
                                    &rhs_fact.fact.origins,
                                ));
                            }
                        }
                    }
                }

                return fact;
            }

            let mut fact = TypeFact::new(
                TypeDescriptor::Structural(Self::make_union(vec![
                    StructuralType::Number,
                    StructuralType::Set(Box::new(StructuralType::Any)),
                ])),
                TypeProvenance::Propagated,
            );

            if !lhs_fact.fact.origins.is_empty() || !rhs_fact.fact.origins.is_empty() {
                fact = fact.with_origins(derived_from_pair(
                    &lhs_fact.fact.origins,
                    &rhs_fact.fact.origins,
                ));
            }

            return fact;
        }

        let result_numeric_type = if lhs_def_integer && rhs_def_integer {
            StructuralType::Integer
        } else {
            StructuralType::Number
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(result_numeric_type),
            TypeProvenance::Propagated,
        );

        if !lhs_fact.fact.origins.is_empty() || !rhs_fact.fact.origins.is_empty() {
            fact = fact.with_origins(derived_from_pair(
                &lhs_fact.fact.origins,
                &rhs_fact.fact.origins,
            ));
        }

        if let (ConstantValue::Known(lhs_val), ConstantValue::Known(rhs_val)) =
            (&lhs_fact.fact.constant, &rhs_fact.fact.constant)
        {
            if *lhs_val == Value::Undefined || *rhs_val == Value::Undefined {
                fact = fact.with_constant(ConstantValue::unknown());
                fact.descriptor = TypeDescriptor::Structural(StructuralType::Unknown);
            } else if let (Ok(lhs_num), Ok(rhs_num)) = (lhs_val.as_number(), rhs_val.as_number()) {
                if matches!(op, ArithOp::Mod) && (!lhs_num.is_integer() || !rhs_num.is_integer()) {
                    fact = fact.with_constant(ConstantValue::unknown());
                    fact.descriptor = TypeDescriptor::Structural(StructuralType::Unknown);
                } else {
                    let result_number = match op {
                        ArithOp::Add => lhs_num.add(rhs_num).ok(),
                        ArithOp::Sub => lhs_num.sub(rhs_num).ok(),
                        ArithOp::Mul => lhs_num.mul(rhs_num).ok(),
                        ArithOp::Div => lhs_num.clone().divide(rhs_num).ok(),
                        ArithOp::Mod => lhs_num.clone().modulo(rhs_num).ok(),
                    };

                    if let Some(num) = result_number {
                        let structural_type = if num.is_integer() {
                            StructuralType::Integer
                        } else {
                            StructuralType::Number
                        };

                        fact = TypeFact::new(
                            TypeDescriptor::Structural(structural_type),
                            TypeProvenance::Propagated,
                        )
                        .with_constant(ConstantValue::known(Value::from(num)));

                        if !lhs_fact.fact.origins.is_empty() || !rhs_fact.fact.origins.is_empty() {
                            fact = fact.with_origins(derived_from_pair(
                                &lhs_fact.fact.origins,
                                &rhs_fact.fact.origins,
                            ));
                        }
                    }
                }
            }
        }

        fact
    }
}

impl TypeAnalyzer {
    fn hybrid_is_definitely_integer(ty: &HybridType) -> bool {
        if let Some(value) = ty.fact.constant.as_value() {
            if let Ok(number) = value.as_number() {
                return number.is_integer();
            }
            return false;
        }

        Self::descriptor_is_definitely_integer(&ty.fact.descriptor)
    }

    fn descriptor_is_definitely_integer(descriptor: &TypeDescriptor) -> bool {
        match descriptor {
            TypeDescriptor::Structural(struct_ty) => {
                Self::structural_is_definitely_integer(struct_ty)
            }
            TypeDescriptor::Schema(schema) => {
                let structural = StructuralType::from_schema(schema);
                Self::structural_is_definitely_integer(&structural)
            }
        }
    }

    fn structural_is_definitely_integer(struct_ty: &StructuralType) -> bool {
        match struct_ty {
            StructuralType::Integer => true,
            StructuralType::Union(variants) => {
                !variants.is_empty() && variants.iter().all(Self::structural_is_definitely_integer)
            }
            StructuralType::Enum(values) => values.iter().all(|value| {
                if let Value::Number(num) = value {
                    num.is_integer()
                } else {
                    false
                }
            }),
            _ => false,
        }
    }
}

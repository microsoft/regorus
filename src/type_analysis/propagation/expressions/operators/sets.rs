// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::boxed::Box;

use crate::ast::{BinOp, Expr, Ref};
use crate::lexer::Span;
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::{
    derived_from_pair, mark_origins_derived, schema_array_items,
};
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_bin_expr(
        &self,
        module_idx: u32,
        span: &Span,
        op: &BinOp,
        lhs: &Ref<Expr>,
        rhs: &Ref<Expr>,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let lhs_type = self.infer_expr(module_idx, lhs, bindings, result, rule_analysis);
        let rhs_type = self.infer_expr(module_idx, rhs, bindings, result, rule_analysis);

        self.check_set_operation_diagnostic(module_idx, span, op, &lhs_type, &rhs_type, result);

        let (lhs_element, lhs_provenance) = match &lhs_type.fact.descriptor {
            TypeDescriptor::Schema(schema) => {
                if let Some((items, _)) = schema_array_items(schema) {
                    (
                        StructuralType::from_schema(&items),
                        lhs_type.fact.provenance.clone(),
                    )
                } else {
                    (StructuralType::Any, lhs_type.fact.provenance.clone())
                }
            }
            TypeDescriptor::Structural(StructuralType::Set(elem)) => {
                ((**elem).clone(), lhs_type.fact.provenance.clone())
            }
            _ => (StructuralType::Any, TypeProvenance::Propagated),
        };

        let rhs_element = match &rhs_type.fact.descriptor {
            TypeDescriptor::Schema(schema) => {
                if let Some((items, _)) = schema_array_items(schema) {
                    StructuralType::from_schema(&items)
                } else {
                    StructuralType::Any
                }
            }
            TypeDescriptor::Structural(StructuralType::Set(elem)) => (**elem).clone(),
            _ => StructuralType::Any,
        };

        let result_element = match op {
            BinOp::Union => Self::join_structural_types(&[lhs_element, rhs_element]),
            BinOp::Intersection => lhs_element,
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Set(Box::new(result_element))),
            lhs_provenance,
        );

        if !lhs_type.fact.origins.is_empty() || !rhs_type.fact.origins.is_empty() {
            fact = fact.with_origins(derived_from_pair(
                &lhs_type.fact.origins,
                &rhs_type.fact.origins,
            ));
        }

        if let (ConstantValue::Known(lhs_val), ConstantValue::Known(rhs_val)) =
            (&lhs_type.fact.constant, &rhs_type.fact.constant)
        {
            if *lhs_val == Value::Undefined || *rhs_val == Value::Undefined {
                fact = fact.with_constant(ConstantValue::known(Value::Undefined));
            } else if let (Ok(lhs_set), Ok(rhs_set)) = (lhs_val.as_set(), rhs_val.as_set()) {
                let result_set = match op {
                    BinOp::Union => {
                        let mut union_set = lhs_set.clone();
                        for item in rhs_set.iter() {
                            union_set.insert(item.clone());
                        }
                        union_set
                    }
                    BinOp::Intersection => lhs_set
                        .iter()
                        .filter(|item| rhs_set.contains(item))
                        .cloned()
                        .collect(),
                };

                fact = fact.with_constant(ConstantValue::known(Value::from(result_set)));
            }
        }

        fact
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_membership_expr(
        &self,
        module_idx: u32,
        span: &Span,
        value: &Ref<Expr>,
        collection: &Ref<Expr>,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let value_type = self.infer_expr(module_idx, value, bindings, result, rule_analysis);
        let collection_type =
            self.infer_expr(module_idx, collection, bindings, result, rule_analysis);

        // Check for membership diagnostic issues
        self.check_membership_diagnostic(module_idx, span, &value_type, &collection_type, result);

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Boolean),
            TypeProvenance::Propagated,
        );

        if !collection_type.fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&collection_type.fact.origins));
        }

        if let (ConstantValue::Known(val), ConstantValue::Known(coll)) =
            (&value_type.fact.constant, &collection_type.fact.constant)
        {
            if *val == Value::Undefined || *coll == Value::Undefined {
                fact = fact.with_constant(ConstantValue::known(Value::Undefined));
            } else {
                let is_member = if let Ok(set) = coll.as_set() {
                    set.contains(val)
                } else if let Ok(arr) = coll.as_array() {
                    arr.contains(val)
                } else if let Ok(obj) = coll.as_object() {
                    obj.contains_key(val)
                } else if let Ok(s) = coll.as_string() {
                    if let Ok(needle) = val.as_string() {
                        s.contains(needle.as_ref())
                    } else {
                        false
                    }
                } else {
                    false
                };

                fact = fact.with_constant(ConstantValue::known(Value::from(is_member)));
            }
        }

        fact
    }
}

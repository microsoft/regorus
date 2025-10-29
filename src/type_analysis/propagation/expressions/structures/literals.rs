// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use crate::ast::{Expr, Ref};
use crate::lexer::Span;
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, PathSegment, RuleAnalysis, StructuralObjectShape, StructuralType,
    TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::{extend_origins_with_segment, mark_origins_derived};
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

impl TypeAnalyzer {
    pub(crate) fn infer_array_literal(
        &self,
        module_idx: u32,
        items: &[Ref<Expr>],
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let mut element_types = Vec::new();
        let mut all_origins = Vec::new();
        let mut constant_elements = Vec::new();
        let mut all_constant = true;

        for (idx, item_expr) in items.iter().enumerate() {
            let item_type = self.infer_expr(module_idx, item_expr, bindings, result, rule_analysis);

            element_types.push(match &item_type.fact.descriptor {
                TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
                TypeDescriptor::Structural(st) => st.clone(),
            });

            if !item_type.fact.origins.is_empty() {
                let item_origins =
                    extend_origins_with_segment(&item_type.fact.origins, PathSegment::Index(idx));
                all_origins.extend(item_origins);
            }

            if let ConstantValue::Known(value) = &item_type.fact.constant {
                constant_elements.push(value.clone());
            } else {
                all_constant = false;
            }
        }

        let element_type = if element_types.is_empty() {
            StructuralType::Any
        } else {
            Self::join_structural_types(&element_types)
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Array(Box::new(element_type))),
            TypeProvenance::Literal,
        );

        if !all_origins.is_empty() {
            fact = fact.with_origins(all_origins);
        }

        if all_constant {
            fact = fact.with_constant(ConstantValue::known(Value::from(constant_elements)));
        }

        fact
    }

    pub(crate) fn infer_set_literal(
        &self,
        module_idx: u32,
        items: &[Ref<Expr>],
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let mut element_types = Vec::new();
        let mut all_origins = Vec::new();
        let mut constant_elements = BTreeSet::new();
        let mut all_constant = true;

        for item_expr in items {
            let item_type = self.infer_expr(module_idx, item_expr, bindings, result, rule_analysis);

            element_types.push(match &item_type.fact.descriptor {
                TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
                TypeDescriptor::Structural(st) => st.clone(),
            });

            if !item_type.fact.origins.is_empty() {
                all_origins.extend(mark_origins_derived(&item_type.fact.origins));
            }

            if let ConstantValue::Known(value) = &item_type.fact.constant {
                constant_elements.insert(value.clone());
            } else {
                all_constant = false;
            }
        }

        let element_type = if element_types.is_empty() {
            StructuralType::Any
        } else {
            Self::join_structural_types(&element_types)
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Set(Box::new(element_type))),
            TypeProvenance::Literal,
        );

        if !all_origins.is_empty() {
            fact = fact.with_origins(all_origins);
        }

        if all_constant {
            fact = fact.with_constant(ConstantValue::known(Value::from(constant_elements)));
        }

        fact
    }

    pub(crate) fn infer_object_literal(
        &self,
        module_idx: u32,
        fields: &[(Span, Ref<Expr>, Ref<Expr>)],
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let mut field_types = BTreeMap::new();
        let mut all_origins = Vec::new();
        let mut constant_fields = BTreeMap::new();
        let mut all_constant = true;

        for (_key_span, key_expr, value_expr) in fields {
            let (key_name, key_value) = if let Expr::String { value, .. }
            | Expr::RawString { value, .. } = key_expr.as_ref()
            {
                (
                    value.as_string().ok().map(|s| s.as_ref().to_owned()),
                    Some(value.clone()),
                )
            } else {
                let key_fact =
                    self.infer_expr(module_idx, key_expr, bindings, result, rule_analysis);
                let key_const = key_fact.fact.constant.as_value().cloned();
                (None, key_const)
            };

            let value_type =
                self.infer_expr(module_idx, value_expr, bindings, result, rule_analysis);

            let value_structural_type = match &value_type.fact.descriptor {
                TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
                TypeDescriptor::Structural(st) => st.clone(),
            };

            if let Some(name) = key_name {
                field_types.insert(name.clone(), value_structural_type);

                if !value_type.fact.origins.is_empty() {
                    let field_origins = extend_origins_with_segment(
                        &value_type.fact.origins,
                        PathSegment::Field(name),
                    );
                    all_origins.extend(field_origins);
                }
            } else if !value_type.fact.origins.is_empty() {
                all_origins.extend(mark_origins_derived(&value_type.fact.origins));
            }

            if let (Some(k), ConstantValue::Known(v)) = (key_value, &value_type.fact.constant) {
                constant_fields.insert(k, v.clone());
            } else {
                all_constant = false;
            }
        }

        let shape = StructuralObjectShape {
            fields: field_types,
        };
        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Object(shape)),
            TypeProvenance::Literal,
        );

        if !all_origins.is_empty() {
            fact = fact.with_origins(all_origins);
        }

        if all_constant {
            fact = fact.with_constant(ConstantValue::known(Value::from(constant_fields)));
        }

        fact
    }
}

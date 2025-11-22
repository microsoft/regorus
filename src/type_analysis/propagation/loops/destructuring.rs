// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;

use crate::compiler::destructuring_planner::DestructuringPlan;
use crate::value::Value;

use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, PathSegment, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact,
};

use super::super::facts::{
    extend_origins_with_segment, mark_origins_derived, schema_array_items, schema_property,
};
use super::super::pipeline::{TypeAnalysisResult, TypeAnalyzer};

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_destructuring_plan(
        &self,
        module_idx: u32,
        plan: &DestructuringPlan,
        source_fact: &TypeFact,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) {
        use DestructuringPlan::*;

        match plan {
            Var(span) => {
                let name = span.text();
                if name != "_" {
                    bindings.ensure_root_scope();
                    bindings.assign(name.to_owned(), source_fact.clone());
                }
            }
            Ignore => {}
            EqualityExpr(expr) => {
                let _ = self.infer_expr(module_idx, expr, bindings, result, rule_analysis);
            }
            EqualityValue(_) => {}
            Array { element_plans } => {
                let element_fact = self.derive_array_element_fact(source_fact);
                for element_plan in element_plans {
                    self.apply_destructuring_plan(
                        module_idx,
                        element_plan,
                        &element_fact,
                        bindings,
                        result,
                        rule_analysis,
                    );
                }
            }
            Object {
                field_plans,
                dynamic_fields,
            } => {
                for (key, field_plan) in field_plans {
                    let field_fact = self.derive_object_field_fact(source_fact, key);
                    self.apply_destructuring_plan(
                        module_idx,
                        field_plan,
                        &field_fact,
                        bindings,
                        result,
                        rule_analysis,
                    );
                }

                for (key_expr, field_plan) in dynamic_fields {
                    let dynamic_fact = self.derive_dynamic_field_fact(source_fact);
                    self.apply_destructuring_plan(
                        module_idx,
                        field_plan,
                        &dynamic_fact,
                        bindings,
                        result,
                        rule_analysis,
                    );
                    let _ = self.infer_expr(module_idx, key_expr, bindings, result, rule_analysis);
                }
            }
        }
    }

    pub(super) fn derive_array_element_fact(&self, source_fact: &TypeFact) -> TypeFact {
        match &source_fact.descriptor {
            TypeDescriptor::Schema(schema) => {
                if let Some((item_schema, schema_constant)) = schema_array_items(schema) {
                    let mut fact = TypeFact::new(
                        TypeDescriptor::Schema(item_schema),
                        source_fact.provenance.clone(),
                    );

                    if let Some(constant) = schema_constant {
                        fact = fact.with_constant(ConstantValue::known(constant));
                    }

                    if !source_fact.origins.is_empty() {
                        fact = fact.with_origins(mark_origins_derived(
                            &extend_origins_with_segment(&source_fact.origins, PathSegment::Any),
                        ));
                    }
                    return fact;
                }
            }
            TypeDescriptor::Structural(StructuralType::Array(element_ty))
            | TypeDescriptor::Structural(StructuralType::Set(element_ty)) => {
                let mut fact = TypeFact::new(
                    TypeDescriptor::Structural((**element_ty).clone()),
                    source_fact.provenance.clone(),
                );
                if !source_fact.origins.is_empty() {
                    fact = fact.with_origins(mark_origins_derived(&extend_origins_with_segment(
                        &source_fact.origins,
                        PathSegment::Any,
                    )));
                }
                return fact;
            }
            _ => {}
        }

        TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Any),
            source_fact.provenance.clone(),
        )
    }

    pub(super) fn derive_object_field_fact(&self, source_fact: &TypeFact, key: &Value) -> TypeFact {
        if let Ok(name) = key.as_string() {
            if let TypeDescriptor::Schema(schema) = &source_fact.descriptor {
                if let Some((prop_schema, schema_constant)) = schema_property(schema, name.as_ref())
                {
                    let mut fact = TypeFact::new(
                        TypeDescriptor::Schema(prop_schema),
                        source_fact.provenance.clone(),
                    );

                    if let Some(constant) = schema_constant {
                        fact = fact.with_constant(ConstantValue::known(constant));
                    }

                    if !source_fact.origins.is_empty() {
                        fact =
                            fact.with_origins(mark_origins_derived(&extend_origins_with_segment(
                                &source_fact.origins,
                                PathSegment::Field(name.as_ref().to_owned()),
                            )));
                    }
                    return fact;
                }
            }

            if let TypeDescriptor::Structural(StructuralType::Object(shape)) =
                &source_fact.descriptor
            {
                if let Some(field_ty) = shape.fields.get(name.as_ref()) {
                    let mut fact = TypeFact::new(
                        TypeDescriptor::Structural(field_ty.clone()),
                        source_fact.provenance.clone(),
                    );
                    if !source_fact.origins.is_empty() {
                        fact =
                            fact.with_origins(mark_origins_derived(&extend_origins_with_segment(
                                &source_fact.origins,
                                PathSegment::Field(name.as_ref().to_owned()),
                            )));
                    }
                    return fact;
                }
            }
        }

        self.derive_dynamic_field_fact(source_fact)
    }

    pub(super) fn derive_dynamic_field_fact(&self, source_fact: &TypeFact) -> TypeFact {
        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Any),
            source_fact.provenance.clone(),
        );
        if !source_fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&extend_origins_with_segment(
                &source_fact.origins,
                PathSegment::Any,
            )));
        }
        fact
    }
}

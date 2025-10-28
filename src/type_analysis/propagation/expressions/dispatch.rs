// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;

use crate::ast::{Expr, Ref};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, HybridType, PathSegment, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact,
    TypeProvenance,
};
use crate::type_analysis::propagation::facts::{
    extend_origins_with_segment, extract_schema_constant, schema_additional_properties_schema,
    schema_array_items,
};
use crate::type_analysis::propagation::pipeline::{AnalysisState, TypeAnalyzer};
use crate::value::Value;

impl TypeAnalyzer {
    pub(crate) fn infer_expr(
        &self,
        module_idx: u32,
        expr: &Ref<Expr>,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) -> HybridType {
        let eidx = expr.eidx();
        let skip_cached_fact = matches!(expr.as_ref(), Expr::Var { .. });

        if !skip_cached_fact {
            if let Some(existing) = result.lookup.get_expr(module_idx, eidx) {
                if !existing.origins.is_empty() {
                    rule_analysis.record_origins(&existing.origins);
                }
                return HybridType::from_fact(existing.clone());
            }
        }

        self.ensure_expr_capacity(module_idx, eidx, result);

        let fact = match expr.as_ref() {
            Expr::String { value, .. } | Expr::RawString { value, .. } => {
                self.infer_string_literal(value)
            }
            Expr::Number { value, .. } => self.infer_number_literal(value),
            Expr::Bool { value, .. } => self.infer_bool_literal(value),
            Expr::Null { value, .. } => self.infer_null_literal(value),
            Expr::Var { value, .. } => {
                self.infer_var(module_idx, eidx, value, bindings, result, rule_analysis)
            }
            Expr::Array { items, .. } => {
                self.infer_array_literal(module_idx, items, bindings, result, rule_analysis)
            }
            Expr::Set { items, .. } => {
                self.infer_set_literal(module_idx, items, bindings, result, rule_analysis)
            }
            Expr::Object { fields, .. } => {
                self.infer_object_literal(module_idx, fields, bindings, result, rule_analysis)
            }
            Expr::ArrayCompr { term, query, .. } => self.infer_array_comprehension(
                module_idx,
                term,
                query,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::SetCompr { term, query, .. } => self.infer_set_comprehension(
                module_idx,
                term,
                query,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::ObjectCompr {
                key, value, query, ..
            } => self.infer_object_comprehension(
                module_idx,
                key,
                value,
                query,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::AssignExpr { lhs, rhs, op, .. } => self.infer_assignment_expr(
                module_idx,
                lhs,
                rhs,
                op,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::BoolExpr {
                span, op, lhs, rhs, ..
            } => self.infer_bool_expr(
                module_idx,
                span,
                op,
                lhs,
                rhs,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::ArithExpr {
                span, op, lhs, rhs, ..
            } => self.infer_arith_expr(
                module_idx,
                span,
                op,
                lhs,
                rhs,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::BinExpr {
                span, op, lhs, rhs, ..
            } => self.infer_bin_expr(
                module_idx,
                span,
                op,
                lhs,
                rhs,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::Membership {
                span,
                value,
                collection,
                ..
            } => self.infer_membership_expr(
                module_idx,
                span,
                value,
                collection,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::UnaryExpr { expr, .. } => {
                self.infer_unary_expr(module_idx, expr, bindings, result, rule_analysis)
            }
            Expr::Call {
                span, fcn, params, ..
            } => self.infer_call_expr(
                module_idx,
                eidx,
                span,
                fcn,
                params,
                bindings,
                result,
                rule_analysis,
            ),
            Expr::RefDot { refr, field, .. } => {
                let base = self.infer_expr(module_idx, refr, bindings, result, rule_analysis);
                if let Some((field_span, field_value)) = field.as_ref() {
                    let mut fact = if let Some(rule_fact) = self.try_resolve_rule_property(
                        module_idx,
                        eidx,
                        refr.as_ref(),
                        field_value,
                        result,
                        rule_analysis,
                    ) {
                        rule_fact
                    } else {
                        self.infer_property_access(
                            module_idx,
                            base.clone(),
                            field_value.clone(),
                            Some(field_span),
                            result,
                        )
                    };

                    if let ConstantValue::Known(base_value) = &base.fact.constant {
                        match base_value {
                            Value::Object(obj) => {
                                if let Value::String(field_name) = field_value {
                                    if let Some(field_const) =
                                        obj.get(&Value::String(field_name.clone()))
                                    {
                                        fact = fact.with_constant(ConstantValue::known(
                                            field_const.clone(),
                                        ));
                                    } else {
                                        fact = fact
                                            .with_constant(ConstantValue::known(Value::Undefined));
                                    }
                                }
                            }
                            Value::Undefined => {
                                fact = fact.with_constant(ConstantValue::known(Value::Undefined));
                            }
                            _ => {}
                        }
                    }

                    if matches!(fact.constant.as_value(), Some(Value::Undefined)) {
                        fact.descriptor = TypeDescriptor::Structural(StructuralType::Unknown);
                    }

                    fact
                } else {
                    base.fact.clone()
                }
            }
            Expr::RefBrack {
                span, refr, index, ..
            } => {
                let index_fact =
                    self.infer_expr(module_idx, index, bindings, result, rule_analysis);
                let base = self.infer_expr(module_idx, refr, bindings, result, rule_analysis);

                // Check for indexing diagnostic issues
                self.check_indexing_diagnostic(module_idx, span, &base, result);

                let base_provenance = match base.fact.provenance {
                    TypeProvenance::SchemaInput => TypeProvenance::SchemaInput,
                    TypeProvenance::SchemaData => TypeProvenance::SchemaData,
                    _ => TypeProvenance::Propagated,
                };
                let index_constant_string = index_fact
                    .fact
                    .constant
                    .as_value()
                    .and_then(|value| value.as_string().ok().map(|s| s.as_ref().to_owned()));
                let mut fact = match &base.fact.descriptor {
                    TypeDescriptor::Schema(schema) => {
                        if let Some((item_schema, schema_constant)) = schema_array_items(schema) {
                            let mut fact = TypeFact::new(
                                TypeDescriptor::Schema(item_schema),
                                base_provenance.clone(),
                            );
                            if let Some(constant) = schema_constant {
                                fact = fact.with_constant(ConstantValue::known(constant));
                            }
                            fact
                        } else if let Some(field_name) = index_constant_string.as_ref() {
                            self.infer_property_access(
                                module_idx,
                                base.clone(),
                                Value::from(field_name.as_str()),
                                Some(index.span()),
                                result,
                            )
                        } else if let Some(additional_schema) =
                            schema_additional_properties_schema(schema)
                        {
                            let mut fact = TypeFact::new(
                                TypeDescriptor::Structural(StructuralType::from_schema(
                                    &additional_schema,
                                )),
                                base_provenance.clone(),
                            );
                            if let Some(constant) = extract_schema_constant(&additional_schema) {
                                fact = fact.with_constant(ConstantValue::known(constant));
                            }
                            fact
                        } else {
                            TypeFact::new(
                                TypeDescriptor::Structural(StructuralType::Any),
                                base_provenance.clone(),
                            )
                        }
                    }
                    TypeDescriptor::Structural(struct_ty) => {
                        if let Some(element_ty) = Self::structural_array_element(struct_ty) {
                            TypeFact::new(
                                TypeDescriptor::Structural(element_ty),
                                TypeProvenance::Propagated,
                            )
                        } else {
                            TypeFact::new(
                                TypeDescriptor::Structural(StructuralType::Any),
                                base_provenance.clone(),
                            )
                        }
                    }
                };

                if !base.fact.origins.is_empty() {
                    let segment = if let Some(value) = index_fact.fact.constant.as_value() {
                        if let Ok(idx) = value.as_u32() {
                            PathSegment::Index(idx as usize)
                        } else if let Ok(field_name) = value.as_string() {
                            PathSegment::Field(field_name.as_ref().to_owned())
                        } else {
                            PathSegment::Any
                        }
                    } else {
                        PathSegment::Any
                    };
                    let origins = extend_origins_with_segment(&base.fact.origins, segment);
                    fact = fact.with_origins(origins);
                }

                if let (ConstantValue::Known(base_value), ConstantValue::Known(index_value)) =
                    (&base.fact.constant, &index_fact.fact.constant)
                {
                    if let Ok(arr) = base_value.as_array() {
                        if let Ok(idx) = index_value.as_u32() {
                            if let Some(element) = arr.get(idx as usize) {
                                fact = fact.with_constant(ConstantValue::known(element.clone()));
                            } else {
                                fact = fact.with_constant(ConstantValue::known(Value::Undefined));
                            }
                        }
                    } else if let Ok(obj) = base_value.as_object() {
                        if let Some(field_value) = obj.get(index_value) {
                            fact = fact.with_constant(ConstantValue::known(field_value.clone()));
                        } else {
                            fact = fact.with_constant(ConstantValue::known(Value::Undefined));
                        }
                    } else if let Ok(set) = base_value.as_set() {
                        let is_member = set.contains(index_value);
                        let origins = fact.origins.clone();
                        fact = TypeFact::new(
                            TypeDescriptor::Structural(StructuralType::Boolean),
                            TypeProvenance::Propagated,
                        )
                        .with_constant(ConstantValue::known(Value::from(is_member)));
                        if !origins.is_empty() {
                            fact = fact.with_origins(origins);
                        }
                    }
                }

                if matches!(fact.constant.as_value(), Some(Value::Undefined)) {
                    fact.descriptor = TypeDescriptor::Structural(StructuralType::Unknown);
                }

                fact
            }
            #[cfg(feature = "rego-extensions")]
            Expr::OrExpr { lhs, rhs, .. } => {
                let _lhs = self.infer_expr(module_idx, lhs, bindings, result, rule_analysis);
                let _rhs = self.infer_expr(module_idx, rhs, bindings, result, rule_analysis);
                TypeFact::new(
                    TypeDescriptor::Structural(StructuralType::Boolean),
                    TypeProvenance::Propagated,
                )
            }
        };

        result.lookup.record_expr(module_idx, eidx, fact.clone());

        if let ConstantValue::Known(value) = &fact.constant {
            result
                .constants
                .record(module_idx, eidx, Some(value.clone()));
        }

        if !fact.origins.is_empty() {
            rule_analysis.record_origins(&fact.origins);
        }

        if let Some(loop_lookup) = self.loop_lookup.as_ref() {
            if let Some(expr_loops) = loop_lookup.get_expr_loops(module_idx, eidx) {
                for loop_info in expr_loops {
                    self.process_hoisted_loop(
                        module_idx,
                        loop_info,
                        bindings,
                        result,
                        rule_analysis,
                    );
                }
            }

            if let Some(plan) = loop_lookup.get_expr_binding_plan(module_idx, eidx) {
                self.apply_binding_plan(
                    module_idx,
                    expr,
                    plan,
                    &fact,
                    bindings,
                    result,
                    rule_analysis,
                );
            }
        }

        HybridType::from_fact(fact)
    }
}

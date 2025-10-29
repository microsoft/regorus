// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;

use crate::lexer::Span;
use crate::type_analysis::model::{
    ConstantValue, HybridType, PathSegment, StructuralType, TypeDescriptor, TypeDiagnostic,
    TypeDiagnosticKind, TypeDiagnosticSeverity, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::{
    extend_origins_with_segment, extract_schema_constant, schema_additional_properties_schema,
    schema_property,
};
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};
use crate::type_analysis::value_utils;
use crate::value::Value;

impl TypeAnalyzer {
    pub(crate) fn infer_property_access(
        &self,
        _module_idx: u32,
        base: HybridType,
        field_value: Value,
        field_span: Option<&Span>,
        result: &mut TypeAnalysisResult,
    ) -> TypeFact {
        let base_provenance = match base.fact.provenance {
            TypeProvenance::SchemaInput => TypeProvenance::SchemaInput,
            TypeProvenance::SchemaData => TypeProvenance::SchemaData,
            _ => TypeProvenance::Propagated,
        };

        if let Value::String(field) = &field_value {
            if let Some(schema) = base.fact.descriptor.as_schema() {
                let missing_prop_severity = Self::schema_missing_property_severity(schema);
                let field_name = field.as_ref();

                if Self::schema_has_named_property(schema, field_name) {
                    if let Some((prop_schema, schema_constant)) =
                        schema_property(schema, field_name)
                    {
                        let mut fact = TypeFact::new(
                            TypeDescriptor::Schema(prop_schema),
                            base_provenance.clone(),
                        );

                        if let Some(constant) = schema_constant {
                            fact = fact.with_constant(ConstantValue::known(constant.clone()));
                            let structural_descriptor =
                                value_utils::value_to_type_fact(&constant).descriptor;
                            fact.descriptor = structural_descriptor;
                        }

                        if !base.fact.origins.is_empty() {
                            let origins = extend_origins_with_segment(
                                &base.fact.origins,
                                PathSegment::Field(field_name.to_owned()),
                            );
                            fact = fact.with_origins(origins);
                        }

                        return fact;
                    }
                } else {
                    if let Some(span) = field_span {
                        if let Some(message) =
                            Self::schema_missing_property_message(schema, field_name)
                        {
                            let (line, col, end_line, end_col) =
                                Self::diagnostic_range_from_span(span);
                            result.diagnostics.push(TypeDiagnostic {
                                file: span.source.get_path().as_str().into(),
                                message,
                                kind: TypeDiagnosticKind::SchemaViolation,
                                severity: missing_prop_severity,
                                line,
                                col,
                                end_line,
                                end_col,
                            });
                        }
                    }

                    if let Some(additional_schema) = schema_additional_properties_schema(schema) {
                        let mut fact = TypeFact::new(
                            TypeDescriptor::Schema(additional_schema.clone()),
                            base_provenance.clone(),
                        );
                        if let Some(constant) = extract_schema_constant(&additional_schema) {
                            fact = fact.with_constant(ConstantValue::known(constant.clone()));
                            let structural_descriptor =
                                value_utils::value_to_type_fact(&constant).descriptor;
                            fact.descriptor = structural_descriptor;
                        }
                        if !base.fact.origins.is_empty() {
                            let origins = extend_origins_with_segment(
                                &base.fact.origins,
                                PathSegment::Field(field_name.to_owned()),
                            );
                            fact = fact.with_origins(origins);
                        }

                        return fact;
                    }
                }
            }

            if let TypeDescriptor::Structural(struct_ty) = &base.fact.descriptor {
                if let Some(field_ty) = Self::structural_field_type(struct_ty, field.as_ref()) {
                    let mut fact = TypeFact::new(
                        TypeDescriptor::Structural(field_ty),
                        TypeProvenance::Propagated,
                    );

                    if !base.fact.origins.is_empty() {
                        let origins = extend_origins_with_segment(
                            &base.fact.origins,
                            PathSegment::Field(field.as_ref().to_owned()),
                        );
                        fact = fact.with_origins(origins);
                    }

                    return fact;
                } else if let Some(message) =
                    Self::structural_missing_property_message(struct_ty, field.as_ref())
                {
                    if let Some(span) = field_span {
                        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);
                        result.diagnostics.push(TypeDiagnostic {
                            file: span.source.get_path().as_str().into(),
                            message,
                            kind: TypeDiagnosticKind::SchemaViolation,
                            severity: TypeDiagnosticSeverity::Error,
                            line,
                            col,
                            end_line,
                            end_col,
                        });
                    }
                }
            }
        }

        let fallback_ty = match &base.fact.descriptor {
            TypeDescriptor::Schema(_) => StructuralType::Any,
            TypeDescriptor::Structural(_) => StructuralType::Unknown,
        };

        TypeFact::new(TypeDescriptor::Structural(fallback_ty), base_provenance)
    }
}

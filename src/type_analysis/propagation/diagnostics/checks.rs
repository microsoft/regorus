// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::String;

use crate::ast::{ArithOp, BinOp, BoolOp};
use crate::lexer::Span;
use crate::type_analysis::model::{
    HybridType, TypeDiagnostic, TypeDiagnosticKind, TypeDiagnosticSeverity,
};
use crate::value::Value;

use super::super::facts::schema_allows_value;
use super::super::pipeline::{TypeAnalysisResult, TypeAnalyzer};

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_equality_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        op: &BoolOp,
        lhs: &HybridType,
        rhs: &HybridType,
        result: &mut TypeAnalysisResult,
    ) {
        if !matches!(op, BoolOp::Eq) {
            return;
        }

        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);

        let (schema_side, const_side) = match (
            lhs.fact.descriptor.as_schema(),
            lhs.fact.constant.as_value(),
            rhs.fact.descriptor.as_schema(),
            rhs.fact.constant.as_value(),
        ) {
            (Some(schema), _, _, Some(constant)) => (Some(schema), Some(constant)),
            (_, Some(constant), Some(schema), _) => (Some(schema), Some(constant)),
            _ => (None, None),
        };

        if let (Some(schema), Some(constant)) = (schema_side, const_side) {
            if !schema_allows_value(schema, constant) {
                result.diagnostics.push(TypeDiagnostic {
                    message: format!("value {} is not allowed by schema enumeration", constant),
                    kind: TypeDiagnosticKind::SchemaViolation,
                    severity: TypeDiagnosticSeverity::Error,
                    file: self.get_file_for_module(module_idx),
                    line,
                    col,
                    end_line,
                    end_col,
                });
            }
        }

        let lhs_struct = Self::hybrid_structural_type(lhs);
        let rhs_struct = Self::hybrid_structural_type(rhs);

        if Self::structural_types_certainly_disjoint(&lhs_struct, &rhs_struct) {
            let lhs_label = Self::hybrid_type_display(lhs);
            let rhs_label = Self::hybrid_type_display(rhs);
            result.diagnostics.push(TypeDiagnostic {
                message: format!(
                    "equality comparison between incompatible types: {} == {}",
                    lhs_label, rhs_label
                ),
                kind: TypeDiagnosticKind::TypeMismatch,
                severity: TypeDiagnosticSeverity::Warning,
                file: self.get_file_for_module(module_idx),
                line,
                col,
                end_line,
                end_col,
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_arithmetic_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        op: &ArithOp,
        lhs: &HybridType,
        rhs: &HybridType,
        result: &mut TypeAnalysisResult,
    ) {
        use ArithOp::*;

        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);

        if matches!(lhs.fact.constant.as_value(), Some(Value::Undefined))
            || matches!(rhs.fact.constant.as_value(), Some(Value::Undefined))
        {
            return;
        }

        let lhs_can_be_numeric = Self::hybrid_can_be_numeric(lhs);
        let rhs_can_be_numeric = Self::hybrid_can_be_numeric(rhs);
        let lhs_can_be_set = Self::hybrid_can_be_set(lhs);
        let rhs_can_be_set = Self::hybrid_can_be_set(rhs);
        let lhs_can_be_integer = Self::hybrid_can_be_integer(lhs);
        let rhs_can_be_integer = Self::hybrid_can_be_integer(rhs);

        let (should_warn, message) = match op {
            Add | Mul | Div => {
                if lhs_can_be_numeric && rhs_can_be_numeric {
                    (false, String::new())
                } else {
                    let lhs_label = Self::hybrid_type_display(lhs);
                    let rhs_label = Self::hybrid_type_display(rhs);
                    (
                        true,
                        format!(
                            "operator {} expects numeric operands; got {} and {}",
                            Self::arithmetic_op_token(op),
                            lhs_label,
                            rhs_label
                        ),
                    )
                }
            }
            Mod => {
                if lhs_can_be_integer && rhs_can_be_integer {
                    (false, String::new())
                } else {
                    let lhs_label = Self::hybrid_type_display(lhs);
                    let rhs_label = Self::hybrid_type_display(rhs);
                    (
                        true,
                        format!(
                            "operator % expects integer operands; got {} and {}",
                            lhs_label, rhs_label
                        ),
                    )
                }
            }
            Sub => {
                let numeric_possible = lhs_can_be_numeric && rhs_can_be_numeric;
                let set_possible = lhs_can_be_set && rhs_can_be_set;

                if numeric_possible || set_possible {
                    (false, String::new())
                } else {
                    let lhs_label = Self::hybrid_type_display(lhs);
                    let rhs_label = Self::hybrid_type_display(rhs);
                    (
                        true,
                        format!(
                            "operator - expects both operands to be numbers or both to be sets; got {} and {}",
                            lhs_label, rhs_label
                        ),
                    )
                }
            }
        };

        if should_warn {
            result.diagnostics.push(TypeDiagnostic {
                message,
                kind: TypeDiagnosticKind::TypeMismatch,
                severity: TypeDiagnosticSeverity::Warning,
                file: self.get_file_for_module(module_idx),
                line,
                col,
                end_line,
                end_col,
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_set_operation_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        op: &BinOp,
        lhs: &HybridType,
        rhs: &HybridType,
        result: &mut TypeAnalysisResult,
    ) {
        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);

        let lhs_can_be_set = Self::hybrid_can_be_set(lhs);
        let rhs_can_be_set = Self::hybrid_can_be_set(rhs);

        if lhs_can_be_set && rhs_can_be_set {
            return;
        }

        let op_label = match op {
            BinOp::Union => "|",
            BinOp::Intersection => "&",
        };

        let lhs_label = Self::hybrid_type_display(lhs);
        let rhs_label = Self::hybrid_type_display(rhs);

        let message = match (lhs_can_be_set, rhs_can_be_set) {
            (false, false) => format!(
                "operator {} expects set operands; got {} and {}",
                op_label, lhs_label, rhs_label
            ),
            (false, true) => format!(
                "operator {} expects left operand to be a set; got {}",
                op_label, lhs_label
            ),
            (true, false) => format!(
                "operator {} expects right operand to be a set; got {}",
                op_label, rhs_label
            ),
            (true, true) => return,
        };

        result.diagnostics.push(TypeDiagnostic {
            message,
            kind: TypeDiagnosticKind::TypeMismatch,
            severity: TypeDiagnosticSeverity::Warning,
            file: self.get_file_for_module(module_idx),
            line,
            col,
            end_line,
            end_col,
        });
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_membership_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        value: &HybridType,
        collection: &HybridType,
        result: &mut TypeAnalysisResult,
    ) {
        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);
        let collection_struct = Self::hybrid_structural_type(collection);

        if !Self::hybrid_can_be_collection(collection) {
            let collection_label = Self::hybrid_type_display(collection);
            result.diagnostics.push(TypeDiagnostic {
                message: format!(
                    "'in' operator requires collection (array, set, or object); got {}",
                    collection_label
                ),
                kind: TypeDiagnosticKind::TypeMismatch,
                severity: TypeDiagnosticSeverity::Warning,
                file: self.get_file_for_module(module_idx),
                line,
                col,
                end_line,
                end_col,
            });
            return;
        }

        // Check element type compatibility for arrays and sets
        let value_struct = Self::hybrid_structural_type(value);

        let element_type = match &collection_struct {
            crate::type_analysis::model::StructuralType::Array(elem)
            | crate::type_analysis::model::StructuralType::Set(elem) => Some(elem.as_ref()),
            _ => None,
        };

        if let Some(elem_ty) = element_type {
            if Self::structural_types_certainly_disjoint(&value_struct, elem_ty) {
                let value_label = Self::hybrid_type_display(value);
                let elem_label = Self::structural_type_display(elem_ty);
                result.diagnostics.push(TypeDiagnostic {
                    message: format!(
                        "'in' operator: element type {} is incompatible with collection element type {}",
                        value_label, elem_label
                    ),
                    kind: TypeDiagnosticKind::TypeMismatch,
                    severity: TypeDiagnosticSeverity::Warning,
                    file: self.get_file_for_module(module_idx),
                    line,
                    col,
                    end_line,
                    end_col,
                });
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_indexing_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        base: &HybridType,
        result: &mut TypeAnalysisResult,
    ) {
        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);
        let base_struct = Self::hybrid_structural_type(base);

        let can_be_indexed = match &base_struct {
            crate::type_analysis::model::StructuralType::Array(_)
            | crate::type_analysis::model::StructuralType::Set(_)
            | crate::type_analysis::model::StructuralType::Object(_)
            | crate::type_analysis::model::StructuralType::String => true,
            crate::type_analysis::model::StructuralType::Union(variants) => {
                variants.iter().any(|v| {
                    matches!(
                        v,
                        crate::type_analysis::model::StructuralType::Array(_)
                            | crate::type_analysis::model::StructuralType::Set(_)
                            | crate::type_analysis::model::StructuralType::Object(_)
                            | crate::type_analysis::model::StructuralType::String
                    )
                })
            }
            crate::type_analysis::model::StructuralType::Any
            | crate::type_analysis::model::StructuralType::Unknown => true,
            _ => false,
        };

        if !can_be_indexed {
            let base_label = Self::hybrid_type_display(base);
            result.diagnostics.push(TypeDiagnostic {
                message: format!(
                    "cannot index into {}; indexing requires array, set, object, or string",
                    base_label
                ),
                kind: TypeDiagnosticKind::TypeMismatch,
                severity: TypeDiagnosticSeverity::Warning,
                file: self.get_file_for_module(module_idx),
                line,
                col,
                end_line,
                end_col,
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_builtin_call_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        builtin_name: &str,
        expected_params: usize,
        actual_params: usize,
        result: &mut TypeAnalysisResult,
    ) {
        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);
        if expected_params != actual_params {
            result.diagnostics.push(TypeDiagnostic {
                message: format!(
                    "builtin '{}' expects {} parameter(s), got {}",
                    builtin_name, expected_params, actual_params
                ),
                kind: TypeDiagnosticKind::TypeMismatch,
                severity: TypeDiagnosticSeverity::Warning,
                file: self.get_file_for_module(module_idx),
                line,
                col,
                end_line,
                end_col,
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_builtin_param_type_diagnostic(
        &self,
        module_idx: u32,
        span: &Span,
        builtin_name: &str,
        param_idx: usize,
        expected_type: &str,
        actual: &HybridType,
        result: &mut TypeAnalysisResult,
    ) {
        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);
        let actual_label = Self::hybrid_type_display(actual);
        result.diagnostics.push(TypeDiagnostic {
            message: format!(
                "builtin '{}' parameter {} expects {}, got {}",
                builtin_name,
                param_idx + 1,
                expected_type,
                actual_label
            ),
            kind: TypeDiagnosticKind::TypeMismatch,
            severity: TypeDiagnosticSeverity::Warning,
            file: self.get_file_for_module(module_idx),
            line,
            col,
            end_line,
            end_col,
        });
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_builtin_additional_rules(
        &self,
        module_idx: u32,
        span: &Span,
        builtin_name: &str,
        args: &[HybridType],
        result: &mut TypeAnalysisResult,
    ) {
        let (line, col, end_line, end_col) = Self::diagnostic_range_from_span(span);
        if builtin_name == "count" {
            if let Some(arg) = args.first() {
                if !Self::hybrid_can_be_collection(arg) {
                    let arg_label = Self::hybrid_type_display(arg);
                    result.diagnostics.push(TypeDiagnostic {
                        message: format!(
                            "builtin 'count' expects array, set, or object; got {}",
                            arg_label
                        ),
                        kind: TypeDiagnosticKind::TypeMismatch,
                        severity: TypeDiagnosticSeverity::Warning,
                        file: self.get_file_for_module(module_idx),
                        line,
                        col,
                        end_line,
                        end_col,
                    });
                }
            }
        }
    }
}

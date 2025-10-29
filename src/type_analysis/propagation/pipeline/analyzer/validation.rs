// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::{borrow::ToOwned, collections::BTreeMap, format, string::String};

use crate::ast::{Rule, RuleHead};
use crate::lexer::Span;
use crate::type_analysis::model::{TypeDiagnostic, TypeDiagnosticKind, TypeDiagnosticSeverity};
use crate::utils::get_path_string;

use super::super::result::AnalysisState;
use super::TypeAnalyzer;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuleKind {
    Complete,
    PartialSet,
    PartialObject,
    Function,
}

impl TypeAnalyzer {
    /// Validate rule definitions for semantic errors:
    /// 1. Default rules cannot be used with partial set/object rules
    /// 2. All definitions of a rule must have the same type (complete/set/function)
    pub(super) fn validate_rule_definitions(&self, result: &mut AnalysisState) {
        let mut rule_types: BTreeMap<String, (RuleKind, u32, Span)> = BTreeMap::new();

        for (module_idx, module) in self.modules.iter().enumerate() {
            let module_idx = module_idx as u32;
            let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
                .unwrap_or_else(|_| "data".to_owned());

            for rule in &module.policy {
                if let Rule::Spec { head, span, .. } = rule.as_ref() {
                    let span_ref = span;
                    if let Some(refr) = Self::rule_head_expression(head) {
                        if let Ok(mut rule_path) = get_path_string(refr.as_ref(), None) {
                            if !rule_path.starts_with("data.") {
                                rule_path = format!("{module_path}.{rule_path}");
                            }

                            let kind = Self::classify_rule_head(head);

                            if let Some((existing_kind, _, first_span)) = rule_types.get(&rule_path)
                            {
                                if !Self::rule_kinds_compatible(existing_kind, &kind) {
                                    let (line, col, end_line, end_col) =
                                        Self::diagnostic_range_from_span(span_ref);
                                    result.diagnostics.push(TypeDiagnostic {
                                        file: span.source.get_path().as_str().into(),
                                        message: format!(
                                            "Rule '{}' has inconsistent types: {} and {}. All definitions of a rule must have the same type.",
                                            rule_path.rsplit('.').next().unwrap_or(&rule_path),
                                            Self::rule_kind_name(existing_kind),
                                            Self::rule_kind_name(&kind)
                                        ),
                                        kind: TypeDiagnosticKind::SchemaViolation,
                                        severity: TypeDiagnosticSeverity::Error,
                                        line,
                                        col,
                                        end_line,
                                        end_col,
                                    });

                                    let (first_line, first_col, first_end_line, first_end_col) =
                                        Self::diagnostic_range_from_span(first_span);
                                    result.diagnostics.push(TypeDiagnostic {
                                        file: first_span.source.get_path().as_str().into(),
                                        message: format!(
                                            "First defined as {} here",
                                            Self::rule_kind_name(existing_kind)
                                        ),
                                        kind: TypeDiagnosticKind::InternalError,
                                        severity: TypeDiagnosticSeverity::Warning,
                                        line: first_line,
                                        col: first_col,
                                        end_line: first_end_line,
                                        end_col: first_end_col,
                                    });
                                }
                            } else {
                                rule_types.insert(rule_path, (kind, module_idx, span.clone()));
                            }
                        }
                    }
                }
            }
        }

        for module in self.modules.iter() {
            let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
                .unwrap_or_else(|_| "data".to_owned());

            for rule in &module.policy {
                if let Rule::Default { refr, span, .. } = rule.as_ref() {
                    let span_ref = span;
                    if let Ok(mut rule_path) = get_path_string(refr.as_ref(), None) {
                        if !rule_path.starts_with("data.") {
                            rule_path = format!("{module_path}.{rule_path}");
                        }

                        let base_path = rule_path
                            .strip_suffix(".default")
                            .unwrap_or(&rule_path)
                            .to_owned();

                        if let Some((kind, _, _)) = rule_types.get(&base_path) {
                            if matches!(kind, RuleKind::PartialSet | RuleKind::PartialObject) {
                                let (line, col, end_line, end_col) =
                                    Self::diagnostic_range_from_span(span_ref);
                                result.diagnostics.push(TypeDiagnostic {
                                    file: span.source.get_path().as_str().into(),
                                    message: format!(
                                        "Default rule cannot be used with partial {} rules. Default rules are only allowed for complete rules.",
                                        if matches!(kind, RuleKind::PartialSet) {
                                            "set"
                                        } else {
                                            "object"
                                        }
                                    ),
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
            }
        }
    }

    fn classify_rule_head(head: &RuleHead) -> RuleKind {
        match head {
            RuleHead::Compr { .. } => RuleKind::Complete,
            RuleHead::Set { key: Some(_), .. } => RuleKind::PartialSet,
            RuleHead::Set { key: None, .. } => RuleKind::PartialObject,
            RuleHead::Func { .. } => RuleKind::Function,
        }
    }

    fn rule_kinds_compatible(a: &RuleKind, b: &RuleKind) -> bool {
        matches!(
            (a, b),
            (RuleKind::Complete, RuleKind::Complete)
                | (RuleKind::PartialSet, RuleKind::PartialSet)
                | (RuleKind::PartialObject, RuleKind::PartialObject)
                | (RuleKind::Function, RuleKind::Function)
        )
    }

    fn rule_kind_name(kind: &RuleKind) -> &'static str {
        match kind {
            RuleKind::Complete => "complete rule",
            RuleKind::PartialSet => "partial set rule",
            RuleKind::PartialObject => "partial object rule",
            RuleKind::Function => "function",
        }
    }
}

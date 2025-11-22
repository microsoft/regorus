// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;

use crate::ast::Query;
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    RuleAnalysis, TypeDiagnostic, TypeDiagnosticKind, TypeDiagnosticSeverity,
};
use crate::type_analysis::propagation::expressions::StatementTruth;

use super::super::super::result::AnalysisState;
use super::super::TypeAnalyzer;

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct QueryEvaluation {
    pub reachable: bool,
    pub always_true: bool,
}

impl TypeAnalyzer {
    pub(crate) fn analyze_query(
        &self,
        module_idx: u32,
        query: &crate::ast::Ref<Query>,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
        allow_unreachable_diag: bool,
    ) -> QueryEvaluation {
        let order = self
            .schedule
            .as_ref()
            .and_then(|schedule| schedule.queries.get(module_idx, query.qidx))
            .map(|qs| qs.order.clone())
            .unwrap_or_else(|| (0..query.stmts.len() as u16).collect());

        let mut eval = QueryEvaluation {
            reachable: true,
            always_true: true,
        };
        for stmt_idx in order {
            if let Some(stmt) = query.stmts.get(stmt_idx as usize) {
                self.seed_statement_loops(module_idx, stmt, bindings, result, rule_analysis);
                let truth = self.analyze_stmt(module_idx, stmt, bindings, result, rule_analysis);
                if !matches!(truth, StatementTruth::AlwaysTrue) {
                    eval.always_true = false;
                }

                if matches!(truth, StatementTruth::AlwaysFalse) {
                    if allow_unreachable_diag {
                        let (line, col, end_line, end_col) =
                            Self::diagnostic_range_from_span(&stmt.span);
                        result.diagnostics.push(TypeDiagnostic {
                            file: stmt.span.source.get_path().as_str().into(),
                            message: String::from(
                                "Statement always evaluates to false; later statements were skipped",
                            ),
                            kind: TypeDiagnosticKind::UnreachableStatement,
                            severity: TypeDiagnosticSeverity::Warning,
                            line,
                            col,
                            end_line,
                            end_col,
                        });
                    }
                    eval.reachable = false;
                    break;
                }
            }
        }

        eval
    }

    pub(crate) fn ensure_expr_capacity(
        &self,
        module_idx: u32,
        expr_idx: u32,
        result: &mut AnalysisState,
    ) {
        result.lookup.ensure_expr_capacity(module_idx, expr_idx);
        result.constants.ensure_capacity(module_idx, expr_idx);
    }
}

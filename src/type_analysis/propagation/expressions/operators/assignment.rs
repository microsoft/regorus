// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;

use crate::ast::{AssignOp, Expr, Ref};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::mark_origins_derived;
use crate::type_analysis::propagation::pipeline::{TypeAnalysisResult, TypeAnalyzer};

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_assignment_expr(
        &self,
        module_idx: u32,
        lhs: &Ref<Expr>,
        rhs: &Ref<Expr>,
        _op: &AssignOp,
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let rhs_fact = self.infer_expr(module_idx, rhs, bindings, result, rule_analysis);

        if let Expr::Var { value, .. } = lhs.as_ref() {
            if let Ok(name) = value.as_string() {
                bindings.ensure_root_scope();
                bindings.assign(name.as_ref().to_owned(), rhs_fact.fact.clone());
            }
        }

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Boolean),
            TypeProvenance::Assignment,
        );

        if !rhs_fact.fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&rhs_fact.fact.origins));
        }

        fact
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Comprehension expression type inference (array, set, object comprehensions)

use alloc::boxed::Box;
use alloc::collections::BTreeMap;

use crate::ast::{Expr, Query, Ref};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    RuleAnalysis, StructuralObjectShape, StructuralType, TypeDescriptor, TypeFact,
};
use crate::type_analysis::propagation::facts::mark_origins_derived;

use super::super::pipeline::AnalysisState;
use super::super::pipeline::TypeAnalyzer;

impl TypeAnalyzer {
    pub(crate) fn infer_array_comprehension(
        &self,
        module_idx: u32,
        term: &Ref<Expr>,
        query: &Ref<Query>,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        bindings.push_scope();
        let _ = self.analyze_query(module_idx, query, bindings, result, rule_analysis, true);
        let term_type = self.infer_expr(module_idx, term, bindings, result, rule_analysis);
        bindings.pop_scope();

        let element_structural = match term_type.fact.descriptor {
            TypeDescriptor::Schema(ref schema) => StructuralType::from_schema(schema),
            TypeDescriptor::Structural(ref st) => st.clone(),
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Array(Box::new(element_structural))),
            term_type.fact.provenance.clone(),
        );

        if !term_type.fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&term_type.fact.origins));
        }

        fact
    }

    pub(crate) fn infer_set_comprehension(
        &self,
        module_idx: u32,
        term: &Ref<Expr>,
        query: &Ref<Query>,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        bindings.push_scope();
        let _ = self.analyze_query(module_idx, query, bindings, result, rule_analysis, true);
        let term_type = self.infer_expr(module_idx, term, bindings, result, rule_analysis);
        bindings.pop_scope();

        let element_structural = match term_type.fact.descriptor {
            TypeDescriptor::Schema(ref schema) => StructuralType::from_schema(schema),
            TypeDescriptor::Structural(ref st) => st.clone(),
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Set(Box::new(element_structural))),
            term_type.fact.provenance.clone(),
        );

        if !term_type.fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&term_type.fact.origins));
        }

        fact
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_object_comprehension(
        &self,
        module_idx: u32,
        key: &Ref<Expr>,
        value: &Ref<Expr>,
        query: &Ref<Query>,
        bindings: &mut ScopedBindings,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        bindings.push_scope();
        let _ = self.analyze_query(module_idx, query, bindings, result, rule_analysis, true);
        let _key_type = self.infer_expr(module_idx, key, bindings, result, rule_analysis);
        let value_type = self.infer_expr(module_idx, value, bindings, result, rule_analysis);
        bindings.pop_scope();

        let shape = StructuralObjectShape {
            fields: BTreeMap::new(),
        };

        let mut fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Object(shape)),
            value_type.fact.provenance.clone(),
        );

        if !value_type.fact.origins.is_empty() {
            fact = fact.with_origins(mark_origins_derived(&value_type.fact.origins));
        }

        fact
    }
}

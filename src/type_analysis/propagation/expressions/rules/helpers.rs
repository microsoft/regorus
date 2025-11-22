// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

use crate::type_analysis::model::{
    SourceOrigin, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::pipeline::TypeAnalyzer;

impl TypeAnalyzer {
    pub(crate) fn merge_rule_facts(facts: &[TypeFact]) -> TypeFact {
        if facts.is_empty() {
            return TypeFact::new(
                TypeDescriptor::Structural(StructuralType::Any),
                TypeProvenance::Unknown,
            );
        }

        if facts.len() == 1 {
            return facts[0].clone();
        }

        let mut structural_types = Vec::with_capacity(facts.len());
        let mut origins: Vec<SourceOrigin> = Vec::new();
        let mut specialization_hits = Vec::new();
        let provenance = facts[0].provenance.clone();

        for fact in facts {
            let structural = match &fact.descriptor {
                TypeDescriptor::Structural(st) => st.clone(),
                TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
            };
            structural_types.push(structural);
            if !fact.origins.is_empty() {
                origins.extend(fact.origins.clone());
            }
            if !fact.specialization_hits.is_empty() {
                specialization_hits.extend(fact.specialization_hits.clone());
            }
        }

        let merged_type = Self::join_structural_types(&structural_types);
        let mut merged_fact = TypeFact::new(TypeDescriptor::Structural(merged_type), provenance);

        if !origins.is_empty() {
            merged_fact = merged_fact.with_origins(origins);
        }

        if !specialization_hits.is_empty() {
            merged_fact = merged_fact.with_specialization_hits(specialization_hits);
        }

        merged_fact
    }
}

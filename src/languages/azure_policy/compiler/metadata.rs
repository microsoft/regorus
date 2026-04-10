// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]

//! Annotation accumulation and metadata population.
//!
//! Stub — real implementation added in a later commit.

use crate::languages::azure_policy::ast::{EffectNode, OperatorKind, PolicyDefinition, PolicyRule};

use super::core::Compiler;

impl Compiler {
    pub(super) const fn record_field_kind(&mut self, _name: &str) {
        _ = self.register_counter;
    }
    pub(super) const fn record_alias(&mut self, _path: &str) {
        _ = self.register_counter;
    }
    pub(super) const fn record_tag_name(&mut self, _tag: &str) {
        _ = self.register_counter;
    }
    pub(super) const fn record_operator(&mut self, _kind: &OperatorKind) {
        _ = self.register_counter;
    }
    pub(super) const fn record_resource_type_from_condition(
        &mut self,
        _condition: &crate::languages::azure_policy::ast::Condition,
    ) {
        _ = self.register_counter;
    }

    #[allow(clippy::unused_self)]
    pub(super) fn resolve_effect_annotation(&self, rule: &PolicyRule) -> alloc::string::String {
        rule.then_block.effect.raw.clone()
    }

    #[allow(clippy::unused_self)]
    pub(super) fn resolve_effect_kind(
        &self,
        effect: &EffectNode,
    ) -> crate::languages::azure_policy::ast::EffectKind {
        effect.kind.clone()
    }

    pub(super) const fn populate_compiled_annotations(&mut self) {
        _ = self.register_counter;
    }
    pub(super) const fn populate_definition_metadata(&mut self, _defn: &PolicyDefinition) {
        _ = self.register_counter;
    }
}

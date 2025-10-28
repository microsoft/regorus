// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, SourceOrigin, SourceRoot, StructuralObjectShape, StructuralType,
    TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::facts::extract_schema_constant;
use crate::type_analysis::propagation::pipeline::{RuleHeadInfo, TypeAnalysisResult, TypeAnalyzer};
use crate::utils::get_path_string;
use crate::utils::path::normalize_rule_path;
use crate::value::Value;

impl TypeAnalyzer {
    pub(crate) fn infer_var(
        &self,
        module_idx: u32,
        expr_idx: u32,
        value: &Value,
        bindings: &ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let name = match value.as_string() {
            Ok(name) => name.as_ref().to_owned(),
            Err(_) => {
                return TypeFact::new(
                    TypeDescriptor::Structural(StructuralType::Any),
                    TypeProvenance::Unknown,
                )
            }
        };
        if name == "input" {
            let mut fact = if let Some(schema) = &self.options.input_schema {
                let mut fact = TypeFact::new(
                    TypeDescriptor::Schema(schema.clone()),
                    TypeProvenance::SchemaInput,
                );
                if let Some(constant) = extract_schema_constant(schema) {
                    fact = fact.with_constant(ConstantValue::known(constant));
                }
                fact
            } else {
                TypeFact::new(
                    TypeDescriptor::Structural(StructuralType::Any),
                    TypeProvenance::SchemaInput,
                )
            };
            fact.origins.push(SourceOrigin::new(SourceRoot::Input));
            return fact;
        } else if name == "data" {
            let mut fact = if let Some(schema) = &self.options.data_schema {
                let mut fact = TypeFact::new(
                    TypeDescriptor::Schema(schema.clone()),
                    TypeProvenance::SchemaData,
                );
                if let Some(constant) = extract_schema_constant(schema) {
                    fact = fact.with_constant(ConstantValue::known(constant));
                }
                fact
            } else {
                TypeFact::new(
                    TypeDescriptor::Structural(StructuralType::Any),
                    TypeProvenance::SchemaData,
                )
            };
            fact.origins.push(SourceOrigin::new(SourceRoot::Data));
            return fact;
        }

        if let Some(fact) = bindings.lookup(&name) {
            return fact.clone();
        }

        let rule_infos = self.rule_heads_for_name(module_idx, &name);
        let current_rule_info = result.lookup.current_rule().map(|path| {
            let normalized = normalize_rule_path(path);
            let base = normalized
                .strip_suffix(".default")
                .unwrap_or(&normalized)
                .to_owned();
            (normalized, base)
        });

        if let Some(fact) = self.collect_rule_facts_from_infos(
            module_idx,
            expr_idx,
            rule_infos,
            current_rule_info.as_ref(),
            result,
            rule_analysis,
        ) {
            return fact;
        }

        if let Some(fact) = self.collect_rule_object_fact(
            module_idx,
            expr_idx,
            &name,
            current_rule_info.as_ref(),
            result,
            rule_analysis,
        ) {
            return fact;
        }

        TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Any),
            TypeProvenance::Unknown,
        )
    }

    fn collect_rule_object_fact(
        &self,
        module_idx: u32,
        expr_idx: u32,
        name: &str,
        current_rule_info: Option<&(String, String)>,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> Option<TypeFact> {
        let mut prefixes: Vec<String> = Vec::new();

        if let Some(module) = self.modules.get(module_idx as usize) {
            if let Ok(module_path) = get_path_string(module.package.refr.as_ref(), Some("data")) {
                prefixes.push(format!("{module_path}.{name}"));
            }
        }

        prefixes.push(format!("data.{name}"));
        prefixes.sort();
        prefixes.dedup();

        let mut field_facts: BTreeMap<String, Vec<TypeFact>> = BTreeMap::new();
        let mut processed_paths: BTreeSet<String> = BTreeSet::new();

        for prefix in prefixes {
            let normalized_prefix = normalize_rule_path(&prefix);

            for info in self.rule_heads_with_prefix(module_idx, &prefix) {
                let normalized_path = normalize_rule_path(&info.path);
                let dependency_base = normalized_path
                    .strip_suffix(".default")
                    .unwrap_or(normalized_path.as_str())
                    .to_owned();

                if !dependency_base.starts_with(&normalized_prefix) {
                    continue;
                }

                if let Some((current_norm, current_base)) = current_rule_info {
                    if normalized_path == *current_norm || dependency_base == *current_base {
                        continue;
                    }
                }

                let remainder = dependency_base[normalized_prefix.len()..].strip_prefix('.');
                let Some(remainder) = remainder else {
                    continue;
                };

                let field_name = remainder.split('.').next().unwrap_or("").to_owned();
                if field_name.is_empty() {
                    continue;
                }

                let first_encounter = processed_paths.insert(normalized_path.clone());

                if first_encounter {
                    result.lookup.record_rule_reference(
                        module_idx,
                        expr_idx,
                        normalized_path.clone(),
                    );
                    rule_analysis.record_rule_dependency(normalized_path.clone());
                }

                let mut head_fact = result
                    .lookup
                    .get_expr(info.module_idx, info.expr_idx)
                    .cloned();
                if head_fact.is_none() {
                    self.ensure_all_rule_definitions_analyzed(&info.path, result);
                    head_fact = result
                        .lookup
                        .get_expr(info.module_idx, info.expr_idx)
                        .cloned();
                }

                if let Some(fact) = head_fact {
                    field_facts
                        .entry(field_name.clone())
                        .or_default()
                        .push(fact);
                }
            }
        }

        if field_facts.is_empty() {
            return None;
        }

        let mut shape = StructuralObjectShape::new();
        let mut aggregated_origins: Vec<SourceOrigin> = Vec::new();

        for (field, facts) in field_facts {
            if facts.is_empty() {
                continue;
            }

            let merged = if facts.len() == 1 {
                facts.into_iter().next().unwrap()
            } else {
                Self::merge_rule_facts(&facts)
            };

            let structural = match &merged.descriptor {
                TypeDescriptor::Structural(st) => st.clone(),
                TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
            };

            shape.fields.insert(field, structural);

            if !merged.origins.is_empty() {
                for origin in merged.origins.iter() {
                    if !aggregated_origins.contains(origin) {
                        aggregated_origins.push(origin.clone());
                    }
                }
            }
        }

        if shape.fields.is_empty() {
            return None;
        }

        let mut object_fact = TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Object(shape)),
            TypeProvenance::Rule,
        );

        if !aggregated_origins.is_empty() {
            object_fact = object_fact.with_origins(aggregated_origins);
        }

        Some(object_fact)
    }

    fn collect_rule_facts_from_infos(
        &self,
        module_idx: u32,
        expr_idx: u32,
        infos: Vec<&RuleHeadInfo>,
        current_rule_info: Option<&(String, String)>,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> Option<TypeFact> {
        if infos.is_empty() {
            return None;
        }

        let mut facts_by_base: BTreeMap<String, Vec<TypeFact>> = BTreeMap::new();
        let mut processed_paths: BTreeSet<String> = BTreeSet::new();

        for info in infos {
            let normalized_path = normalize_rule_path(&info.path);
            let dependency_base = normalized_path
                .strip_suffix(".default")
                .unwrap_or(normalized_path.as_str())
                .to_owned();

            if let Some((current_norm, current_base)) = current_rule_info {
                if normalized_path == *current_norm || dependency_base == *current_base {
                    continue;
                }
            }

            let first_encounter = processed_paths.insert(normalized_path.clone());

            if first_encounter {
                result
                    .lookup
                    .record_rule_reference(module_idx, expr_idx, normalized_path.clone());
                rule_analysis.record_rule_dependency(normalized_path.clone());
            }

            let mut head_fact = result
                .lookup
                .get_expr(info.module_idx, info.expr_idx)
                .cloned();
            if head_fact.is_none() {
                self.ensure_all_rule_definitions_analyzed(&info.path, result);
                head_fact = result
                    .lookup
                    .get_expr(info.module_idx, info.expr_idx)
                    .cloned();
            }

            if let Some(fact) = head_fact {
                facts_by_base
                    .entry(dependency_base.clone())
                    .or_default()
                    .push(fact);
            }
        }

        if facts_by_base.is_empty() {
            return None;
        }

        let mut merged = Vec::new();
        for (_base, mut facts) in facts_by_base {
            if facts.len() == 1 {
                merged.push(facts.pop().unwrap());
            } else {
                merged.push(Self::merge_rule_facts(&facts));
            }
        }

        Some(Self::merge_rule_facts(&merged))
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::{
    borrow::ToOwned,
    collections::{BTreeMap, BTreeSet},
    format,
    string::String,
    vec::Vec,
};

use crate::ast::{Expr, Module, Rule, RuleHead};
use crate::utils::{get_path_string, path::normalize_rule_path};

use super::super::result::AnalysisState;
use super::TypeAnalyzer;

#[derive(Clone, Debug)]
pub(crate) struct RuleHeadInfo {
    pub module_idx: u32,
    pub rule_idx: usize,
    pub expr_idx: u32,
    pub path: String,
}

pub(super) type RuleHeadIndex = (
    Vec<BTreeMap<String, Vec<RuleHeadInfo>>>,
    BTreeMap<String, Vec<RuleHeadInfo>>,
);

impl TypeAnalyzer {
    pub(super) fn build_rule_head_index(modules: &[crate::ast::Ref<Module>]) -> RuleHeadIndex {
        let mut module_rule_heads: Vec<BTreeMap<String, Vec<RuleHeadInfo>>> =
            Vec::with_capacity(modules.len());
        let mut global_rule_heads: BTreeMap<String, Vec<RuleHeadInfo>> = BTreeMap::new();

        for (module_idx, module) in modules.iter().enumerate() {
            let module_idx = module_idx as u32;
            let mut module_map: BTreeMap<String, Vec<RuleHeadInfo>> = BTreeMap::new();
            let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
                .unwrap_or_else(|_| "data".to_owned());

            for (rule_idx, rule) in module.policy.iter().enumerate() {
                match rule.as_ref() {
                    Rule::Spec { head, .. } => {
                        if let Some(refr) = Self::rule_head_expression(head) {
                            Self::record_rule_head(
                                module_idx,
                                rule_idx,
                                refr.eidx(),
                                refr.as_ref(),
                                &module_path,
                                &mut module_map,
                                &mut global_rule_heads,
                            );
                        }
                    }
                    Rule::Default { refr, .. } => {
                        Self::record_rule_head(
                            module_idx,
                            rule_idx,
                            refr.eidx(),
                            refr.as_ref(),
                            &module_path,
                            &mut module_map,
                            &mut global_rule_heads,
                        );
                    }
                }
            }

            module_rule_heads.push(module_map);
        }

        (module_rule_heads, global_rule_heads)
    }

    pub(crate) fn rule_heads_for_name(&self, module_idx: u32, name: &str) -> Vec<&RuleHeadInfo> {
        let mut matches: Vec<&RuleHeadInfo> = Vec::new();

        if let Some(module_heads) = self.module_rule_heads.get(module_idx as usize) {
            if let Some(local) = module_heads.get(name) {
                for info in local {
                    if !matches.iter().any(|existing| {
                        existing.module_idx == info.module_idx && existing.expr_idx == info.expr_idx
                    }) {
                        matches.push(info);
                    }
                }
            }
        }

        if let Some(global) = self.global_rule_heads.get(name) {
            for info in global {
                if !matches.iter().any(|existing| {
                    existing.module_idx == info.module_idx && existing.expr_idx == info.expr_idx
                }) {
                    matches.push(info);
                }
            }
        }

        matches
    }

    pub(crate) fn rule_heads_with_prefix(
        &self,
        module_idx: u32,
        prefix: &str,
    ) -> Vec<&RuleHeadInfo> {
        let normalized_prefix = normalize_rule_path(prefix);
        let mut matches: Vec<&RuleHeadInfo> = Vec::new();
        let mut seen: BTreeSet<(u32, u32)> = BTreeSet::new();

        if let Some(module_heads) = self.module_rule_heads.get(module_idx as usize) {
            for infos in module_heads.values() {
                for info in infos {
                    if Self::rule_path_has_prefix(&info.path, &normalized_prefix)
                        && seen.insert((info.module_idx, info.expr_idx))
                    {
                        matches.push(info);
                    }
                }
            }
        }

        for infos in self.global_rule_heads.values() {
            for info in infos {
                if Self::rule_path_has_prefix(&info.path, &normalized_prefix)
                    && seen.insert((info.module_idx, info.expr_idx))
                {
                    matches.push(info);
                }
            }
        }

        matches
    }

    fn rule_path_has_prefix(path: &str, normalized_prefix: &str) -> bool {
        let normalized_path = normalize_rule_path(path);
        if normalized_path.len() <= normalized_prefix.len() {
            return false;
        }

        normalized_path.starts_with(normalized_prefix)
            && matches!(
                normalized_path.chars().nth(normalized_prefix.len()),
                Some('.') | Some('[')
            )
    }

    pub(crate) fn ensure_all_rule_definitions_analyzed(
        &self,
        rule_path: &str,
        result: &mut AnalysisState,
    ) {
        let normalized = normalize_rule_path(rule_path);
        let base_path = normalized.strip_suffix(".default").unwrap_or(&normalized);

        for (module_idx, module) in self.modules.iter().enumerate() {
            let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
                .unwrap_or_else(|_| "data".to_owned());

            for (rule_idx, rule) in module.policy.iter().enumerate() {
                if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                    if let Ok(var_path) = get_path_string(refr.as_ref(), Some(&module_path)) {
                        let rule_normalized = normalize_rule_path(&var_path);
                        let rule_base = rule_normalized
                            .strip_suffix(".default")
                            .unwrap_or(&rule_normalized);

                        if rule_base == base_path {
                            self.ensure_rule_analyzed(module_idx as u32, rule_idx, result);
                        }
                    }
                }
            }
        }
    }

    fn record_rule_head(
        module_idx: u32,
        rule_idx: usize,
        expr_idx: u32,
        expr: &Expr,
        module_path: &str,
        module_map: &mut BTreeMap<String, Vec<RuleHeadInfo>>,
        global_map: &mut BTreeMap<String, Vec<RuleHeadInfo>>,
    ) {
        if let Ok(mut path) = get_path_string(expr, None) {
            if !path.starts_with("data.") {
                path = format!("{module_path}.{path}");
            }

            let info = RuleHeadInfo {
                module_idx,
                rule_idx,
                expr_idx,
                path: path.clone(),
            };
            let key = Self::rule_name_key(&path).to_owned();

            Self::insert_rule_head(module_map, key.clone(), info.clone());
            Self::insert_rule_head(global_map, key, info);
        }
    }

    fn insert_rule_head(
        map: &mut BTreeMap<String, Vec<RuleHeadInfo>>,
        key: String,
        info: RuleHeadInfo,
    ) {
        let entry = map.entry(key).or_default();
        if !entry.iter().any(|existing| {
            existing.module_idx == info.module_idx && existing.expr_idx == info.expr_idx
        }) {
            entry.push(info);
        }
    }

    fn rule_name_key(path: &str) -> &str {
        path.rsplit('.').next().unwrap_or(path)
    }

    pub(super) fn rule_head_expression(head: &RuleHead) -> Option<&crate::ast::Ref<Expr>> {
        match head {
            RuleHead::Compr { refr, .. }
            | RuleHead::Set { refr, .. }
            | RuleHead::Func { refr, .. } => Some(refr),
        }
    }

    pub(crate) fn rule_head_expression_from_rule(rule: &Rule) -> Option<&crate::ast::Ref<Expr>> {
        match rule {
            Rule::Spec { head, .. } => Self::rule_head_expression(head),
            Rule::Default { refr, .. } => Some(refr),
        }
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::{borrow::ToOwned, collections::BTreeSet, format, vec, vec::Vec};

use crate::ast::Expr;
use crate::utils::get_path_string;
use crate::utils::path::{matches_path_pattern, normalize_rule_path};

use super::TypeAnalyzer;

impl TypeAnalyzer {
    /// Resolve entrypoint patterns to concrete (module_idx, rule_idx) pairs.
    /// Returns None if no filtering configured, otherwise Some(entrypoint_set).
    /// Also tracks default rules that should be included.
    pub(super) fn resolve_entrypoints(&self) -> Option<BTreeSet<(u32, usize)>> {
        if !self.entrypoint_filtering {
            return None;
        }

        let entrypoints = self.options.entrypoints.as_ref()?;
        let mut resolved = BTreeSet::new();

        for pattern in entrypoints {
            for (module_idx, module) in self.modules.iter().enumerate() {
                for (rule_idx, rule) in module.policy.iter().enumerate() {
                    if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                        if let Expr::Var { .. } = refr.as_ref() {
                            let module_path =
                                get_path_string(module.package.refr.as_ref(), Some("data"))
                                    .unwrap_or_else(|_| "data".to_owned());

                            let var_path = get_path_string(refr.as_ref(), Some(&module_path))
                                .unwrap_or_else(|_| "unknown".to_owned());

                            let normalized = normalize_rule_path(&var_path);
                            if matches_path_pattern(&normalized, pattern) {
                                resolved.insert((module_idx as u32, rule_idx));
                                self.find_and_add_default_rule(
                                    &normalized,
                                    module_idx as u32,
                                    &mut resolved,
                                );
                            }
                        }
                    }
                }
            }
        }

        Some(resolved)
    }

    /// Find and include the default rule for a given rule path.
    pub(super) fn find_and_add_default_rule(
        &self,
        rule_path: &str,
        hint_module_idx: u32,
        resolved: &mut BTreeSet<(u32, usize)>,
    ) {
        let default_path = format!("{rule_path}.default");

        let search_modules: Vec<usize> = if (hint_module_idx as usize) < self.modules.len() {
            let mut mods = vec![hint_module_idx as usize];
            mods.extend((0..self.modules.len()).filter(|&i| i != hint_module_idx as usize));
            mods
        } else {
            (0..self.modules.len()).collect()
        };

        for module_idx in search_modules {
            let module = &self.modules[module_idx];
            for (rule_idx, rule) in module.policy.iter().enumerate() {
                if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                    if let Expr::Var { .. } = refr.as_ref() {
                        let module_path =
                            get_path_string(module.package.refr.as_ref(), Some("data"))
                                .unwrap_or_else(|_| "data".to_owned());

                        let var_path = get_path_string(refr.as_ref(), Some(&module_path))
                            .unwrap_or_else(|_| "unknown".to_owned());

                        let normalized = normalize_rule_path(&var_path);

                        if normalized == default_path {
                            resolved.insert((module_idx as u32, rule_idx));
                            self.included_defaults
                                .borrow_mut()
                                .insert(default_path.clone());
                            return;
                        }
                    }
                }
            }
        }
    }
}

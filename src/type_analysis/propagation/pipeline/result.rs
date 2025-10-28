// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::type_analysis::constants::ConstantStore;
use crate::type_analysis::context::LookupContext;
use crate::type_analysis::model::{RuleAnalysis, RuleSpecializationSignature, TypeDiagnostic};
use crate::type_analysis::result::RuleSpecializationRecord;

#[derive(Clone, Debug, Default)]
pub struct BodyQueryTruth {
    pub reachable: bool,
    pub always_true: bool,
}

/// Intermediate state produced by the propagation pipeline.
#[derive(Clone, Debug)]
pub struct AnalysisState {
    pub lookup: LookupContext,
    pub constants: ConstantStore,
    pub diagnostics: Vec<TypeDiagnostic>,
    pub rule_info: Vec<Vec<RuleAnalysis>>,
    pub body_query_truths: Vec<Vec<Vec<BodyQueryTruth>>>,
    pub function_rule_specializations:
        BTreeMap<(u32, usize), BTreeMap<RuleSpecializationSignature, RuleSpecializationRecord>>,
    /// Requested entrypoint patterns (if filtering was enabled)
    pub(crate) requested_entrypoints: Vec<String>,
    /// Default rules included due to entrypoint filtering
    pub(crate) included_defaults: BTreeSet<String>,
}

impl Default for AnalysisState {
    fn default() -> Self {
        Self::new()
    }
}

impl AnalysisState {
    pub fn new() -> Self {
        AnalysisState {
            lookup: LookupContext::new(),
            constants: ConstantStore::new(),
            diagnostics: Vec::new(),
            rule_info: Vec::new(),
            body_query_truths: Vec::new(),
            function_rule_specializations: BTreeMap::new(),
            requested_entrypoints: Vec::new(),
            included_defaults: BTreeSet::new(),
        }
    }

    pub fn ensure_rule_capacity(&mut self, module_idx: u32, rule_count: usize) {
        let module_idx = module_idx as usize;
        if self.rule_info.len() <= module_idx {
            self.rule_info.resize_with(module_idx + 1, Vec::new);
        }
        let module_rules = &mut self.rule_info[module_idx];
        if module_rules.len() < rule_count {
            module_rules.resize(rule_count, RuleAnalysis::default());
        }
    }

    pub fn record_rule_analysis(
        &mut self,
        module_idx: u32,
        rule_idx: usize,
        analysis: RuleAnalysis,
    ) {
        self.ensure_rule_capacity(module_idx, rule_idx + 1);
        self.rule_info[module_idx as usize][rule_idx] = analysis;
    }

    pub fn record_function_specialization(&mut self, record: RuleSpecializationRecord) {
        let key = (record.signature.module_idx, record.signature.rule_idx);
        let signature = record.signature.clone();
        self.function_rule_specializations
            .entry(key)
            .or_insert_with(BTreeMap::new)
            .insert(signature, record);
    }

    pub fn record_body_query_truth(
        &mut self,
        module_idx: u32,
        rule_idx: usize,
        body_idx: usize,
        reachable: bool,
        always_true: bool,
    ) {
        let module_idx_usize = module_idx as usize;

        if self.body_query_truths.len() <= module_idx_usize {
            self.body_query_truths
                .resize_with(module_idx_usize + 1, Vec::new);
        }

        let module_rules = &mut self.body_query_truths[module_idx_usize];
        if module_rules.len() <= rule_idx {
            module_rules.resize_with(rule_idx + 1, Vec::new);
        }

        let rule_bodies = &mut module_rules[rule_idx];
        if rule_bodies.len() <= body_idx {
            rule_bodies.resize(body_idx + 1, BodyQueryTruth::default());
        }

        rule_bodies[body_idx] = BodyQueryTruth {
            reachable,
            always_true,
        };
    }
}

/// Temporary alias to ease transition while call sites are updated.
pub(crate) type TypeAnalysisResult = AnalysisState;

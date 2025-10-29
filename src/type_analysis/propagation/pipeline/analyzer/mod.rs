// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::{
    borrow::ToOwned,
    collections::{BTreeMap, BTreeSet},
    string::String,
    vec::Vec,
};

use crate::ast::{Expr, Module};
use crate::compiler::hoist::HoistedLoopsLookup;
use crate::lexer::Span;
use crate::scheduler::Schedule;
use crate::Rc;

use crate::utils::get_path_string;

use super::{result::AnalysisState, TypeAnalysisOptions};

mod entrypoints;
mod rule_analysis;
mod rule_index;
mod validation;

pub(crate) use rule_index::RuleHeadInfo;

pub struct TypeAnalyzer {
    pub(crate) modules: Rc<Vec<crate::ast::Ref<Module>>>,
    pub(crate) schedule: Option<Rc<Schedule>>,
    pub(crate) options: TypeAnalysisOptions,
    pub(crate) loop_lookup: Option<Rc<HoistedLoopsLookup>>,
    module_rule_heads: Vec<BTreeMap<String, Vec<RuleHeadInfo>>>,
    global_rule_heads: BTreeMap<String, Vec<RuleHeadInfo>>,
    analysis_stack: core::cell::RefCell<Vec<(u32, usize)>>,
    entrypoint_filtering: bool,
    requested_entrypoints: Vec<String>,
    included_defaults: core::cell::RefCell<BTreeSet<String>>,
    function_param_facts:
        core::cell::RefCell<BTreeMap<(u32, usize), Vec<crate::type_analysis::model::TypeFact>>>,
    constant_eval_engine: core::cell::OnceCell<core::cell::RefCell<crate::engine::Engine>>,
    disable_function_generic_pass: bool,
}

impl TypeAnalyzer {
    pub fn new(
        modules: &[crate::ast::Ref<Module>],
        schedule: Option<&Schedule>,
        options: TypeAnalysisOptions,
    ) -> Self {
        let (module_rule_heads, global_rule_heads) = Self::build_rule_head_index(modules);
        let entrypoint_filtering = options.is_entrypoint_filtered();
        let requested_entrypoints = options.entrypoints.clone().unwrap_or_default();
        let disable_function_generic_pass = options.disable_function_generic_pass;

        TypeAnalyzer {
            modules: Rc::new(modules.to_vec()),
            schedule: schedule.map(|sched| {
                Rc::new(Schedule {
                    queries: sched.queries.clone(),
                })
            }),
            loop_lookup: options.loop_lookup.clone(),
            options,
            module_rule_heads,
            global_rule_heads,
            analysis_stack: core::cell::RefCell::new(Vec::new()),
            entrypoint_filtering,
            requested_entrypoints,
            included_defaults: core::cell::RefCell::new(BTreeSet::new()),
            function_param_facts: core::cell::RefCell::new(BTreeMap::new()),
            constant_eval_engine: core::cell::OnceCell::new(),
            disable_function_generic_pass,
        }
    }

    /// Create a TypeAnalyzer from an engine that has been prepared for evaluation.
    /// The engine will be used for constant folding of rules.
    pub fn from_engine(
        engine: &mut crate::engine::Engine,
        options: TypeAnalysisOptions,
    ) -> Option<Self> {
        let (modules, schedule, engine_loop_lookup, _compiled_policy) =
            engine.get_type_analysis_context()?;

        let (module_rule_heads, global_rule_heads) = Self::build_rule_head_index(modules.as_ref());
        let entrypoint_filtering = options.is_entrypoint_filtered();
        let requested_entrypoints = options.entrypoints.clone().unwrap_or_default();
        let disable_function_generic_pass = options.disable_function_generic_pass;

        let analyzer = TypeAnalyzer {
            modules,
            schedule,
            loop_lookup: options.loop_lookup.clone().or(engine_loop_lookup),
            options,
            module_rule_heads,
            global_rule_heads,
            analysis_stack: core::cell::RefCell::new(Vec::new()),
            entrypoint_filtering,
            requested_entrypoints,
            included_defaults: core::cell::RefCell::new(BTreeSet::new()),
            function_param_facts: core::cell::RefCell::new(BTreeMap::new()),
            constant_eval_engine: core::cell::OnceCell::new(),
            disable_function_generic_pass,
        };

        // Seed the engine for constant folding.
        let _ = analyzer
            .constant_eval_engine
            .set(core::cell::RefCell::new(engine.clone()));

        Some(analyzer)
    }

    pub(crate) fn diagnostic_range_from_span(span: &Span) -> (u32, u32, u32, u32) {
        let (line, col) = span.source.offset_to_line_col(span.start);
        let mut end_line = line;
        let mut end_col = col;
        let mut advanced = false;

        for ch in span.text().chars() {
            advanced = true;
            if ch == '\n' {
                end_line += 1;
                end_col = 1;
            } else {
                end_col += 1;
            }
        }

        if !advanced {
            end_col += 1;
        }

        (line, col, end_line, end_col)
    }

    pub fn analyze_modules(&self) -> crate::type_analysis::TypeAnalysisResult {
        let mut state = AnalysisState::new();

        self.validate_rule_definitions(&mut state);
        state.requested_entrypoints = self.requested_entrypoints.clone();

        if let Some(entrypoints) = self.resolve_entrypoints() {
            state.included_defaults = self.included_defaults.borrow().clone();

            for (module_idx, rule_idx) in &entrypoints {
                let module = &self.modules[*module_idx as usize];
                let rule = &module.policy[*rule_idx];
                if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                    if let Expr::Var { .. } = refr.as_ref() {
                        let module_path =
                            get_path_string(module.package.refr.as_ref(), Some("data"))
                                .unwrap_or_else(|_| "data".to_owned());

                        let var_path = get_path_string(refr.as_ref(), Some(&module_path))
                            .unwrap_or_else(|_| "unknown".to_owned());

                        state.lookup.mark_reachable(var_path);
                    }
                }
            }

            for (module_idx, module) in self.modules.iter().enumerate() {
                let module_idx_u32 = module_idx as u32;
                state
                    .lookup
                    .ensure_expr_capacity(module_idx_u32, module.num_expressions);
                state.ensure_rule_capacity(module_idx_u32, module.policy.len());

                for rule_idx in 0..module.policy.len() {
                    if entrypoints.contains(&(module_idx_u32, rule_idx)) {
                        self.ensure_rule_analyzed(module_idx_u32, rule_idx, &mut state);
                    }
                }
            }
        } else {
            for (module_idx, module) in self.modules.iter().enumerate() {
                let module_idx = module_idx as u32;
                state
                    .lookup
                    .ensure_expr_capacity(module_idx, module.num_expressions);
                state.ensure_rule_capacity(module_idx, module.policy.len());
                self.analyze_module(module_idx, module, &mut state);
            }
        }

        // Convert AnalysisState to public TypeAnalysisResult
        crate::type_analysis::TypeAnalysisResult::from_analysis_state(state, &self.modules)
    }

    pub(crate) fn prepare_function_rule_specialization(
        &self,
        module_idx: u32,
        rule_idx: usize,
        facts: &[crate::type_analysis::model::TypeFact],
        result: &mut AnalysisState,
    ) -> Option<Vec<crate::type_analysis::model::TypeFact>> {
        let mut previous = None;
        if let Some(module) = self.modules.get(module_idx as usize) {
            if let Some(rule) = module.policy.get(rule_idx) {
                if matches!(
                    rule.as_ref(),
                    crate::ast::Rule::Spec {
                        head: crate::ast::RuleHead::Func { .. },
                        ..
                    }
                ) {
                    previous = self
                        .function_param_facts
                        .borrow_mut()
                        .insert((module_idx, rule_idx), facts.to_vec());

                    result.ensure_rule_capacity(module_idx, rule_idx + 1);
                    result.rule_info[module_idx as usize][rule_idx] =
                        crate::type_analysis::model::RuleAnalysis::default();

                    if let Some(refr) = Self::rule_head_expression_from_rule(rule.as_ref()) {
                        result
                            .lookup
                            .expr_types_mut()
                            .clear(module_idx, refr.eidx());
                    }
                }
            }
        }

        previous
    }

    pub(crate) fn restore_function_rule_specialization(
        &self,
        module_idx: u32,
        rule_idx: usize,
        previous: Option<Vec<crate::type_analysis::model::TypeFact>>,
    ) {
        let mut store = self.function_param_facts.borrow_mut();
        if let Some(prev) = previous {
            store.insert((module_idx, rule_idx), prev);
        } else {
            store.remove(&(module_idx, rule_idx));
        }
    }

    pub(crate) fn try_evaluate_rule_constant(
        &self,
        _module_idx: u32,
        rule_path: &str,
    ) -> Option<crate::value::Value> {
        use crate::engine::Engine;

        let engine_cell = self.constant_eval_engine.get_or_init(|| {
            core::cell::RefCell::new(Engine::new_with_modules(self.modules.clone()))
        });

        let mut engine = engine_cell.borrow_mut();
        engine.try_eval_rule_constant(rule_path)
    }
}

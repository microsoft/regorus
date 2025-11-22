// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Prototype result data model for the type analyser.
//! This module is not yet wired into the main pipeline; it exists so we can
//! iterate on the structures without disturbing the current implementation.

mod deps;
mod entrypoints;
mod expressions;
mod rules;

use alloc::{borrow::ToOwned, collections::BTreeMap, format, string::String, vec, vec::Vec};

use crate::ast::{Expr, Rule, RuleBody, RuleHead};
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, RuleConstantState, StructuralType, TypeDescriptor, TypeDiagnostic,
    TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::TypeAnalyzer;
use crate::utils::get_path_string;
use crate::value::Value;

pub use deps::{DependencyEdge, DependencyGraph, DependencyKind};
pub use entrypoints::{DynamicLookupPattern, EntrypointSummary};
pub use expressions::ExpressionFacts;
pub use rules::{
    DefinitionSummary, ModuleSummary, RuleBodyKind, RuleBodySummary, RuleKind,
    RuleSpecializationRecord, RuleSpecializationTrace, RuleSummary, RuleTable, RuleVerboseInfo,
    TraceLocal, TraceStatement,
};

/// Top-level aggregate returned after analysing a module set.
#[derive(Clone, Debug, Default)]
pub struct TypeAnalysisResult {
    pub expressions: ExpressionFacts,
    pub rules: RuleTable,
    pub dependencies: DependencyGraph,
    pub entrypoints: EntrypointSummary,
    pub diagnostics: Vec<TypeDiagnostic>,
}

fn rule_returns_boolean_by_default(head: &RuleHead) -> bool {
    matches!(
        head,
        RuleHead::Func { assign: None, .. }
            | RuleHead::Compr { assign: None, .. }
            | RuleHead::Set { .. }
    )
}

fn default_true_body_fact() -> TypeFact {
    TypeFact::new(
        TypeDescriptor::Structural(StructuralType::Boolean),
        TypeProvenance::Propagated,
    )
    .with_constant(ConstantValue::known(Value::from(true)))
}

fn is_constant_body(value_fact: Option<&TypeFact>, body: &RuleBody) -> bool {
    if !body.query.as_ref().stmts.is_empty() {
        return false;
    }

    matches!(
        value_fact,
        Some(fact) if matches!(fact.constant, ConstantValue::Known(_))
    )
}

impl TypeAnalysisResult {
    /// Create TypeAnalysisResult from internal AnalysisState.
    /// This converts the mutable pipeline state into an immutable public result.
    pub(crate) fn from_analysis_state(
        state: super::propagation::AnalysisState,
        modules: &[crate::ast::Ref<crate::ast::Module>],
    ) -> Self {
        // Build ExpressionFacts from lookup and constants
        let expressions = ExpressionFacts {
            facts: state.lookup.clone(),
            constants: state.constants.clone(),
        };

        // Collect reachable rules
        let reachable = expressions.facts.reachable_rules().cloned().collect();

        // Convert dynamic references
        let dynamic_refs = expressions
            .facts
            .dynamic_references()
            .iter()
            .map(|dr| DynamicLookupPattern {
                static_prefix: dr.static_prefix.clone(),
                pattern: dr.pattern.clone(),
            })
            .collect();

        // Build RuleTable with rule metadata
        let mut modules_summary = Vec::with_capacity(modules.len());
        let mut rules_by_path: BTreeMap<String, RuleSummary> = BTreeMap::new();

        for (module_idx, module_ref) in modules.iter().enumerate() {
            let module = module_ref.as_ref();
            let module_idx_u32 = module_idx as u32;
            let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
                .unwrap_or_else(|_| "data".to_owned());
            let source_name = module.package.span.source.get_path().clone();

            let module_rules: &[RuleAnalysis] = state
                .rule_info
                .get(module_idx)
                .map(Vec::as_slice)
                .unwrap_or_default();

            let mut rule_paths: Vec<String> = Vec::new();
            let mut rule_summaries: Vec<RuleSummary> = Vec::new();

            for (rule_idx, rule_ref) in module.policy.iter().enumerate() {
                let rule = rule_ref.as_ref();
                let analysis = module_rules
                    .get(rule_idx)
                    .cloned()
                    .unwrap_or_else(RuleAnalysis::default);

                let head_expr = rule_head_expression(rule);
                let head_expr_idx = head_expr.map(|expr| expr.eidx());
                let head_value_expr_idx = rule_head_value_expr_idx(rule);
                let rule_path = head_expr
                    .and_then(|refr| get_path_string(refr.as_ref(), Some(&module_path)).ok())
                    .unwrap_or_else(|| unknown_rule_path(&module_path, rule_idx));

                let specializations: Vec<RuleSpecializationRecord> = state
                    .function_rule_specializations
                    .get(&(module_idx_u32, rule_idx))
                    .map(|specs| specs.values().cloned().collect())
                    .unwrap_or_default();

                let rule_dependencies = analysis
                    .rule_dependencies
                    .iter()
                    .map(|target| DependencyEdge {
                        source: rule_path.clone(),
                        target: target.clone(),
                        kind: DependencyKind::StaticCall,
                    })
                    .collect();

                let head_fact = head_expr_idx
                    .and_then(|idx| state.lookup.get_expr(module_idx_u32, idx))
                    .cloned();

                let constant_value = match &analysis.constant_state {
                    RuleConstantState::Done(value) => Some(value.clone()),
                    _ => None,
                };

                let aggregated_head_fact = aggregate_definition_head_fact(
                    module_idx_u32,
                    head_expr_idx,
                    head_value_expr_idx,
                    &head_fact,
                    &specializations,
                );
                let aggregated_parameter_facts =
                    aggregate_definition_parameter_facts(&specializations);

                // Extract span information from rule
                let head_span = head_expr.map(|expr| {
                    let span = expr.span();
                    rules::SourceSpan {
                        file: span.source.get_path().clone(),
                        line: span.line,
                        col: span.col,
                    }
                });

                let definition_span = rule.span().clone();
                let def_span = Some(rules::SourceSpan {
                    file: definition_span.source.get_path().clone(),
                    line: definition_span.line,
                    col: definition_span.col,
                });

                let bodies_summary = match rule {
                    Rule::Spec { head, bodies, .. } => bodies
                        .iter()
                        .enumerate()
                        .map(|(body_idx, body)| {
                            let span = body.span.clone();
                            let span = rules::SourceSpan {
                                file: span.source.get_path().clone(),
                                line: span.line,
                                col: span.col,
                            };

                            let value_expr_idx =
                                body.assign.as_ref().map(|assign| assign.value.eidx()).or(
                                    if body_idx == 0 {
                                        head_value_expr_idx
                                    } else {
                                        None
                                    },
                                );

                            let mut value_fact = value_expr_idx
                                .and_then(|idx| state.lookup.get_expr(module_idx_u32, idx))
                                .cloned()
                                .or_else(|| {
                                    value_expr_idx.and_then(|idx| {
                                        specializations.iter().find_map(|spec| {
                                            spec.expr_facts
                                                .get(&module_idx_u32)
                                                .and_then(|exprs| exprs.get(&idx).cloned())
                                        })
                                    })
                                });

                            if value_fact.is_none()
                                && body_idx == 0
                                && rule_returns_boolean_by_default(head)
                            {
                                value_fact = Some(default_true_body_fact());
                            }

                            let is_constant = is_constant_body(value_fact.as_ref(), body);

                            rules::RuleBodySummary {
                                body_idx,
                                kind: if body_idx == 0 {
                                    rules::RuleBodyKind::Primary
                                } else {
                                    rules::RuleBodyKind::Else
                                },
                                span: Some(span),
                                value_expr_idx,
                                value_fact,
                                is_constant,
                            }
                        })
                        .collect(),
                    Rule::Default { .. } => Vec::new(),
                };

                let definition = DefinitionSummary {
                    definition_idx: rule_idx,
                    module_idx: module_idx_u32,
                    span: def_span,
                    analysis: analysis.clone(),
                    head_fact: head_fact.clone(),
                    aggregated_head_fact: aggregated_head_fact.clone(),
                    aggregated_parameter_facts: aggregated_parameter_facts.clone(),
                    bodies: bodies_summary,
                    constant_value: constant_value.clone(),
                    specializations: specializations.clone(),
                    ..DefinitionSummary::default()
                };
                let definitions = vec![definition];
                let rule_aggregated_head_fact = aggregate_rule_head_fact(&definitions);
                let rule_aggregated_parameter_facts = aggregate_rule_parameter_facts(&definitions);

                let mut rule_summary = RuleSummary {
                    id: rule_path.clone(),
                    module_idx: module_idx_u32,
                    head_span,
                    definitions,
                    kind: classify_rule(rule),
                    arity: rule_arity(rule),
                    head_expr: head_expr_idx,
                    constant_state: analysis.constant_state.clone(),
                    input_dependencies: analysis.input_dependencies.clone(),
                    rule_dependencies,
                    aggregated_head_fact: rule_aggregated_head_fact,
                    aggregated_parameter_facts: rule_aggregated_parameter_facts,
                    specializations,
                    ..RuleSummary::default()
                };

                rule_summary.trace = None; // traces populated elsewhere

                rule_paths.push(rule_path.clone());
                rules_by_path.insert(rule_path.clone(), rule_summary.clone());
                rule_summaries.push(rule_summary);
            }

            modules_summary.push(ModuleSummary {
                module_idx: module_idx_u32,
                package_path: module_path,
                source_name,
                rule_paths,
                rules: rule_summaries,
            });
        }

        let rules = RuleTable {
            by_path: rules_by_path,
            modules: modules_summary,
        };

        // Build DependencyGraph (empty for now)
        let dependencies = DependencyGraph::default();

        // Build EntrypointSummary from state fields
        let entrypoints = EntrypointSummary {
            requested: state.requested_entrypoints,
            reachable,
            included_defaults: state.included_defaults,
            dynamic_refs,
        };

        TypeAnalysisResult {
            expressions,
            rules,
            dependencies,
            entrypoints,
            diagnostics: state.diagnostics,
        }
    }
}

fn rule_head_expression(rule: &Rule) -> Option<&crate::ast::Ref<Expr>> {
    match rule {
        Rule::Spec { head, .. } => match head {
            RuleHead::Compr { refr, .. }
            | RuleHead::Set { refr, .. }
            | RuleHead::Func { refr, .. } => Some(refr),
        },
        Rule::Default { refr, .. } => Some(refr),
    }
}

fn rule_head_value_expr_idx(rule: &Rule) -> Option<u32> {
    match rule {
        Rule::Spec { head, .. } => match head {
            RuleHead::Compr { assign, .. } | RuleHead::Func { assign, .. } => {
                assign.as_ref().map(|assign| assign.value.eidx())
            }
            RuleHead::Set { .. } => None,
        },
        Rule::Default { value, .. } => Some(value.eidx()),
    }
}

fn classify_rule(rule: &Rule) -> RuleKind {
    match rule {
        Rule::Spec { head, .. } => match head {
            RuleHead::Func { .. } => RuleKind::Function,
            RuleHead::Set { .. } => RuleKind::PartialSet,
            RuleHead::Compr { .. } => RuleKind::PartialObject,
        },
        Rule::Default { .. } => RuleKind::Complete,
    }
}

fn rule_arity(rule: &Rule) -> Option<usize> {
    match rule {
        Rule::Spec {
            head: RuleHead::Func { args, .. },
            ..
        } => Some(args.len()),
        Rule::Default { args, .. } if !args.is_empty() => Some(args.len()),
        _ => None,
    }
}

fn unknown_rule_path(module_path: &str, rule_idx: usize) -> String {
    format!("{module_path}::<rule_{rule_idx}>")
}

fn aggregate_definition_head_fact(
    module_idx: u32,
    head_expr_idx: Option<u32>,
    head_value_expr_idx: Option<u32>,
    head_fact: &Option<TypeFact>,
    specializations: &[RuleSpecializationRecord],
) -> Option<TypeFact> {
    let mut all_facts: Vec<TypeFact> = Vec::new();

    if let Some(fact) = head_fact {
        all_facts.push(fact.clone());
    }

    for spec in specializations {
        if let Some(fact) = &spec.head_fact {
            all_facts.push(fact.clone());
        }

        if spec
            .head_fact
            .as_ref()
            .map(fact_is_informative)
            .unwrap_or(false)
        {
            continue;
        }

        if let Some(module_map) = spec.expr_facts.get(&module_idx) {
            if let Some(expr_idx) = head_value_expr_idx {
                if let Some(expr_fact) = module_map.get(&expr_idx) {
                    all_facts.push(expr_fact.clone());
                    continue;
                }
            }

            if let Some(expr_idx) = head_expr_idx {
                if let Some(expr_fact) = module_map.get(&expr_idx) {
                    all_facts.push(expr_fact.clone());
                }
            }
        }
    }

    if all_facts.is_empty() {
        return None;
    }

    let informative: Vec<TypeFact> = all_facts
        .iter()
        .filter(|fact| fact_is_informative(fact))
        .cloned()
        .collect();

    if !informative.is_empty() {
        Some(TypeAnalyzer::merge_rule_facts(&informative))
    } else {
        Some(TypeAnalyzer::merge_rule_facts(&all_facts))
    }
}

fn aggregate_definition_parameter_facts(
    specializations: &[RuleSpecializationRecord],
) -> Vec<Option<TypeFact>> {
    let max_params = specializations
        .iter()
        .map(|spec| spec.parameter_facts.len())
        .max()
        .unwrap_or(0);

    let mut merged: Vec<Option<TypeFact>> = Vec::with_capacity(max_params);

    for index in 0..max_params {
        let mut slot_facts = Vec::new();
        for spec in specializations {
            if let Some(fact) = spec.parameter_facts.get(index) {
                slot_facts.push(fact.clone());
            }
        }

        if slot_facts.is_empty() {
            merged.push(None);
            continue;
        }

        let informative: Vec<TypeFact> = slot_facts
            .iter()
            .filter(|fact| fact_is_informative(fact))
            .cloned()
            .collect();

        if !informative.is_empty() {
            merged.push(Some(TypeAnalyzer::merge_rule_facts(&informative)));
        } else {
            merged.push(Some(TypeAnalyzer::merge_rule_facts(&slot_facts)));
        }
    }

    merged
}

fn aggregate_rule_head_fact(definitions: &[DefinitionSummary]) -> Option<TypeFact> {
    let mut all_facts: Vec<TypeFact> = Vec::new();
    for definition in definitions {
        if let Some(fact) = &definition.aggregated_head_fact {
            all_facts.push(fact.clone());
        }
    }

    if all_facts.is_empty() {
        return None;
    }

    let informative: Vec<TypeFact> = all_facts
        .iter()
        .filter(|fact| fact_is_informative(fact))
        .cloned()
        .collect();

    if !informative.is_empty() {
        Some(TypeAnalyzer::merge_rule_facts(&informative))
    } else {
        Some(TypeAnalyzer::merge_rule_facts(&all_facts))
    }
}

fn aggregate_rule_parameter_facts(definitions: &[DefinitionSummary]) -> Vec<Option<TypeFact>> {
    let max_params = definitions
        .iter()
        .map(|definition| definition.aggregated_parameter_facts.len())
        .max()
        .unwrap_or(0);

    let mut merged: Vec<Option<TypeFact>> = Vec::with_capacity(max_params);

    for index in 0..max_params {
        let mut slot_facts = Vec::new();
        for definition in definitions {
            if let Some(fact) = definition
                .aggregated_parameter_facts
                .get(index)
                .and_then(|opt| opt.clone())
            {
                slot_facts.push(fact);
            }
        }

        if slot_facts.is_empty() {
            merged.push(None);
            continue;
        }

        let informative: Vec<TypeFact> = slot_facts
            .iter()
            .filter(|fact| fact_is_informative(fact))
            .cloned()
            .collect();

        if !informative.is_empty() {
            merged.push(Some(TypeAnalyzer::merge_rule_facts(&informative)));
        } else {
            merged.push(Some(TypeAnalyzer::merge_rule_facts(&slot_facts)));
        }
    }

    merged
}

fn fact_is_informative(fact: &TypeFact) -> bool {
    match &fact.descriptor {
        TypeDescriptor::Structural(ty) => !structural_contains_unknownish(ty),
        _ => true,
    }
}

fn structural_contains_unknownish(ty: &StructuralType) -> bool {
    match ty {
        StructuralType::Any | StructuralType::Unknown => true,
        StructuralType::Union(variants) => variants.iter().any(structural_contains_unknownish),
        _ => false,
    }
}

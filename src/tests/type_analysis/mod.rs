// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, ExprRef, Literal, Module, Query, Ref, Rule, RuleHead};
use crate::lexer::Source;
use crate::parser::Parser;
use crate::scheduler::Analyzer as SchedulerAnalyzer;
use crate::schema::Schema;
use crate::type_analysis::{
    ConstantValue, StructuralType, TypeAnalysisOptions, TypeAnalysisResult, TypeAnalyzer,
    TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::utils::get_path_string;
use crate::value::Value;

use super::interpreter::process_value;

use alloc::{borrow::ToOwned, boxed::Box, collections::BTreeMap, format, string::String, vec::Vec};
use anyhow::{anyhow, bail, Context, Result};
use core::mem::discriminant;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use test_generator::test_resources;

#[derive(Debug, Deserialize)]
struct TypeYamlTest {
    cases: Vec<TypeCase>,
}

#[derive(Debug, Deserialize)]
struct TypeCase {
    note: String,
    modules: Vec<String>,
    #[serde(default)]
    input_schema: Option<serde_json::Value>,
    #[serde(default)]
    data_schema: Option<serde_json::Value>,
    #[serde(default)]
    rules: Vec<RuleExpectation>,
    #[serde(default)]
    exprs: Vec<ExprExpectation>,
    #[serde(default)]
    diagnostics: Vec<DiagnosticExpectation>,
}

#[derive(Debug, Deserialize)]
struct RuleExpectation {
    rule: String,
    #[serde(rename = "type")]
    r#type: TypeExpectation,
    #[serde(default)]
    constant: Option<Value>,
    #[serde(default)]
    provenance: Option<String>,
    #[serde(default)]
    schema_backed: Option<bool>,
    #[serde(default)]
    line: Option<u32>,
    #[serde(default)]
    col: Option<u32>,
}

#[derive(Debug, Deserialize)]
struct ExprExpectation {
    expr: String,
    #[serde(rename = "type")]
    r#type: TypeExpectation,
    #[serde(default)]
    constant: Option<Value>,
    #[serde(default)]
    provenance: Option<String>,
    #[serde(default)]
    schema_backed: Option<bool>,
    #[serde(default)]
    line: Option<u32>,
    #[serde(default)]
    col: Option<u32>,
}

#[derive(Debug, Deserialize)]
struct DiagnosticExpectation {
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    message: Option<String>,
    #[serde(default)]
    line: Option<u32>,
    #[serde(default)]
    col: Option<u32>,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum TypeExpectation {
    Simple(String),
    Detailed(DetailedTypeExpectation),
}

#[derive(Debug, Deserialize)]
struct DetailedTypeExpectation {
    kind: String,
    #[serde(default)]
    element: Option<Box<TypeExpectation>>,
    #[serde(default)]
    #[serde(alias = "fields")]
    properties: Option<HashMap<String, TypeExpectation>>,
    #[serde(default)]
    variants: Option<Vec<TypeExpectation>>,
}

#[derive(Clone)]
struct ExprInfo {
    module_idx: u32,
    expr: ExprRef,
    text: String,
    line: u32,
    col: u32,
}

#[derive(Clone)]
struct RuleInfo {
    fact: TypeFact,
    line: u32,
    col: u32,
}

fn yaml_test_impl(path: &str) -> Result<()> {
    let yaml = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read yaml test file {path}"))?;
    let test: TypeYamlTest = serde_yaml::from_str(&yaml)
        .with_context(|| format!("failed to parse yaml test file {path}"))?;

    for case in test.cases.iter() {
        run_case(case).with_context(|| format!("case `{}`", case.note))?;
    }

    Ok(())
}

fn run_case(case: &TypeCase) -> Result<()> {
    let mut sources = Vec::with_capacity(case.modules.len());
    let mut modules = Vec::with_capacity(case.modules.len());

    for (idx, module_src) in case.modules.iter().enumerate() {
        let source = Source::from_contents(format!("module_{idx}.rego"), module_src.clone())?;
        let mut parser = Parser::new(&source)?;
        parser.enable_rego_v1()?;
        let module = parser.parse()?;
        modules.push(Ref::new(module));
        sources.push(source);
    }

    let schedule = SchedulerAnalyzer::new().analyze(&modules)?;

    let options = TypeAnalysisOptions {
        input_schema: parse_optional_schema(case.input_schema.clone())?,
        data_schema: parse_optional_schema(case.data_schema.clone())?,
        loop_lookup: None,
        entrypoints: None,
        disable_function_generic_pass: true,
    };

    let analyzer = TypeAnalyzer::new(&modules, Some(&schedule), options);
    let result = analyzer.analyze_modules();

    let rule_map = if case.rules.is_empty() {
        BTreeMap::new()
    } else {
        collect_rule_facts(&modules, &result)?
    };
    let exprs = collect_exprs(&modules);
    check_rules(case, &rule_map)?;
    check_exprs(case, &exprs, &result)?;
    check_diagnostics(case, &result)?;

    Ok(())
}

fn parse_optional_schema(raw: Option<serde_json::Value>) -> Result<Option<Schema>> {
    match raw {
        Some(value) => {
            let schema = Schema::from_serde_json_value(value)
                .map_err(|e| anyhow!("failed to parse schema: {e}"))?;
            Ok(Some(schema))
        }
        None => Ok(None),
    }
}

fn collect_rule_facts(
    modules: &[Ref<Module>],
    result: &TypeAnalysisResult,
) -> Result<BTreeMap<String, RuleInfo>> {
    let mut rules = BTreeMap::new();

    for (module_idx, module) in modules.iter().enumerate() {
        let module_idx = module_idx as u32;
        let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))?;
        for rule in &module.policy {
            match rule.as_ref() {
                Rule::Spec { head, .. } => {
                    if let Some((refr, span)) = rule_head_expression(head) {
                        let mut path = get_path_string(refr.as_ref(), None)?;
                        if !path.starts_with("data.") {
                            path = format!("{module_path}.{path}");
                        }
                        let fact = resolve_rule_fact(result, module_idx, refr.eidx(), &path)
                            .with_context(|| {
                                format!(
                                    "missing type fact for rule `{path}` (module {module_idx}, expr {})",
                                    refr.eidx()
                                )
                            })?;
                        rules.insert(
                            path,
                            RuleInfo {
                                fact,
                                line: span.line,
                                col: span.col,
                            },
                        );
                    }
                }
                Rule::Default { refr, span, .. } => {
                    let mut path = get_path_string(refr.as_ref(), None)?;
                    if !path.starts_with("data.") {
                        path = format!("{module_path}.{path}");
                    }
                    let fact = resolve_rule_fact(result, module_idx, refr.eidx(), &path)
                        .with_context(|| {
                            format!(
                                "missing type fact for default rule `{path}` (module {module_idx}, expr {})",
                                refr.eidx()
                            )
                        })?;
                    rules.insert(
                        path,
                        RuleInfo {
                            fact,
                            line: span.line,
                            col: span.col,
                        },
                    );
                }
            }
        }
    }

    Ok(rules)
}

fn resolve_rule_fact(
    result: &TypeAnalysisResult,
    module_idx: u32,
    expr_idx: u32,
    path: &str,
) -> Option<TypeFact> {
    let expr_fact = result
        .expressions
        .facts
        .get_expr(module_idx, expr_idx)
        .cloned();

    let summary_fact = result.rules.by_path.get(path).and_then(|summary| {
        summary.aggregated_head_fact.clone().or_else(|| {
            summary.definitions.iter().find_map(|definition| {
                definition
                    .head_fact
                    .clone()
                    .or_else(|| definition.aggregated_head_fact.clone())
            })
        })
    });

    match (expr_fact, summary_fact) {
        (Some(expr), Some(summary)) => {
            let expr_informative = descriptor_is_informative(&expr.descriptor);
            let summary_informative = descriptor_is_informative(&summary.descriptor);

            if summary_informative && !expr_informative {
                Some(merge_fact_with_constant(summary, &expr))
            } else {
                Some(expr)
            }
        }
        (Some(expr), None) => Some(expr),
        (None, Some(summary)) => Some(summary),
        (None, None) => None,
    }
}

fn descriptor_is_informative(descriptor: &TypeDescriptor) -> bool {
    match descriptor {
        TypeDescriptor::Structural(ty) => !structural_contains_unknownish(ty),
        TypeDescriptor::Schema(_) => true,
    }
}

fn structural_contains_unknownish(ty: &StructuralType) -> bool {
    match ty {
        StructuralType::Any | StructuralType::Unknown => true,
        StructuralType::Union(variants) => variants.iter().any(structural_contains_unknownish),
        _ => false,
    }
}

fn merge_fact_with_constant(mut primary: TypeFact, fallback: &TypeFact) -> TypeFact {
    if matches!(primary.constant, ConstantValue::Unknown) {
        if let ConstantValue::Known(value) = &fallback.constant {
            primary = primary.with_constant(ConstantValue::known(value.clone()));
        }
    }

    if primary.origins.is_empty() && !fallback.origins.is_empty() {
        primary = primary.with_origins(fallback.origins.clone());
    }

    primary
}

fn rule_head_expression(head: &RuleHead) -> Option<(&ExprRef, &crate::lexer::Span)> {
    match head {
        RuleHead::Compr { refr, span, .. }
        | RuleHead::Set { refr, span, .. }
        | RuleHead::Func { refr, span, .. } => Some((refr, span)),
    }
}

fn collect_exprs(modules: &[Ref<Module>]) -> Vec<ExprInfo> {
    let mut exprs = Vec::new();
    let mut visited: HashSet<(u32, u32)> = HashSet::new();

    for (module_idx, module) in modules.iter().enumerate() {
        let module_idx = module_idx as u32;
        for rule in &module.policy {
            match rule.as_ref() {
                Rule::Spec { head, bodies, .. } => {
                    if let Some((refr, _)) = rule_head_expression(head) {
                        record_expr(&mut exprs, &mut visited, module_idx, refr);
                    }

                    collect_rule_head(head, module_idx, &mut exprs, &mut visited);

                    for body in bodies {
                        if let Some(assign) = &body.assign {
                            record_expr(&mut exprs, &mut visited, module_idx, &assign.value);
                            collect_expr(
                                assign.value.clone(),
                                module_idx,
                                &mut exprs,
                                &mut visited,
                            );
                        }
                        collect_query(&body.query, module_idx, &mut exprs, &mut visited);
                    }
                }
                Rule::Default {
                    refr, value, span, ..
                } => {
                    record_expr(&mut exprs, &mut visited, module_idx, refr);
                    collect_expr(refr.clone(), module_idx, &mut exprs, &mut visited);
                    record_expr(&mut exprs, &mut visited, module_idx, value);
                    collect_expr(value.clone(), module_idx, &mut exprs, &mut visited);
                    exprs.push(ExprInfo {
                        module_idx,
                        expr: value.clone(),
                        text: span.text().trim().to_owned(),
                        line: span.line,
                        col: span.col,
                    });
                }
            }
        }
    }

    exprs
}

fn collect_rule_head(
    head: &RuleHead,
    module_idx: u32,
    exprs: &mut Vec<ExprInfo>,
    visited: &mut HashSet<(u32, u32)>,
) {
    match head {
        RuleHead::Compr { assign, .. } | RuleHead::Func { assign, .. } => {
            if let Some(assign) = assign {
                record_expr(exprs, visited, module_idx, &assign.value);
                collect_expr(assign.value.clone(), module_idx, exprs, visited);
            }
        }
        RuleHead::Set { key, .. } => {
            if let Some(key) = key {
                record_expr(exprs, visited, module_idx, key);
                collect_expr(key.clone(), module_idx, exprs, visited);
            }
        }
    }
}

fn collect_query(
    query: &Ref<Query>,
    module_idx: u32,
    exprs: &mut Vec<ExprInfo>,
    visited: &mut HashSet<(u32, u32)>,
) {
    for stmt in &query.stmts {
        for with in &stmt.with_mods {
            record_expr(exprs, visited, module_idx, &with.refr);
            collect_expr(with.refr.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, &with.r#as);
            collect_expr(with.r#as.clone(), module_idx, exprs, visited);
        }
        collect_literal(&stmt.literal, module_idx, exprs, visited);
    }
}

fn collect_literal(
    literal: &Literal,
    module_idx: u32,
    exprs: &mut Vec<ExprInfo>,
    visited: &mut HashSet<(u32, u32)>,
) {
    match literal {
        Literal::SomeVars { .. } => {}
        Literal::SomeIn {
            key,
            value,
            collection,
            ..
        } => {
            if let Some(k) = key {
                record_expr(exprs, visited, module_idx, k);
                collect_expr(k.clone(), module_idx, exprs, visited);
            }
            record_expr(exprs, visited, module_idx, value);
            collect_expr(value.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, collection);
            collect_expr(collection.clone(), module_idx, exprs, visited);
        }
        Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
            record_expr(exprs, visited, module_idx, expr);
            collect_expr(expr.clone(), module_idx, exprs, visited);
        }
        Literal::Every { domain, query, .. } => {
            record_expr(exprs, visited, module_idx, domain);
            collect_expr(domain.clone(), module_idx, exprs, visited);
            collect_query(query, module_idx, exprs, visited);
        }
    }
}

fn record_expr(
    exprs: &mut Vec<ExprInfo>,
    visited: &mut HashSet<(u32, u32)>,
    module_idx: u32,
    expr: &ExprRef,
) {
    let key = (module_idx, expr.eidx());
    if !visited.insert(key) {
        return;
    }

    let span = expr.span();
    exprs.push(ExprInfo {
        module_idx,
        expr: expr.clone(),
        text: span.text().trim().to_owned(),
        line: span.line,
        col: span.col,
    });
}

fn collect_expr(
    expr: ExprRef,
    module_idx: u32,
    exprs: &mut Vec<ExprInfo>,
    visited: &mut HashSet<(u32, u32)>,
) {
    match expr.as_ref() {
        Expr::Array { items, .. } | Expr::Set { items, .. } => {
            for item in items {
                record_expr(exprs, visited, module_idx, item);
                collect_expr(item.clone(), module_idx, exprs, visited);
            }
        }
        Expr::Object { fields, .. } => {
            for (_, key_expr, value_expr) in fields {
                record_expr(exprs, visited, module_idx, key_expr);
                collect_expr(key_expr.clone(), module_idx, exprs, visited);
                record_expr(exprs, visited, module_idx, value_expr);
                collect_expr(value_expr.clone(), module_idx, exprs, visited);
            }
        }
        Expr::ArrayCompr { term, query, .. } | Expr::SetCompr { term, query, .. } => {
            record_expr(exprs, visited, module_idx, term);
            collect_expr(term.clone(), module_idx, exprs, visited);
            collect_query(query, module_idx, exprs, visited);
        }
        Expr::ObjectCompr {
            key, value, query, ..
        } => {
            record_expr(exprs, visited, module_idx, key);
            collect_expr(key.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, value);
            collect_expr(value.clone(), module_idx, exprs, visited);
            collect_query(query, module_idx, exprs, visited);
        }
        Expr::Call { fcn, params, .. } => {
            record_expr(exprs, visited, module_idx, fcn);
            collect_expr(fcn.clone(), module_idx, exprs, visited);
            for param in params {
                record_expr(exprs, visited, module_idx, param);
                collect_expr(param.clone(), module_idx, exprs, visited);
            }
        }
        Expr::UnaryExpr { expr: inner, .. } => {
            record_expr(exprs, visited, module_idx, inner);
            collect_expr(inner.clone(), module_idx, exprs, visited);
        }
        Expr::RefDot { refr, .. } | Expr::RefBrack { refr, .. } => {
            record_expr(exprs, visited, module_idx, refr);
            collect_expr(refr.clone(), module_idx, exprs, visited);
            if let Expr::RefBrack { index, .. } = expr.as_ref() {
                record_expr(exprs, visited, module_idx, index);
                collect_expr(index.clone(), module_idx, exprs, visited);
            }
        }
        Expr::BinExpr { lhs, rhs, .. }
        | Expr::BoolExpr { lhs, rhs, .. }
        | Expr::ArithExpr { lhs, rhs, .. } => {
            record_expr(exprs, visited, module_idx, lhs);
            collect_expr(lhs.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, rhs);
            collect_expr(rhs.clone(), module_idx, exprs, visited);
        }
        #[cfg(feature = "rego-extensions")]
        Expr::OrExpr { lhs, rhs, .. } => {
            record_expr(exprs, visited, module_idx, lhs);
            collect_expr(lhs.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, rhs);
            collect_expr(rhs.clone(), module_idx, exprs, visited);
        }
        Expr::AssignExpr { lhs, rhs, .. } => {
            record_expr(exprs, visited, module_idx, lhs);
            collect_expr(lhs.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, rhs);
            collect_expr(rhs.clone(), module_idx, exprs, visited);
        }
        Expr::Membership {
            key,
            value,
            collection,
            ..
        } => {
            if let Some(key) = key {
                record_expr(exprs, visited, module_idx, key);
                collect_expr(key.clone(), module_idx, exprs, visited);
            }
            record_expr(exprs, visited, module_idx, value);
            collect_expr(value.clone(), module_idx, exprs, visited);
            record_expr(exprs, visited, module_idx, collection);
            collect_expr(collection.clone(), module_idx, exprs, visited);
        }
        Expr::String { .. }
        | Expr::RawString { .. }
        | Expr::Number { .. }
        | Expr::Bool { .. }
        | Expr::Null { .. }
        | Expr::Var { .. } => {}
    }
}

fn check_rules(case: &TypeCase, rules: &BTreeMap<String, RuleInfo>) -> Result<()> {
    for expectation in &case.rules {
        let info = rules.get(&expectation.rule).with_context(|| {
            format!("rule `{}` not found in analysed modules", expectation.rule)
        })?;

        if let Some(expected_line) = expectation.line {
            if info.line != expected_line {
                bail!(
                    "rule `{}` line mismatch: expected {expected_line}, found {}",
                    expectation.rule,
                    info.line
                );
            }
        }

        if let Some(expected_col) = expectation.col {
            if info.col != expected_col {
                bail!(
                    "rule `{}` column mismatch: expected {expected_col}, found {}",
                    expectation.rule,
                    info.col
                );
            }
        }

        check_fact(
            &expectation.rule,
            &expectation.r#type,
            expectation,
            &info.fact,
        )?;
    }

    Ok(())
}

fn check_exprs(case: &TypeCase, exprs: &[ExprInfo], result: &TypeAnalysisResult) -> Result<()> {
    for expectation in &case.exprs {
        let matches: Vec<&ExprInfo> = exprs
            .iter()
            .filter(|info| info.text == expectation.expr.trim())
            .collect();

        let target = match (matches.len(), expectation.line, expectation.col) {
            (0, _, _) => {
                bail!("expression `{}` not found", expectation.expr.trim());
            }
            (1, _, _) => matches[0],
            (_, Some(line), col) => matches
                .iter()
                .find(|info| info.line == line && col.is_none_or(|c| info.col == c))
                .copied()
                .with_context(|| {
                    format!(
                        "expression `{}` not found at line {line}{}",
                        expectation.expr.trim(),
                        col.map_or(String::new(), |c| format!(" col {c}"))
                    )
                })?,
            (n, None, None) => {
                bail!(
                    "expression `{}` matched {n} times; specify line/col to disambiguate",
                    expectation.expr.trim()
                );
            }
            _ => {
                bail!(
                    "expression `{}` matched multiple times; specify both line and col",
                    expectation.expr.trim()
                );
            }
        };

        let fact = result
            .expressions
            .facts
            .get_expr(target.module_idx, target.expr.eidx())
            .with_context(|| {
                format!(
                    "missing type fact for expression `{}` (module {}, expr {})",
                    expectation.expr.trim(),
                    target.module_idx,
                    target.expr.eidx()
                )
            })?;

        check_fact(
            &format!(
                "expression `{}` (line {}, col {})",
                expectation.expr.trim(),
                target.line,
                target.col
            ),
            &expectation.r#type,
            expectation,
            fact,
        )?;
    }

    Ok(())
}

fn check_diagnostics(case: &TypeCase, result: &TypeAnalysisResult) -> Result<()> {
    if case.diagnostics.is_empty() {
        if !result.diagnostics.is_empty() {
            bail!(
                "expected no diagnostics but found {} entries: {}",
                result.diagnostics.len(),
                summarize_diagnostics(&result.diagnostics)
            );
        }
        return Ok(());
    }

    if result.diagnostics.len() != case.diagnostics.len() {
        bail!(
            "diagnostic count mismatch: expected {}, found {} (actual: {})",
            case.diagnostics.len(),
            result.diagnostics.len(),
            summarize_diagnostics(&result.diagnostics)
        );
    }

    for (idx, (expected, actual)) in case
        .diagnostics
        .iter()
        .zip(result.diagnostics.iter())
        .enumerate()
    {
        if let Some(kind) = &expected.kind {
            let actual_kind = format_diag_kind(&actual.kind);
            if actual_kind != kind.as_str() {
                bail!(
                    "diagnostic #{idx} kind mismatch: expected `{}`, found `{actual_kind}`",
                    kind
                );
            }
        }

        if let Some(message) = &expected.message {
            if !actual.message.contains(message) {
                bail!(
                    "diagnostic #{idx} message mismatch: expected substring `{message}`, actual `{}`",
                    actual.message
                );
            }
        }

        if let Some(line) = expected.line {
            if actual.line != line {
                bail!(
                    "diagnostic #{idx} line mismatch: expected {line}, found {}",
                    actual.line
                );
            }
        }

        if let Some(col) = expected.col {
            if actual.col != col {
                bail!(
                    "diagnostic #{idx} column mismatch: expected {col}, found {}",
                    actual.col
                );
            }
        }
    }

    Ok(())
}

fn summarize_diagnostics(diags: &[crate::type_analysis::TypeDiagnostic]) -> String {
    diags
        .iter()
        .map(|diag| {
            format!(
                "{}:{} {}: {}",
                diag.line,
                diag.col,
                format_diag_kind(&diag.kind),
                diag.message
            )
        })
        .collect::<Vec<_>>()
        .join("; ")
}

fn check_fact<T>(
    label: &str,
    expected_type: &TypeExpectation,
    expectation: &T,
    fact: &TypeFact,
) -> Result<()>
where
    T: FactExpectation,
{
    expected_type
        .matches(fact.descriptor())
        .with_context(|| format!("{label}: type mismatch"))?;

    if let Some(expected) = expectation.expected_constant()? {
        match &fact.constant {
            ConstantValue::Known(actual) => {
                let processed = process_value(&expected)?;
                if processed != *actual {
                    bail!(
                        "{label}: constant mismatch. expected {}, found {}",
                        serde_yaml::to_string(&processed)?,
                        serde_yaml::to_string(actual)?
                    );
                }
            }
            ConstantValue::Unknown => {
                bail!("{label}: expected constant value but analysis returned unknown");
            }
        }
    }

    if let Some(expected_schema) = expectation.expect_schema_backed() {
        let is_schema = matches!(fact.descriptor, TypeDescriptor::Schema(_));
        if is_schema != expected_schema {
            bail!("{label}: schema-backed mismatch. expected {expected_schema}, found {is_schema}");
        }
    }

    if let Some(expected_prov) = expectation.expected_provenance()? {
        if discriminant(&fact.provenance) != discriminant(&expected_prov) {
            bail!(
                "{label}: provenance mismatch. expected {:?}, found {:?}",
                expected_prov,
                fact.provenance
            );
        }
    }

    Ok(())
}

trait FactExpectation {
    fn expected_constant(&self) -> Result<Option<Value>>;
    fn expected_provenance(&self) -> Result<Option<TypeProvenance>>;
    fn expect_schema_backed(&self) -> Option<bool>;
}

impl FactExpectation for RuleExpectation {
    fn expected_constant(&self) -> Result<Option<Value>> {
        Ok(self.constant.clone())
    }

    fn expected_provenance(&self) -> Result<Option<TypeProvenance>> {
        parse_provenance(self.provenance.as_deref())
    }

    fn expect_schema_backed(&self) -> Option<bool> {
        self.schema_backed
    }
}

impl FactExpectation for ExprExpectation {
    fn expected_constant(&self) -> Result<Option<Value>> {
        Ok(self.constant.clone())
    }

    fn expected_provenance(&self) -> Result<Option<TypeProvenance>> {
        parse_provenance(self.provenance.as_deref())
    }

    fn expect_schema_backed(&self) -> Option<bool> {
        self.schema_backed
    }
}

fn parse_provenance(raw: Option<&str>) -> Result<Option<TypeProvenance>> {
    let Some(raw) = raw else {
        return Ok(None);
    };

    let prov = match raw {
        "SchemaInput" => TypeProvenance::SchemaInput,
        "SchemaData" => TypeProvenance::SchemaData,
        "Literal" => TypeProvenance::Literal,
        "Assignment" => TypeProvenance::Assignment,
        "Propagated" => TypeProvenance::Propagated,
        "Builtin" => TypeProvenance::Builtin,
        "Rule" => TypeProvenance::Rule,
        "Unknown" => TypeProvenance::Unknown,
        other => bail!("unknown provenance `{other}`"),
    };

    Ok(Some(prov))
}

impl TypeExpectation {
    fn matches(&self, descriptor: &TypeDescriptor) -> Result<()> {
        match self {
            TypeExpectation::Simple(name) => match_simple_type(name, descriptor),
            TypeExpectation::Detailed(detail) => match_detailed_type(detail, descriptor),
        }
    }
}

fn match_simple_type(expected: &str, descriptor: &TypeDescriptor) -> Result<()> {
    let expected = expected.trim();
    let actual = descriptor_kind(descriptor);
    if !equals_ignore_ascii_case(expected, actual) {
        bail!("expected type `{expected}`, found `{actual}`");
    }
    Ok(())
}

fn match_detailed_type(
    detail: &DetailedTypeExpectation,
    descriptor: &TypeDescriptor,
) -> Result<()> {
    let actual = structural_view(descriptor);
    let kind = detail.kind.trim();

    match kind.to_ascii_lowercase().as_str() {
        "any" => {
            if !matches!(actual, StructuralType::Any) {
                bail!("expected Any but found {}", structural_kind_name(&actual));
            }
        }
        "boolean" => require_kind("Boolean", &actual)?,
        "number" => require_kind("Number", &actual)?,
        "integer" => require_kind("Integer", &actual)?,
        "string" => require_kind("String", &actual)?,
        "null" => require_kind("Null", &actual)?,
        "array" => {
            let StructuralType::Array(inner) = actual else {
                bail!("expected Array but found {}", structural_kind_name(&actual));
            };
            if let Some(expected_inner) = &detail.element {
                expected_inner.matches(&TypeDescriptor::structural((*inner).clone()))?;
            }
        }
        "set" => {
            let StructuralType::Set(inner) = actual else {
                bail!("expected Set but found {}", structural_kind_name(&actual));
            };
            if let Some(expected_inner) = &detail.element {
                expected_inner.matches(&TypeDescriptor::structural((*inner).clone()))?;
            }
        }
        "object" => {
            let StructuralType::Object(shape) = actual else {
                bail!(
                    "expected Object but found {}",
                    structural_kind_name(&actual)
                );
            };
            if let Some(props) = &detail.properties {
                for (name, expected_type) in props {
                    let Some(actual_field) = shape.fields.get(name) else {
                        bail!("expected object field `{name}` not found");
                    };
                    expected_type.matches(&TypeDescriptor::structural(actual_field.clone()))?;
                }
            }
        }
        "union" => {
            let StructuralType::Union(actual_variants) = actual else {
                bail!("expected Union but found {}", structural_kind_name(&actual));
            };

            if let Some(expected_variants) = &detail.variants {
                if actual_variants.len() != expected_variants.len() {
                    bail!(
                        "expected {} union variants but found {}",
                        expected_variants.len(),
                        actual_variants.len()
                    );
                }

                let mut remaining: Vec<StructuralType> = actual_variants.clone();

                for expected_variant in expected_variants {
                    let position = remaining.iter().position(|candidate| {
                        expected_variant
                            .matches(&TypeDescriptor::structural(candidate.clone()))
                            .is_ok()
                    });

                    if let Some(idx) = position {
                        remaining.remove(idx);
                    } else {
                        bail!(
                            "union variant {:?} not found in actual type",
                            expected_variant
                        );
                    }
                }
            }
        }
        other => {
            bail!("unknown detailed type kind `{other}`");
        }
    }

    Ok(())
}

fn structural_view(descriptor: &TypeDescriptor) -> StructuralType {
    match descriptor {
        TypeDescriptor::Structural(ty) => ty.clone(),
        TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
    }
}

fn descriptor_kind(descriptor: &TypeDescriptor) -> &'static str {
    match descriptor {
        TypeDescriptor::Structural(ty) => structural_kind_name(ty),
        TypeDescriptor::Schema(_) => "Schema",
    }
}

fn structural_kind_name(ty: &StructuralType) -> &'static str {
    match ty {
        StructuralType::Any => "Any",
        StructuralType::Boolean => "Boolean",
        StructuralType::Number => "Number",
        StructuralType::Integer => "Integer",
        StructuralType::String => "String",
        StructuralType::Null => "Null",
        StructuralType::Array(_) => "Array",
        StructuralType::Set(_) => "Set",
        StructuralType::Object(_) => "Object",
        StructuralType::Union(_) => "Union",
        StructuralType::Enum(_) => "Enum",
        StructuralType::Unknown => "Unknown",
    }
}

fn require_kind(expected: &str, actual: &StructuralType) -> Result<()> {
    if !equals_ignore_ascii_case(expected, structural_kind_name(actual)) {
        bail!(
            "expected {expected} but found {}",
            structural_kind_name(actual)
        );
    }
    Ok(())
}

fn equals_ignore_ascii_case(a: &str, b: &str) -> bool {
    a.eq_ignore_ascii_case(b)
}

fn format_diag_kind(kind: &crate::type_analysis::TypeDiagnosticKind) -> &'static str {
    match kind {
        crate::type_analysis::TypeDiagnosticKind::SchemaViolation => "SchemaViolation",
        crate::type_analysis::TypeDiagnosticKind::InternalError => "InternalError",
        crate::type_analysis::TypeDiagnosticKind::TypeMismatch => "TypeMismatch",
        crate::type_analysis::TypeDiagnosticKind::UnreachableStatement => "UnreachableStatement",
    }
}

trait DescriptorExt {
    fn descriptor(&self) -> &TypeDescriptor;
}

impl DescriptorExt for TypeFact {
    fn descriptor(&self) -> &TypeDescriptor {
        &self.descriptor
    }
}

#[test_resources("tests/type_analysis/**/*.yaml")]
fn run(path: &str) {
    yaml_test_impl(path).unwrap();
}

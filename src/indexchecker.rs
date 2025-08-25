// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(debug_assertions)]

use crate::ast::*;
use alloc::collections::BTreeSet;
use alloc::format;
use anyhow::{bail, Result};

// Ensures that indexes are unique and continuous, starting from 0.
#[derive(Default)]
pub struct IndexChecker<'a> {
    eidx: BTreeSet<u32>,
    sidx: BTreeSet<u32>,
    qidx: BTreeSet<u32>,
    ridx: BTreeSet<u32>,
    module: Option<&'a Module>,
}

#[cfg(debug_assertions)]
impl<'a> IndexChecker<'a> {
    fn check_query(&mut self, query: &Query) -> Result<()> {
        let qidx = query.qidx;
        if !self.qidx.insert(qidx) {
            bail!(query
                .span
                .error(format!("query with qidx {qidx} already exists").as_str()));
        }
        self.check_qidx(query)?;

        for stmt in &query.stmts {
            if !self.sidx.insert(stmt.sidx) {
                bail!(stmt
                    .span
                    .error(format!("statement with sidx {} already exists", stmt.sidx).as_str()));
            }
            self.check_sidx(stmt)?;
            match &stmt.literal {
                Literal::Every { domain, query, .. } => {
                    self.check_eidx(domain)?;
                    self.check_query(query.as_ref())?;
                }
                Literal::SomeVars { .. } => (),
                Literal::Expr { expr, .. } => self.check_eidx(expr.as_ref())?,
                Literal::SomeIn {
                    key,
                    value,
                    collection,
                    ..
                } => {
                    if let Some(key) = key {
                        self.check_eidx(key.as_ref())?;
                    }
                    self.check_eidx(value.as_ref())?;
                    self.check_eidx(collection.as_ref())?;
                }
                Literal::NotExpr { expr, .. } => {
                    self.check_eidx(expr.as_ref())?;
                }
            }
            for with_mod in &stmt.with_mods {
                self.check_eidx(with_mod.refr.as_ref())?;
                self.check_eidx(with_mod.r#as.as_ref())?;
            }
        }

        Ok(())
    }

    fn check_eidx(&mut self, expr: &Expr) -> Result<()> {
        use Expr::*;
        let eidx = expr.eidx();
        if !self.eidx.insert(eidx) {
            bail!(expr
                .span()
                .error(format!("expression with eidx {eidx} already exists").as_str()));
        }

        // Check that the span in expression_spans matches the expression's span
        if let Some(module) = self.module {
            if let Some(stored_span) = module.expression_spans.get(eidx as usize) {
                let expr_span = expr.span();
                if stored_span.start != expr_span.start || stored_span.end != expr_span.end {
                    bail!(expr
                        .span()
                        .error(format!(
                            "expression span position mismatch at eidx {}: stored span positions ({}..{}) != expression span positions ({}..{})",
                            eidx,
                            stored_span.start,
                            stored_span.end,
                            expr_span.start,
                            expr_span.end
                        ).as_str()));
                }
            } else {
                bail!(expr
                    .span()
                    .error(format!("missing span in expression_spans for eidx {}", eidx).as_str()));
            }
        }

        match expr {
            String { .. }
            | RawString { .. }
            | Number { .. }
            | Bool { .. }
            | Null { .. }
            | Var { .. } => (),

            Array { items, .. } => {
                for elem in items {
                    self.check_eidx(elem.as_ref())?;
                }
            }
            Set { items, .. } => {
                for elem in items {
                    self.check_eidx(elem.as_ref())?;
                }
            }

            Object { fields, .. } => {
                for pair in fields {
                    self.check_eidx(pair.1.as_ref())?;
                    self.check_eidx(pair.2.as_ref())?;
                }
            }

            ArrayCompr { term, query, .. } => {
                self.check_eidx(term.as_ref())?;
                self.check_query(query.as_ref())?;
            }

            SetCompr { term, query, .. } => {
                self.check_eidx(term.as_ref())?;
                self.check_query(query.as_ref())?;
            }

            ObjectCompr {
                key, value, query, ..
            } => {
                self.check_eidx(key.as_ref())?;
                self.check_eidx(value.as_ref())?;
                self.check_query(query.as_ref())?;
            }

            Call { fcn, params, .. } => {
                self.check_eidx(fcn.as_ref())?;
                for param in params {
                    self.check_eidx(param.as_ref())?;
                }
            }

            UnaryExpr { expr, .. } => {
                self.check_eidx(expr.as_ref())?;
            }

            RefBrack { refr, index, .. } => {
                self.check_eidx(refr.as_ref())?;
                self.check_eidx(index.as_ref())?;
            }
            RefDot { refr, .. } => {
                self.check_eidx(refr.as_ref())?;
            }

            BinExpr { lhs, rhs, .. }
            | BoolExpr { lhs, rhs, .. }
            | ArithExpr { lhs, rhs, .. }
            | AssignExpr { lhs, rhs, .. } => {
                self.check_eidx(lhs.as_ref())?;
                self.check_eidx(rhs.as_ref())?;
            }

            Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key {
                    self.check_eidx(key.as_ref())?;
                }
                self.check_eidx(value.as_ref())?;
                self.check_eidx(collection.as_ref())?;
            }

            #[cfg(feature = "rego-extensions")]
            OrExpr { lhs, rhs, .. } => {
                self.check_eidx(lhs.as_ref())?;
                self.check_eidx(rhs.as_ref())?;
            }
        }

        Ok(())
    }

    fn check_sidx(&mut self, stmt: &LiteralStmt) -> Result<()> {
        let sidx = stmt.sidx;

        // Check that the span in statement_spans matches the statement's span
        if let Some(module) = self.module {
            if let Some(stored_span) = module.statement_spans.get(sidx as usize) {
                let stmt_span = &stmt.span;
                if stored_span.start != stmt_span.start || stored_span.end != stmt_span.end {
                    bail!(stmt
                        .span
                        .error(format!(
                            "statement span position mismatch at sidx {}: stored span positions ({}..{}) != statement span positions ({}..{})",
                            sidx,
                            stored_span.start,
                            stored_span.end,
                            stmt_span.start,
                            stmt_span.end
                        ).as_str()));
                }
            } else {
                bail!(stmt
                    .span
                    .error(format!("missing span in statement_spans for sidx {}", sidx).as_str()));
            }
        }

        Ok(())
    }

    fn check_qidx(&mut self, query: &Query) -> Result<()> {
        let qidx = query.qidx;

        // Check that the span in query_spans matches the query's span
        if let Some(module) = self.module {
            if let Some(stored_span) = module.query_spans.get(qidx as usize) {
                let query_span = &query.span;
                if stored_span.start != query_span.start || stored_span.end != query_span.end {
                    bail!(query
                        .span
                        .error(format!(
                            "query span position mismatch at qidx {}: stored span positions ({}..{}) != query span positions ({}..{})",
                            qidx,
                            stored_span.start,
                            stored_span.end,
                            query_span.start,
                            query_span.end
                        ).as_str()));
                }
            } else {
                bail!(query
                    .span
                    .error(format!("missing span in query_spans for qidx {}", qidx).as_str()));
            }
        }

        Ok(())
    }

    fn check_ridx(&mut self, rule: &Rule) -> Result<()> {
        let ridx = rule.ridx();

        // Check that the span in rule_spans matches the rule's span
        if let Some(module) = self.module {
            if let Some(stored_span) = module.rule_spans.get(ridx as usize) {
                let rule_span = rule.span();
                if stored_span.start != rule_span.start || stored_span.end != rule_span.end {
                    bail!(rule
                        .span()
                        .error(format!(
                            "rule span position mismatch at ridx {}: stored span positions ({}..{}) != rule span positions ({}..{})",
                            ridx,
                            stored_span.start,
                            stored_span.end,
                            rule_span.start,
                            rule_span.end
                        ).as_str()));
                }
            } else {
                bail!(rule
                    .span()
                    .error(format!("missing span in rule_spans for ridx {}", ridx).as_str()));
            }
        }

        if !self.ridx.insert(ridx) {
            bail!(rule
                .span()
                .error(format!("ridx {} was seen before", ridx).as_str()));
        }

        Ok(())
    }

    fn check_rule_assign(&mut self, assign: &RuleAssign) -> Result<()> {
        self.check_eidx(&assign.value)
    }

    fn check_rule_body(&mut self, body: &RuleBody) -> Result<()> {
        if let Some(assign) = &body.assign {
            self.check_rule_assign(assign)?;
        }
        self.check_query(&body.query)
    }

    fn check_rule_heade(&mut self, head: &RuleHead) -> Result<()> {
        match head {
            RuleHead::Compr { refr, assign, .. } => {
                self.check_eidx(refr.as_ref())?;
                if let Some(assign) = assign {
                    self.check_rule_assign(assign)?;
                }
            }
            RuleHead::Func {
                refr, args, assign, ..
            } => {
                self.check_eidx(refr.as_ref())?;
                if let Some(assign) = assign {
                    self.check_rule_assign(assign)?;
                }
                for arg in args {
                    self.check_eidx(arg.as_ref())?;
                }
            }

            RuleHead::Set { refr, key, .. } => {
                self.check_eidx(refr.as_ref())?;
                if let Some(key) = key {
                    self.check_eidx(key.as_ref())?;
                }
            }
        }

        Ok(())
    }

    fn check_gathered_indexes(
        &self,
        num_idx: u32,
        idx_set: &BTreeSet<u32>,
        idx_type: &str,
    ) -> Result<()> {
        if num_idx == 0 {
            if !idx_set.is_empty() {
                bail!("no {idx_type} indexes should be collected when num_{idx_type}s is 0");
            }
            return Ok(());
        }

        if idx_set
            .first()
            .unwrap_or_else(|| panic!("no {idx_type} indexes collected"))
            != &0
        {
            bail!("start {idx_type} index must be 0");
        }

        let last_idx = idx_set
            .last()
            .unwrap_or_else(|| panic!("no {idx_type} indexes collected"));
        if last_idx != &(num_idx - 1) {
            bail!(
                "last {idx_type} index must be {} got {last_idx} instead",
                num_idx - 1
            );
        }

        Ok(())
    }
    pub fn check_module(&mut self, module: &'a Module) -> Result<()> {
        self.module = Some(module);

        self.check_eidx(module.package.refr.as_ref())?;
        for import in &module.imports {
            self.check_eidx(import.refr.as_ref())?;
        }

        for rule in &module.policy {
            self.check_ridx(rule.as_ref())?;
            match rule.as_ref() {
                Rule::Spec { head, bodies, .. } => {
                    self.check_rule_heade(head)?;
                    for body in bodies {
                        self.check_rule_body(body)?;
                    }
                }
                Rule::Default {
                    refr, args, value, ..
                } => {
                    self.check_eidx(refr.as_ref())?;
                    for arg in args {
                        self.check_eidx(arg.as_ref())?;
                    }
                    self.check_eidx(value.as_ref())?;
                }
            }
        }

        if module.num_expressions == 0 {
            bail!("module must have at least one expression");
        }

        self.check_gathered_indexes(module.num_expressions, &self.eidx, "expression")?;
        self.check_gathered_indexes(module.num_statements, &self.sidx, "statement")?;
        self.check_gathered_indexes(module.num_queries, &self.qidx, "query")?;
        self.check_gathered_indexes(module.num_rules, &self.ridx, "rule")?;

        Ok(())
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::panic_in_result_fn,
    clippy::arithmetic_side_effects,
    clippy::shadow_unrelated,
    clippy::unused_self,
    clippy::pattern_type_mismatch
)]
#![cfg(debug_assertions)]
#![allow(clippy::panic)] // debug-only index checks panic on invariants

use crate::ast::*;
use alloc::collections::BTreeSet;
use alloc::format;
use anyhow::{bail, Result};

// Ensures that indexes are unique and continuous, starting from 0.
#[derive(Default)]
pub struct IndexChecker {
    eidx: BTreeSet<u32>,
    sidx: BTreeSet<u32>,
    qidx: BTreeSet<u32>,
}

#[cfg(debug_assertions)]
impl IndexChecker {
    fn check_query(&mut self, query: &Query) -> Result<()> {
        let qidx = query.qidx;
        if !self.qidx.insert(qidx) {
            bail!(query
                .span
                .error(format!("query with qidx {qidx} already exists").as_str()));
        }

        for stmt in &query.stmts {
            if !self.sidx.insert(stmt.sidx) {
                bail!(stmt
                    .span
                    .error(format!("statement with sidx {} already exists", stmt.sidx).as_str()));
            }
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
    pub fn check_module(&mut self, module: &Module) -> Result<()> {
        self.check_eidx(module.package.refr.as_ref())?;
        for import in &module.imports {
            self.check_eidx(import.refr.as_ref())?;
        }

        for rule in &module.policy {
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

        Ok(())
    }
}

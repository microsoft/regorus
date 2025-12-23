#![allow(
    clippy::if_then_some_else_none,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};

use anyhow::Result;

use crate::ast::Expr::{self, *};
use crate::ast::{AssignOp, ExprRef};
use crate::lexer::{SourceStr, Span};
use crate::value::Value;

#[derive(Clone, Default, Debug)]
pub struct Scope {
    pub locals: BTreeMap<SourceStr, Span>,
    pub unscoped: BTreeSet<SourceStr>,
    pub inputs: BTreeSet<SourceStr>,
    pub uses_input: bool,
}

pub fn traverse(expr: &ExprRef, f: &mut dyn FnMut(&ExprRef) -> Result<bool>) -> Result<()> {
    if !f(expr)? {
        return Ok(());
    }

    match expr.as_ref() {
        Expr::String { .. }
        | RawString { .. }
        | Number { .. }
        | Bool { .. }
        | Null { .. }
        | Var { .. } => (),

        Array { items, .. } | Set { items, .. } => {
            for item in items {
                traverse(item, f)?;
            }
        }
        Object { fields, .. } => {
            for (_, key, value) in fields {
                traverse(key, f)?;
                traverse(value, f)?;
            }
        }

        ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => (),

        Call { params, .. } => {
            for param in params {
                traverse(param, f)?;
            }
        }

        UnaryExpr { expr, .. } => traverse(expr, f)?,

        RefDot { refr, .. } => traverse(refr, f)?,

        RefBrack { refr, index, .. } => {
            traverse(refr, f)?;
            traverse(index, f)?;
        }

        BinExpr { lhs, rhs, .. }
        | BoolExpr { lhs, rhs, .. }
        | ArithExpr { lhs, rhs, .. }
        | AssignExpr { lhs, rhs, .. } => {
            traverse(lhs, f)?;
            traverse(rhs, f)?;
        }

        #[cfg(feature = "rego-extensions")]
        OrExpr { lhs, rhs, .. } => {
            traverse(lhs, f)?;
            traverse(rhs, f)?;
        }

        Membership {
            key,
            value,
            collection,
            ..
        } => {
            if let Some(key) = key.as_ref() {
                traverse(key, f)?;
            }
            traverse(value, f)?;
            traverse(collection, f)?;
        }
    }

    Ok(())
}

pub fn var_exists(var: &Span, parent_scopes: &[Scope]) -> bool {
    let name = var.source_str();

    for scope in parent_scopes.iter().rev() {
        if scope.unscoped.contains(&name) {
            return true;
        }

        if let Some(span) = scope.locals.get(&name) {
            if span.line <= var.line {
                return true;
            }
        }
    }

    false
}

pub fn gather_assigned_vars(
    expr: &ExprRef,
    can_shadow: bool,
    parent_scopes: &[Scope],
    scope: &mut Scope,
) -> Result<()> {
    traverse(expr, &mut |node| match node.as_ref() {
        Var { span, .. } if matches!(span.text(), "_" | "input" | "data") => {
            if span.text() == "input" {
                scope.uses_input = true;
            }
            Ok(false)
        }
        Var { span, .. } if can_shadow => {
            scope.locals.insert(span.source_str(), span.clone());
            Ok(false)
        }
        Var { span, .. } if var_exists(span, parent_scopes) => {
            scope.inputs.insert(span.source_str());
            Ok(false)
        }
        Var { span, .. } => {
            scope.unscoped.insert(span.source_str());
            Ok(false)
        }
        Array { .. } | Object { .. } => Ok(true),
        _ => Ok(false),
    })
}

pub fn gather_input_vars(expr: &ExprRef, parent_scopes: &[Scope], scope: &mut Scope) -> Result<()> {
    traverse(expr, &mut |node| match node.as_ref() {
        Var { span, .. } => {
            let name = span.source_str();
            if name.text() == "input" {
                scope.uses_input = true;
            } else if !scope.unscoped.contains(&name) && var_exists(span, parent_scopes) {
                scope.inputs.insert(name);
            }
            Ok(false)
        }
        _ => Ok(true),
    })
}

pub fn gather_loop_vars(expr: &ExprRef, parent_scopes: &[Scope], scope: &mut Scope) -> Result<()> {
    traverse(expr, &mut |node| match node.as_ref() {
        Var { span, .. } if span.text() == "input" => {
            scope.uses_input = true;
            Ok(false)
        }
        RefBrack { index, .. } => {
            gather_assigned_vars(index, false, parent_scopes, scope)?;
            Ok(true)
        }
        _ => Ok(true),
    })
}

pub fn gather_vars(
    expr: &ExprRef,
    can_shadow: bool,
    parent_scopes: &[Scope],
    scope: &mut Scope,
) -> Result<()> {
    if let AssignExpr { op, lhs, rhs, .. } = expr.as_ref() {
        gather_assigned_vars(lhs, *op == AssignOp::ColEq, parent_scopes, scope)?;
        gather_assigned_vars(rhs, false, parent_scopes, scope)?;
    } else {
        gather_assigned_vars(expr, can_shadow, parent_scopes, scope)?;
    }

    gather_input_vars(expr, parent_scopes, scope)?;
    gather_loop_vars(expr, parent_scopes, scope)
}

pub fn collect_expr_dependencies(expr: &ExprRef) -> Option<BTreeSet<String>> {
    let mut deps = BTreeSet::new();
    let mut valid = true;

    if traverse(expr, &mut |node| match node.as_ref() {
        Var { value, .. } => {
            if let Value::String(name) = value {
                let var = name.as_ref();
                if var != "_" {
                    deps.insert(var.to_string());
                }
            }
            Ok(false)
        }
        ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => {
            valid = false;
            Ok(false)
        }
        #[cfg(feature = "rego-extensions")]
        OrExpr { .. } => {
            valid = false;
            Ok(false)
        }
        _ => Ok(true),
    })
    .is_err()
    {
        return None;
    }

    if valid {
        Some(deps)
    } else {
        None
    }
}

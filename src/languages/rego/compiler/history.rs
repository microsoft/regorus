// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Lowering of `history.require(request, language)` / `history.forbid(...)`
//! into one typed history-table rule evaluated by a single `HistoryStep`.

#![allow(clippy::pattern_type_mismatch)]

use super::{Compiler, CompilerError, Register, Result, SpannedCompilerError};
use crate::ast::{ArithOp, BinOp, BoolOp, Expr, ExprRef};
use crate::languages::history_table::{
    table_rule, SourceComponent, SourceEvent, ACTION, PRINCIPAL, RESOURCE,
};
use crate::lexer::Span;
use crate::rvm::instructions::HistoryStepParams;
use crate::rvm::program::HistoryTable;
use crate::rvm::Instruction;
use crate::value::Value;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};

/// Maximum number of history events one `HistoryStep` dispatch consumes.
pub const HISTORY_BATCH_SIZE: u32 = 256;

const COORDINATES: [(&str, Component); 3] = [
    ("principal", PRINCIPAL),
    ("action", ACTION),
    ("resource", RESOURCE),
];

type Event<'a> = SourceEvent<'a>;

pub(super) fn history_mode(path: &str) -> Option<RuleMode> {
    match path {
        "history.require" => Some(RuleMode::Require),
        "history.forbid" => Some(RuleMode::Forbid),
        _ => None,
    }
}

impl Compiler<'_> {
    pub(super) fn compile_history_rule(
        &mut self,
        mode: RuleMode,
        params: &[ExprRef],
        span: &Span,
    ) -> Result<Register> {
        let [request, language] = params else {
            return Err(general(
                "history.require and history.forbid take two arguments: a request pattern and a history expression",
            )
            .at(span));
        };
        let rule = Rule::new(mode, lower_request(request)?, lower_language(language)?);
        let table_rule = table_rule(&rule)
            .map_err(|error| general(format!("invalid history rule: {error}")).at(span))?;
        if self.program.history_tables.is_empty() {
            self.program
                .add_history_table(HistoryTable { rules: Vec::new() });
        }
        let rules = &mut self
            .program
            .history_tables
            .first_mut()
            .ok_or_else(|| general("missing history table").at(span))?
            .rules;
        let rule_index =
            u16::try_from(rules.len()).map_err(|_| general("too many history rules").at(span))?;
        rules.push(table_rule);
        let dest = self.alloc_register()?;
        let params_index = self.program.add_history_step_params(HistoryStepParams {
            table: 0,
            rule: rule_index,
            batch_size: HISTORY_BATCH_SIZE,
            dest,
        });
        self.emit_instruction(Instruction::HistoryStep { params_index }, span);
        Ok(dest)
    }
}

fn general(message: impl Into<String>) -> CompilerError {
    CompilerError::General {
        message: message.into(),
    }
}

fn invalid(expr: &Expr, message: impl Into<String>) -> SpannedCompilerError {
    general(message).at(expr.span())
}

fn text(value: &Value) -> Option<&str> {
    match value {
        Value::String(text) => Some(text),
        _ => None,
    }
}

fn var_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Var { value, .. } => text(value),
        _ => None,
    }
}

fn string_literal(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::String { value, .. } | Expr::RawString { value, .. } => text(value),
        _ => None,
    }
}

fn coordinate(name: &str) -> Option<Component> {
    COORDINATES
        .iter()
        .find(|&&(coordinate, _)| coordinate == name)
        .map(|&(_, component)| component)
}

fn tagged(component: Component, text: &str) -> SourceComponent<'_> {
    match component {
        PRINCIPAL => SourceComponent::Principal(text),
        ACTION => SourceComponent::Action(text),
        _ => SourceComponent::Resource(text),
    }
}

fn lower_request(expr: &Expr) -> Result<Head<Event<'_>>> {
    const SHAPE: &str =
        "request pattern must be an object with string keys principal, action, resource";
    let Expr::Object { fields, .. } = expr else {
        return Err(invalid(expr, SHAPE));
    };
    let mut slots: [Option<ComponentPattern<SourceComponent<'_>>>; 3] = [None, None, None];
    for (_, key, value) in fields {
        let (name, component) = string_literal(key)
            .and_then(|name| Some((name, coordinate(name)?)))
            .ok_or_else(|| invalid(key, SHAPE))?;
        let slot = slots
            .get_mut(component.index())
            .ok_or_else(|| invalid(key, SHAPE))?;
        if slot.is_some() {
            return Err(invalid(
                key,
                format!("duplicate request coordinate `{name}`"),
            ));
        }
        *slot = Some(if let Some(constant) = string_literal(value) {
            ComponentPattern::constant(tagged(component, constant))
        } else {
            match var_name(value) {
                Some("_") => continue,
                Some(variable) if coordinate(variable).is_some() => {
                    return Err(invalid(
                        value,
                        format!("variable `{variable}` shadows the coordinate name; rename it"),
                    ));
                }
                Some("any") => {
                    return Err(invalid(
                        value,
                        "variable `any` names the universal history; rename it",
                    ));
                }
                Some(variable) => ComponentPattern::variable(variable),
                None => {
                    return Err(invalid(
                        value,
                        format!(
                            "request coordinate `{name}` must be a string constant or a variable"
                        ),
                    ));
                }
            }
        });
    }
    // `$` never occurs in Rego identifiers, so wildcard slots bind unreachable variables.
    let [principal, action, resource] = slots;
    Ok(Head::new([
        principal.unwrap_or_else(|| ComponentPattern::variable("$principal")),
        action.unwrap_or_else(|| ComponentPattern::variable("$action")),
        resource.unwrap_or_else(|| ComponentPattern::variable("$resource")),
    ]))
}

fn lower_language(expr: &Expr) -> Result<RegexExpr<Event<'_>>> {
    Ok(match expr {
        Expr::Var { .. } => match var_name(expr) {
            Some("any") => RegexExpr::all(),
            name => {
                return Err(invalid(
                    expr,
                    format!(
                        "unknown name `{}` in history expression",
                        name.unwrap_or_default()
                    ),
                ));
            }
        },
        Expr::Bool {
            value: Value::Bool(value),
            ..
        } => RegexExpr::test(if *value {
            TestExpr::true_test()
        } else {
            TestExpr::false_test()
        }),
        Expr::Set { items, .. } => RegexExpr::test(TestExpr::and(
            items
                .iter()
                .map(|item| lower_atom(item))
                .collect::<Result<Vec<_>>>()?,
        )),
        Expr::Array { items, .. } => RegexExpr::concat(
            items
                .iter()
                .map(|item| lower_language(item))
                .collect::<Result<Vec<_>>>()?,
        ),
        Expr::BinExpr { op, lhs, rhs, .. } => {
            let pair = [lower_language(lhs)?, lower_language(rhs)?];
            match op {
                BinOp::Union => RegexExpr::union(pair),
                BinOp::Intersection => RegexExpr::intersect(pair),
            }
        }
        Expr::ArithExpr {
            op: ArithOp::Sub,
            lhs,
            rhs,
            ..
        } => RegexExpr::intersect([
            lower_language(lhs)?,
            RegexExpr::complement(lower_language(rhs)?),
        ]),
        Expr::Call { fcn, params, .. } if var_name(fcn) == Some("star") => {
            let [inner] = params.as_slice() else {
                return Err(invalid(expr, "star takes one argument"));
            };
            RegexExpr::star(lower_language(inner)?)
        }
        // `set()` is the empty set literal: one event with no constraint.
        Expr::Call { fcn, params, .. } if var_name(fcn) == Some("set") && params.is_empty() => {
            RegexExpr::test(TestExpr::and([]))
        }
        _ => {
            return Err(invalid(
                expr,
                "unsupported history expression; expected any, true, false, a set of comparisons, an array, a | b, a & b, a - b, or star(a)",
            ));
        }
    })
}

fn lower_atom(expr: &Expr) -> Result<TestExpr<Event<'_>>> {
    const SHAPE: &str = "comparison must be `principal|action|resource == term` or `!= term`";
    let Expr::BoolExpr { op, lhs, rhs, .. } = expr else {
        return Err(invalid(expr, SHAPE));
    };
    let comparison = match op {
        BoolOp::Eq => Comparison::Eq,
        BoolOp::Ne => Comparison::Neq,
        _ => return Err(invalid(expr, SHAPE)),
    };
    let component = var_name(lhs)
        .and_then(coordinate)
        .ok_or_else(|| invalid(expr, SHAPE))?;
    let pattern = if let Some(constant) = string_literal(rhs) {
        ComponentPattern::constant(tagged(component, constant))
    } else {
        match var_name(rhs) {
            Some(variable)
                if variable != "_" && variable != "any" && coordinate(variable).is_none() =>
            {
                ComponentPattern::variable(variable)
            }
            _ => {
                return Err(invalid(
                    rhs,
                    "comparison term must be a string constant or a request variable",
                ));
            }
        }
    };
    Ok(TestExpr::atom(
        comparison,
        AtomPattern::new(component, pattern),
    ))
}

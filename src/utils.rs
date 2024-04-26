// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::builtins::*;
use crate::lexer::*;

use std::collections::BTreeMap;
use thiserror::Error;

#[macro_export]
macro_rules! bail {
    ($err:literal $(,)?) => {
        return Err(std::convert::From::from($err))
    };
    ($err:expr $(,)?) => {
        return Err(std::convert::From::from($err))
    };
}

type Result<T> = std::result::Result<T, UtilsError>;

#[derive(Error, Debug)]
pub enum UtilsError {
    #[error("not a simple ref: {0}")]
    NotASimpleRef(String),
    #[error("fullpath {full_path} was previously defined with {arity} arguments.")]
    PreviouslyDefined { full_path: String, arity: u8 },
}

pub fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
    let mut comps: Vec<&str> = vec![];
    let mut expr = Some(refr);
    while expr.is_some() {
        match expr {
            Some(Expr::RefDot { refr, field, .. }) => {
                comps.push(field.0.text());
                expr = Some(refr);
            }
            Some(Expr::RefBrack { refr, index, .. }) => {
                if let Expr::String(s) = index.as_ref() {
                    comps.push(s.0.text());
                }
                expr = Some(refr);
            }
            Some(Expr::Var(v)) => {
                comps.push(v.0.text());
                expr = None;
            }
            _ => {
                let expr = format!("{:?}", expr);
                return Err(UtilsError::NotASimpleRef(expr));
            }
        }
    }
    if let Some(d) = document {
        comps.push(d);
    };
    comps.reverse();
    Ok(comps.join("."))
}

pub type FunctionTable = BTreeMap<String, (Vec<Ref<Rule>>, u8, Ref<Module>)>;

fn get_extra_arg_impl(
    expr: &Expr,
    module: Option<&str>,
    functions: &FunctionTable,
) -> Result<Option<Ref<Expr>>> {
    if let Expr::Call { fcn, params, .. } = expr {
        let full_path = get_path_string(fcn, module)?;
        let n_args = if let Some((_, n_args, _)) = functions.get(&full_path) {
            *n_args
        } else {
            let path = get_path_string(fcn, None)?;
            if let Some((_, n_args, _)) = functions.get(&path) {
                *n_args
            } else if let Some((_, n_args)) = BUILTINS.get(path.as_str()) {
                *n_args
            } else {
                #[cfg(feature = "deprecated")]
                if let Some((_, n_args)) = DEPRECATED.get(path.as_str()) {
                    *n_args
                } else {
                    return Ok(None);
                }
                #[cfg(not(feature = "deprecated"))]
                return Ok(None);
            }
        };
        if (n_args as usize) + 1 == params.len() {
            return Ok(params.last().cloned());
        }
    }
    Ok(None)
}

pub fn get_extra_arg(
    expr: &Expr,
    module: Option<&str>,
    functions: &FunctionTable,
) -> Option<Ref<Expr>> {
    match get_extra_arg_impl(expr, module, functions) {
        Ok(a) => a,
        _ => None,
    }
}

pub fn gather_functions(modules: &[Ref<Module>]) -> Result<FunctionTable> {
    let mut table = FunctionTable::new();

    for module in modules {
        let module_path = get_path_string(&module.package.refr, Some("data"))?;
        for rule in &module.policy {
            if let Rule::Spec {
                head: RuleHead::Func { refr, args, .. },
                ..
            } = rule.as_ref()
            {
                let full_path = get_path_string(refr, Some(module_path.as_str()))?;

                if let Some((functions, arity, _)) = table.get_mut(&full_path) {
                    if args.len() as u8 != *arity {
                        return Err(UtilsError::PreviouslyDefined {
                            full_path,
                            arity: *arity,
                        });
                    }
                    functions.push(rule.clone());
                } else {
                    table.insert(
                        full_path,
                        (vec![rule.clone()], args.len() as u8, module.clone()),
                    );
                }
            }
        }
    }
    Ok(table)
}

pub fn get_root_var(mut expr: &Expr) -> Result<SourceStr> {
    let empty = expr.span().source_str().clone_empty();
    loop {
        match expr {
            Expr::Var(v) => return Ok(v.0.source_str()),
            Expr::RefDot { refr, .. } | Expr::RefBrack { refr, .. } => expr = refr,
            _ => return Ok(empty),
        }
    }
}

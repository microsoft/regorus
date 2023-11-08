// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::builtins::*;

use std::collections::BTreeMap;

use anyhow::{bail, Result};

pub fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
    let mut comps: Vec<&str> = vec![];
    let mut expr = Some(refr);
    while expr.is_some() {
        match expr {
            Some(Expr::RefDot { refr, field, .. }) => {
                comps.push(&field.text());
                expr = Some(refr);
            }
            Some(Expr::RefBrack { refr, index, .. })
                if matches!(index.as_ref(), Expr::String(_)) =>
            {
                if let Expr::String(s) = index.as_ref() {
                    comps.push(&s.text());
                    expr = Some(refr);
                }
            }
            Some(Expr::Var(v)) => {
                comps.push(&v.text());
                expr = None;
            }
            _ => bail!("internal error: not a simple ref"),
        }
    }
    if let Some(d) = document {
        comps.push(d);
    };
    comps.reverse();
    Ok(comps.join("."))
}

pub type FunctionTable<'a> = BTreeMap<String, (Vec<&'a Rule>, u8)>;

pub fn get_extra_arg<'a>(expr: &'a Expr, functions: &FunctionTable) -> Option<&'a Expr> {
    if let Expr::Call { fcn, params, .. } = expr {
        if let Ok(path) = get_path_string(fcn, None) {
            let n_args = if let Some((_, n_args)) = functions.get(&path) {
                *n_args
            } else if let Some((_, n_args)) = BUILTINS.get(path.as_str()) {
                *n_args
            } else if let Some((_, n_args)) = DEPRECATED.get(path.as_str()) {
                *n_args
            } else {
                return None;
            };
            if n_args as usize == params.len() - 1 {
                return params.last();
            }
        }
    }

    None
}

pub fn gather_functions<'a>(modules: &[&'a Module]) -> Result<FunctionTable<'a>> {
    let mut table = FunctionTable::new();

    for module in modules {
        let module_path = get_path_string(&module.package.refr, Some("data"))?;
        for rule in &module.policy {
            if let Rule::Spec {
                span,
                head: RuleHead::Func { refr, args, .. },
                ..
            } = rule
            {
                let full_path = get_path_string(refr, Some(module_path.as_str()))?;

                if let Some((functions, arity)) = table.get_mut(&full_path) {
                    if args.len() as u8 != *arity {
                        bail!(span.error(
                            format!("{full_path} was previously defined with {arity} arguments.")
                                .as_str()
                        ));
                    }
                    functions.push(rule);
                } else {
                    table.insert(full_path, (vec![rule], args.len() as u8));
                }
            }
        }
    }
    Ok(table)
}

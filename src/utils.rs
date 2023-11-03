// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::builtins::*;

use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
    let mut comps = vec![];
    let mut expr = Some(refr);
    while expr.is_some() {
        match expr {
            Some(Expr::RefDot { refr, field, .. }) => {
                comps.push(field.text());
                expr = Some(refr);
            }
            Some(Expr::RefBrack { refr, index, .. })
                if matches!(index.as_ref(), Expr::String(_)) =>
            {
                if let Expr::String(s) = index.as_ref() {
                    comps.push(s.text());
                    expr = Some(refr);
                }
            }
            Some(Expr::Var(v)) => {
                comps.push(v.text());
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

pub fn get_extra_arg<'a>(expr: &'a Expr, arities: &HashMap<String, u8>) -> Option<&'a Expr<'a>> {
    if let Expr::Call { fcn, params, .. } = expr {
        if let Ok(path) = get_path_string(fcn, None) {
            let n_args = if let Some(n_args) = arities.get(&path) {
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

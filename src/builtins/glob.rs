// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string, ensure_string_collection};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
//use glob::{Pattern, MatchOptions};
use wax::{Glob, Pattern};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("glob.match", (glob_match, 3));
    m.insert("glob.quote_meta", (quote_meta, 1));
}

const PLACE_HOLDER: &str = "\0";

fn suppress_unix_style_delimiter(s: &str) -> Result<String> {
    // Replace unix-style delimiter with placeholder so that no delimiter is
    // encountered during glob matching.
    Ok(s.replace('/', PLACE_HOLDER))
}

fn make_delimiters_unix_style(s: &str, delimiters: &[char]) -> Result<String> {
    if s.contains(PLACE_HOLDER) {
        bail!("string contains internal glob placeholder");
    }

    let has_unix_style = delimiters.contains(&'/');

    let mut s = if !has_unix_style {
        suppress_unix_style_delimiter(s)?
    } else {
        s.to_string()
    };

    for d in delimiters {
        if *d == ':' {
            s = s.replace(*d, PLACE_HOLDER);
        } else if *d != '/' {
            // Insert / before occurances of delimiter.
            s = s.replace(*d, format!("/{}/", *d).as_str());
        }
    }

    Ok(s)
}

fn make_glob<'a>(pattern: &'a str, span: &'a Span) -> Result<Glob<'a>> {
    Glob::new(pattern).or_else(|_| bail!(span.error("invalid glob")))
}

fn glob_match(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "glob.match";
    ensure_args_count(span, name, params, args, 3)?;

    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[2], &args[2])?;

    let pattern = pattern.as_ref();
    let value = value.as_ref();

    if let Value::Null = &args[1] {
        // Ensure that / is not treated as a delimiter.
        let value = suppress_unix_style_delimiter(value)?;
        let pattern = suppress_unix_style_delimiter(pattern)?;

        let glob = make_glob(&pattern, params[0].span())?;
        return Ok(Value::Bool(glob.is_match(&value[..])));
    }

    let delimiters = if let Value::Array(_) = &args[1] {
        ensure_string_collection(name, &params[1], &args[1])?
    } else {
        bail!(params[1]
            .span()
            .error(format!("{name} requires string array").as_str()));
    };

    if delimiters.iter().any(|d| d.len() > 1) {
        bail!(params[1]
            .span()
            .error("delimiters must be single character"));
    }

    let mut delimiters: Vec<char> = delimiters.iter().filter_map(|d| d.chars().next()).collect();

    if delimiters.is_empty() {
        delimiters.push('.');
    }

    let pattern = make_delimiters_unix_style(pattern, &delimiters)?;
    let value = make_delimiters_unix_style(value, &delimiters)?;

    let glob = make_glob(&pattern, params[0].span())?;
    Ok(Value::Bool(glob.is_match(&value[..])))
}

fn quote_meta(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "glob.quote_meta";
    ensure_args_count(span, name, params, args, 1)?;

    let pattern = ensure_string(name, &params[0], &args[0])?;
    // Ensure that the glob is valid.
    let _ = make_glob(&pattern, params[0].span())?;
    Ok(Value::String(pattern.as_ref().replace('*', "\\*").into()))
}

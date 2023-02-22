// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

pub mod aggregates;
pub mod arrays;
pub mod comparison;
pub mod numbers;
pub mod sets;
pub mod types;
pub mod utils;

use crate::ast::Expr;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;
use lazy_static::lazy_static;

pub type BuiltinFcn = fn(&Span, &[Expr], &[Value]) -> Result<Value>;

#[rustfmt::skip]
lazy_static! {
    pub static ref BUILTINS: HashMap<&'static str, BuiltinFcn> = {
	let mut m : HashMap<&'static str, BuiltinFcn>  = HashMap::new();

	numbers::register(&mut m);
	aggregates::register(&mut m);
	arrays::register(&mut m);
	types::register(&mut m);

	m
    };
}

pub fn must_cache(path: &str) -> Option<&'static str> {
    match path {
        "rand.intn" => Some("rand.intn"),
        _ => None,
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

pub mod comparison;
pub mod numbers;
pub mod sets;
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

	// numbers
	m.insert("abs", numbers::abs);
	m.insert("ceil", numbers::ceil);
	m.insert("floor", numbers::floor);
	m.insert("numbers.range", numbers::range);
	m.insert("rand.intn", numbers::intn);
	m.insert("round", numbers::round);		

	// sets
	m.insert("intersection", sets::intersection_of_set_of_sets);
	m.insert("union", sets::union_of_set_of_sets);
	
	m
    };
}

pub fn must_cache(path: &str) -> Option<&'static str> {
    match path {
        "rand.intn" => Some("rand.intn"),
        _ => None,
    }
}

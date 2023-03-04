// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod aggregates;
mod arrays;
mod bitwise;
pub mod comparison;
mod debugging;
pub mod numbers;
pub mod sets;
mod strings;
mod tracing;
pub mod types;
mod utils;

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
	
	// comparison functions are directly called.
	numbers::register(&mut m);
	aggregates::register(&mut m);
	arrays::register(&mut m);
	sets::register(&mut m);
	//objects::register(&mut m);
	strings::register(&mut m);
	//regex::register(&mut m);
	//glob::register(&mut m);
	bitwise::register(&mut m);
	//conversions::register(&mut m);
	//units::register(&mut m);
	types::register(&mut m);
	//encoding::register(&mut m);
	//token_signing::register(&mut m);
	//token_verification::register(&mut m);
	//time::register(&mut m);
	//cryptography::register(&mut m);
	//graphs::register(&mut m);
	//graphql::register(&mut m);
	//http::register(&mut m);
	//cryptography::register(&mut m);
	//net::register(&mut m);
	//uuid::register(&mut m);
	//semantic_versions::register(&mut m);
	//rego::register(&mut m);
	//opa::register(&mut m);
	debugging::register(&mut m);
	tracing::register(&mut m);
	
	m
    };
}

pub fn must_cache(path: &str) -> Option<&'static str> {
    match path {
        "rand.intn" => Some("rand.intn"),
        _ => None,
    }
}

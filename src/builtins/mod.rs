// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod aggregates;
mod arrays;
mod bitwise;
pub mod comparison;
mod conversions;

#[cfg(feature = "crypto")]
mod crypto;
mod debugging;
#[cfg(feature = "deprecated")]
pub mod deprecated;
mod encoding;
#[cfg(feature = "glob")]
mod glob;
#[cfg(feature = "graph")]
mod graph;
#[cfg(feature = "http")]
mod http;
#[cfg(feature = "jwt")]
mod jwt;
pub mod numbers;
mod objects;
#[cfg(feature = "opa-runtime")]
mod opa;
#[cfg(feature = "regex")]
mod regex;
#[cfg(feature = "semver")]
mod semver;
pub mod sets;
mod strings;
#[cfg(feature = "time")]
mod time;
mod tracing;
pub mod types;
mod units;
mod utils;
#[cfg(feature = "uuid")]
mod uuid;

#[cfg(feature = "opa-testutil")]
mod test;

use crate::ast::{Expr, Ref};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;
use lazy_static::lazy_static;

pub type BuiltinFcn = (fn(&Span, &[Ref<Expr>], &[Value], bool) -> Result<Value>, u8);

pub use debugging::print_to_string;

#[cfg(feature = "deprecated")]
pub use deprecated::DEPRECATED;

#[rustfmt::skip]
lazy_static! {
    pub static ref BUILTINS: HashMap<&'static str, BuiltinFcn> = {
	let mut m : HashMap<&'static str, BuiltinFcn>  = HashMap::new();
	
	// comparison functions are directly called.
	numbers::register(&mut m);
	aggregates::register(&mut m);
	arrays::register(&mut m);
	sets::register(&mut m);
	objects::register(&mut m);
	strings::register(&mut m);
	
	#[cfg(feature = "regex")]
	regex::register(&mut m);
	
	#[cfg(feature = "glob")]
	glob::register(&mut m);
	
	#[cfg(feature = "graph")]
	graph::register(&mut m);
	
	bitwise::register(&mut m);
	conversions::register(&mut m);
	//units::register(&mut m);
	types::register(&mut m);
	encoding::register(&mut m);
	#[cfg(feature = "jwt")]
	jwt::register(&mut m);
	#[cfg(feature = "time")]
	time::register(&mut m);

	#[cfg(feature = "crypto")]
	crypto::register(&mut m);
	//graphql::register(&mut m);
	#[cfg(feature = "http")]
	http::register(&mut m);
	//net::register(&mut m);
	#[cfg(feature = "uuid")]
	uuid::register(&mut m);
	#[cfg(feature = "semver")]
	semver::register(&mut m);
	//rego::register(&mut m);
	#[cfg(feature = "opa-runtime")]
	opa::register(&mut m);
	debugging::register(&mut m);
	tracing::register(&mut m);
	units::register(&mut m);

	#[cfg(feature = "opa-testutil")]
	test::register(&mut m);

	m
    };
}

pub fn must_cache(path: &str) -> Option<&'static str> {
    match path {
        "opa.runtime" => Some("opa.runtime"),
        "rand.intn" => Some("rand.intn"),
        "time.now_ns" => Some("time.now_ns"),
        "uuid.rfc4122" => Some("uuid.rfc4122"),
        _ => None,
    }
}

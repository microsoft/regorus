// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::arithmetic_side_effects,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::panic,
    clippy::shadow_unrelated,
    clippy::unwrap_used,
    clippy::missing_const_for_fn,
    clippy::option_if_let_else,
    clippy::semicolon_if_nothing_returned,
    clippy::useless_let_if_seq
)] // builtins perform validated indexing and intentional arithmetic/string ops

mod aggregates;
mod arrays;
mod bitwise;
pub mod comparison;
mod conversions;

mod encoding;
#[cfg(feature = "glob")]
mod glob;
#[cfg(feature = "graph")]
mod graph;
#[cfg(feature = "http")]
mod http;
#[cfg(feature = "net")]
mod net;

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

use crate::Map as BuiltinsMap;

use anyhow::Result;
use lazy_static::lazy_static;

pub type BuiltinFcn = (fn(&Span, &[Ref<Expr>], &[Value], bool) -> Result<Value>, u8);

#[rustfmt::skip]
lazy_static! {
    pub static ref BUILTINS: BuiltinsMap<&'static str, BuiltinFcn> = {
	let mut m : BuiltinsMap<&'static str, BuiltinFcn>  = BuiltinsMap::new();

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
	#[cfg(feature = "time")]
	time::register(&mut m);

	//graphql::register(&mut m);
	#[cfg(feature = "http")]
	http::register(&mut m);
	#[cfg(feature = "net")]
	net::register(&mut m);
	//net::register(&mut m);
	#[cfg(feature = "uuid")]
	uuid::register(&mut m);
	#[cfg(feature = "semver")]
	semver::register(&mut m);
	//rego::register(&mut m);
	#[cfg(feature = "opa-runtime")]
	opa::register(&mut m);
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

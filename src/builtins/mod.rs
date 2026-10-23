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
#[cfg(feature = "azure_policy")]
pub mod azure_policy;
mod bitwise;
pub mod comparison;
mod conversions;

mod encoding;
#[cfg(feature = "glob")]
mod glob;
#[cfg(feature = "graph")]
mod graph;
#[cfg(feature = "history")]
pub mod history;
#[cfg(feature = "http")]
mod http;
#[cfg(feature = "net")]
mod net;

#[cfg(feature = "jsonpatch")]
mod json_patch;
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
	#[cfg(feature = "history")]
	history::register(&mut m);

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
	#[cfg(feature = "azure_policy")]
	azure_policy::register(&mut m);
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

/// Resource failures must retain their identity through evaluator error envelopes.
pub fn is_fatal_builtin_error(error: &anyhow::Error) -> bool {
    #[cfg(feature = "history")]
    if error
        .downcast_ref::<history::HistoryError>()
        .is_some_and(history::HistoryError::is_fatal)
    {
        return true;
    }
    error.downcast_ref::<crate::LimitError>().is_some()
}

#[cfg(feature = "history")]
#[allow(clippy::redundant_pub_crate)] // `HistoryMatchState` is crate-private.
pub(crate) fn history_match_with_context(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    state: &mut history::HistoryMatchState,
    timer: &mut crate::utils::limits::ExecutionTimer,
) -> Result<Value> {
    utils::ensure_args_count(span, "history.match", params, args, 3)?;
    let Value::Array(ref events) = args[1] else {
        return Err(span.error("`history.match` expects an array history"));
    };
    let mut world = history::ObservationWorld;
    match state.evaluate(&args[0], events, &args[2], timer, &mut world) {
        Ok(result) => Ok(Value::Bool(result)),
        Err(history::HistoryError::Limit(error)) => Err(error.into()),
        Err(error) if error.is_fatal() => Err(error.into()),
        Err(error) => Err(span.error(&alloc::format!("{error}"))),
    }
}

#[cfg(feature = "history")]
fn history_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    use crate::utils::limits::{fallback_execution_timer_config, monotonic_now, ExecutionTimer};

    let mut state = history::HistoryMatchState::default();
    let mut timer = ExecutionTimer::new(fallback_execution_timer_config());
    if let Some(now) = monotonic_now() {
        timer.start(now);
    }
    history_match_with_context(span, params, args, &mut state, &mut timer)
}

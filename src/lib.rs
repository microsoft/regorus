// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Unsafe code should not be used.
// Hard to reason about correctness, and maintainability.
#![forbid(unsafe_code)]
// Ensure that all lint names are valid.
#![deny(unknown_lints)]
// Fail-fast lints: correctness, safety, and API surface
#![deny(
    // Panic sources - catch all ways code can panic
    clippy::panic, // forbid explicit panic! macro
    clippy::unreachable, // catches unreachable! macro usage
    clippy::todo, // blocks remaining todo! placeholders
    clippy::unimplemented, // blocks unimplemented! placeholders
    clippy::unwrap_used, // reject Result/Option unwraps
    clippy::expect_used, // reject expect with panic messages
    clippy::manual_assert, // prefer assert! over manual if/panic
    clippy::indexing_slicing, // reject unchecked [] indexing
    clippy::arithmetic_side_effects, // reject overflowing/unchecked math
    clippy::panic_in_result_fn, // disallow panic inside functions returning Result

    // Rust warnings/upstream
    dead_code, // ban unused items
    deprecated, // prevent use of deprecated APIs
    deprecated_in_future, // catch items scheduled for deprecation
    exported_private_dependencies, // avoid leaking private deps in public API
    future_incompatible, // catch patterns slated to break
    invalid_doc_attributes, // ensure doc attributes are valid
    keyword_idents, // disallow identifiers that are keywords
    macro_use_extern_crate, // block legacy macro_use extern crate
    missing_debug_implementations, // require Debug on public types
    // TODO: Address in future pass
    // missing_docs, // require docs on public items
    non_ascii_idents, // disallow non-ASCII identifiers
    nonstandard_style, // enforce idiomatic naming/style
    noop_method_call, // catch no-op method calls
    trivial_bounds, // forbid useless trait bounds
    trivial_casts, // block needless casts
    unreachable_code, // catch dead/unreachable code
    unreachable_patterns, // catch unreachable match arms
    // TODO: Address in future pass
    // unreachable_pub,
    unused_extern_crates, // remove unused extern crate declarations
    unused_import_braces, // avoid unused braces in imports
    absolute_paths_not_starting_with_crate, // enforce crate:: prefix for absolute paths

    // Unsafe code / low-level hazards
    clippy::unseparated_literal_suffix, // enforce underscore before literal suffixes
    clippy::print_stderr, // discourage printing to stderr
    clippy::use_debug, // discourage Debug formatting in display contexts

    // Documentation & diagnostics
    // TODO: Address in future pass
    // clippy::doc_link_with_quotes, // avoid quoted intra-doc links
    // clippy::doc_markdown, // flag bad Markdown in docs
    // clippy::missing_docs_in_private_items, // require docs on private items
    // clippy::missing_errors_doc, // require docs for error cases

    // API correctness / style
    clippy::missing_const_for_fn, // suggest const fn where possible
    clippy::option_if_let_else, // prefer map_or/unwrap_or_else over if/let
    clippy::if_then_some_else_none, // prefer Option combinators over if/else
    clippy::semicolon_if_nothing_returned, // enforce trailing semicolon for unit
    clippy::unused_self, // remove unused self parameters
    clippy::used_underscore_binding, // avoid using bindings prefixed with _
    clippy::useless_let_if_seq, // simplify let-if sequences
    clippy::similar_names, // flag confusingly similar identifiers
    clippy::shadow_unrelated, // discourage shadowing unrelated variables
    clippy::redundant_pub_crate, // avoid pub(crate) on already pub items
    clippy::wildcard_dependencies, // disallow wildcard Cargo dependency versions
    // TODO: Address in future pass
    // clippy::wildcard_imports, // discourage glob imports

    // Numeric correctness
    // TODO: Address in future pass
    clippy::float_cmp, // avoid exact float equality checks
    clippy::float_cmp_const, // avoid comparing floats to consts directly
    clippy::float_equality_without_abs, // require tolerance in float equality
    clippy::suspicious_operation_groupings, // catch ambiguous operator precedence

    // no_std hygiene
    clippy::std_instead_of_core, // prefer core/alloc over std in no_std

    // Misc polish
    clippy::dbg_macro, // forbid dbg! in production code
    clippy::debug_assert_with_mut_call, // avoid mutating inside debug_assert
    clippy::empty_line_after_outer_attr, // enforce spacing after outer attrs
    clippy::empty_structs_with_brackets, // use unit structs without braces
)]
// Advisory lints: useful, but not fatal
#![warn(
    clippy::assertions_on_result_states, // avoid asserts on Result state
    clippy::match_like_matches_macro, // prefer matches! macro over verbose match
    clippy::needless_continue, // remove redundant continue statements
    clippy::unused_trait_names, // drop unused trait imports
    clippy::verbose_file_reads, // prefer concise file read helpers
    clippy::as_conversions, // discourage lossy as casts
    clippy::pattern_type_mismatch, // catch mismatched types in patterns
)]
#![cfg_attr(docsrs, feature(doc_cfg))]
// Use README.md as crate documentation.
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]
// We'll default to building for no_std - use core, alloc instead of std.
#![no_std]

extern crate alloc;
use serde::Serialize;

// Import std crate if building with std support.
// We don't import types or macros from std.
// As a result, types and macros from std must be qualified via `std::`
// making dependencies on std easier to spot.
#[cfg(any(feature = "std", test))]
extern crate std;

#[cfg(feature = "mimalloc")]
mimalloc::assign_global!();

mod ast;
mod builtins;
mod compile;
mod compiled_policy;
mod compiler;
mod engine;
mod indexchecker;
mod interpreter;

pub mod languages {
    #[cfg(feature = "azure-rbac")]
    pub mod azure_rbac;

    #[cfg(feature = "rvm")]
    pub mod rego;
}

mod lexer;
pub(crate) mod lookup;
mod number;
mod parser;
mod policy_info;
mod query;
#[cfg(feature = "azure_policy")]
pub mod registry;
#[cfg(feature = "rvm")]
pub mod rvm;
mod scheduler;
#[cfg(feature = "azure_policy")]
mod schema;
#[cfg(feature = "azure_policy")]
pub mod target;
#[cfg(any(test, all(feature = "yaml", feature = "std")))]
pub mod test_utils;
pub mod utils;
mod value;

#[cfg(feature = "azure_policy")]
pub use {
    compile::compile_policy_for_target,
    schema::{error::ValidationError, validate::SchemaValidator, Schema},
    target::Target,
};

pub use compile::{compile_policy_with_entrypoint, PolicyModule};
pub use compiled_policy::CompiledPolicy;
pub use engine::Engine;
pub use lexer::Source;
pub use policy_info::PolicyInfo;
pub use utils::limits::LimitError;
#[cfg(feature = "allocator-memory-limits")]
pub use utils::limits::{
    check_global_memory_limit, enforce_memory_limit, flush_thread_memory_counters,
    global_memory_limit, set_global_memory_limit, set_thread_flush_threshold_override,
    thread_memory_flush_threshold,
};
pub use value::Value;

#[cfg(feature = "arc")]
pub use alloc::sync::Arc as Rc;

#[cfg(not(feature = "arc"))]
pub use alloc::rc::Rc;

#[cfg(feature = "std")]
use std::collections::{hash_map::Entry as MapEntry, HashMap as Map, HashSet as Set};

#[cfg(not(feature = "std"))]
use alloc::collections::{btree_map::Entry as MapEntry, BTreeMap as Map, BTreeSet as Set};

use alloc::{
    borrow::ToOwned as _,
    boxed::Box,
    format,
    string::{String, ToString as _},
    vec,
    vec::Vec,
};

use core::fmt;

/// Location of an [`Expression`] in a Rego query.
///
/// ```
/// # use regorus::Engine;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "  \n  1 + 2".
/// let results = Engine::new().eval_query("  \n  1 + 2".to_string(), false)?;
///
/// // Fetch the location for the expression.
/// let loc = &results.result[0].expressions[0].location;
///
/// assert_eq!(loc.row, 2);
/// assert_eq!(loc.col, 3);
/// # Ok(())
/// # }
/// ````
/// See also [`QueryResult`].
#[derive(Debug, Clone, Serialize, Eq, PartialEq)]
pub struct Location {
    /// Line number. Starts at 1.
    pub row: u32,
    /// Column number. Starts at 1.
    pub col: u32,
}

/// An expression in a Rego query.
///
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "1 + 2".
/// let results = Engine::new().eval_query("1 + 2".to_string(), false)?;
///
/// // Fetch the expression from results.
/// let expr = &results.result[0].expressions[0];
///
/// assert_eq!(expr.value, Value::from(3u64));
/// assert_eq!(expr.text.as_ref(), "1 + 2");
/// # Ok(())
/// # }
/// ```
/// See also [`QueryResult`].
#[derive(Debug, Clone, Serialize, Eq, PartialEq)]
pub struct Expression {
    /// Computed value of the expression.
    pub value: Value,

    /// The Rego expression.
    pub text: Rc<str>,

    /// Location of the expression in the query string.
    pub location: Location,
}

/// Result of evaluating a Rego query.
///
/// A query containing single expression.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "1 + 2".
/// let results = Engine::new().eval_query("1 + 2".to_string(), false)?;
///
/// // Fetch the first (sole) result.
/// let result = &results.result[0];
///
/// assert_eq!(result.expressions[0].value, Value::from(3u64));
/// assert_eq!(result.expressions[0].text.as_ref(), "1 + 2");
/// # Ok(())
/// # }
/// ```
///
/// A query containing multiple expressions.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "1 + 2; 3.5 * 4".
/// let results = Engine::new().eval_query("1 + 2; 3.55 * 4".to_string(), false)?;
///
/// // Fetch the first (sole) result.
/// let result = &results.result[0];
///
/// // First expression.
/// assert_eq!(result.expressions[0].value, Value::from(3u64));
/// assert_eq!(result.expressions[0].text.as_ref(), "1 + 2");
///
/// // Second expression.
/// assert_eq!(result.expressions[1].value, Value::from(14.2));
/// assert_eq!(result.expressions[1].text.as_ref(), "3.55 * 4");
/// # Ok(())
/// # }
/// ```
///
/// Expressions that create bindings (i.e. associate names to values) evaluate to
/// either true or false. The value of bindings are available in the `bindings` field.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "x = 1; y = x > 0".
/// let results = Engine::new().eval_query("x = 1; y = x > 0".to_string(), false)?;
///
/// // Fetch the first (sole) result.
/// let result = &results.result[0];
///
/// // First expression is true.
/// assert_eq!(result.expressions[0].value, Value::from(true));
/// assert_eq!(result.expressions[0].text.as_ref(), "x = 1");
///
/// // Second expression is true.
/// assert_eq!(result.expressions[1].value, Value::from(true));
/// assert_eq!(result.expressions[1].text.as_ref(), "y = x > 0");
///
/// // bindings contains the value for each named expession.
/// assert_eq!(result.bindings[&Value::from("x")], Value::from(1u64));
/// assert_eq!(result.bindings[&Value::from("y")], Value::from(true));
/// # Ok(())
/// # }
/// ```
///
/// If any expression evaluates to false, then no results are produced.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "true; true; false".
/// let results = Engine::new().eval_query("true; true; false".to_string(), false)?;
///
/// assert!(results.result.is_empty());
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Serialize, Eq, PartialEq)]
pub struct QueryResult {
    /// Expressions in the query.
    ///
    /// Each statement in the query is treated as a separte expression.
    ///
    pub expressions: Vec<Expression>,

    /// Bindings created in the query.
    #[serde(skip_serializing_if = "Value::is_empty_object")]
    pub bindings: Value,
}

impl Default for QueryResult {
    fn default() -> Self {
        Self {
            bindings: Value::new_object(),
            expressions: vec![],
        }
    }
}

/// Results of evaluating a Rego query.
///
/// Generates the same `json` representation as `opa eval`.
///
/// Queries typically produce a single result.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "1 + 1".
/// let results = Engine::new().eval_query("1 + 1".to_string(), false)?;
///
/// assert_eq!(results.result.len(), 1);
/// assert_eq!(results.result[0].expressions[0].value, Value::from(2u64));
/// assert_eq!(results.result[0].expressions[0].text.as_ref(), "1 + 1");
/// # Ok(())
/// # }
/// ```
///
/// If a query contains only one expression, and even if the expression evaluates
/// to false, the value will be returned.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "1 > 2" which is false.
/// let results = Engine::new().eval_query("1 > 2".to_string(), false)?;
///
/// assert_eq!(results.result.len(), 1);
/// assert_eq!(results.result[0].expressions[0].value, Value::from(false));
/// assert_eq!(results.result[0].expressions[0].text.as_ref(), "1 > 2");
/// # Ok(())
/// # }
/// ```
///
/// In a query containing multiple expressions, if  any expression evaluates to false,
/// then no results are produced.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "true; true; false".
/// let results = Engine::new().eval_query("true; true; false".to_string(), false)?;
///
/// assert!(results.result.is_empty());
/// # Ok(())
/// # }
/// ```
///
/// Note that `=` is different from `==`. The former evaluates to undefined if the LHS and RHS
/// are not equal. The latter evaluates to either true or false.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// // Create engine and evaluate "1 = 2" which is undefined and produces no resutl.
/// let results = Engine::new().eval_query("1 = 2".to_string(), false)?;
///
/// assert_eq!(results.result.len(), 0);
///
/// // Create engine and evaluate "1 == 2" which evaluates to false.
/// let results = Engine::new().eval_query("1 == 2".to_string(), false)?;
///
/// assert_eq!(results.result.len(), 1);
/// assert_eq!(results.result[0].expressions[0].value, Value::from(false));
/// assert_eq!(results.result[0].expressions[0].text.as_ref(), "1 == 2");
/// # Ok(())
/// # }
/// ```
///
/// Queries containing loops produce multiple results.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// let results = Engine::new().eval_query("x = [1, 2, 3][_]".to_string(), false)?;
///
/// // Three results are produced, one of each value of x.
/// assert_eq!(results.result.len(), 3);
///
/// // Assert expressions and bindings of results.
/// assert_eq!(results.result[0].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[0].expressions[0].text.as_ref(), "x = [1, 2, 3][_]");
/// assert_eq!(results.result[0].bindings[&Value::from("x")], Value::from(1u64));
///
/// assert_eq!(results.result[1].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[1].expressions[0].text.as_ref(), "x = [1, 2, 3][_]");
/// assert_eq!(results.result[1].bindings[&Value::from("x")], Value::from(2u64));
///
/// assert_eq!(results.result[2].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[2].expressions[0].text.as_ref(), "x = [1, 2, 3][_]");
/// assert_eq!(results.result[2].bindings[&Value::from("x")], Value::from(3u64));
/// # Ok(())
/// # }
/// ```
///
/// Loop iterations that evaluate to false or undefined don't produce results.
/// ```
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// let results = Engine::new().eval_query("x = [1, 2, 3][_]; x >= 2".to_string(), false)?;
///
/// // Two results are produced, one for x = 2 and another for x = 3.
/// assert_eq!(results.result.len(), 2);
///
/// // Assert expressions and bindings of results.
/// assert_eq!(results.result[0].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[0].expressions[0].text.as_ref(), "x = [1, 2, 3][_]");
/// assert_eq!(results.result[0].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[0].expressions[1].text.as_ref(), "x >= 2");
/// assert_eq!(results.result[0].bindings[&Value::from("x")], Value::from(2u64));
///
/// assert_eq!(results.result[1].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[1].expressions[0].text.as_ref(), "x = [1, 2, 3][_]");
/// assert_eq!(results.result[1].expressions[0].value, Value::Bool(true));
/// assert_eq!(results.result[1].expressions[1].text.as_ref(), "x >= 2");
/// assert_eq!(results.result[1].bindings[&Value::from("x")], Value::from(3u64));
/// # Ok(())
/// # }
/// ```
///
/// See [QueryResult] for examples of different kinds of results.
#[derive(Debug, Clone, Default, Serialize, Eq, PartialEq)]
pub struct QueryResults {
    /// Collection of results of evaluting a query.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub result: Vec<QueryResult>,
}

/// A user defined builtin function implementation.
///
/// It is not necessary to implement this trait directly.
pub trait Extension: FnMut(Vec<Value>) -> anyhow::Result<Value> + Send + Sync {
    /// Fn, FnMut etc are not sized and cannot be cloned in their boxed form.
    /// clone_box exists to overcome that.
    fn clone_box<'a>(&self) -> Box<dyn 'a + Extension>
    where
        Self: 'a;
}

/// Automatically make matching closures a valid [`Extension`].
impl<F> Extension for F
where
    F: FnMut(Vec<Value>) -> anyhow::Result<Value> + Clone + Send + Sync,
{
    fn clone_box<'a>(&self) -> Box<dyn 'a + Extension>
    where
        Self: 'a,
    {
        Box::new(self.clone())
    }
}

/// Implement clone for a boxed extension using [`Extension::clone_box`].
impl Clone for Box<dyn '_ + Extension> {
    fn clone(&self) -> Self {
        (**self).clone_box()
    }
}

impl fmt::Debug for dyn Extension {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> core::result::Result<(), fmt::Error> {
        f.write_fmt(format_args!("<extension>"))
    }
}

#[cfg(feature = "coverage")]
#[cfg_attr(docsrs, doc(cfg(feature = "coverage")))]
pub mod coverage {
    use crate::*;

    #[allow(missing_debug_implementations)]
    #[derive(Default, serde::Serialize, serde::Deserialize)]
    /// Coverage information about a rego policy file.
    pub struct File {
        /// Path of the policy file.
        pub path: String,

        /// The rego policy.
        pub code: String,

        /// Lines that were evaluated.
        pub covered: alloc::collections::BTreeSet<u32>,

        /// Lines that were not evaluated.
        pub not_covered: alloc::collections::BTreeSet<u32>,
    }

    #[allow(missing_debug_implementations)]
    #[derive(Default, serde::Serialize, serde::Deserialize)]
    /// Policy coverage report.
    pub struct Report {
        /// Coverage information for files.
        pub files: Vec<File>,
    }

    impl Report {
        /// Produce an ANSI color encoded version of the report.
        ///
        /// Covered lines are green.
        /// Lines that are not covered are red.
        ///
        /// <img src="https://github.com/microsoft/regorus/blob/main/docs/coverage.png?raw=true">
        #[allow(clippy::arithmetic_side_effects)]
        pub fn to_string_pretty(&self) -> anyhow::Result<String> {
            let mut s = String::default();
            s.push_str("COVERAGE REPORT:\n");
            for file in self.files.iter() {
                if file.not_covered.is_empty() {
                    s.push_str(&format!("{} has full coverage\n", file.path));
                    continue;
                }

                s.push_str(&format!("{}:\n", file.path));
                for (line_idx, code) in file.code.split('\n').enumerate() {
                    let line = u32::try_from(line_idx + 1).unwrap_or(u32::MAX);
                    if file.not_covered.contains(&line) {
                        s.push_str(&format!("\x1b[31m {line:4}  {code}\x1b[0m\n"));
                    } else if file.covered.contains(&line) {
                        s.push_str(&format!("\x1b[32m {line:4}  {code}\x1b[0m\n"));
                    } else {
                        s.push_str(&format!(" {line:4}  {code}\n"));
                    }
                }
            }

            s.push('\n');
            Ok(s)
        }
    }
}

/// Items in `unstable` are likely to change.
#[doc(hidden)]
pub mod unstable {
    pub use crate::ast::*;
    pub use crate::lexer::*;
    pub use crate::parser::*;
}

#[cfg(test)]
mod tests;

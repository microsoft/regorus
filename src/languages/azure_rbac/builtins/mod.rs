// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure RBAC builtins.
//!
//! These builtins are a small, zero-copy focused API intended to be shared by
//! the interpreter and future RVM lowering.

mod actions;
mod bools;
mod common;
mod datetime;
mod evaluator;
mod functions;
mod ids;
mod ip;
mod lists;
mod numbers;
mod quantifiers;
mod strings;
mod time_of_day;

pub use evaluator::{DefaultRbacBuiltinEvaluator, RbacBuiltinContext, RbacBuiltinError};
pub use ids::RbacBuiltin;

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Use README.md as crate documentation.
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]

mod ast;
mod builtins;
mod engine;
mod interpreter;
mod lexer;
mod number;
mod parser;
mod scheduler;
mod utils;
mod value;

pub use engine::Engine;
pub use interpreter::{QueryResult, QueryResults};
pub use value::Value;

/// Items in `unstable` are likely to change.
pub mod unstable {
    pub use crate::ast::*;
    pub use crate::lexer::*;
    pub use crate::parser::*;
}

#[cfg(test)]
mod tests;

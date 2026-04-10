// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure Policy language support: AST types, aliases, and string utilities.

#[allow(clippy::pattern_type_mismatch)]
pub mod aliases;
pub mod ast;
#[cfg(feature = "rvm")]
pub mod compiler;
pub mod expr;
pub mod parser;
pub mod strings;

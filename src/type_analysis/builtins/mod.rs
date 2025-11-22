// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod catalog;
mod matching;
mod spec;
mod table;

pub use matching::{combined_arg_origins, matches_template};
pub use spec::return_descriptor;
pub use spec::{BuiltinPurity, BuiltinSpec, BuiltinTableError, BuiltinTypeTemplate};
pub use table::{lookup, override_builtin_table, reset_builtin_table};

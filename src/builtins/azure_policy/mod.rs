// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure Policy builtins: operators, logic functions, and ARM template functions.

#![deny(
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
)]

pub mod helpers;
mod operators;
mod template_functions;
mod template_functions_collection;
mod template_functions_datetime;
mod template_functions_encoding;
mod template_functions_misc;
mod template_functions_numeric;
mod template_functions_string;

use crate::builtins;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    // Logic functions
    m.insert("azure.policy.logic_all", (operators::logic_all, 0));
    m.insert("azure.policy.logic_any", (operators::logic_any, 0));
    m.insert("azure.policy.if", (operators::if_fn, 3));

    // Field resolution
    m.insert("azure.policy.resolve_field", (operators::resolve_field, 2));

    // Parameter resolution with default-value fallback
    m.insert("azure.policy.get_parameter", (operators::get_parameter, 3));

    // ARM template functions
    template_functions::register(m);
    template_functions_string::register(m);
    template_functions_encoding::register(m);
    template_functions_collection::register(m);
    template_functions_numeric::register(m);
    template_functions_datetime::register(m);
    template_functions_misc::register(m);
}

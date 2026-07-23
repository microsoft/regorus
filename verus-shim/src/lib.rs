// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! No-op stand-ins for the Verus attribute/macros used to annotate source for
//! verification (`verus_verify`, `verus_spec`, `proof!`).
//!
//! When the `verus` feature is enabled, the real macros are provided by
//! `vstd::prelude`. When it is disabled, these no-ops are imported instead so
//! that a normal `cargo build` compiles the annotated source as ordinary Rust:
//! the attributes are stripped (their contents discarded) and `proof!` blocks
//! expand to nothing.

use proc_macro::TokenStream;

/// No-op replacement for `#[verus_verify]`. Returns the annotated item
/// unchanged, discarding any attribute arguments (e.g. `external_derive`).
#[proc_macro_attribute]
pub fn verus_verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// No-op replacement for `#[verus_spec(...)]`. Returns the annotated item
/// unchanged, discarding the specification.
#[proc_macro_attribute]
pub fn verus_spec(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// No-op replacement for `proof! { ... }`. Expands to nothing.
#[proc_macro]
pub fn proof(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}

/// No-op replacement for `proof_decl! { ... }`. Expands to nothing.
#[proc_macro]
pub fn proof_decl(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}

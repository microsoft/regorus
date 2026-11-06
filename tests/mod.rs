// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(feature = "azure_policy")]
mod azure_policy_builtins;

#[cfg(feature = "coverage")]
mod coverage;

mod engine;
mod lexer;
mod parser;
mod value;

#[cfg(all(
    feature = "opa-testutil",
    feature = "rvm",
    feature = "std",
    feature = "arc"
))]
#[allow(dead_code)]
#[path = "opa.rs"]
mod opa_harness;

#[cfg(feature = "azure_policy")]
mod azure_policy;

#[cfg(feature = "rvm")]
mod explanation_corpus;

#[cfg(feature = "rvm")]
mod rvm;

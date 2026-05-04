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

#[cfg(feature = "azure_policy")]
mod azure_policy;

#[cfg(all(
    feature = "rvm",
    any(feature = "test-utils", all(feature = "yaml", feature = "std"))
))]
mod explanation_corpus;

#[cfg(feature = "rvm")]
mod rvm;

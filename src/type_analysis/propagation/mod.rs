// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
mod diagnostics;
mod expressions;
mod facts;
mod loops;
mod pipeline;

pub use pipeline::{AnalysisState, TypeAnalysisOptions, TypeAnalyzer};

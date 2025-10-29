// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod analyzer;
mod options;
mod result;

pub(crate) use analyzer::RuleHeadInfo;
pub use analyzer::TypeAnalyzer;
pub use options::TypeAnalysisOptions;
pub use result::AnalysisState;
pub(crate) use result::TypeAnalysisResult;

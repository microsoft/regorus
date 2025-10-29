// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;
use alloc::vec::Vec;

use crate::compiler::hoist::HoistedLoopsLookup;
use crate::schema::Schema;
use crate::Rc;

/// Configuration for the type analyser.
#[derive(Clone, Debug)]
pub struct TypeAnalysisOptions {
    pub input_schema: Option<Schema>,
    pub data_schema: Option<Schema>,
    pub loop_lookup: Option<Rc<HoistedLoopsLookup>>,
    /// Optional entrypoint filtering - analyze only rules reachable from these paths
    pub entrypoints: Option<Vec<String>>,
    /// Experimental: disable the generic pass for function rules.
    pub disable_function_generic_pass: bool,
}

impl Default for TypeAnalysisOptions {
    fn default() -> Self {
        Self {
            input_schema: None,
            data_schema: None,
            loop_lookup: None,
            entrypoints: None,
            disable_function_generic_pass: true,
        }
    }
}

impl TypeAnalysisOptions {
    /// Check if entrypoint filtering is enabled
    pub fn is_entrypoint_filtered(&self) -> bool {
        self.entrypoints.is_some()
    }

    /// Get the list of entrypoints (empty if not filtered)
    pub fn get_entrypoints(&self) -> &[String] {
        self.entrypoints.as_deref().unwrap_or(&[])
    }
}

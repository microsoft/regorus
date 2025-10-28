// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Expression-level result structures captured by the analyser.

use crate::type_analysis::constants::ConstantStore;
use crate::type_analysis::context::LookupContext;

/// Combined set of per-expression facts and constant information.
#[derive(Clone, Debug, Default)]
pub struct ExpressionFacts {
    pub facts: LookupContext,
    pub constants: ConstantStore,
}

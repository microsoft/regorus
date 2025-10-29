// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::type_analysis::model::StructuralType;
use crate::type_analysis::propagation::pipeline::TypeAnalyzer;

impl TypeAnalyzer {
    /// Check if a structural type is definitely numeric
    pub(crate) fn is_numeric_type(ty: &StructuralType) -> bool {
        matches!(ty, StructuralType::Number | StructuralType::Integer)
    }
}

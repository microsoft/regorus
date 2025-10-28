// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

use crate::type_analysis::model::{PathSegment, SourceOrigin};

pub(crate) fn extend_origins_with_segment(
    origins: &[SourceOrigin],
    segment: PathSegment,
) -> Vec<SourceOrigin> {
    origins
        .iter()
        .map(|origin| {
            let mut updated = origin.clone();
            updated.path.push(segment.clone());
            updated
        })
        .collect()
}

pub(crate) fn mark_origins_derived(origins: &[SourceOrigin]) -> Vec<SourceOrigin> {
    origins
        .iter()
        .map(|origin| {
            let mut updated = origin.clone();
            updated.derived = true;
            updated
        })
        .collect()
}

pub(crate) fn derived_from_pair(lhs: &[SourceOrigin], rhs: &[SourceOrigin]) -> Vec<SourceOrigin> {
    lhs.iter()
        .chain(rhs.iter())
        .map(|origin| {
            let mut updated = origin.clone();
            updated.derived = true;
            updated
        })
        .collect()
}

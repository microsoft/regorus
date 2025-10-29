// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum StructuralCategory {
    Boolean,
    Number,
    String,
    Null,
    Array,
    Set,
    Object,
    Undefined,
}

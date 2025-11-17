// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use serde::{Deserialize, Serialize};

/// Empty span placeholder since we don't need spans for RBAC
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct EmptySpan;

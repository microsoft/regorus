// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! String operations for ARM and Azure Policy.
//!
//! This module provides precise implementations of the string comparison
//! semantics used by ARM (Azure Resource Manager) and Azure Policy:
//!
//! - **[`keys`]**: ASCII case-insensitive comparison for ARM object property
//!   keys (`OrdinalIgnoreCase` — only folds A-Z ↔ a-z).
//!
//! - **[`case_fold`]**: Full Unicode case folding for Azure Policy condition
//!   value comparisons (`InvariantCultureIgnoreCase`). Backed by ICU4X
//!   [`icu_casemap`] so that ß = SS, ﬃ = FFI, etc.
//!
//! # Design rationale
//!
//! ARM property key names are restricted to ASCII (letters, digits,
//! underscores), so `eq_ignore_ascii_case` is both correct and fast for key
//! lookup.
//!
//! Azure Policy condition operators (`equals`, `contains`, `like`, …) compare
//! string *values* using .NET's `InvariantCultureIgnoreCase`, which performs
//! full Unicode case folding.  We use ICU4X's `CaseMapper::fold` / `fold_string`
//! for this — it is the same ICU backing that .NET 5+ uses internally.

pub mod case_fold;
pub mod keys;

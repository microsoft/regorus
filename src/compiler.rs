// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::missing_const_for_fn,
    clippy::option_if_let_else,
    clippy::if_then_some_else_none,
    clippy::unused_self,
    clippy::semicolon_if_nothing_returned,
    clippy::useless_let_if_seq
)]
//! Compiler-related functionality for Regorus.
//!
//! This module contains utilities and data structures used during
//! the compilation phase to prepare policies for efficient execution.

pub mod context;
pub mod destructuring_planner;
pub mod hoist;

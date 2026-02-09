// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod allocator;
mod common;
mod compile;
mod compiled_policy;
mod effect_registry;
mod engine;
mod limits;
mod lock;
mod panic_guard;
#[cfg(feature = "rbac")]
mod rbac;
#[cfg(feature = "rvm")]
pub(crate) mod rvm;
mod schema_registry;
mod target_registry;

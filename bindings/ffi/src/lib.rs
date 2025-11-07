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
mod lock;
mod schema_registry;
mod target_registry;

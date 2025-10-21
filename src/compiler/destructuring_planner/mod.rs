// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Destructuring and binding planner utilities.
//!
//! This module hierarchy reorganizes the binding planner into smaller components
//! so the compiler can evolve without ambiguity with FFI bindings. Submodules
//! will be filled in as code is migrated from the legacy `bindings` module.

pub mod assignment;
pub mod context;
pub mod destructuring;
pub mod error;
pub mod parameters;
pub mod plans;
pub mod some_in;
pub mod utils;

pub use assignment::create_assignment_binding_plan;
pub use context::{ScopingMode, VariableBindingContext};
pub use destructuring::create_destructuring_plan;
pub use error::{map_binding_error, BindingPlannerError, Result};
pub use parameters::{create_loop_index_binding_plan, create_parameter_binding_plan};
pub use plans::{AssignmentPlan, BindingPlan, DestructuringPlan, WildcardSide};
pub use some_in::create_some_in_binding_plan;

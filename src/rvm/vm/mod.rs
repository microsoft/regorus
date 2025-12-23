// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod arithmetic;
mod comprehension;
mod context;
mod dispatch;
mod errors;
mod execution;
mod execution_model;
mod functions;
mod loops;
mod machine;
mod rules;
mod state;
mod virtual_data;

pub use context::{CallRuleContext, IterationState, LoopContext};
pub use errors::{Result, VmError};
pub use execution_model::{ExecutionMode, ExecutionState, SuspendReason};
pub use machine::RegoVM;

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// RVM - Rego Virtual Machine
// A register-based virtual machine for executing Rego policies

pub mod instructions;
pub mod program;
pub mod tests;
pub mod vm;

pub use instructions::Instruction;
pub use program::{
    generate_assembly_listing, generate_tabular_assembly_listing, AssemblyListingConfig, Program,
};
pub use vm::RegoVM;

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::OsString;

use anyhow::Result;
use clap::Args;

use crate::tasks::util::{run_cargo_step, workspace_root};

/// Builds the ensure_no_std harness for an embedded target.
#[derive(Args, Default)]
pub struct TestNoStdCommand {
    /// Target triple to compile (defaults to thumbv7m-none-eabi).
    #[arg(long, default_value = "thumbv7m-none-eabi")]
    pub target: String,

    /// Compile artefacts in release mode.
    #[arg(long)]
    pub release: bool,

    /// Propagate --frozen to the cargo invocations.
    #[arg(long)]
    pub frozen: bool,
}

impl TestNoStdCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let project_dir = workspace.join("tests/ensure_no_std");

        let mut args = vec![
            OsString::from("build"),
            OsString::from("--target"),
            OsString::from(&self.target),
        ];
        if self.release {
            args.push(OsString::from("--release"));
        }
        if self.frozen {
            args.push(OsString::from("--frozen"));
        }
        run_cargo_step(&project_dir, "cargo build (tests/ensure_no_std)", args)?;
        Ok(())
    }
}

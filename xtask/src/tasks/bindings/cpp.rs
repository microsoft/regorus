// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use clap::Args;

use super::c::{prepare_ffi_artifacts, run_binding};

#[derive(Args, Default)]
pub struct TestCppCommand {
    /// Build the FFI crate in release mode before exercising the binding.
    #[arg(long)]
    pub release: bool,

    /// Pass --frozen to the preparatory cargo invocations.
    #[arg(long)]
    pub frozen: bool,

    /// Reuse previously built FFI artefacts instead of rebuilding.
    #[arg(long)]
    pub skip_ffi: bool,
}

impl TestCppCommand {
    pub fn run(&self) -> Result<()> {
        if !self.skip_ffi {
            prepare_ffi_artifacts(self.release, self.frozen)?;
        }
        run_binding("bindings/cpp", "regorus_test", self.release)?;
        run_binding("bindings/cpp", "regorus_rvm_test", self.release)
    }
}

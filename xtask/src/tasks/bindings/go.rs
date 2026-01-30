// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, Result};
use clap::Args;

use super::c::prepare_ffi_artifacts;
use crate::tasks::util::{add_library_search_path, run_command, workspace_root};

/// Builds the Go binding sample and runs its smoke test.
#[derive(Args, Default)]
pub struct TestGoCommand {
    /// Build the FFI crate in release mode before exercising the Go sample.
    #[arg(long)]
    pub release: bool,

    /// Skip rebuilding the FFI artefacts and reuse existing outputs.
    #[arg(long)]
    pub skip_ffi: bool,

    /// Pass --frozen to the preparatory cargo invocations.
    #[arg(long)]
    pub frozen: bool,
}

impl TestGoCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let ffi_dir = workspace.join("bindings/ffi");
        let go_dir = workspace.join("bindings/go");
        let profile = if self.release { "release" } else { "debug" };

        if !self.skip_ffi {
            prepare_ffi_artifacts(self.release, self.frozen)?;
        }

        run_go_command(&go_dir, ["mod", "tidy"], "go mod tidy (bindings/go)")?;
        run_go_command(&go_dir, ["build"], "go build (bindings/go)")?;

        let lib_dir = ffi_dir.join("target").join(profile);
        let mut go_test = Command::new("go");
        go_test.current_dir(&go_dir);
        go_test.arg("test");
        go_test.arg("./...");
        add_library_search_path(&mut go_test, &lib_dir);
        run_command(go_test, "go test ./... (bindings/go)")?;

        let binary = go_test_binary(&go_dir);
        if !binary.exists() {
            return Err(anyhow!(
                "expected Go test binary at {} after build",
                binary.display()
            ));
        }

        let mut run = Command::new(&binary);
        run.current_dir(&go_dir);
        add_library_search_path(&mut run, &lib_dir);
        run_command(run, "regorus_test (bindings/go)")
    }
}

fn run_go_command<const N: usize>(dir: &Path, args: [&str; N], label: &str) -> Result<()> {
    let mut cmd = Command::new("go");
    cmd.current_dir(dir);
    for arg in args {
        cmd.arg(arg);
    }
    run_command(cmd, label)
}

fn go_test_binary(dir: &Path) -> PathBuf {
    if cfg!(windows) {
        dir.join("regorus_test.exe")
    } else {
        dir.join("regorus_test")
    }
}

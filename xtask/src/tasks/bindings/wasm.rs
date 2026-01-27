// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::Result;
use clap::Args;

use crate::tasks::util::{run_command, workspace_root};

#[derive(Args, Default)]
pub struct BuildWasmCommand {
    /// Optimise the generated WASM artefacts (defaults to debug builds).
    #[arg(long)]
    pub release: bool,

    /// Target environment passed to wasm-pack (defaults to nodejs).
    #[arg(long, value_name = "TARGET", default_value = "nodejs")]
    pub target: String,

    /// Override the directory that receives wasm-pack outputs.
    #[arg(long, value_name = "PATH")]
    pub out_dir: Option<PathBuf>,
}

impl BuildWasmCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let wasm_dir = workspace.join("bindings/wasm");
        build_wasm(
            &wasm_dir,
            self.release,
            &self.target,
            self.out_dir.as_deref(),
        )
    }
}

#[derive(Args, Default)]
pub struct TestWasmCommand {
    /// Optimise the generated WASM artefacts (defaults to debug builds).
    #[arg(long)]
    pub release: bool,

    /// Target environment passed to wasm-pack (defaults to nodejs).
    #[arg(long, value_name = "TARGET", default_value = "nodejs")]
    pub target: String,

    /// Override the directory that receives wasm-pack outputs.
    #[arg(long, value_name = "PATH")]
    pub out_dir: Option<PathBuf>,

    /// Node.js executable used for the sample script.
    #[arg(long, value_name = "EXE", default_value = "node")]
    pub node: String,

    /// Accepted for compatibility with CI; ignored because wasm-pack controls builds.
    #[arg(long)]
    pub frozen: bool,

    /// Skip rebuilding the wasm artefacts before running the sample.
    #[arg(long)]
    pub skip_build: bool,
}

impl TestWasmCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let wasm_dir = workspace.join("bindings/wasm");

        if !self.skip_build {
            build_wasm(
                &wasm_dir,
                self.release,
                &self.target,
                self.out_dir.as_deref(),
            )?;
        }

        run_wasm_tests(&wasm_dir, self.release)?;

        let mut node = Command::new(&self.node);
        node.current_dir(&wasm_dir);
        node.arg("test.js");
        let label = format!("{} test.js (bindings/wasm)", self.node);
        run_command(node, &label)
    }
}

fn build_wasm(wasm_dir: &Path, release: bool, target: &str, out_dir: Option<&Path>) -> Result<()> {
    let mut pack = Command::new("wasm-pack");
    pack.current_dir(wasm_dir);
    pack.arg("build");
    pack.arg("--target");
    pack.arg(target);
    if release {
        pack.arg("--release");
    }
    if let Some(out_dir) = out_dir {
        pack.arg("--out-dir");
        pack.arg(out_dir);
    }
    run_command(pack, "wasm-pack build (bindings/wasm)")
}
fn run_wasm_tests(wasm_dir: &Path, release: bool) -> Result<()> {
    let mut test = Command::new("wasm-pack");
    test.current_dir(wasm_dir);
    test.arg("test");
    test.arg("--node");
    if release {
        test.arg("--release");
    }
    run_command(test, "wasm-pack test --node (bindings/wasm)")
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result};
use clap::Args;

use crate::tasks::util::{run_cargo_step, run_command, workspace_root};

const BINDING_MANIFESTS: &[&str] = &[
    "bindings/ffi/Cargo.toml",
    "bindings/java/Cargo.toml",
    "bindings/python/Cargo.toml",
    "bindings/wasm/Cargo.toml",
    // TODO: Reenable this once Ruby binding is actively maintained
    //"bindings/ruby/Cargo.toml",
];

/// Runs Clippy across the workspace and binding crates with CI-equivalent checks.
#[derive(Args, Default)]
pub struct ClippyCommand {
    /// Emit SARIF output to the supplied path (relative to the workspace by default).
    #[arg(long, value_name = "PATH")]
    pub sarif: Option<PathBuf>,
}

impl ClippyCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();

        match self.sarif.as_ref() {
            Some(sarif) => run_clippy_with_sarif(&workspace, sarif)?,
            None => {
                run_cargo_step(
                    &workspace,
                    "cargo clippy --all-targets --all-features -- -Dwarnings",
                    [
                        "clippy",
                        "--all-targets",
                        "--all-features",
                        "--",
                        "-Dwarnings",
                    ],
                )?;
            }
        }

        run_cargo_step(
            &workspace,
            "cargo clippy --no-default-features -- -Dwarnings",
            ["clippy", "--no-default-features", "--", "-Dwarnings"],
        )?;

        for manifest in BINDING_MANIFESTS {
            let label =
                format!("cargo clippy --manifest-path {manifest} --all-targets -- -Dwarnings");
            run_cargo_step(
                &workspace,
                &label,
                [
                    "clippy",
                    "--manifest-path",
                    manifest,
                    "--all-targets",
                    "--",
                    "-Dwarnings",
                ],
            )?;
        }

        Ok(())
    }
}

fn run_clippy_with_sarif(workspace: &Path, sarif: &Path) -> Result<()> {
    let sarif_path = if sarif.is_absolute() {
        sarif.to_path_buf()
    } else {
        workspace.join(sarif)
    };

    if let Some(parent) = sarif_path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("failed to create SARIF directory at {}", parent.display()))?;
    }

    let xtask_target = workspace.join("target").join("xtask");
    std::fs::create_dir_all(&xtask_target).with_context(|| {
        format!(
            "failed to ensure xtask scratch directory at {}",
            xtask_target.display()
        )
    })?;
    let json_path = xtask_target.join("clippy.json");

    let json_file = File::create(&json_path).with_context(|| {
        format!(
            "failed to create intermediate clippy output at {}",
            json_path.display()
        )
    })?;

    let mut cargo = Command::new("cargo");
    cargo.current_dir(workspace);
    cargo.arg("clippy");
    cargo.arg("--all-targets");
    cargo.arg("--all-features");
    cargo.arg("--message-format=json");
    cargo.arg("--");
    cargo.arg("-Dwarnings");
    cargo.stdout(Stdio::from(json_file));
    run_command(
        cargo,
        "cargo clippy --all-targets --all-features --message-format=json -- -Dwarnings",
    )?;

    let json_input = File::open(&json_path).with_context(|| {
        format!(
            "failed to reopen clippy JSON output at {}",
            json_path.display()
        )
    })?;
    let sarif_file = File::create(&sarif_path)
        .with_context(|| format!("failed to create SARIF output at {}", sarif_path.display()))?;

    let mut sarif_cmd = Command::new("clippy-sarif");
    sarif_cmd.stdin(Stdio::from(json_input));
    sarif_cmd.stdout(Stdio::from(sarif_file));
    run_command(sarif_cmd, "clippy-sarif")?;

    let formatted_path = sarif_path.with_extension("sarif.tmp");
    let sarif_input = File::open(&sarif_path)
        .with_context(|| format!("failed to reopen SARIF output at {}", sarif_path.display()))?;
    let sarif_output = File::create(&formatted_path).with_context(|| {
        format!(
            "failed to create SARIF output at {}",
            formatted_path.display()
        )
    })?;

    let mut fmt = Command::new("sarif-fmt");
    fmt.stdin(Stdio::from(sarif_input));
    fmt.stdout(Stdio::from(sarif_output));
    run_command(fmt, "sarif-fmt")?;

    let formatted_len = fs::metadata(&formatted_path)
        .map(|metadata| metadata.len())
        .unwrap_or(0);
    if formatted_len == 0 {
        let _ = fs::remove_file(&formatted_path);
        println!("sarif-fmt produced empty output, keeping original SARIF");
    } else {
        fs::rename(&formatted_path, &sarif_path).with_context(|| {
            format!("failed to replace SARIF output at {}", sarif_path.display())
        })?;
    }

    println!("SARIF report written to {}", sarif_path.display());

    Ok(())
}

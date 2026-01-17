// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context, Result};
use clap::Args;

use crate::tasks::util::{dedup, run_cargo_step, workspace_root};

/// Builds the regorus FFI crate for the selected targets.
#[derive(Args)]
pub struct BuildFfiCommand {
    /// Target triples to compile (defaults to the current host when omitted).
    #[arg(long = "target", value_name = "TRIPLE")]
    targets: Vec<String>,

    /// Build in release mode instead of debug.
    #[arg(long)]
    release: bool,
}

impl BuildFfiCommand {
    pub fn run(&self) -> Result<()> {
        let workspace_root = workspace_root();
        let targets = resolve_targets(self.targets.clone())?;
        let profile = profile_dir(self.release);

        build_targets(&workspace_root, &targets, self.release)?;

        let base = workspace_root.join("bindings/ffi/target");
        if targets.len() == 1 {
            println!(
                "Built FFI artefacts at {}",
                artifact_path(&base, targets[0].as_str(), profile).display()
            );
        } else {
            println!("Built FFI artefacts:");
            for triple in &targets {
                println!(
                    "  {} -> {}",
                    triple,
                    artifact_path(&base, triple, profile).display()
                );
            }
        }

        Ok(())
    }
}

/// Resolves the list of target triples to compile, defaulting to the host.
pub fn resolve_targets(mut targets: Vec<String>) -> Result<Vec<String>> {
    if targets.is_empty() {
        targets.push(detect_host_triple()?);
    }

    dedup(&mut targets);
    Ok(targets)
}

/// Compiles the FFI crate for the supplied target triples.
pub fn build_targets(root: &Path, targets: &[String], release: bool) -> Result<()> {
    for target in targets {
        cargo_build(root, target, release)?;
    }
    Ok(())
}

/// Returns the cargo profile directory associated with the release flag.
pub fn profile_dir(release: bool) -> &'static str {
    if release {
        "release"
    } else {
        "debug"
    }
}

pub fn detect_host_triple() -> Result<String> {
    let output = Command::new("rustc")
        .arg("-Vv")
        .output()
        .context("failed to invoke rustc")?;

    if !output.status.success() {
        bail!(
            "rustc -Vv failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let stdout = String::from_utf8(output.stdout).context("rustc output was not valid UTF-8")?;
    for line in stdout.lines() {
        if let Some(rest) = line.strip_prefix("host: ") {
            return Ok(rest.trim().to_string());
        }
    }

    Err(anyhow!("failed to detect host target triple"))
}

fn cargo_build(root: &Path, target: &str, release: bool) -> Result<()> {
    let dir = root.join("bindings/ffi");
    let mut args = vec![
        OsString::from("build"),
        OsString::from("--locked"),
        OsString::from("--target"),
        OsString::from(target),
    ];
    if release {
        args.push(OsString::from("--release"));
    }

    let title = format!("cargo build (ffi:{target})");
    run_cargo_step(&dir, &title, args)
}

fn artifact_path(base: &Path, target: &str, profile: &str) -> PathBuf {
    base.join(target).join(profile)
}

/// Executes the FFI binding test suite.
#[derive(Args, Default)]
pub struct TestFfiCommand {
    /// Build the FFI crate in release mode prior to testing.
    #[arg(long)]
    pub release: bool,

    /// Pass --frozen to all cargo invocations.
    #[arg(long)]
    pub frozen: bool,
}

impl TestFfiCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let ffi_dir = workspace.join("bindings/ffi");

        let mut build_args = vec![OsString::from("build"), OsString::from("--locked")];
        if self.release {
            build_args.push(OsString::from("--release"));
        }
        if self.frozen {
            build_args.push(OsString::from("--frozen"));
        }
        let build_label = if self.release {
            "cargo build --release (bindings/ffi)"
        } else {
            "cargo build (bindings/ffi)"
        };
        run_cargo_step(&ffi_dir, build_label, build_args)?;

        let mut test_args = vec![OsString::from("test"), OsString::from("--locked")];
        if self.release {
            test_args.push(OsString::from("--release"));
        }
        if self.frozen {
            test_args.push(OsString::from("--frozen"));
        }
        test_args.push(OsString::from("--features"));
        test_args.push(OsString::from("contention_checks"));
        run_cargo_step(
            &ffi_dir,
            "cargo test --features contention_checks (bindings/ffi)",
            test_args,
        )?;

        Ok(())
    }
}

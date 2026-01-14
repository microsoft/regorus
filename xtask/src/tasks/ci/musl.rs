// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::OsString;
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{anyhow, Result};
use clap::Args;

use crate::tasks::util::{
    opa_passing_arguments, run_cargo_step as util_run_cargo_step, workspace_root,
};

/// Exercises the MUSL build and test matrix used in CI.
#[derive(Args, Default)]
pub struct TestMuslCommand {
    /// Target triple to compile and test against.
    #[arg(long, default_value = "x86_64-unknown-linux-musl")]
    pub target: String,

    /// Compile artefacts in release mode.
    #[arg(long)]
    pub release: bool,

    /// Propagate --frozen to all cargo invocations.
    #[arg(long)]
    pub frozen: bool,

    /// Feature list passed to the OPA conformance tests.
    #[arg(long, default_value = "opa-testutil,serde_json/arbitrary_precision")]
    pub opa_features: String,
}

impl TestMuslCommand {
    pub fn run(&self) -> Result<()> {
        ensure_musl_gcc()?;

        let workspace = workspace_root();

        run_build_all_targets(&workspace, &self.target, self.release, self.frozen)?;
        run_cargo_test(&workspace, &self.target, self.release, self.frozen, &[])?;
        run_named_test(&workspace, &self.target, self.release, self.frozen, "aci")?;
        run_named_test(&workspace, &self.target, self.release, self.frozen, "kata")?;
        run_opa_tests(
            &workspace,
            &self.target,
            self.release,
            self.frozen,
            &self.opa_features,
        )
    }
}

fn ensure_musl_gcc() -> Result<()> {
    let status = Command::new("musl-gcc")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();

    match status {
        Ok(result) if result.success() => Ok(()),
        _ => Err(anyhow!(
            "musl-gcc is required but was not found in PATH. Install musl-tools to continue."
        )),
    }
}
fn run_build_all_targets(
    workspace: &Path,
    target: &str,
    release: bool,
    frozen: bool,
) -> Result<()> {
    let mut args = cargo_target_args("build", target, release, frozen);
    args.push(OsString::from("--all-targets"));
    util_run_cargo_step(workspace, "cargo build --all-targets (musl)", args)
}

fn run_cargo_test(
    workspace: &Path,
    target: &str,
    release: bool,
    frozen: bool,
    extra: &[&str],
) -> Result<()> {
    let mut args = cargo_target_args("test", target, release, frozen);
    for arg in extra {
        args.push(OsString::from(*arg));
    }
    let mut label = String::from("cargo test (musl)");
    if release {
        label.push_str(" --release");
    }
    if !extra.is_empty() {
        label.push(' ');
        label.push_str(&extra.join(" "));
    }
    util_run_cargo_step(workspace, &label, args)
}

fn run_named_test(
    workspace: &Path,
    target: &str,
    release: bool,
    frozen: bool,
    name: &str,
) -> Result<()> {
    run_cargo_test(workspace, target, release, frozen, &["--test", name])
}

fn run_opa_tests(
    workspace: &Path,
    target: &str,
    release: bool,
    frozen: bool,
    features: &str,
) -> Result<()> {
    let tests = opa_passing_arguments(workspace)?;
    let mut args = cargo_target_args("test", target, release, frozen);
    args.push(OsString::from("--features"));
    args.push(OsString::from(features));
    args.push(OsString::from("--test"));
    args.push(OsString::from("opa"));
    args.push(OsString::from("--"));
    for entry in tests {
        args.push(OsString::from(entry));
    }

    let mut label = format!("cargo test --test opa --features {} (musl)", features);
    if release {
        label.push_str(" --release");
    }

    util_run_cargo_step(workspace, &label, args)
}

fn cargo_target_args(subcommand: &str, target: &str, release: bool, frozen: bool) -> Vec<OsString> {
    let mut args = vec![OsString::from(subcommand)];
    if release {
        args.push(OsString::from("--release"));
    }
    if frozen {
        args.push(OsString::from("--frozen"));
    }
    args.push(OsString::from("--locked"));
    args.push(OsString::from("--target"));
    args.push(OsString::from(target));
    args
}

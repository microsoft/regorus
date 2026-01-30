// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::tasks::util::{run_cargo_step, run_command, workspace_root};
use anyhow::{anyhow, Context, Result};
use clap::Args;

#[derive(Args, Default)]
pub struct TestCCommand {
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

#[derive(Args, Default)]
pub struct TestCNoStdCommand {
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

impl TestCCommand {
    pub fn run(&self) -> Result<()> {
        if !self.skip_ffi {
            prepare_ffi_artifacts(self.release, self.frozen)?;
        }
        run_binding("bindings/c", "regorus_test", self.release)?;
        run_binding("bindings/c", "regorus_rvm_test", self.release)
    }
}

impl TestCNoStdCommand {
    pub fn run(&self) -> Result<()> {
        if !self.skip_ffi {
            prepare_ffi_artifacts(self.release, self.frozen)?;
        }
        run_binding("bindings/c-nostd", "regorus_test", self.release)
    }
}

pub(super) fn run_binding(relative_dir: &str, binary_name: &str, release: bool) -> Result<()> {
    let workspace = workspace_root();
    let source_dir = workspace.join(relative_dir);
    let build_dir = source_dir.join("build");
    fs::create_dir_all(&build_dir).with_context(|| {
        format!(
            "failed to create build directory at {}",
            build_dir.display()
        )
    })?;

    let build_type = if release { "Release" } else { "Debug" };
    let mut configure = Command::new("cmake");
    configure.arg("-S").arg(&source_dir);
    configure.arg("-B").arg(&build_dir);
    configure.arg(format!("-DCMAKE_BUILD_TYPE={build_type}"));
    run_command(configure, &format!("cmake configure ({relative_dir})"))?;

    let mut build = Command::new("cmake");
    build.arg("--build").arg(&build_dir);
    build.arg("--config").arg(build_type);
    run_command(build, &format!("cmake build ({relative_dir})"))?;

    let executable = locate_executable(&build_dir, binary_name)?;
    let mut run = Command::new(&executable);
    run.current_dir(&build_dir);
    run_command(run, &format!("{binary_name} ({relative_dir})"))?;

    Ok(())
}

fn locate_executable(build_dir: &Path, binary_name: &str) -> Result<PathBuf> {
    let mut candidates = Vec::new();
    if cfg!(windows) {
        let exe = format!("{binary_name}.exe");
        candidates.push(build_dir.join(&exe));
        candidates.push(build_dir.join("Release").join(&exe));
        candidates.push(build_dir.join("Debug").join(&exe));
    } else {
        candidates.push(build_dir.join(binary_name));
        candidates.push(build_dir.join("Release").join(binary_name));
        candidates.push(build_dir.join("Debug").join(binary_name));
    }

    for candidate in candidates {
        if candidate.exists() {
            return Ok(candidate);
        }
    }

    Err(anyhow!(
        "failed to locate built executable '{}' under {}",
        binary_name,
        build_dir.display()
    ))
}

pub(super) fn prepare_ffi_artifacts(release: bool, frozen: bool) -> Result<()> {
    let workspace = workspace_root();
    let ffi_dir = workspace.join("bindings/ffi");

    let mut build_args = vec!["build", "--locked"];
    if release {
        build_args.push("--release");
    }
    if frozen {
        build_args.push("--frozen");
    }
    let build_label = if release {
        "cargo build --release (bindings/ffi)"
    } else {
        "cargo build (bindings/ffi)"
    };
    run_cargo_step(&ffi_dir, build_label, build_args)
}

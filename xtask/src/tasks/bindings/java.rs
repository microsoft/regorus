// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, Context, Result};
use clap::Args;

use crate::tasks::util::{path_separator, run_cargo_step, run_command, workspace_root};

#[derive(Args, Default)]
pub struct BuildJavaCommand {
    /// Skip the Maven test phase while packaging.
    #[arg(long)]
    pub skip_tests: bool,
}

impl BuildJavaCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let java_dir = workspace.join("bindings/java");

        run_command(self.into_command(&java_dir)?, "mvn package (bindings/java)")
    }

    fn into_command(&self, java_dir: &Path) -> Result<Command> {
        let mut mvn = Command::new("mvn");
        mvn.current_dir(java_dir);
        mvn.arg("--batch-mode");
        mvn.arg("--no-transfer-progress");
        mvn.arg("package");
        if self.skip_tests {
            mvn.arg("-DskipTests");
        }
        Ok(mvn)
    }
}

#[derive(Args, Default)]
pub struct TestJavaCommand {
    /// Build the JNI artefacts in release mode before testing.
    #[arg(long)]
    pub release: bool,

    /// Propagate --frozen to cargo invocations.
    #[arg(long)]
    pub frozen: bool,
}

impl TestJavaCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let java_dir = workspace.join("bindings/java");

        build_java_crate(&workspace, self.release, self.frozen)?;
        run_command(
            BuildJavaCommand { skip_tests: false }.into_command(&java_dir)?,
            "mvn package (bindings/java)",
        )?;
        run_java_integration(&java_dir, self.release)
    }
}
fn build_java_crate(workspace: &Path, release: bool, frozen: bool) -> Result<()> {
    let mut args = vec!["build"];
    if release {
        args.push("--release");
    }
    if frozen {
        args.push("--frozen");
    }
    args.push("--manifest-path");
    args.push("bindings/java/Cargo.toml");
    args.push("--locked");
    run_cargo_step(workspace, "cargo build (bindings/java)", args)
}

fn run_java_integration(java_dir: &Path, release: bool) -> Result<()> {
    let jar = locate_java_jar(java_dir)?;
    let separator = path_separator();
    let classpath = format!("{}{}.", jar.display(), separator);

    let mut javac = Command::new("javac");
    javac.current_dir(java_dir);
    javac.arg("-cp");
    javac.arg(&classpath);
    javac.arg("Test.java");
    run_command(javac, "javac Test.java (bindings/java)")?;

    let profile = if release { "release" } else { "debug" };
    let lib_path = java_dir.join("target").join(profile);
    let mut java = Command::new("java");
    java.current_dir(java_dir);
    java.arg(format!("-Djava.library.path={}", lib_path.display()));
    java.arg("-cp");
    java.arg(&classpath);
    java.arg("Test");
    run_command(java, "java Test (bindings/java)")
}

fn locate_java_jar(java_dir: &Path) -> Result<PathBuf> {
    let target_dir = java_dir.join("target");
    let entries = fs::read_dir(&target_dir).with_context(|| {
        format!(
            "failed to enumerate built JARs under {}",
            target_dir.display()
        )
    })?;

    let mut candidates = Vec::new();
    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !file_name.starts_with("regorus-java-") || !file_name.ends_with(".jar") {
            continue;
        }
        if file_name.contains("-sources") || file_name.contains("-javadoc") {
            continue;
        }
        candidates.push(path);
    }

    candidates.sort();
    candidates
        .pop()
        .ok_or_else(|| anyhow!("no regorus-java jar found under {}", target_dir.display()))
}

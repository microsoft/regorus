// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, Context, Result};
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

    /// Build the explanations-enabled experimental npm artifact.
    #[arg(long)]
    pub experimental: bool,
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
            self.experimental,
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

    /// Build and test the explanations-enabled experimental npm artifact.
    #[arg(long)]
    pub experimental: bool,
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
                self.experimental,
            )?;
        }

        run_wasm_tests(&wasm_dir, self.release, self.experimental)?;

        let mut node = Command::new(&self.node);
        node.current_dir(&wasm_dir);
        node.arg("test.js");
        node.env(
            "REGORUS_WASM_PACKAGE_DIR",
            if self.experimental {
                self.out_dir
                    .as_deref()
                    .unwrap_or_else(|| Path::new("pkg-experimental"))
            } else {
                self.out_dir.as_deref().unwrap_or_else(|| Path::new("pkg"))
            },
        );
        node.env(
            "REGORUS_WASM_EXPERIMENTAL",
            if self.experimental { "1" } else { "0" },
        );
        let label = format!("{} test.js (bindings/wasm)", self.node);
        run_command(node, &label)
    }
}

fn build_wasm(
    wasm_dir: &Path,
    release: bool,
    target: &str,
    out_dir: Option<&Path>,
    experimental: bool,
) -> Result<()> {
    let output_dir = out_dir.unwrap_or_else(|| {
        Path::new(if experimental {
            "pkg-experimental"
        } else {
            "pkg"
        })
    });
    let mut pack = Command::new("wasm-pack");
    pack.current_dir(wasm_dir);
    pack.arg("build");
    pack.arg("--target");
    pack.arg(target);
    if release {
        pack.arg("--release");
    }
    pack.arg("--out-dir");
    pack.arg(output_dir);
    if experimental {
        pack.arg("--");
        pack.arg("--features");
        pack.arg("explanations");
    }
    run_command(pack, "wasm-pack build (bindings/wasm)")?;

    if experimental {
        rewrite_experimental_package_metadata(wasm_dir, output_dir)?;
    }
    Ok(())
}
fn run_wasm_tests(wasm_dir: &Path, release: bool, experimental: bool) -> Result<()> {
    let mut test = Command::new("wasm-pack");
    test.current_dir(wasm_dir);
    test.arg("test");
    test.arg("--node");
    if release {
        test.arg("--release");
    }
    if experimental {
        test.arg("--");
        test.arg("--features");
        test.arg("explanations");
    }
    run_command(test, "wasm-pack test --node (bindings/wasm)")
}

fn rewrite_experimental_package_metadata(wasm_dir: &Path, output_dir: &Path) -> Result<()> {
    let package_json = wasm_dir.join(output_dir).join("package.json");
    let contents = fs::read_to_string(&package_json)
        .with_context(|| format!("failed to read {}", package_json.display()))?;
    let manifest_path = wasm_dir.join("Cargo.toml");
    let manifest = fs::read_to_string(&manifest_path)
        .with_context(|| format!("failed to read {}", manifest_path.display()))?
        .parse::<toml_edit::DocumentMut>()
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;
    let version = manifest["package"]["version"]
        .as_str()
        .ok_or_else(|| anyhow!("bindings/wasm Cargo.toml has no package version"))?;
    let experimental_version_path = wasm_dir.join("../experimental-version.txt");
    let experimental_version = fs::read_to_string(&experimental_version_path)
        .with_context(|| format!("failed to read {}", experimental_version_path.display()))?;
    let experimental_version = experimental_version.trim();
    if experimental_version.is_empty() {
        return Err(anyhow!(
            "{} contains an empty experimental version",
            experimental_version_path.display()
        ));
    }
    let standard_name = "\"name\": \"regorusjs\"";
    let standard_version = format!("\"version\": \"{version}\"");
    let contents = contents
        .replace(standard_name, "\"name\": \"regorusjs-experimental\"")
        .replace(
            &standard_version,
            &format!("\"version\": \"{version}-experimental.{experimental_version}\""),
        );
    if contents.contains(standard_name) || contents.contains(&standard_version) {
        return Err(anyhow!(
            "failed to rewrite experimental WASM package name or version in {}",
            package_json.display()
        ));
    }
    fs::write(&package_json, contents)
        .with_context(|| format!("failed to update {}", package_json.display()))
}

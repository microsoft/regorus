// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Updates dependencies across all Cargo manifests in the workspace.
//!
//! This task runs `cargo update` on the root workspace and each binding that has
//! a Cargo.lock file, ensuring all lock files are refreshed with the latest
//! compatible dependency versions according to their version constraints.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};
use clap::Args;

/// CLI entry point for `cargo xtask update-deps`.
#[derive(Args)]
pub struct UpdateDepsCommand {
    /// Perform a dry run without actually updating lock files
    #[arg(long)]
    dry_run: bool,
}

impl UpdateDepsCommand {
    /// Executes the dependency update workflow.
    pub fn run(&self) -> Result<()> {
        let workspace_root = workspace_root();

        println!("Updating workspace dependencies...");

        // Update root workspace
        if self.dry_run {
            println!("  [dry-run] Would update root workspace Cargo.lock");
        } else {
            update_manifest(&workspace_root, "Cargo.toml")?;
            println!("  ✓ Updated root workspace");
        }

        // Update each binding with a Cargo.lock
        let bindings = vec![
            ("ffi", "bindings/ffi/Cargo.toml"),
            ("java", "bindings/java/Cargo.toml"),
            ("python", "bindings/python/Cargo.toml"),
            ("wasm", "bindings/wasm/Cargo.toml"),
            ("ruby", "bindings/ruby/ext/regorusrb/Cargo.toml"),
        ];

        for (name, manifest) in bindings {
            let manifest_path = workspace_root.join(manifest);
            if !manifest_path.exists() {
                continue;
            }

            // Check if Cargo.lock exists
            if let Some(parent) = manifest_path.parent() {
                let lock_path = parent.join("Cargo.lock");
                if lock_path.exists() {
                    if self.dry_run {
                        println!("  [dry-run] Would update {} binding", name);
                    } else {
                        update_manifest(&workspace_root, manifest)?;
                        println!("  ✓ Updated {} binding", name);
                    }
                }
            }
        }

        println!("\nDependency update complete!");
        Ok(())
    }
}

/// Returns the workspace root (one level above this crate).
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask resides in workspace root")
        .to_path_buf()
}

/// Runs cargo update for a specific manifest.
fn update_manifest(root: &Path, manifest: &str) -> Result<()> {
    let manifest_path = root.join(manifest);

    let output = Command::new("cargo")
        .arg("update")
        .arg("--manifest-path")
        .arg(&manifest_path)
        .output()
        .context("failed to run cargo update")?;

    if !output.status.success() {
        bail!(
            "cargo update failed for {}: {}",
            manifest_path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }

    Ok(())
}

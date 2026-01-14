// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use clap::Args;

use crate::tasks::util::{run_cargo_step, workspace_root};

const BINDING_MANIFESTS: &[&str] = &[
    "bindings/ffi/Cargo.toml",
    "bindings/java/Cargo.toml",
    "bindings/python/Cargo.toml",
    "bindings/wasm/Cargo.toml",
    "bindings/ruby/Cargo.toml",
];

/// Formats every Rust crate in the repository, including binding workspaces.
#[derive(Args, Default)]
pub struct FmtCommand {
    /// Fail instead of writing edits when formatting differs
    #[arg(long)]
    check: bool,
}

impl FmtCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();

        let mut fmt_args = vec!["fmt", "--all"];
        if self.check {
            fmt_args.extend(["--", "--check"]);
        }

        let fmt_label = if self.check {
            "cargo fmt --all -- --check"
        } else {
            "cargo fmt --all"
        };

        run_cargo_step(&workspace, fmt_label, fmt_args)?;

        for manifest in BINDING_MANIFESTS {
            let mut args = vec!["fmt", "--manifest-path", *manifest];
            let label = if self.check {
                args.extend(["--", "--check"]);
                format!("cargo fmt --manifest-path {manifest} -- --check")
            } else {
                format!("cargo fmt --manifest-path {manifest}")
            };

            run_cargo_step(&workspace, &label, args)?;
        }

        Ok(())
    }
}

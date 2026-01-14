// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::OsString;
use std::process::Command;

use anyhow::Result;
use clap::Args;

use crate::tasks::util::{run_cargo_step, run_command, workspace_root};

/// Runs the Ruby binding smoke tests.
#[derive(Args, Default)]
pub struct TestRubyCommand {
    /// Skip installing the bundler gem before running tests.
    #[arg(long)]
    pub skip_bundler_install: bool,

    /// Skip the Rust clippy pass prior to executing the Ruby test suite.
    #[arg(long)]
    pub skip_clippy: bool,

    /// Propagate --frozen to cargo invocations ahead of the Ruby test suite.
    #[arg(long)]
    pub frozen: bool,
}

impl TestRubyCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let ruby_dir = workspace.join("bindings/ruby");

        if !self.skip_bundler_install {
            let mut gem = Command::new("gem");
            gem.current_dir(&ruby_dir);
            gem.arg("install");
            gem.arg("bundler");
            gem.arg("--user-install");
            run_command(gem, "gem install bundler (bindings/ruby)")?;
        }

        let mut bundle_install = Command::new("bundle");
        bundle_install.current_dir(&ruby_dir);
        bundle_install.arg("install");
        run_command(bundle_install, "bundle install (bindings/ruby)")?;

        if !self.skip_clippy {
            let mut clippy_args = vec![
                OsString::from("clippy"),
                OsString::from("--all-targets"),
                OsString::from("--no-deps"),
            ];
            if self.frozen {
                clippy_args.insert(1, OsString::from("--frozen"));
            }
            clippy_args.push(OsString::from("--"));
            clippy_args.push(OsString::from("-Dwarnings"));

            run_cargo_step(
                &ruby_dir,
                "cargo clippy --all-targets --no-deps -- -Dwarnings (bindings/ruby)",
                clippy_args,
            )?;
        }

        let mut rake = Command::new("bundle");
        rake.current_dir(&ruby_dir);
        rake.arg("exec");
        rake.arg("rake");
        run_command(rake, "bundle exec rake (bindings/ruby)")
    }
}

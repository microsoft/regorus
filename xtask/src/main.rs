// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod tasks;

use anyhow::Result;
use clap::{Parser, Subcommand};

use tasks::{BindingsCommand, UpdateDepsCommand};

#[derive(Parser)]
#[command(author, version, about, propagate_version = true)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Bump binding manifests to match the main regorus crate version
    Bindings(BindingsCommand),
    /// Update dependencies across all workspace Cargo.lock files
    UpdateDeps(UpdateDepsCommand),
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Bindings(cmd) => cmd.run()?,
        Commands::UpdateDeps(cmd) => cmd.run()?,
    }

    Ok(())
}

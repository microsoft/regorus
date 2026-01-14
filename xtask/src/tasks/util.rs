// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

/// Returns the root of the workspace that hosts the xtask crate.
pub fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask resides in workspace root")
        .to_path_buf()
}

/// Runs a command, surfaces the command line, and maps a failing exit status to an error.
pub fn run_command(mut command: Command, label: &str) -> Result<()> {
    let display = format_command(&command);
    println!("$ {}", display);

    let status = command
        .status()
        .with_context(|| format!("failed to spawn {}", label))?;
    if !status.success() {
        bail!("{} failed with status {}", label, status);
    }

    Ok(())
}

/// Prints a simple section header to highlight the upcoming action.
pub fn log_step(title: &str) {
    println!("\n=== {} ===", title);
}

/// Logs a section heading and executes a cargo subcommand.
pub fn run_cargo_step<I, S>(workspace: &Path, title: &str, args: I) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    run_cargo_in_step(workspace, title, args)
}

/// Logs a section heading and executes a cargo subcommand within the provided directory.
pub fn run_cargo_in_step<I, S>(directory: &Path, title: &str, args: I) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let heading = format!("Running {}", title);
    log_step(&heading);
    let mut command = Command::new("cargo");
    command.current_dir(directory);
    command.args(args);
    run_command(command, title)
}

/// Formats a command with its arguments for diagnostic output.
pub fn format_command(command: &Command) -> String {
    let mut parts = Vec::new();
    parts.push(command.get_program().to_string_lossy().into_owned());
    for arg in command.get_args() {
        parts.push(arg.to_string_lossy().into_owned());
    }
    parts.join(" ")
}

/// Deduplicates the provided vector while preserving the original order.
pub fn dedup(values: &mut Vec<String>) {
    let mut unique = Vec::new();
    for value in values.drain(..) {
        if unique.iter().any(|existing| existing == &value) {
            continue;
        }
        unique.push(value);
    }
    *values = unique;
}

/// Returns the platform-specific path list separator character.
pub fn path_separator() -> &'static str {
    if cfg!(windows) {
        ";"
    } else {
        ":"
    }
}

/// Returns the environment variable used for dynamic library lookup.
pub fn library_search_env_var() -> &'static str {
    if cfg!(windows) {
        "PATH"
    } else if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else {
        "LD_LIBRARY_PATH"
    }
}

/// Ensures the provided directory is prepended to the requested environment variable.
pub fn prepend_env_path(command: &mut Command, key: &str, dir: &Path) {
    let mut value = OsString::new();
    value.push(dir);

    if let Some(existing) = std::env::var_os(key) {
        if !existing.is_empty() {
            value.push(path_separator());
            value.push(existing);
        }
    }

    command.env(key, value);
}

/// Prepends the supplied directory to the standard dynamic library search path.
pub fn add_library_search_path(command: &mut Command, dir: &Path) {
    let key = library_search_env_var();
    prepend_env_path(command, key, dir);
}

/// Returns the host architecture string expected by dotnet CLI switches.
pub fn dotnet_host_arch() -> &'static str {
    match std::env::consts::ARCH {
        "aarch64" => "arm64",
        "x86_64" => "x64",
        "arm" => "arm",
        "x86" => "x86",
        _ => "x64",
    }
}

/// Loads the list of passing OPA tests from the repository.
pub fn opa_passing_arguments(root: &Path) -> Result<Vec<String>> {
    let listing = root.join("tests/opa.passing");
    let contents = fs::read_to_string(&listing).with_context(|| {
        format!(
            "failed to read list of passing OPA tests from {}",
            listing.display()
        )
    })?;

    Ok(contents
        .split_whitespace()
        .filter(|entry| !entry.is_empty())
        .map(|entry| entry.to_string())
        .collect())
}

// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
use super::util::{run_command, workspace_root};
use anyhow::{bail, ensure, Context, Result};
use clap::Args;
use serde_json::Value;
use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

const RUST: &str = "nightly-2026-09-17";
const LEAN: &str = "leanprover/lean4:v4.35.0-rc4";
const AENEAS_REV: &str = "cd419953b67caae3e4d6b514b3ee3f3f1ff76ea1";
const MATHLIB_REV: &str = "1f414401f69059aa7eead47b53ee40bd38455eeb";
const GENERATED: &str = "RegorusHistory/Generated";
const MARKER: &str = ".regorus-history-generated";
const OWNER: &str = "regorus-history-extract\n";
const NORMALIZE: &[&str] = &[
    "test_and",
    "test_or",
    "test_not",
    "regex_test",
    "regex_union",
    "regex_intersect",
    "regex_concat",
    "regex_star",
    "regex_not",
    "nullable",
    "transition_const",
    "transition_if",
    "transition_union",
    "transition_intersect",
    "transition_not",
    "transition_append",
    "clean_transition_path",
];
const SYMBOLIC: &[&str] = &["symbolic_derivative", "interpret_transition"];

#[derive(Args)]
pub struct ExtractHistoryLeanCommand {}

fn command(program: impl AsRef<std::ffi::OsStr>) -> Command {
    let mut cmd = Command::new(program);
    cmd.env_remove("CHARON_TOOLCHAIN_IS_IN_PATH");
    cmd
}
fn capture(mut cmd: Command, label: &str) -> Result<String> {
    let output = cmd
        .output()
        .with_context(|| format!("failed to run {label}"))?;
    ensure!(
        output.status.success(),
        "{label} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(String::from_utf8(output.stdout)?.trim().to_owned())
}
fn rustup(args: &[&str]) -> Command {
    let mut cmd = command("rustup");
    cmd.args(args);
    cmd
}
fn lake(stage: &Path, args: &[&str]) -> Command {
    let mut cmd = command("elan");
    cmd.args(["run", LEAN, "lake"])
        .args(args)
        .current_dir(stage);
    cmd
}
struct Tools {
    aeneas: PathBuf,
    charon: PathBuf,
}
fn preflight() -> Result<Tools> {
    let home = env::var_os("AENEAS_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".aeneas")))
        .context("set AENEAS_HOME or HOME to locate pinned extraction tools")?;
    let aeneas =
        fs::canonicalize(home.join("bin/aeneas")).context("missing pinned Aeneas executable")?;
    let charon =
        fs::canonicalize(home.join("bin/charon")).context("missing pinned Charon executable")?;
    let driver = charon
        .parent()
        .context("Charon has no parent directory")?
        .join("charon-driver");
    ensure!(
        driver.is_file(),
        "charon-driver must be beside resolved Charon executable: {}",
        driver.display()
    );
    fs::canonicalize(&driver).context("cannot resolve charon-driver")?;
    let mut cmd = command(&aeneas);
    cmd.arg("-version");
    let version = capture(cmd, "Aeneas version")?;
    ensure!(
        version == "aeneas nightly-2026.10.15-cd41995" || version == format!("aeneas {AENEAS_REV}"),
        "unexpected Aeneas version: {version}"
    );
    let mut cmd = command(&charon);
    cmd.arg("version");
    let version = capture(cmd, "Charon version")?;
    ensure!(
        version == "0.1.287 (26abff028ced534ebf8e861f2d3dd1743e2aa318)",
        "unexpected Charon version: {version}"
    );
    let mut cmd = command(&charon);
    cmd.arg("toolchain-version");
    ensure!(
        capture(cmd, "Charon toolchain")? == RUST,
        "Charon toolchain must be {RUST}"
    );
    let version = capture(rustup(&["run", RUST, "rustc", "-vV"]), "pinned Rust SDK")?;
    let host = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .context("rustc did not report native host")?;
    let components = capture(
        rustup(&["component", "list", "--installed", "--toolchain", RUST]),
        "installed Rust components",
    )?;
    for component in [
        format!("rustc-dev-{host}"),
        format!("llvm-tools-{host}"),
        "rust-src".to_owned(),
    ] {
        ensure!(
            components
                .lines()
                .any(|line| line.split_whitespace().next() == Some(component.as_str())),
            "missing installed {RUST} component {component}; refusing automatic SDK installation"
        );
    }
    let version = capture(lake(Path::new("."), &["--version"]), "pinned Lean SDK")?;
    ensure!(
        version.contains("Lean version 4.35.0-rc4") || version.contains("Lean 4.35.0-rc4"),
        "unexpected Lean/Lake version: {version}"
    );
    Ok(Tools { aeneas, charon })
}

impl ExtractHistoryLeanCommand {
    pub fn run(&self) -> Result<()> {
        let tools = preflight()?;
        let root = workspace_root();
        let project = root.join("verification/aeneas/history");
        let harness = project.join("rust");
        let final_lean = project.join("lean");
        let output = root.join("target/aeneas/history");
        let stage = output.join("stage");
        let llbc = output.join("regorus_history_extract.llbc");
        let target = output.join("cargo");
        // ponytail: one extractor per checkout uses fixed staging; use isolated checkouts if concurrent extraction is needed.
        fs::create_dir_all(&stage)?;
        for entry in fs::read_dir(&stage)? {
            let entry = entry?;
            if entry.file_name() != ".lake" && entry.file_name() != "lake-manifest.json" {
                remove(&entry.path())?;
            }
        }
        for name in ["lean-toolchain", "lakefile.toml", "RegorusHistory.lean"] {
            fs::copy(final_lean.join(name), stage.join(name))?;
        }
        if final_lean.join("lake-manifest.json").is_file() {
            fs::copy(
                final_lean.join("lake-manifest.json"),
                stage.join("lake-manifest.json"),
            )?;
        }
        let mut cmd = rustup(&["run", RUST, "cargo", "test", "--manifest-path"]);
        cmd.arg(harness.join("Cargo.toml"))
            .arg("--lib")
            .current_dir(&harness);
        run_command(cmd, "history extraction Rust smoke")?;
        let mut cmd = rustup(&["run", RUST, "cargo", "clean", "--manifest-path"]);
        cmd.arg(harness.join("Cargo.toml"))
            .args(["--package", "regorus-history-extract", "--target-dir"])
            .arg(&target)
            .current_dir(&harness);
        run_command(cmd, "fresh history extraction MIR")?;
        if llbc.exists() {
            fs::remove_file(&llbc)?;
        }
        let mut cmd = command(&tools.charon);
        cmd.current_dir(&harness)
            .env("CARGO_TARGET_DIR", &target)
            .args([
                "cargo",
                "--preset=aeneas",
                "--abort-on-error",
                "--error-on-warnings",
                "--start-from=crate::normalize",
                "--start-from=crate::symbolic",
                "--start-from=crate::store",
                "--start-from=crate::smoke",
            ]);
        // Only scalar error construction is external: no semantic or storage body is hidden.
        for diagnostic in [
            "error::normalization_invariant",
            "error::symbolic_invariant",
            "error::invalid_truth_assignment",
            "error::graph_id_overflow",
            "error::graph_index_overflow",
            "error::invalid_atom_set",
            "error::missing_transition_atom",
            "store::store_invariant",
            "store::inconsistent_nullability",
        ] {
            cmd.arg(format!("--opaque=crate::{diagnostic}"));
        }
        cmd.arg(format!("--dest-file={}", llbc.display()))
            .args(["--", "--lib"]);
        run_command(cmd, "Charon history extraction")?;
        ensure!(llbc.is_file(), "Charon did not produce {}", llbc.display());
        let mut cmd = command(&tools.aeneas);
        // The pinned reporter crashes on builtin unit; report checked manifest externals below.
        cmd.args([
            "-backend",
            "lean",
            "-split-files",
            "-emit-json",
            "-loops-to-rec",
            "-abort-on-error",
            "-warnings-as-errors",
            "-namespace",
            "RegorusHistory",
            "-dest",
        ])
        .arg(&stage)
        .args(["-subdir", GENERATED])
        .arg(&llbc)
        .current_dir(&harness);
        run_command(cmd, "Aeneas history translation")?;
        for name in ["Types", "Funs"] {
            let template = stage
                .join(GENERATED)
                .join(format!("{name}External_Template.lean"));
            if template.is_file() {
                fs::copy(
                    template,
                    stage.join(GENERATED).join(format!("{name}External.lean")),
                )?;
            }
            ensure!(
                stage.join(GENERATED).join(format!("{name}.lean")).is_file(),
                "missing generated {name}.lean"
            );
        }
        let manifest: Value = serde_json::from_slice(&fs::read(stage.join("translation.json"))?)?;
        let names = validate_coverage(&manifest)?;
        run_command(
            lake(&stage, &["--wfail", "build", "RegorusHistory"]),
            "Lean history elaboration",
        )?;
        validate_lock(&serde_json::from_slice(&fs::read(
            stage.join("lake-manifest.json"),
        )?)?)?;
        let mut coverage = String::from("import RegorusHistory.Generated.Funs\n");
        for name in &names {
            ensure!(
                !name.is_empty()
                    && name
                        .chars()
                        .all(|ch| ch.is_alphanumeric() || "_.'".contains(ch)),
                "unsafe Lean manifest name {name:?}"
            );
            coverage.push_str(&format!("#check {name}\n"));
        }
        fs::write(stage.join("Coverage.lean"), coverage)?;
        run_command(
            lake(
                &stage,
                &["env", "lean", "-DwarningAsError=true", "Coverage.lean"],
            ),
            "Lean production function coverage",
        )?;
        report_assumptions(&manifest)?;
        fs::write(stage.join(GENERATED).join(MARKER), OWNER)?;
        publish(&stage, &final_lean)?;
        println!("Extraction and Lean elaboration succeeded: {}/19 required production functions. No correctness proof is claimed.", names.len());
        Ok(())
    }
}

fn source(entry: &Value) -> String {
    entry
        .pointer("/source/file")
        .and_then(Value::as_str)
        .unwrap_or("")
        .replace('\\', "/")
}
fn validate_coverage(manifest: &Value) -> Result<Vec<String>> {
    ensure!(
        manifest.get("crate").and_then(Value::as_str) == Some("regorus_history_extract"),
        "wrong translation crate"
    );
    let functions = manifest
        .get("functions")
        .and_then(Value::as_array)
        .context("missing manifest functions")?;
    for entry in functions {
        let file = source(entry);
        if entry.get("is_local").and_then(Value::as_bool) == Some(true)
            && ["normalize", "symbolic"]
                .iter()
                .any(|module| file.ends_with(&format!("src/builtins/history/{module}.rs")))
        {
            ensure!(
                entry.get("is_opaque").and_then(Value::as_bool) == Some(false),
                "opaque local production helper: {}",
                entry["rust_name"]
            );
        }
    }
    let mut names = Vec::new();
    for (module, required) in [("normalize", NORMALIZE), ("symbolic", SYMBOLIC)] {
        for function in required {
            let rust_name = format!("regorus_history_extract::{module}::{function}");
            let entries: Vec<_> = functions
                .iter()
                .filter(|entry| {
                    entry.get("rust_name").and_then(Value::as_str) == Some(rust_name.as_str())
                        && entry.get("loop").is_none_or(Value::is_null)
                })
                .collect();
            ensure!(
                entries.len() == 1,
                "missing or duplicate production function {rust_name}"
            );
            let entry = entries[0];
            ensure!(
                entry.get("is_local").and_then(Value::as_bool) == Some(true)
                    && entry.get("is_opaque").and_then(Value::as_bool) == Some(false)
                    && source(entry).ends_with(&format!("src/builtins/history/{module}.rs")),
                "invalid production coverage for {rust_name}"
            );
            names.push(
                entry
                    .get("lean_name")
                    .and_then(Value::as_str)
                    .context("missing Lean function name")?
                    .to_owned(),
            );
        }
    }
    Ok(names)
}
fn validate_lock(lock: &Value) -> Result<()> {
    let packages = lock
        .get("packages")
        .and_then(Value::as_array)
        .context("missing Lake packages")?;
    for (name, rev) in [("aeneas", AENEAS_REV), ("mathlib", MATHLIB_REV)] {
        let matches: Vec<_> = packages
            .iter()
            .filter(|package| package.get("name").and_then(Value::as_str) == Some(name))
            .collect();
        ensure!(
            matches.len() == 1,
            "missing or duplicate Lake package {name}"
        );
        let package = matches[0];
        ensure!(
            package.get("type").and_then(Value::as_str) == Some("git")
                && package.get("rev").and_then(Value::as_str) == Some(rev),
            "wrong pinned Lake revision for {name}"
        );
        if name == "aeneas" {
            ensure!(
                package.get("subDir").and_then(Value::as_str) == Some("backends/lean"),
                "wrong Aeneas Lake subDir"
            );
        }
    }
    Ok(())
}
fn report_assumptions(manifest: &Value) -> Result<()> {
    println!("Generated external assumptions (outside the selected semantic-core target):");
    for kind in [
        "functions",
        "types",
        "globals",
        "trait_decls",
        "trait_impls",
    ] {
        let entries = manifest
            .get(kind)
            .and_then(Value::as_array)
            .with_context(|| format!("missing manifest {kind}"))?;
        for entry in entries {
            let file = entry
                .get("lean_file")
                .and_then(Value::as_str)
                .context("missing external Lean file")?
                .replace('\\', "/");
            if ["TypesExternal_Template.lean", "FunsExternal_Template.lean"]
                .iter()
                .any(|name| file.rsplit('/').next() == Some(name))
            {
                if kind == "functions" {
                    ensure!(
                        entry.get("is_opaque").and_then(Value::as_bool) == Some(true),
                        "external function is not marked opaque: {}",
                        entry["rust_name"]
                    );
                }
                println!(
                    "  {kind}: {} -> {} ({file})",
                    entry["rust_name"], entry["lean_name"]
                );
            }
        }
    }
    Ok(())
}
fn remove(path: &Path) -> Result<()> {
    if path.is_dir() && !path.is_symlink() {
        fs::remove_dir_all(path)?;
    } else {
        fs::remove_file(path)?;
    }
    Ok(())
}
fn copy_tree(from: &Path, to: &Path) -> Result<()> {
    fs::create_dir_all(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        ensure!(
            !entry.file_type()?.is_symlink(),
            "refusing generated symlink {}",
            entry.path().display()
        );
        let dest = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_tree(&entry.path(), &dest)?;
        } else {
            fs::copy(entry.path(), dest)?;
        }
    }
    Ok(())
}
fn publish(stage: &Path, destination: &Path) -> Result<()> {
    let generated = destination.join(GENERATED);
    if generated.exists() {
        ensure!(
            !generated.is_symlink(),
            "refusing symlink generated destination"
        );
        let nonempty = fs::read_dir(&generated)?.next().transpose()?.is_some();
        ensure!(
            !nonempty || fs::read_to_string(generated.join(MARKER)).ok().as_deref() == Some(OWNER),
            "refusing to replace unowned generated directory {}",
            generated.display()
        );
    }
    let transaction = destination.join(format!(".history-publication-{}", std::process::id()));
    ensure!(
        !transaction.exists(),
        "publication recovery directory already exists: {}",
        transaction.display()
    );
    fs::create_dir(&transaction)?;
    let fresh = transaction.join("new");
    let backup = transaction.join("old");
    fs::create_dir(&fresh)?;
    fs::create_dir(&backup)?;
    let names = [GENERATED, "translation.json", "lake-manifest.json"];
    let prepare = (|| -> Result<()> {
        copy_tree(&stage.join(GENERATED), &fresh.join(GENERATED))?;
        for name in &names[1..] {
            fs::copy(stage.join(name), fresh.join(name))?;
        }
        Ok(())
    })();
    if let Err(error) = prepare {
        fs::remove_dir_all(&transaction)?;
        return Err(error);
    }
    let mut saved = Vec::new();
    let mut installed = Vec::new();
    let result = (|| -> Result<()> {
        for name in names {
            let dest = destination.join(name);
            fs::create_dir_all(
                dest.parent()
                    .context("publication destination has no parent")?,
            )?;
            if dest.exists() {
                let old = backup.join(name);
                fs::create_dir_all(old.parent().context("backup has no parent")?)?;
                fs::rename(&dest, old)?;
                saved.push(name);
            }
            fs::rename(fresh.join(name), &dest)?;
            installed.push(name);
        }
        Ok(())
    })();
    if let Err(error) = result {
        let mut failures = Vec::new();
        for name in installed.iter().rev() {
            if let Err(error) = remove(&destination.join(name)) {
                failures.push(error.to_string());
            }
        }
        for name in saved.iter().rev() {
            if let Err(error) = fs::rename(backup.join(name), destination.join(name)) {
                failures.push(error.to_string());
            }
        }
        if !failures.is_empty() {
            bail!(
                "publication failed: {error:#}; rollback failed: {}; recovery retained at {}",
                failures.join("; "),
                transaction.display()
            );
        }
        fs::remove_dir_all(&transaction)?;
        return Err(error.context("publication failed; previous generated outputs restored"));
    }
    // Publication is committed; a cleanup failure cannot safely roll back a partially deleted backup.
    if let Err(error) = fs::remove_dir_all(&transaction) {
        eprintln!(
            "generated outputs published; backup cleanup failed at {}: {error}",
            transaction.display()
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn aeneas_history_rejects_invalid_production_coverage() {
        let mut functions = Vec::new();
        for (module, required) in [("normalize", NORMALIZE), ("symbolic", SYMBOLIC)] {
            for function in required {
                functions.push(json!({"rust_name": format!("regorus_history_extract::{module}::{function}"), "lean_name": format!("RegorusHistory.{module}.{function}"), "is_local": true, "is_opaque": false, "source": {"file": format!("/repo/src/builtins/history/{module}.rs")}, "loop": null}));
            }
        }
        let valid = json!({"crate": "regorus_history_extract", "functions": functions});
        assert_eq!(validate_coverage(&valid).unwrap().len(), 19);
        let mut opaque = valid.clone();
        opaque["functions"][0]["is_opaque"] = json!(true);
        assert!(validate_coverage(&opaque).is_err());
        let mut harness = valid.clone();
        harness["functions"][0]["source"]["file"] =
            json!("verification/aeneas/history/rust/src/normalize.rs");
        assert!(validate_coverage(&harness).is_err());
        let mut missing = valid;
        missing["functions"].as_array_mut().unwrap().remove(0);
        assert!(validate_coverage(&missing).is_err());
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Keeps every language binding in lockstep with the core `regorus` crate version.
//!
//! The command follows the pattern popularised by large Rust workspaces such as
//! [`rust-analyzer`](https://github.com/rust-lang/rust-analyzer),
//! [`gitoxide`](https://github.com/Byron/gitoxide), and
//! [`ripgrep`](https://github.com/BurntSushi/ripgrep): a dedicated `xtask`
//! binary shells out to Git to detect source changes and rewrites the affected
//! manifests in one shot. That approach gives us deterministic edits (the Rust
//! code owns every write) while piggybacking on Git's knowledge of tracked vs
//! ignored files, so we avoid re-implementing ignore logic or path matching by
//! hand.

// Version management quick reference:
// - Run `cargo xtask bindings` after bumping the root crate; untouched bindings align to the core (e.g. root 0.5.2 pulls a quiet binding from 0.5.1 → 0.5.2).
// - Binding edits trigger a SemVer "minor" bump even while major = 0: 0.5.1+changes → 0.6.0, and 0.5.3+changes still lands on 0.6.0 even if the root sits at 0.5.2.
// - When the root races ahead, we follow it: a clean binding at 0.6.2 syncing against root 0.7.0 ends up at 0.7.0.
// - Use `cargo xtask bindings --check` in CI or pre-commit to fail fast when any manifest would be rewritten.

use std::collections::HashSet;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context, Result};
use clap::Args;
use regex::Regex;
use semver::{BuildMetadata, Prerelease, Version};
use toml_edit::{value, DocumentMut};

/// CLI entry point for `cargo xtask bindings`.
#[derive(Args)]
pub struct BindingsCommand {
    /// Override the version applied to bindings (defaults to regorus crate version)
    #[arg(long, value_name = "VERSION")]
    new_version: Option<String>,

    /// Compare binding sources against this git ref (defaults to merge-base with origin/main)
    #[arg(long, value_name = "REF")]
    base_ref: Option<String>,

    /// Return an error instead of writing files when updates are needed
    #[arg(long)]
    check: bool,
}

impl BindingsCommand {
    /// Executes the bindings update workflow and reports any edits performed.
    pub fn run(&self) -> Result<()> {
        let workspace_root = workspace_root();
        let root_version = match self.new_version.as_deref() {
            Some(explicit) => Version::parse(explicit)
                .with_context(|| format!("invalid --new-version '{explicit}'"))?,
            None => read_root_crate_version(&workspace_root)?,
        };

        let watch_dirs = collect_watch_dirs();
        let changed_paths =
            collect_changed_paths(&workspace_root, self.base_ref.as_deref(), &watch_dirs)?;

        let mut touched_paths = Vec::new();
        let mut summaries = Vec::new();

        for binding in BINDINGS {
            let binding_changed = binding_has_changes(binding, &changed_paths);
            let current_version = read_binding_version(&workspace_root, binding)?;
            let desired_version = desired_version(&current_version, &root_version, binding_changed);
            let mut files =
                apply_binding_version(&workspace_root, binding, &desired_version, self.check)?;
            let files_modified = !files.is_empty();
            touched_paths.append(&mut files);
            let version_changed = desired_version != current_version;

            summaries.push(BindingSummary {
                name: binding.name,
                desired_version,
                version_changed,
                binding_changed,
                files_modified,
            });
        }

        if !self.check {
            if touched_paths.is_empty() {
                println!("Bindings already up to date (target {}).", root_version);
            } else {
                println!("Updated binding versions:");
                for summary in summaries.into_iter().filter(|s| s.files_modified) {
                    let reason = if summary.binding_changed && summary.version_changed {
                        "binding changes detected"
                    } else if summary.version_changed {
                        "aligned with core version"
                    } else {
                        "metadata normalized"
                    };
                    println!(
                        "  {} -> {} ({reason})",
                        summary.name, summary.desired_version
                    );
                }
            }
        }

        Ok(())
    }
}

/// Captures what happened for a single binding during a run.
struct BindingSummary {
    name: &'static str,
    desired_version: Version,
    version_changed: bool,
    binding_changed: bool,
    files_modified: bool,
}

/// Static description of each binding and the artefacts that should be updated.
struct Binding {
    name: &'static str,
    watch: &'static [&'static str],
    manifest: Option<&'static str>,
    ruby_version: Option<&'static str>,
    pom_xml: Option<&'static str>,
    csharp_project: Option<&'static str>,
    csharp_dependents: &'static [&'static str],
}

/// Shared empty slice to keep the binding declarations uncluttered.
const EMPTY: &[&str] = &[];

/// Declarative inventory of the bindings we keep in sync.
const BINDINGS: &[Binding] = &[
    Binding {
        name: "ffi",
        watch: &["bindings/ffi"],
        manifest: Some("bindings/ffi/Cargo.toml"),
        ruby_version: None,
        pom_xml: None,
        csharp_project: None,
        csharp_dependents: EMPTY,
    },
    Binding {
        name: "java",
        watch: &["bindings/java"],
        manifest: Some("bindings/java/Cargo.toml"),
        ruby_version: None,
        pom_xml: Some("bindings/java/pom.xml"),
        csharp_project: None,
        csharp_dependents: EMPTY,
    },
    Binding {
        name: "python",
        watch: &["bindings/python"],
        manifest: Some("bindings/python/Cargo.toml"),
        ruby_version: None,
        pom_xml: None,
        csharp_project: None,
        csharp_dependents: EMPTY,
    },
    Binding {
        name: "wasm",
        watch: &["bindings/wasm"],
        manifest: Some("bindings/wasm/Cargo.toml"),
        ruby_version: None,
        pom_xml: None,
        csharp_project: None,
        csharp_dependents: EMPTY,
    },
    Binding {
        name: "ruby",
        watch: &["bindings/ruby"],
        manifest: Some("bindings/ruby/ext/regorusrb/Cargo.toml"),
        ruby_version: Some("bindings/ruby/lib/regorus/version.rb"),
        pom_xml: None,
        csharp_project: None,
        csharp_dependents: EMPTY,
    },
    Binding {
        name: "csharp",
        watch: &["bindings/csharp"],
        manifest: None,
        ruby_version: None,
        pom_xml: None,
        csharp_project: Some("bindings/csharp/Regorus/Regorus.csproj"),
        csharp_dependents: &[
            "bindings/csharp/Regorus.Tests/Regorus.Tests.csproj",
            "bindings/csharp/Benchmarks/Benchmarks.csproj",
            "bindings/csharp/TargetExampleApp/TargetExampleApp.csproj",
            "bindings/csharp/TestApp/TestApp.csproj",
        ],
    },
];

/// Returns the workspace root (one level above this crate).
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask resides in workspace root")
        .to_path_buf()
}

/// Collects the unique set of directories whose contents we monitor for changes.
/// Collects the unique set of directories whose contents we monitor for changes.
fn collect_watch_dirs() -> Vec<&'static str> {
    let mut seen = HashSet::new();
    BINDINGS
        .iter()
        .flat_map(|binding| binding.watch.iter().copied())
        .filter(|dir| seen.insert(*dir))
        .collect()
}

/// Returns every binding-relative path that changed compared to the base
/// revision as well as unstaged or untracked files in the working tree.
fn collect_changed_paths(
    root: &Path,
    base_ref: Option<&str>,
    watch_dirs: &[&'static str],
) -> Result<HashSet<String>> {
    let mut paths = HashSet::new();

    if !watch_dirs.is_empty() {
        if let Some(base) = resolve_base_ref(root, base_ref)? {
            let mut args: Vec<&str> = vec!["diff", "--name-only", base.as_str()];
            args.push("--");
            args.extend(watch_dirs.iter().copied());
            let diff = run_git(root, args)?;
            for line in diff.lines() {
                let trimmed = line.trim();
                if !trimmed.is_empty() {
                    paths.insert(trimmed.to_string());
                }
            }
        }

        let mut status_args: Vec<&str> = vec!["status", "--porcelain"]; // covers tracked + untracked
        status_args.push("--");
        status_args.extend(watch_dirs.iter().copied());
        let status = run_git(root, status_args)?;
        for line in status.lines() {
            if line.len() < 4 {
                continue;
            }
            let details = line[3..].trim();
            if details.is_empty() {
                continue;
            }
            let path = details.split(" -> ").last().unwrap().to_string();
            paths.insert(path);
        }
    }

    Ok(paths)
}

/// Picks the git commit to diff against: explicit flag, merge-base with
/// `origin/main`, then the immediate parent commit as a fallback.
fn resolve_base_ref(root: &Path, explicit: Option<&str>) -> Result<Option<String>> {
    if let Some(reference) = explicit {
        return Ok(Some(reference.to_string()));
    }

    if let Ok(output) = run_git(root, ["merge-base", "HEAD", "origin/main"]) {
        if let Some(line) = output.lines().next() {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                return Ok(Some(trimmed.to_string()));
            }
        }
    }

    if let Ok(output) = run_git(root, ["rev-parse", "HEAD^"]) {
        if let Some(line) = output.lines().next() {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                return Ok(Some(trimmed.to_string()));
            }
        }
    }

    Ok(None)
}

/// Runs `git` with the supplied arguments and returns stdout as UTF-8 text.
fn run_git<I, S>(root: &Path, args: I) -> Result<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = Command::new("git")
        .current_dir(root)
        .args(args)
        .output()
        .context("failed to invoke git")?;
    if !output.status.success() {
        bail!(
            "git command failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    String::from_utf8(output.stdout).context("git output was not valid UTF-8")
}

/// Checks whether any watched path for this binding changed.
fn binding_has_changes(binding: &Binding, changed_paths: &HashSet<String>) -> bool {
    changed_paths.iter().any(|path| {
        let path_ref = Path::new(path);
        binding
            .watch
            .iter()
            .any(|prefix| path_ref.starts_with(Path::new(prefix)))
    })
}

/// Reads the version declared in the root `Cargo.toml`.
fn read_root_crate_version(root: &Path) -> Result<Version> {
    let manifest = fs::read_to_string(root.join("Cargo.toml"))
        .context("failed to read workspace Cargo.toml")?;
    let doc = manifest
        .parse::<DocumentMut>()
        .context("failed to parse workspace Cargo.toml")?;
    let version = doc["package"]["version"]
        .as_str()
        .ok_or_else(|| anyhow!("workspace Cargo.toml missing package.version"))?;
    Version::parse(version)
        .with_context(|| format!("invalid workspace package.version '{version}'"))
}

/// Reads the authoritative version for a binding (Cargo manifest or C# project).
fn read_binding_version(root: &Path, binding: &Binding) -> Result<Version> {
    if let Some(manifest) = binding.manifest {
        return read_manifest_version(&root.join(manifest));
    }
    if let Some(project) = binding.csharp_project {
        return read_csharp_version(root.join(project));
    }
    bail!("binding '{}' missing version source", binding.name)
}

fn read_manifest_version(path: &Path) -> Result<Version> {
    let contents =
        fs::read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;
    let doc = contents
        .parse::<DocumentMut>()
        .with_context(|| format!("failed to parse {}", path.display()))?;
    let version = doc["package"]["version"]
        .as_str()
        .ok_or_else(|| anyhow!("{} missing package.version", path.display()))?;
    Version::parse(version)
        .with_context(|| format!("invalid version '{}' in {}", version, path.display()))
}

fn read_csharp_version(path: PathBuf) -> Result<Version> {
    let contents =
        fs::read_to_string(&path).with_context(|| format!("failed to read {}", path.display()))?;
    let re = Regex::new(r#"(?s)<VersionPrefix>(?P<value>[^<]+)</VersionPrefix>"#)?;
    let caps = re
        .captures(&contents)
        .ok_or_else(|| anyhow!("{} missing <VersionPrefix> entry", path.display()))?;
    let version = caps.name("value").unwrap().as_str();
    Version::parse(version)
        .with_context(|| format!("invalid VersionPrefix '{}' in {}", version, path.display()))
}

/// Calculates the version to write, bumping the minor release when the binding
/// changed while never regressing below the current version.
fn desired_version(current: &Version, target: &Version, binding_changed: bool) -> Version {
    let mut candidate = target.clone();

    if binding_changed {
        candidate.minor += 1;
        candidate.patch = 0;
        candidate.pre = Prerelease::EMPTY;
        candidate.build = BuildMetadata::EMPTY;
    }

    if candidate < *current {
        candidate = current.clone();
    }

    candidate
}

/// Applies the chosen version across every artefact owned by the binding.
fn apply_binding_version(
    root: &Path,
    binding: &Binding,
    version: &Version,
    check: bool,
) -> Result<Vec<String>> {
    let mut touched = Vec::new();
    let version_str = version.to_string();

    if let Some(manifest) = binding.manifest {
        if update_manifest_version(root, manifest, &version_str, check)? {
            touched.push(manifest.to_string());
            // Update Cargo.lock if it exists in the same directory
            if let Some(parent) = root.join(manifest).parent() {
                let lock_path = parent.join("Cargo.lock");
                if lock_path.exists() && !check {
                    update_cargo_lock(root, manifest)?;
                }
            }
        }
    }

    if let Some(version_file) = binding.ruby_version {
        if update_ruby_version(root, version_file, &version_str, check)? {
            touched.push(version_file.to_string());
        }
    }

    if let Some(pom_path) = binding.pom_xml {
        if update_java_pom(root, pom_path, &version_str, check)? {
            touched.push(pom_path.to_string());
        }
    }

    if let Some(project) = binding.csharp_project {
        touched.extend(update_csharp_projects(
            root,
            project,
            binding.csharp_dependents,
            &version_str,
            check,
        )?);
    }

    Ok(touched)
}

/// Updates a Cargo manifest with the supplied version string.
fn update_manifest_version(
    root: &Path,
    manifest: &str,
    version: &str,
    check: bool,
) -> Result<bool> {
    let path = root.join(manifest);
    edit_file(&path, check, |contents| {
        let mut doc = contents
            .parse::<DocumentMut>()
            .with_context(|| format!("failed to parse {}", path.display()))?;
        let current = doc["package"]["version"]
            .as_str()
            .ok_or_else(|| anyhow!("{} missing package.version", path.display()))?;
        if current == version {
            return Ok(None);
        }
        doc["package"]["version"] = value(version);
        Ok(Some(doc.to_string()))
    })
}

/// Rewrites the Ruby gem version constant.
fn update_ruby_version(
    root: &Path,
    version_file: &str,
    version: &str,
    check: bool,
) -> Result<bool> {
    let path = root.join(version_file);
    edit_file(&path, check, |contents| {
        let re = Regex::new(r#"(?m)^(?P<prefix>\s*VERSION\s*=\s*")(?P<value>[^"]+)(?P<suffix>")"#)?;
        if let Some(caps) = re.captures(contents) {
            if caps.name("value").unwrap().as_str() == version {
                return Ok(None);
            }
            let updated = re.replace(contents, |caps: &regex::Captures| {
                format!("{}{}{}", &caps["prefix"], version, &caps["suffix"])
            });
            Ok(Some(updated.into_owned()))
        } else {
            bail!("{} missing VERSION constant", path.display());
        }
    })
}

/// Updates the Maven `pom.xml` entry for the Java binding.
fn update_java_pom(root: &Path, pom_path: &str, version: &str, check: bool) -> Result<bool> {
    let path = root.join(pom_path);
    edit_file(&path, check, |contents| {
        let re = Regex::new(
            r#"(?s)(<artifactId>regorus-java</artifactId>\s*<version>)(?P<value>[^<]+)(</version>)"#,
        )?;
        if let Some(caps) = re.captures(contents) {
            if caps.name("value").unwrap().as_str() == version {
                return Ok(None);
            }
            let updated = re.replace(contents, |caps: &regex::Captures| {
                format!("{}{}{}", &caps[1], version, &caps[3])
            });
            Ok(Some(updated.into_owned()))
        } else {
            bail!("{} missing regorus-java version", path.display());
        }
    })
}

/// Updates the NuGet packaging project and any sample/test consumers.
fn update_csharp_projects(
    root: &Path,
    package_project: &str,
    dependent_projects: &[&str],
    version: &str,
    check: bool,
) -> Result<Vec<String>> {
    let mut touched = Vec::new();
    let version_prefix = Regex::new(
        r#"(?s)(?P<prefix><VersionPrefix>)(?P<value>[^<]+)(?P<suffix></VersionPrefix>)"#,
    )?;
    let pkg_ref = Regex::new(
        r#"(?i)(?P<prefix><PackageReference[^>]*Include="regorus"[^>]*Version=")(?P<value>\d+\.\d+\.\d+)(?P<suffix>[^\"]*")"#,
    )?;

    let package_path = root.join(package_project);
    if edit_file(&package_path, check, |contents| {
        let mut changed = false;
        let mut new_contents = contents.to_owned();

        if version_prefix.is_match(&new_contents) {
            new_contents = version_prefix
                .replace(&new_contents, |caps: &regex::Captures| {
                    let current = caps.name("value").unwrap().as_str();
                    if current == version {
                        caps[0].to_string()
                    } else {
                        changed = true;
                        format!("{}{}{}", &caps["prefix"], version, &caps["suffix"])
                    }
                })
                .into_owned();
        }

        let replaced = pkg_ref.replace_all(&new_contents, |caps: &regex::Captures| {
            let current = caps.name("value").unwrap().as_str();
            if current == version {
                caps[0].to_string()
            } else {
                changed = true;
                format!("{}{}{}", &caps["prefix"], version, &caps["suffix"])
            }
        });
        let final_contents = replaced.into_owned();

        if changed && final_contents != *contents {
            Ok(Some(final_contents))
        } else {
            Ok(None)
        }
    })? {
        touched.push(package_project.to_string());
    }

    for rel_path in dependent_projects {
        let path = root.join(rel_path);
        if edit_file(&path, check, |contents| {
            let mut changed = false;
            let replaced = pkg_ref.replace_all(contents, |caps: &regex::Captures| {
                let current = caps.name("value").unwrap().as_str();
                if current == version {
                    caps[0].to_string()
                } else {
                    changed = true;
                    format!("{}{}{}", &caps["prefix"], version, &caps["suffix"])
                }
            });
            let new_contents = replaced.into_owned();
            if changed && new_contents != *contents {
                Ok(Some(new_contents))
            } else {
                Ok(None)
            }
        })? {
            touched.push((*rel_path).to_string());
        }
    }

    touched.sort();
    touched.dedup();
    Ok(touched)
}

/// Reads a file, applies a transformation, and writes it back unless `--check`
/// is set.
fn edit_file<F>(path: &Path, check: bool, apply: F) -> Result<bool>
where
    F: FnOnce(&str) -> Result<Option<String>>,
{
    let original =
        fs::read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;

    if let Some(updated) = apply(&original)? {
        if check {
            bail!("{} requires updates", path.display());
        }
        fs::write(path, updated).with_context(|| format!("failed to write {}", path.display()))?;
        return Ok(true);
    }

    Ok(false)
}

/// Updates Cargo.lock after a manifest version change by running cargo update.
/// Uses --precise to only update the version entry without touching dependencies.
fn update_cargo_lock(root: &Path, manifest: &str) -> Result<()> {
    let manifest_path = root.join(manifest);

    // Read the package name and version from the manifest
    let contents = fs::read_to_string(&manifest_path)
        .with_context(|| format!("failed to read {}", manifest_path.display()))?;
    let doc = contents
        .parse::<DocumentMut>()
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;

    let package_name = doc["package"]["name"]
        .as_str()
        .ok_or_else(|| anyhow!("{} missing package.name", manifest_path.display()))?;
    let version = doc["package"]["version"]
        .as_str()
        .ok_or_else(|| anyhow!("{} missing package.version", manifest_path.display()))?;

    let output = Command::new("cargo")
        .arg("update")
        .arg("--package")
        .arg(package_name)
        .arg("--precise")
        .arg(version)
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

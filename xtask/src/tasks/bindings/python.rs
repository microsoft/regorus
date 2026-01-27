// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context, Result};
use clap::Args;

use crate::tasks::util::{path_separator, run_cargo_step, run_command, workspace_root};

const MIN_PYTHON_VERSION: (u32, u32) = (3, 10);

#[derive(Args, Default)]
pub struct BuildPythonCommand {
    /// Optimise the wheel artefacts (defaults to debug builds).
    #[arg(long)]
    pub release: bool,

    /// Cross-compile for the provided Rust target triple.
    #[arg(long, value_name = "TRIPLE")]
    pub target: Option<String>,

    /// Override the directory that receives built wheel files.
    #[arg(long, value_name = "PATH")]
    pub target_dir: Option<PathBuf>,

    /// Propagate --frozen to cargo invocations prior to packaging.
    #[arg(long)]
    pub frozen: bool,
}

impl BuildPythonCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let python_dir = workspace.join("bindings/python");

        build_python_crate(
            &python_dir,
            self.release,
            self.target.as_deref(),
            self.frozen,
        )?;

        let wheel_dir = self
            .target_dir
            .clone()
            .unwrap_or_else(|| python_dir.join("wheels"));
        fs::create_dir_all(&wheel_dir).with_context(|| {
            format!(
                "failed to create Python wheel directory at {}",
                wheel_dir.display()
            )
        })?;

        let mut maturin = Command::new("maturin");
        maturin.current_dir(&python_dir);
        maturin.arg("build");
        if self.release {
            maturin.arg("--release");
        }
        if let Some(target) = &self.target {
            maturin.arg("--target");
            maturin.arg(target);
        }
        maturin.arg("--target-dir");
        maturin.arg(&wheel_dir);
        run_command(maturin, "maturin build (bindings/python)")
    }
}

#[derive(Args, Default)]
pub struct TestPythonCommand {
    /// Optimise the extension module used for testing (defaults to debug builds).
    #[arg(long)]
    pub release: bool,

    /// Cross-compile for the provided Rust target triple.
    #[arg(long, value_name = "TRIPLE")]
    pub target: Option<String>,

    /// Python interpreter used to run the sample and tests.
    #[arg(long, value_name = "EXE", default_value = "python3")]
    pub python: String,
}

impl TestPythonCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let python_dir = workspace.join("bindings/python");

        let (venv_python, venv_dir) = ensure_virtual_env(&python_dir, &self.python)?;

        install_testing_dependencies(&venv_python)?;

        install_local_package(&python_dir, self.release, self.target.as_deref(), &venv_dir)?;

        let mut sample = Command::new(&venv_python);
        sample.current_dir(&python_dir);
        sample.arg("test.py");
        let sample_label = format!("{} test.py (bindings/python)", venv_python.display());
        run_command(sample, &sample_label)?;

        let mut pytest = Command::new(&venv_python);
        pytest.current_dir(&python_dir);
        pytest.arg("-m");
        pytest.arg("pytest");
        pytest.arg("test_extensions.py");
        let pytest_label = format!(
            "{} -m pytest test_extensions.py (bindings/python)",
            venv_python.display()
        );
        run_command(pytest, &pytest_label)
    }
}

fn install_testing_dependencies(venv_python: &Path) -> Result<()> {
    let mut install = Command::new(venv_python);
    install.arg("-m");
    install.arg("pip");
    install.arg("install");
    install.arg("pytest");
    let label = format!(
        "{} -m pip install pytest (bindings/python)",
        venv_python.display()
    );
    run_command(install, &label)
}

fn install_local_package(
    python_dir: &Path,
    release: bool,
    target: Option<&str>,
    venv_dir: &Path,
) -> Result<()> {
    let mut maturin = Command::new("maturin");
    maturin.current_dir(python_dir);
    maturin.arg("develop");
    if release {
        maturin.arg("--release");
    }
    if let Some(target) = target {
        maturin.arg("--target");
        maturin.arg(target);
    }
    maturin.env("VIRTUAL_ENV", venv_dir);
    let bin_dir = venv_bin_dir(venv_dir);
    let mut path_value = bin_dir.clone().into_os_string();
    if let Some(existing) = std::env::var_os("PATH") {
        if !existing.is_empty() {
            path_value.push(path_separator());
            path_value.push(existing);
        }
    }
    maturin.env("PATH", path_value);
    run_command(maturin, "maturin develop (bindings/python)")
}

fn build_python_crate(
    python_dir: &Path,
    release: bool,
    target: Option<&str>,
    frozen: bool,
) -> Result<()> {
    let mut args = Vec::new();
    args.push(OsString::from("build"));
    if release {
        args.push(OsString::from("--release"));
    }
    if let Some(target) = target {
        args.push(OsString::from("--target"));
        args.push(OsString::from(target));
    }
    if frozen {
        args.push(OsString::from("--frozen"));
    }
    args.push(OsString::from("--locked"));
    run_cargo_step(python_dir, "cargo build (bindings/python)", args)
}

fn ensure_virtual_env(python_dir: &Path, python: &str) -> Result<(PathBuf, PathBuf)> {
    ensure_python_version(std::ffi::OsStr::new(python), python)?;

    let venv_dir = python_dir.join(".venv");
    if venv_dir.exists() {
        let existing_python = venv_bin_dir(&venv_dir).join(venv_python_name());
        if existing_python.exists()
            && ensure_python_version(
                existing_python.as_os_str(),
                &existing_python.display().to_string(),
            )
            .is_ok()
        {
            return Ok((existing_python, venv_dir));
        }

        fs::remove_dir_all(&venv_dir).with_context(|| {
            format!(
                "failed to remove incompatible virtual environment at {}",
                venv_dir.display()
            )
        })?;
    }

    let mut create = Command::new(python);
    create.current_dir(python_dir);
    create.arg("-m");
    create.arg("venv");
    create.arg(".venv");
    let label = format!("{} -m venv .venv (bindings/python)", python);
    run_command(create, &label)?;

    let python_path = venv_bin_dir(&venv_dir).join(venv_python_name());
    ensure_python_version(python_path.as_os_str(), &python_path.display().to_string())?;

    Ok((python_path, venv_dir))
}

fn venv_bin_dir(venv_dir: &Path) -> PathBuf {
    if cfg!(windows) {
        venv_dir.join("Scripts")
    } else {
        venv_dir.join("bin")
    }
}

fn venv_python_name() -> &'static str {
    if cfg!(windows) {
        "python.exe"
    } else {
        "python"
    }
}

fn ensure_python_version(executable: &std::ffi::OsStr, label: &str) -> Result<()> {
    let (major, minor) = query_python_version(executable, label)?;
    if (major, minor) < MIN_PYTHON_VERSION {
        bail!(
            "Python interpreter {} reports version {}.{}; the bindings require Python >= {}.{}. Use --python to provide a compatible interpreter.",
            label,
            major,
            minor,
            MIN_PYTHON_VERSION.0,
            MIN_PYTHON_VERSION.1
        );
    }
    Ok(())
}

fn query_python_version(executable: &std::ffi::OsStr, label: &str) -> Result<(u32, u32)> {
    let output = Command::new(executable)
        .arg("-c")
        .arg("import sys; print(f'{sys.version_info[0]}.{sys.version_info[1]}')")
        .output()
        .with_context(|| format!("failed to query Python version from {}", label))?;

    if !output.status.success() {
        bail!(
            "{} -c 'import sys; ...' exited with status {}",
            label,
            output.status
        );
    }

    let stdout = String::from_utf8(output.stdout)
        .with_context(|| format!("failed to decode Python version output from {}", label))?;
    let trimmed = stdout.trim();
    let mut parts = trimmed.split('.');
    let major = parts
        .next()
        .ok_or_else(|| anyhow!("missing major version in '{}'", trimmed))?
        .parse::<u32>()
        .with_context(|| format!("failed to parse major version from '{}'", trimmed))?;
    let minor = parts
        .next()
        .ok_or_else(|| anyhow!("missing minor version in '{}'", trimmed))?
        .parse::<u32>()
        .with_context(|| format!("failed to parse minor version from '{}'", trimmed))?;

    Ok((major, minor))
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use clap::Args;

use super::c::{TestCCommand, TestCNoStdCommand};
use super::cpp::TestCppCommand;
use super::csharp::{build_nuget_package, BuildNugetConfig, TestCsharpCommand};
use super::ffi;
use super::java::{BuildJavaCommand, TestJavaCommand};
use super::python::{BuildPythonCommand, TestPythonCommand};
use super::wasm::{BuildWasmCommand, TestWasmCommand};
use crate::tasks::util::workspace_root;

/// Builds every published binding with opinionated defaults.
#[derive(Args, Default)]
pub struct BuildAllBindingsCommand {
    /// Optimise artefacts where supported (defaults to debug builds).
    #[arg(long)]
    pub release: bool,
}

impl BuildAllBindingsCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();
        let release = self.release;

        let targets = ffi::resolve_targets(Vec::new())?;
        ffi::build_targets(&workspace, &targets, release)?;

        let ffi_dir = workspace.join("bindings/ffi/target");
        let nuget_result = build_nuget_package(&BuildNugetConfig {
            targets: Vec::new(),
            release,
            clean: false,
            artifacts_dir: Some(ffi_dir.clone()),
            enforce_artifacts: false,
            repository_commit: None,
            include_symbols: false,
        })?;

        if nuget_result.packages.is_empty() {
            println!("NuGet packaging completed but no archives were produced.");
        } else {
            for package in &nuget_result.packages {
                println!("NuGet package ready at {}", package.display());
            }
        }

        BuildJavaCommand { skip_tests: true }.run()?;
        BuildPythonCommand {
            release,
            target: None,
            target_dir: None,
            frozen: false,
        }
        .run()?;
        BuildWasmCommand {
            release,
            target: "nodejs".to_string(),
            out_dir: None,
        }
        .run()?;

        println!("Completed building all bindings.");
        Ok(())
    }
}

/// Executes the smoke tests for all bindings in sequence.
#[derive(Args, Default)]
pub struct TestAllBindingsCommand {
    /// Optimise artefacts where supported (defaults to debug builds).
    #[arg(long)]
    pub release: bool,

    /// Python executable leveraged by the binding tests.
    #[arg(long, value_name = "EXE", default_value = "python3")]
    pub python: String,

    /// Node.js executable leveraged by the WASM test.
    #[arg(long, value_name = "EXE", default_value = "node")]
    pub node: String,
}

impl TestAllBindingsCommand {
    pub fn run(&self) -> Result<()> {
        TestCCommand {
            release: self.release,
            frozen: false,
            skip_ffi: false,
        }
        .run()?;
        TestCppCommand {
            release: self.release,
            frozen: false,
            skip_ffi: true,
        }
        .run()?;
        TestCNoStdCommand {
            release: self.release,
            frozen: false,
            skip_ffi: true,
        }
        .run()?;
        TestJavaCommand {
            release: self.release,
            frozen: false,
        }
        .run()?;

        TestPythonCommand {
            release: self.release,
            target: None,
            python: self.python.clone(),
        }
        .run()?;

        TestWasmCommand {
            release: self.release,
            target: "nodejs".to_string(),
            out_dir: None,
            node: self.node.clone(),
            frozen: false,
            skip_build: false,
        }
        .run()?;

        TestCsharpCommand {
            targets: Vec::new(),
            release: self.release,
            clean: false,
            artifacts_dir: None,
            enforce_artifacts: false,
            force_nuget: false,
            nuget_dir: None,
        }
        .run()?;

        println!("Completed testing all bindings.");
        Ok(())
    }
}

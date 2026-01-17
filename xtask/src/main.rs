// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod tasks;

use anyhow::Result;
use clap::{Parser, Subcommand};

use tasks::{
    BindingsCommand, BuildAllBindingsCommand, BuildFfiCommand, BuildJavaCommand, BuildNugetCommand,
    BuildPythonCommand, BuildWasmCommand, CiDebugCommand, CiReleaseCommand, ClippyCommand,
    FmtCommand, PrecommitCommand, PrepushCommand, TestAllBindingsCommand, TestCCommand,
    TestCNoStdCommand, TestCppCommand, TestCsharpCommand, TestFfiCommand, TestGoCommand,
    TestJavaCommand, TestMuslCommand, TestNoStdCommand, TestPythonCommand, TestRubyCommand,
    TestWasmCommand, UpdateDepsCommand,
};

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
    /// Build the regorus FFI crate for selected targets
    #[command(name = "build-ffi", alias = "ffi")]
    Ffi(BuildFfiCommand),
    /// Run the release-focused CI workflow locally
    CiRelease(CiReleaseCommand),
    /// Run the debug-focused CI workflow locally
    CiDebug(CiDebugCommand),
    /// Format the workspace and all binding crates
    Fmt(FmtCommand),
    /// Run clippy across the workspace and all binding crates
    Clippy(ClippyCommand),
    /// Run the repository pre-commit validation sequence
    PreCommit(PrecommitCommand),
    /// Run the repository pre-push validation sequence
    PrePush(PrepushCommand),
    /// Build every binding artefact with opinionated defaults
    BuildAllBindings(BuildAllBindingsCommand),
    /// Build the Java bindings via Maven
    BuildJava(BuildJavaCommand),
    /// Execute the Java binding test suite
    TestJava(TestJavaCommand),
    /// Build the Python wheels via maturin
    BuildPython(BuildPythonCommand),
    /// Execute the Python binding tests
    TestPython(TestPythonCommand),
    /// Build the WASM bindings via wasm-pack
    BuildWasm(BuildWasmCommand),
    /// Execute the WASM binding smoke tests
    TestWasm(TestWasmCommand),
    /// Execute the FFI binding test suite
    TestFfi(TestFfiCommand),
    /// Execute the Go binding smoke tests
    TestGo(TestGoCommand),
    /// Execute all binding smoke tests
    TestAllBindings(TestAllBindingsCommand),
    /// Execute the MUSL cross-compilation test matrix
    TestMusl(TestMuslCommand),
    /// Build the ensure_no_std harness for the embedded target
    TestNoStd(TestNoStdCommand),
    /// Configure, build, and run the C binding sample
    TestC(TestCCommand),
    /// Configure, build, and run the C++ binding sample
    TestCpp(TestCppCommand),
    /// Configure, build, and run the no_std C binding sample
    #[command(name = "test-c-no-std", alias = "test-c-nostd")]
    TestCNoStd(TestCNoStdCommand),
    /// Execute the Ruby binding smoke tests
    TestRuby(TestRubyCommand),
    /// Build and validate the C# binding via its NuGet package
    TestCsharp(TestCsharpCommand),
    /// Build the Regorus C# NuGet package from local artefacts
    #[command(name = "build-csharp", alias = "build-nuget", alias = "nuget")]
    BuildCsharp(BuildNugetCommand),
    /// Update dependencies across all workspace Cargo.lock files
    UpdateDeps(UpdateDepsCommand),
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Bindings(cmd) => cmd.run()?,
        Commands::Ffi(cmd) => cmd.run()?,
        Commands::CiRelease(cmd) => cmd.run()?,
        Commands::CiDebug(cmd) => cmd.run()?,
        Commands::Fmt(cmd) => cmd.run()?,
        Commands::Clippy(cmd) => cmd.run()?,
        Commands::PreCommit(cmd) => cmd.run()?,
        Commands::PrePush(cmd) => cmd.run()?,
        Commands::BuildAllBindings(cmd) => cmd.run()?,
        Commands::BuildJava(cmd) => cmd.run()?,
        Commands::TestJava(cmd) => cmd.run()?,
        Commands::BuildPython(cmd) => cmd.run()?,
        Commands::TestPython(cmd) => cmd.run()?,
        Commands::BuildWasm(cmd) => cmd.run()?,
        Commands::TestWasm(cmd) => cmd.run()?,
        Commands::TestFfi(cmd) => cmd.run()?,
        Commands::TestGo(cmd) => cmd.run()?,
        Commands::TestAllBindings(cmd) => cmd.run()?,
        Commands::TestMusl(cmd) => cmd.run()?,
        Commands::TestNoStd(cmd) => cmd.run()?,
        Commands::TestC(cmd) => cmd.run()?,
        Commands::TestCpp(cmd) => cmd.run()?,
        Commands::TestCNoStd(cmd) => cmd.run()?,
        Commands::TestRuby(cmd) => cmd.run()?,
        Commands::TestCsharp(cmd) => cmd.run()?,
        Commands::BuildCsharp(cmd) => cmd.run()?,
        Commands::UpdateDeps(cmd) => cmd.run()?,
    }

    Ok(())
}

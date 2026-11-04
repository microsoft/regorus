// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Shared corpus of policies and inputs for explanation (causality) and
//! partial-evaluation tests. See `README.md` in this directory for the format.
//!
//! Every example's value is checked on the interpreter and on the RVM in both
//! execution modes. `corpus_matches_opa` additionally checks the expected
//! values against an OPA binary when `REGORUS_OPA` points to one.

#![cfg(feature = "rvm")]

use anyhow::{anyhow, bail, Context, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
use regorus::test_utils::process_value;
use regorus::{Engine, Rc, Value};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use test_generator::test_resources;

const CASES_DIR: &str = "tests/explanation_corpus/cases";

/// Language constructs a case exercises. Every variant must be covered by at
/// least one case (`corpus_is_well_formed`).
#[derive(Deserialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
enum Construct {
    CompleteRule,
    PartialSet,
    PartialObject,
    Function,
    Else,
    Default,
    MultipleBodies,
    Negation,
    SomeIn,
    Every,
    Membership,
    Comprehension,
    HelperRule,
    With,
    Builtin,
    UndefinedVsFalse,
    Conflict,
    RuntimeError,
    Secret,
    UnknownInput,
}

const ALL_CONSTRUCTS: &[Construct] = &[
    Construct::CompleteRule,
    Construct::PartialSet,
    Construct::PartialObject,
    Construct::Function,
    Construct::Else,
    Construct::Default,
    Construct::MultipleBodies,
    Construct::Negation,
    Construct::SomeIn,
    Construct::Every,
    Construct::Membership,
    Construct::Comprehension,
    Construct::HelperRule,
    Construct::With,
    Construct::Builtin,
    Construct::UndefinedVsFalse,
    Construct::Conflict,
    Construct::RuntimeError,
    Construct::Secret,
    Construct::UnknownInput,
];

/// Keeps an explicit YAML `null` as `Some(Value::Null)`; only an absent
/// field is `None`.
fn present<'de, D: serde::Deserializer<'de>>(d: D) -> Result<Option<Value>, D::Error> {
    Value::deserialize(d).map(Some)
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct CorpusFile {
    cases: Vec<Case>,
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Case {
    note: String,
    description: String,
    constructs: Vec<Construct>,
    modules: Vec<String>,
    query: String,
    #[serde(default, deserialize_with = "present")]
    data: Option<Value>,
    #[serde(default)]
    rego_v0: bool,
    /// Input paths that partial evaluation treats as unknown. Each example's
    /// input supplies one concrete assignment of them.
    #[serde(default)]
    unknowns: Vec<String>,
    /// Values in `input` or `data` that are sensitive.
    #[serde(default)]
    secrets: Vec<Value>,
    /// Set when OPA can't evaluate this case; the reason is required.
    opa_skip: Option<String>,
    /// Whether builtin errors are errors (true) or make the expression
    /// Undefined (false, OPA's default). Applied to every evaluator and OPA.
    #[serde(default)]
    strict_builtin_errors: bool,
    /// Reserved for the expected partial-evaluation result.
    #[serde(default, deserialize_with = "present")]
    partial_eval: Option<Value>,
    examples: Vec<Example>,
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Example {
    note: String,
    /// Absent means no input document, so `input` is Undefined.
    #[serde(default, deserialize_with = "present")]
    input: Option<Value>,
    #[serde(default, deserialize_with = "present")]
    want_result: Option<Value>,
    want_error: Option<String>,
    divergence: Option<Divergence>,
    /// Reserved for the expected explanation report.
    #[serde(default, deserialize_with = "present")]
    explanation: Option<Value>,
}

/// A known case where regorus differs from the expected (OPA) behavior.
/// `want_*` stays the correct outcome; this records what regorus does today.
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Divergence {
    reason: String,
    engines: Vec<EngineKind>,
    #[serde(default, deserialize_with = "present")]
    actual_result: Option<Value>,
    actual_error: Option<String>,
}

#[derive(Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum EngineKind {
    Interpreter,
    Rvm,
}

#[derive(Debug, Clone, PartialEq)]
enum Outcome {
    Value(Value),
    Error(String),
}

impl Outcome {
    fn from_want(result: &Option<Value>, error: &Option<String>) -> Result<Self> {
        match (result, error) {
            (Some(v), None) => Ok(Outcome::Value(process_value(v)?)),
            (None, Some(e)) if !e.trim().is_empty() => Ok(Outcome::Error(e.clone())),
            _ => bail!("set exactly one of a result or a non-empty error"),
        }
    }

    fn matches(&self, actual: &Result<Value>) -> bool {
        match (self, actual) {
            (Outcome::Value(want), Ok(got)) => want == got,
            (Outcome::Error(want), Err(e)) => format!("{e:#}").contains(want.as_str()),
            _ => false,
        }
    }
}

fn describe(actual: &Result<Value>) -> String {
    match actual {
        Ok(Value::Undefined) => "undefined".to_string(),
        Ok(v) => v.to_json_str().unwrap_or_else(|_| format!("{v:?}")),
        Err(e) => format!("error: {e:#}"),
    }
}

fn load(path: &Path) -> Result<CorpusFile> {
    let text = fs::read_to_string(path)?;
    yaml_serde::from_str(&text).with_context(|| format!("parsing {}", path.display()))
}

fn corpus_files() -> Result<Vec<PathBuf>> {
    let mut files: Vec<PathBuf> = fs::read_dir(CASES_DIR)?
        .map(|e| e.map(|e| e.path()))
        .collect::<std::io::Result<_>>()?;
    files.retain(|p| p.extension().and_then(|e| e.to_str()) == Some("yaml"));
    files.sort();
    Ok(files)
}

fn new_engine(case: &Case, example: &Example) -> Result<Engine> {
    let mut engine = Engine::new();
    engine.set_rego_v0(case.rego_v0);
    engine.set_strict_builtin_errors(case.strict_builtin_errors);
    for (idx, module) in case.modules.iter().enumerate() {
        engine.add_policy(format!("corpus_{idx}.rego"), module.clone())?;
    }
    if let Some(data) = &case.data {
        engine.add_data(data.clone())?;
    }
    if let Some(input) = &example.input {
        engine.set_input(input.clone());
    }
    Ok(engine)
}

fn run_interpreter(case: &Case, example: &Example) -> Result<Value> {
    new_engine(case, example)?.eval_rule(case.query.clone())
}

fn run_rvm(case: &Case, example: &Example, mode: ExecutionMode) -> Result<Value> {
    let mut engine = new_engine(case, example)?;
    let entrypoint: Rc<str> = case.query.as_str().into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let program = Compiler::compile_from_policy(&compiled, &[case.query.as_str()])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_strict_builtin_errors(case.strict_builtin_errors);
    vm.set_data(engine.get_data())?;
    // The VM's default input is null; an absent input must be Undefined.
    vm.set_input(example.input.clone().unwrap_or(Value::Undefined));
    vm.set_execution_mode(mode);
    let result = vm.execute()?;
    if mode == ExecutionMode::RunToCompletion {
        return Ok(result);
    }
    match vm.execution_state() {
        ExecutionState::Completed { result } => Ok(result.clone()),
        ExecutionState::Error { error } => Err(anyhow!("{error}")),
        other => bail!("suspendable execution did not complete: {other:?}"),
    }
}

fn expected_for(example: &Example, engine: EngineKind) -> Result<Outcome> {
    match &example.divergence {
        Some(d) if d.engines.contains(&engine) => {
            Outcome::from_want(&d.actual_result, &d.actual_error)
        }
        _ => Outcome::from_want(&example.want_result, &example.want_error),
    }
}

fn run_file(path: &Path) -> Result<()> {
    let corpus = load(path)?;
    let mut failures = Vec::new();
    for case in &corpus.cases {
        for example in &case.examples {
            let runs = [
                (
                    "interpreter",
                    EngineKind::Interpreter,
                    run_interpreter(case, example),
                ),
                (
                    "rvm run-to-completion",
                    EngineKind::Rvm,
                    run_rvm(case, example, ExecutionMode::RunToCompletion),
                ),
                (
                    "rvm suspendable",
                    EngineKind::Rvm,
                    run_rvm(case, example, ExecutionMode::Suspendable),
                ),
            ];
            for (label, kind, actual) in runs {
                let expected = expected_for(example, kind)?;
                if !expected.matches(&actual) {
                    failures.push(format!(
                        "{}/{} [{label}]: expected {expected:?}, got {}",
                        case.note,
                        example.note,
                        describe(&actual)
                    ));
                }
            }
        }
    }
    if !failures.is_empty() {
        bail!("{} mismatches:\n{}", failures.len(), failures.join("\n"));
    }
    Ok(())
}

#[test_resources("tests/explanation_corpus/cases/*.yaml")]
fn corpus_values(file: &str) {
    run_file(Path::new(file)).unwrap();
}

fn contains_value(haystack: &Value, needle: &Value) -> bool {
    if haystack == needle {
        return true;
    }
    match haystack {
        Value::Array(items) => items.iter().any(|v| contains_value(v, needle)),
        Value::Set(items) => items.iter().any(|v| contains_value(v, needle)),
        Value::Object(fields) => fields
            .iter()
            .any(|(k, v)| contains_value(k, needle) || contains_value(v, needle)),
        _ => false,
    }
}

/// Error messages quote the failing source line, so an expected error text
/// that also occurs in the policy could match the wrong error.
fn check_error_text(case: &Case, outcome: &Outcome) -> Result<()> {
    if let Outcome::Error(text) = outcome {
        if case.modules.iter().any(|m| m.contains(text.as_str())) {
            bail!("error text {text:?} also occurs in the policy source");
        }
    }
    Ok(())
}

fn check_case_shape(case: &Case) -> Result<()> {
    if case.note.trim().is_empty() || case.query.trim().is_empty() {
        bail!("empty note or query");
    }
    if case.modules.is_empty() || case.modules.iter().any(|m| m.trim().is_empty()) {
        bail!("no modules, or an empty module");
    }
    if case.constructs.is_empty() {
        bail!("no constructs listed");
    }
    if case.description.trim().is_empty() {
        bail!("empty description");
    }
    if case.partial_eval.is_some() {
        bail!("partial_eval is reserved until partial evaluation can check it");
    }
    if matches!(&case.opa_skip, Some(reason) if reason.trim().is_empty()) {
        bail!("opa_skip needs a reason");
    }
    if case.constructs.contains(&Construct::UnknownInput) == case.unknowns.is_empty() {
        bail!("`unknowns` must be set exactly when constructs include unknown_input");
    }
    for unknown in &case.unknowns {
        if unknown != "input" && !unknown.starts_with("input.") {
            bail!("unknown path {unknown} is not under input");
        }
    }
    if case.constructs.contains(&Construct::Secret) == case.secrets.is_empty() {
        bail!("`secrets` must be set exactly when constructs include secret");
    }
    for secret in &case.secrets {
        let found = case.examples.iter().any(|e| {
            e.input.as_ref().is_some_and(|i| contains_value(i, secret))
                || case
                    .data
                    .as_ref()
                    .is_some_and(|d| contains_value(d, secret))
        });
        if !found {
            bail!("secret {secret} does not appear in any input or data");
        }
    }

    let mut wants = Vec::new();
    let mut example_notes = BTreeSet::new();
    for example in &case.examples {
        if example.note.trim().is_empty() {
            bail!("empty example note");
        }
        if !example_notes.insert(example.note.as_str()) {
            bail!("duplicate example note {}", example.note);
        }
        if example.explanation.is_some() {
            bail!(
                "{}: explanation is reserved until reports can be checked",
                example.note
            );
        }
        let want = Outcome::from_want(&example.want_result, &example.want_error)
            .with_context(|| format!("{}: want", example.note))?;
        check_error_text(case, &want).with_context(|| format!("{}: want", example.note))?;
        if let Some(d) = &example.divergence {
            if d.reason.trim().is_empty() || d.engines.is_empty() {
                bail!("{}: divergence needs a reason and engines", example.note);
            }
            let actual = Outcome::from_want(&d.actual_result, &d.actual_error)
                .with_context(|| format!("{}: divergence", example.note))?;
            check_error_text(case, &actual)
                .with_context(|| format!("{}: divergence", example.note))?;
            if actual == want {
                bail!("{}: divergence actual equals want", example.note);
            }
        }
        if !wants.contains(&want) {
            wants.push(want);
        }
    }
    // Each matching example needs a nonmatching twin in the same case.
    if wants.len() < 2 {
        bail!("needs at least two examples with different expected outcomes");
    }
    Ok(())
}

#[test]
fn corpus_is_well_formed() -> Result<()> {
    let mut notes = BTreeSet::new();
    let mut examples = 0usize;
    let mut divergent = 0usize;
    let mut coverage: BTreeMap<Construct, usize> = BTreeMap::new();
    let files = corpus_files()?;
    if files.is_empty() {
        bail!("no corpus files in {CASES_DIR}");
    }
    for path in files {
        for case in load(&path)?.cases {
            if !notes.insert(case.note.clone()) {
                bail!("duplicate case note {}", case.note);
            }
            check_case_shape(&case).with_context(|| format!("case {}", case.note))?;
            examples += case.examples.len();
            divergent += case
                .examples
                .iter()
                .filter(|e| e.divergence.is_some())
                .count();
            for construct in &case.constructs {
                *coverage.entry(*construct).or_default() += 1;
            }
        }
    }
    let missing: Vec<_> = ALL_CONSTRUCTS
        .iter()
        .filter(|c| !coverage.contains_key(c))
        .collect();
    if !missing.is_empty() {
        bail!("constructs without a case: {missing:?}");
    }
    println!(
        "{} cases, {examples} examples ({divergent} with a known divergence)",
        notes.len()
    );
    for (construct, count) in &coverage {
        println!("  {construct:?}: {count} cases");
    }
    Ok(())
}

/// Sets have no JSON form; OPA prints them as sorted arrays.
fn to_opa_json(value: &Value) -> Result<Value> {
    if *value == Value::Undefined {
        return Ok(Value::Undefined);
    }
    Value::from_json_str(&value.to_json_str()?)
}

fn remove_dir(dir: &Path) -> Result<()> {
    match fs::remove_dir_all(dir) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
            Err(e).with_context(|| format!("removing {}", dir.display()))
        }
        _ => Ok(()),
    }
}

/// Runs `opa eval`. An evaluation error is `Ok(Err(..))`; anything else that
/// stops OPA from evaluating (bad flags, parse or compile errors) is `Err`.
fn run_opa(opa: &Path, dir: &Path, case: &Case, example: &Example) -> Result<Result<Value>> {
    remove_dir(dir)?;
    let policy_dir = dir.join("policy");
    fs::create_dir_all(&policy_dir)?;
    for (idx, module) in case.modules.iter().enumerate() {
        fs::write(policy_dir.join(format!("corpus_{idx}.rego")), module)?;
    }
    let mut cmd = Command::new(opa);
    cmd.args(["eval", "--format", "json", "--data"])
        .arg(&policy_dir);
    if case.rego_v0 {
        cmd.arg("--v0-compatible");
    }
    if case.strict_builtin_errors {
        cmd.arg("--strict-builtin-errors");
    }
    if let Some(data) = &case.data {
        let path = dir.join("data.json");
        fs::write(&path, data.to_json_str()?)?;
        cmd.arg("--data").arg(path);
    }
    if let Some(input) = &example.input {
        let path = dir.join("input.json");
        fs::write(&path, input.to_json_str()?)?;
        cmd.arg("--input").arg(path);
    }
    cmd.arg(&case.query);
    let output = cmd
        .output()
        .with_context(|| format!("running {}", opa.display()))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = Value::from_json_str(&stdout)
        .map_err(|_| anyhow!("unexpected OPA output:\n{stdout}\n{stderr}"))?;
    if output.status.success() {
        return Ok(Ok(parsed["result"][0]["expressions"][0]["value"].clone()));
    }
    let errors = match &parsed["errors"] {
        Value::Array(errors) if !errors.is_empty() => errors.clone(),
        _ => bail!("OPA failed without errors:\n{stdout}\n{stderr}"),
    };
    let is_eval_error =
        |e: &Value| matches!(&e["code"], Value::String(c) if c.starts_with("eval_"));
    if !errors.iter().all(is_eval_error) {
        bail!("OPA could not evaluate the policy:\n{stdout}");
    }
    Ok(Err(anyhow!("{stdout}")))
}

/// Checks every expected outcome against OPA. Set `REGORUS_OPA` to an OPA
/// binary to run it; otherwise the test does nothing.
#[test]
fn corpus_matches_opa() -> Result<()> {
    let Some(opa) = std::env::var_os("REGORUS_OPA") else {
        println!("REGORUS_OPA not set; skipping the OPA comparison");
        return Ok(());
    };
    let opa = PathBuf::from(opa);
    let work = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("explanation_corpus_opa_{}", std::process::id()));
    let mut failures = Vec::new();
    let mut checked = 0usize;
    for path in corpus_files()? {
        for case in load(&path)?.cases {
            if case.opa_skip.is_some() {
                continue;
            }
            for example in &case.examples {
                let want = Outcome::from_want(&example.want_result, &example.want_error)?;
                let actual = run_opa(&opa, &work, &case, example)
                    .with_context(|| format!("{}/{}", case.note, example.note))?;
                checked += 1;
                let agrees = match (&want, &actual) {
                    (Outcome::Value(want), Ok(got)) => &to_opa_json(want)? == got,
                    (Outcome::Error(_), Err(_)) => true,
                    _ => false,
                };
                if !agrees {
                    failures.push(format!(
                        "{}/{}: expected {want:?}, OPA gave {}",
                        case.note,
                        example.note,
                        describe(&actual)
                    ));
                }
            }
        }
    }
    remove_dir(&work)?;
    println!("checked {checked} examples against OPA");
    if !failures.is_empty() {
        bail!(
            "{} disagreements with OPA:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
    Ok(())
}

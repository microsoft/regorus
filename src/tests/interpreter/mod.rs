// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::semicolon_if_nothing_returned,
    clippy::pattern_type_mismatch,
    clippy::print_stderr
)] // test harness asserts and unwraps to validate interpreter behavior

use std::env;

use crate::test_utils::{check_output, ValueOrVec};
use crate::utils::limits::{
    acquire_limits_test_lock, fallback_execution_timer_config, ExecutionTimerConfig,
};
use crate::*;

use anyhow::{bail, Result};
use core::num::NonZeroU32;
use core::time::Duration;
use serde::{Deserialize, Serialize};
use test_generator::test_resources;
use timer_test_support::{
    apply_engine_timer, configure_time_source, reset_time_source, GlobalTimerGuard,
};

mod timer_test_support {
    use super::{ExecutionTimerTestConfig, TimeSourceTestConfig};
    #[cfg(any(test, not(feature = "std")))]
    use crate::utils::limits::set_time_source;
    use crate::utils::limits::{
        fallback_execution_timer_config, set_fallback_execution_timer_config, ExecutionTimerConfig,
        TimeSource,
    };
    use crate::Engine;
    use anyhow::{anyhow, Result};
    use core::num::NonZeroU32;
    use core::time::Duration;
    use std::collections::VecDeque;
    use std::sync::{Mutex, Once};
    use std::vec::Vec;

    pub struct GlobalTimerGuard {
        previous: Option<ExecutionTimerConfig>,
        changed: bool,
    }

    impl GlobalTimerGuard {
        pub fn apply(spec: Option<&ExecutionTimerTestConfig>) -> Result<Self> {
            let previous = fallback_execution_timer_config();
            let mut changed = false;

            if let Some(config_spec) = spec {
                if config_spec.disable.unwrap_or(false) {
                    set_fallback_execution_timer_config(None);
                    changed = true;
                } else {
                    let config = config_from_spec(config_spec)?;
                    set_fallback_execution_timer_config(config);
                    changed = true;
                }
            }

            Ok(Self { previous, changed })
        }
    }

    impl Drop for GlobalTimerGuard {
        fn drop(&mut self) {
            if self.changed {
                set_fallback_execution_timer_config(self.previous);
            }
        }
    }

    pub fn configure_time_source(spec: Option<&TimeSourceTestConfig>) {
        ensure_time_source_registered();

        let mut state = TIME_SOURCE_STATE
            .lock()
            .expect("time source mutex poisoned");

        if let Some(cfg) = spec {
            state.default_increment = cfg
                .default_increment_ms
                .map(Duration::from_millis)
                .unwrap_or(DEFAULT_INCREMENT);
            state.template_increments = cfg
                .increments_ms
                .iter()
                .copied()
                .map(Duration::from_millis)
                .collect();
        } else {
            state.default_increment = DEFAULT_INCREMENT;
            state.template_increments.clear();
        }

        state.reset_from_template();
    }

    pub fn reset_time_source() {
        let mut state = TIME_SOURCE_STATE
            .lock()
            .expect("time source mutex poisoned");
        state.reset_from_template();
    }

    pub fn apply_engine_timer(engine: &mut Engine, spec: &ExecutionTimerTestConfig) -> Result<()> {
        if spec.disable.unwrap_or(false) {
            engine.clear_execution_timer_config();
            return Ok(());
        }

        match config_from_spec(spec)? {
            Some(config) => engine.set_execution_timer_config(config),
            None => engine.clear_execution_timer_config(),
        }
        Ok(())
    }

    const DEFAULT_INCREMENT: Duration = Duration::from_millis(1);

    struct TestTimeSource;

    struct TimeSourceState {
        current: Duration,
        started: bool,
        default_increment: Duration,
        increments: VecDeque<Duration>,
        template_increments: Vec<Duration>,
    }

    impl TimeSourceState {
        const fn new() -> Self {
            Self {
                current: Duration::ZERO,
                started: false,
                default_increment: DEFAULT_INCREMENT,
                increments: VecDeque::new(),
                template_increments: Vec::new(),
            }
        }

        fn reset_from_template(&mut self) {
            self.current = Duration::ZERO;
            self.started = false;
            self.increments = VecDeque::from(self.template_increments.clone());
        }
    }

    impl TimeSource for TestTimeSource {
        fn now(&self) -> Option<Duration> {
            let mut state = TIME_SOURCE_STATE
                .lock()
                .expect("time source mutex poisoned");

            if !state.started {
                state.started = true;
                return Some(state.current);
            }

            let increment = state
                .increments
                .pop_front()
                .unwrap_or(state.default_increment);
            state.current = state.current.saturating_add(increment);
            Some(state.current)
        }
    }

    static TEST_TIME_SOURCE: TestTimeSource = TestTimeSource;
    static TIME_SOURCE_STATE: Mutex<TimeSourceState> = Mutex::new(TimeSourceState::new());
    static TIME_SOURCE_ONCE: Once = Once::new();

    fn ensure_time_source_registered() {
        #[cfg(any(test, not(feature = "std")))]
        TIME_SOURCE_ONCE.call_once(|| {
            let _ = set_time_source(&TEST_TIME_SOURCE);
        });
    }

    fn config_from_spec(spec: &ExecutionTimerTestConfig) -> Result<Option<ExecutionTimerConfig>> {
        let limit_ms = match spec.limit_ms {
            Some(value) => value,
            None => return Ok(None),
        };

        let check_interval = spec
            .check_interval
            .map(|interval| {
                NonZeroU32::new(interval)
                    .ok_or_else(|| anyhow!("execution_timer.check_interval must be non-zero"))
            })
            .transpose()? // Result<Option<NonZeroU32>>
            .unwrap_or(NonZeroU32::MIN);

        Ok(Some(ExecutionTimerConfig {
            limit: Duration::from_millis(limit_ms),
            check_interval,
        }))
    }
}

#[cfg(feature = "azure_policy")]
mod load_target_definitions {
    use super::*;
    use std::{eprintln, sync::Once};
    static INIT: Once = Once::new();

    /// Load and register all target definitions from tests/interpreter/target/definitions
    /// This function is called once and loads all JSON target definition files.
    pub fn load() -> Result<()> {
        INIT.call_once(|| {
            if let Err(e) = load_target_definitions_impl() {
                eprintln!("Failed to load target definitions: {}", e);
            }
        });
        Ok(())
    }

    fn load_target_definitions_impl() -> Result<()> {
        use crate::registry::targets;
        use crate::target::Target;
        use std::fs;
        use std::path::Path;

        let definitions_path = Path::new("tests/interpreter/cases/target/definitions");

        if !definitions_path.exists() {
            eprintln!("Target definitions directory does not exist");
            return Ok(());
        }

        let entries = fs::read_dir(definitions_path)?;
        let mut found = false;

        for entry in entries {
            let entry = entry?;
            let path = entry.path();

            // Only process JSON files
            if path.extension().and_then(|s| s.to_str()) == Some("json") {
                let contents = fs::read_to_string(&path)?;

                match Target::from_json_str(&contents) {
                    Ok(target) => {
                        let target_name = target.name.clone();
                        let target_rc = Rc::new(target);
                        found = true;
                        if let Err(e) = targets::register(target_rc.clone()) {
                            eprintln!("Failed to register target '{}': {}", target_name, e);
                        }
                    }
                    Err(e) => {
                        eprintln!(
                            "Failed to parse target definition from {}: {}",
                            path.display(),
                            e
                        );
                    }
                }
            }
        }

        if !found {
            eprintln!("No target definitions were found");
        }

        Ok(())
    }

    #[test]
    fn test_load_target_definitions() -> Result<()> {
        use crate::registry::targets;

        // Load target definitions
        load()?;

        // Check that the sample targets were loaded
        assert!(
            targets::contains("target.tests.sample_test_target"),
            "Sample target should be loaded"
        );
        assert!(
            targets::contains("target.tests.azure_compute"),
            "Azure compute target should be loaded"
        );

        // Verify we can retrieve the targets
        let sample_target = targets::get("target.tests.sample_test_target");
        assert!(
            sample_target.is_some(),
            "Should be able to retrieve sample target"
        );

        let azure_target = targets::get("target.tests.azure_compute");
        assert!(
            azure_target.is_some(),
            "Should be able to retrieve azure target"
        );

        // Verify target properties
        if let Some(target) = sample_target {
            assert_eq!(target.name.as_ref(), "target.tests.sample_test_target");
            assert_eq!(target.version.as_ref(), "1.0.0");
        }

        if let Some(target) = azure_target {
            assert_eq!(target.name.as_ref(), "target.tests.azure_compute");
            assert_eq!(target.version.as_ref(), "1.0.0");
        }

        Ok(())
    }
}

fn push_query_results(query_results: QueryResults, results: &mut Vec<Value>) {
    if query_results.result.len() == 1 {
        if let Some(query_result) = query_results.result.last() {
            if !query_result.bindings.is_empty_object() {
                results.push(query_result.bindings.clone());
            } else {
                for e in query_result.expressions.iter() {
                    results.push(e.value.clone());
                }
            }
        }
    } else {
        for r in query_results.result.iter() {
            if !r.bindings.is_empty_object() {
                results.push(r.bindings.clone());
            } else {
                results.push(Value::from_array(
                    r.expressions.iter().map(|e| e.value.clone()).collect(),
                ));
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn eval_file(
    regos: &[String],
    data_opt: Option<Value>,
    input_opt: Option<ValueOrVec>,
    query: &str,
    enable_tracing: bool,
    strict: bool,
    v0: bool,
    execution_timer: Option<&ExecutionTimerTestConfig>,
) -> Result<(Vec<Value>, Vec<String>)> {
    let mut engine: Engine = Engine::new();
    engine.set_rego_v0(v0);
    engine.set_strict_builtin_errors(strict);
    engine.set_gather_prints(true);

    #[cfg(feature = "coverage")]
    engine.set_enable_coverage(true);

    let use_default_timer =
        execution_timer.is_none() && fallback_execution_timer_config().is_none();

    if let Some(spec) = execution_timer {
        apply_engine_timer(&mut engine, spec)?;
    } else if use_default_timer {
        engine.set_execution_timer_config(default_engine_execution_timer_config());
    }

    let mut results = vec![];
    let mut files = vec![];

    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        engine.add_policy(file.to_string(), contents.to_string())?;
    }

    if let Some(data) = data_opt {
        engine.add_data(data)?;
    }

    let mut inputs = vec![];
    match input_opt {
        Some(ValueOrVec::Single(single_input)) => inputs.push(single_input),
        Some(ValueOrVec::Many(mut many_input)) => inputs.append(&mut many_input),
        _ => (),
    }

    let mut engine_full = engine.clone();
    if let Some(spec) = execution_timer {
        apply_engine_timer(&mut engine_full, spec)?;
    } else if use_default_timer {
        engine_full.set_execution_timer_config(default_engine_execution_timer_config());
    }

    if inputs.is_empty() {
        // Now eval the query.
        reset_time_source();
        let r = engine.eval_query(query.to_string(), enable_tracing)?;
        reset_time_source();
        let r_full = engine_full.eval_query_and_all_rules(query.to_string(), enable_tracing)?;
        if r != r_full {
            std::println!(
                "{}\n{}",
                serde_json::to_string_pretty(&r_full)?,
                serde_json::to_string_pretty(&r)?
            );
            assert_eq!(r_full, r);
        }

        push_query_results(r, &mut results);
    } else {
        for input in inputs {
            engine.set_input(input.clone());
            engine_full.set_input(input);

            // Now eval the query.
            reset_time_source();
            let r = engine.eval_query(query.to_string(), enable_tracing)?;
            reset_time_source();
            let r_full = engine_full.eval_query_and_all_rules(query.to_string(), enable_tracing)?;
            if r != r_full {
                std::println!(
                    "{}\n{}",
                    serde_json::to_string_pretty(&r_full)?,
                    serde_json::to_string_pretty(&r)?
                );
                assert_eq!(r_full, r);
            }

            push_query_results(r, &mut results);
        }
    }

    Ok((results, engine.take_prints()?))
}

#[cfg(feature = "azure_policy")]
#[allow(clippy::too_many_arguments)]
pub fn eval_file_with_rule_evaluation(
    regos: &[String],
    data_opt: Option<Value>,
    input_opt: Option<ValueOrVec>,
    query: &str,
    _enable_tracing: bool,
    strict: bool,
    v0: bool,
    execution_timer: Option<&ExecutionTimerTestConfig>,
) -> Result<(Vec<Value>, Vec<String>)> {
    let mut engine: Engine = Engine::new();
    engine.set_rego_v0(v0);
    engine.set_strict_builtin_errors(strict);
    engine.set_gather_prints(true);

    #[cfg(feature = "coverage")]
    engine.set_enable_coverage(true);

    let use_default_timer =
        execution_timer.is_none() && fallback_execution_timer_config().is_none();

    if let Some(spec) = execution_timer {
        apply_engine_timer(&mut engine, spec)?;
    } else if use_default_timer {
        engine.set_execution_timer_config(default_engine_execution_timer_config());
    }

    let mut results = vec![];
    let mut files = vec![];

    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        engine.add_policy(file.to_string(), contents.to_string())?;
    }

    if let Some(data) = data_opt {
        engine.add_data(data)?;
    }

    // Also test using the newer CompilerPolicy API.
    let compiled_policy = engine.clone().compile_for_target()?;

    let mut inputs = vec![];
    match input_opt {
        Some(ValueOrVec::Single(single_input)) => inputs.push(single_input),
        Some(ValueOrVec::Many(mut many_input)) => inputs.append(&mut many_input),
        _ => {
            // For target tests without input, use an empty object as default
            inputs.push(Value::new_object());
        }
    }

    for input in inputs {
        engine.set_input(input.clone());
        // Use eval_rule instead of eval_query for target tests
        reset_time_source();
        let r_engine = engine.eval_rule(query.to_string())?;
        reset_time_source();
        let r_compiled_policy = compiled_policy.eval_with_input(input)?;
        assert_eq!(r_engine, r_compiled_policy);
        results.push(r_engine);
    }

    Ok((results, engine.take_prints()?))
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Default)]
#[serde(default)]
pub struct ExecutionTimerTestConfig {
    limit_ms: Option<u64>,
    check_interval: Option<u32>,
    disable: Option<bool>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Default)]
#[serde(default)]
pub struct TimeSourceTestConfig {
    increments_ms: Vec<u64>,
    default_increment_ms: Option<u64>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    data: Option<Value>,
    input: Option<ValueOrVec>,
    modules: Vec<String>,
    note: String,
    query: String,
    sort_bindings: Option<bool>,
    want_result: Option<ValueOrVec>,
    want_prints: Option<Vec<String>>,
    no_result: Option<bool>,
    skip: Option<bool>,
    error: Option<String>,
    traces: Option<bool>,
    want_error: Option<String>,
    want_error_code: Option<String>,
    #[serde(default = "default_strict")]
    strict: bool,
    #[serde(default)]
    execution_timer: Option<ExecutionTimerTestConfig>,
    #[serde(default)]
    global_execution_timer: Option<ExecutionTimerTestConfig>,
    #[serde(default)]
    time_source: Option<TimeSourceTestConfig>,
}

fn default_strict() -> bool {
    true
}

fn default_engine_execution_timer_config() -> ExecutionTimerConfig {
    ExecutionTimerConfig {
        limit: Duration::from_secs(5),
        check_interval: NonZeroU32::new(100).unwrap_or(NonZeroU32::MIN),
    }
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    let _limits_lock = acquire_limits_test_lock();

    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    #[cfg(feature = "azure_policy")]
    load_target_definitions::load().expect("Failed to load target definitions");

    #[cfg(not(feature = "std"))]
    {
        // Skip tests that depend on bultins that need std feature.
        let skip = [
            "intn.yaml",
            "is_valid.yaml",
            "add_date.yaml",
            "date.yaml",
            "clock.yaml",
            "compare.yaml",
            "diff.yaml",
            "format.yaml",
            "globmatch.yaml",
            "now_ns.yaml",
            "parse_duration_ns.yaml",
            "parse_ns.yaml",
            "parse_rfc3339_ns.yaml",
            "weekday.yaml",
            "generate.yaml",
            "parse.yaml",
            "tests.yaml",
        ];
        for s in skip {
            if file.contains(s) {
                std::println!("skipped {file} in no_std mode.");
                return Ok(());
            }
        }
    }
    #[cfg(not(feature = "graph"))]
    {
        // Skip tests that depend on graph builtin that need graph feature.
        if file.contains("walk.yaml") {
            std::println!("skipped {file} without graph feature.");
            return Ok(());
        }
    }

    std::println!("running {file}");

    let v0 = !file.contains("bindings.yaml");

    for case in test.cases {
        std::print!("case {} ", case.note);
        if case.skip == Some(true) {
            std::println!("skipped");
            continue;
        }

        let _timer_guard = GlobalTimerGuard::apply(case.global_execution_timer.as_ref())?;
        configure_time_source(case.time_source.as_ref());

        match (&case.want_result, &case.error) {
            (Some(_), None) | (None, Some(_)) => (),
            _ if case.no_result != Some(true) => {
                panic!("either want_result, error or no_result must be specified in test case.")
            }
            _ => (),
        }

        let enable_tracing = case.traces.is_some() && case.traces.unwrap();

        let is_target_test = file.contains("target");

        let result = if is_target_test {
            #[cfg(feature = "azure_policy")]
            {
                eval_file_with_rule_evaluation(
                    &case.modules,
                    case.data,
                    case.input,
                    case.query.as_str(),
                    enable_tracing,
                    case.strict,
                    v0,
                    case.execution_timer.as_ref(),
                )
            }
            #[cfg(not(feature = "azure_policy"))]
            {
                panic!("Target tests require azure_policy feature")
            }
        } else {
            eval_file(
                &case.modules,
                case.data,
                case.input,
                case.query.as_str(),
                enable_tracing,
                case.strict,
                v0,
                case.execution_timer.as_ref(),
            )
        };

        match result {
            Ok((results, prints)) => match case.want_result {
                Some(want_result) => {
                    let mut expected_results = vec![];
                    match want_result {
                        ValueOrVec::Single(single_result) => expected_results.push(single_result),
                        ValueOrVec::Many(mut many_result) => {
                            expected_results.append(&mut many_result)
                        }
                    }

                    check_output(&results, &expected_results)?;
                    if let Some(expected_prints) = case.want_prints {
                        assert_eq!(expected_prints.len(), prints.len());
                        for (idx, ep) in expected_prints.into_iter().enumerate() {
                            if ep != prints[idx] {
                                std::println!(
                                    "print mismatch :\n{}",
                                    prettydiff::diff_chars(&ep, &prints[idx])
                                );
                                panic!("exiting");
                            }
                        }
                    }
                }
                _ if case.no_result == Some(true) => (),
                _ => bail!("eval succeeded and did not produce any errors"),
            },
            Err(actual) => match &case.error {
                Some(expected) => {
                    let actual = actual.to_string();
                    if !actual.contains(expected) {
                        bail!(
                            "Error message\n`{}\n`\ndoes not contain `{}`",
                            actual,
                            expected
                        );
                    }
                    std::println!("{actual}");
                }
                _ => return Err(actual),
            },
        }

        std::println!("passed");
    }

    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    #[cfg(not(feature = "rego-extensions"))]
    if file.contains("rego-extensions") {
        return Ok(());
    }

    // Targets are supported only with azure_policy feature.
    #[cfg(not(feature = "azure_policy"))]
    if file.contains("target") {
        return Ok(());
    }

    match yaml_test_impl(file) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{e}");
        }
    }
}

#[test]
fn yaml_test_basic() -> Result<()> {
    yaml_test("tests/interpreter/cases/basic_001.yaml")
}

#[test]
#[ignore = "intended for use by scripts/yaml-test-eval"]
fn one_yaml() -> Result<()> {
    let mut file = String::default();

    for a in env::args() {
        if a.ends_with(".yaml") {
            file = a;
        }
    }

    if file.is_empty() {
        bail!("missing <yaml-file>");
    }

    yaml_test(file.as_str())
}

#[test_resources("tests/interpreter/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

#[test]
fn test_get_data() -> Result<()> {
    let mut engine = Engine::new();

    // Merge { "x" : 1, "y" : {} }
    engine.add_data(Value::from_json_str(r#"{ "x" : 1, "y" : {}}"#)?)?;

    // Merge { "z" : 2 }
    engine.add_data(Value::from_json_str(r#"{ "z" : 2 }"#)?)?;

    // Add a policy
    engine.add_policy("policy.rego".to_string(), "package a".to_string())?;

    // Evaluate virtual data document. The virtual document includes all rules as well.
    let v_data = engine.eval_query("data".to_string(), false)?.result[0].expressions[0]
        .value
        .clone();
    // There must be an empty package.
    assert_eq!(v_data["a"], Value::new_object());

    // Get the data document.
    let data = engine.get_data();

    // There must NOT be any value of `a`.
    assert_eq!(data["a"], Value::Undefined);

    Ok(())
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Rc, Value};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

fn compile(sources: &[String]) -> Arc<Program> {
    let entries = ["data.probe.r0", "data.probe.safe"];
    let mut engine = Engine::new();
    for (index, source) in sources.iter().enumerate() {
        engine
            .add_policy(format!("native-depth-{index}.rego"), source.clone())
            .unwrap();
    }
    let policy = engine
        .compile_with_entrypoint(&Rc::from(entries[0]))
        .unwrap();
    Compiler::compile_from_policy(&policy, &entries).unwrap()
}

fn chain(depth: usize, virtual_lookup: bool, subobject: bool) -> Vec<String> {
    if virtual_lookup {
        return (0..depth)
            .map(|index| {
                let mut source = if index == 0 {
                    String::from("package probe\nsafe := 7\n")
                } else {
                    format!("package level{index}\n")
                };
                if index + 1 == depth {
                    source.push_str(&format!("r{index} := 42\n"));
                } else {
                    let lookup = if subobject {
                        format!(
                            "object.get(data.level{}, input.next[{index}], 99)",
                            index + 1
                        )
                    } else {
                        format!("data.level{}[input.next[{index}]]", index + 1)
                    };
                    source.push_str(&format!("default r{index} := 99\nr{index} := {lookup}\n"));
                }
                source
            })
            .collect();
    }
    let mut source = String::from("package probe\nsafe := 7\n");
    for index in 0..depth - 1 {
        source.push_str(&format!(
            "default r{index} := 99\nr{index} := r{}\n",
            index + 1
        ));
    }
    source.push_str(&format!("r{} := 42\n", depth - 1));
    vec![source]
}

fn assert_depth_error(vm: &RegoVM, result: Result<Value, VmError>) {
    assert!(
        matches!(
            result,
            Err(VmError::RuleCallDepthExceeded { limit: 16, .. })
        ),
        "{result:?}"
    );
    assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
    assert!(vm.get_call_stack().is_empty());
}

fn run_depth_cases() {
    for (virtual_lookup, subobject) in [(false, false), (true, false), (true, true)] {
        for depth in [16, 17, 18, 82] {
            let program = compile(&chain(depth, virtual_lookup, subobject));
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                eprintln!(
                    "depth={depth}, virtual={virtual_lookup}, subobject={subobject}, mode={mode:?}"
                );
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                let next: Vec<Value> = (1..depth)
                    .map(|index| Value::from(format!("r{index}")))
                    .collect();
                let mut input = Value::new_object();
                input
                    .as_object_mut()
                    .unwrap()
                    .insert(Value::from("next"), Value::from(next));
                vm.set_input(input);

                // In suspendable mode the entry rule itself is an explicit
                // frame, so only its virtual callees consume native depth.
                let native_depth = if virtual_lookup && mode == ExecutionMode::Suspendable {
                    depth - 1
                } else {
                    depth
                };
                let should_error =
                    native_depth > 16 && (virtual_lookup || mode == ExecutionMode::RunToCompletion);
                for _ in 0..2 {
                    let result = vm.execute_entry_point_by_name("data.probe.r0");
                    if should_error {
                        assert_depth_error(&vm, result);
                    } else {
                        assert_eq!(result.unwrap(), Value::from(42));
                    }
                    assert_eq!(
                        vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                        Value::from(7)
                    );
                }

                if mode == ExecutionMode::Suspendable && virtual_lookup {
                    vm.set_step_mode(true);
                    vm.execute_entry_point_by_name("data.probe.r0").unwrap();
                    let mut resumed_active_rule = false;
                    let mut completed = false;
                    for _ in 0..10_000 {
                        assert!(matches!(
                            vm.execution_state(),
                            ExecutionState::Suspended { .. }
                        ));
                        resumed_active_rule |= !vm.get_call_stack().is_empty();
                        let result = vm.resume(None);
                        if should_error && result.is_err() {
                            assert_depth_error(&vm, result);
                            completed = true;
                            break;
                        }
                        let value = result.unwrap();
                        if matches!(vm.execution_state(), ExecutionState::Completed { .. }) {
                            assert!(!should_error, "depth error was swallowed");
                            assert_eq!(value, Value::from(42));
                            completed = true;
                            break;
                        }
                    }
                    assert!(completed, "step execution must terminate");
                    assert!(resumed_active_rule);
                    vm.set_step_mode(false);
                    assert_eq!(
                        vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                        Value::from(7)
                    );
                }
            }
        }
    }
}

fn run_function_depth_cases() {
    for depth in [16, 17, 82] {
        let mut source = String::from("package probe\nr0 := f1(42)\nsafe := 7\n");
        for index in 1..depth - 1 {
            source.push_str(&format!("f{index}(x) := f{}(x)\n", index + 1));
        }
        source.push_str(&format!("f{}(x) := x\n", depth - 1));
        let program = compile(&[source]);
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            eprintln!("function depth={depth}, mode={mode:?}");
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            let result = vm.execute_entry_point_by_name("data.probe.r0");
            if depth > 16 && mode == ExecutionMode::RunToCompletion {
                assert_depth_error(&vm, result);
            } else {
                assert_eq!(result.unwrap(), Value::from(42));
            }
            assert_eq!(
                vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                Value::from(7)
            );
        }
    }
}

fn run_mixed_depth_cases() {
    // Functions are uncached, so this schedules an explicit child while
    // synchronous virtual-document evaluation is retaining a native frame.
    let mut sources = chain(18, true, true);
    sources[1] = String::from(
        "package level1\n\
         b(x) := x\n\
         default r1 := 99\n\
         r1 := [b(input.seed), object.get(data.level2, input.next[1], 99)][1]\n",
    );
    let program = compile(&sources);
    for step_mode in [false, true] {
        eprintln!("mixed explicit/native depth, step={step_mode}");
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.set_step_mode(step_mode);
        let next: Vec<Value> = (1..18)
            .map(|index| Value::from(format!("r{index}")))
            .collect();
        let mut input = Value::new_object();
        input
            .as_object_mut()
            .unwrap()
            .insert(Value::from("next"), Value::from(next));
        input
            .as_object_mut()
            .unwrap()
            .insert(Value::from("seed"), Value::from(0));
        vm.set_input(input);
        let mut result = vm.execute_entry_point_by_name("data.probe.r0");
        if step_mode {
            for _ in 0..10_000 {
                if !matches!(vm.execution_state(), ExecutionState::Suspended { .. }) {
                    break;
                }
                result = vm.resume(None);
            }
        }
        assert_depth_error(&vm, result);
        vm.set_step_mode(false);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
            Value::from(7)
        );
    }
}

#[test]
fn native_depth_child() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_some() {
        run_depth_cases();
        run_function_depth_cases();
        run_mixed_depth_cases();
    }
}

#[test]
fn native_depth_is_bounded() {
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "native_depth_child", "--nocapture"])
        .env("REGORUS_NATIVE_DEPTH_CHILD", "1")
        .env("RUST_MIN_STACK", "2097152")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "native-depth subprocess failed: {status}");
            break;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("native-depth subprocess exceeded deadline");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(feature = "rvm")]

use anyhow::Result;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, SuspendReason, VmError};
use regorus::rvm::{Instruction, Program, RegoVM};
use regorus::utils::limits::{
    fallback_execution_timer_config, set_fallback_execution_timer_config, ExecutionTimerConfig,
};
use regorus::Value;
use std::num::NonZeroU32;
use std::sync::Mutex;
use std::thread::sleep;
use std::time::Duration;

static LIMITS_TEST_LOCK: Mutex<()> = Mutex::new(());

struct FallbackGuard(Option<ExecutionTimerConfig>);

impl Drop for FallbackGuard {
    fn drop(&mut self) {
        set_fallback_execution_timer_config(self.0);
    }
}

fn install_fallback_config(config: Option<ExecutionTimerConfig>) -> FallbackGuard {
    let previous = fallback_execution_timer_config();
    set_fallback_execution_timer_config(config);
    FallbackGuard(previous)
}

#[test]
fn vm_execution_time_limit_triggers_error() -> Result<()> {
    let _lock = LIMITS_TEST_LOCK.lock().unwrap();
    let config = ExecutionTimerConfig {
        limit: Duration::from_nanos(1),
        check_interval: NonZeroU32::new(1).unwrap(),
    };
    let _guard = install_fallback_config(Some(config));

    let mut program = Program::new();
    program.dispatch_window_size = 2;
    program.max_rule_window_size = 2;
    program.entry_points.insert("main".to_string(), 0);

    const INSTRUCTION_COUNT: usize = 60_000;
    program.instructions = (0..INSTRUCTION_COUNT)
        .map(|_| Instruction::LoadNull { dest: 0 })
        .collect();
    program.instructions.push(Instruction::Return { value: 0 });
    program.instruction_spans = vec![None; program.instructions.len()];
    program.main_entry_point = 0;

    let program = std::sync::Arc::new(program);

    let mut vm = RegoVM::new();
    vm.set_max_instructions(usize::MAX);
    vm.load_program(program);

    let result = vm.execute();
    assert!(
        matches!(result, Err(VmError::TimeLimitExceeded { .. })),
        "expected time limit error but got {result:?}"
    );

    Ok(())
}

#[test]
fn vm_execution_time_limit_override_allows_completion() -> Result<()> {
    let _lock = LIMITS_TEST_LOCK.lock().unwrap();
    let strict_config = ExecutionTimerConfig {
        limit: Duration::from_nanos(1),
        check_interval: NonZeroU32::new(1).unwrap(),
    };
    let _guard = install_fallback_config(Some(strict_config));

    let mut program = Program::new();
    program.dispatch_window_size = 2;
    program.max_rule_window_size = 2;
    program.entry_points.insert("main".to_string(), 0);
    program.instructions = vec![
        Instruction::LoadNull { dest: 0 },
        Instruction::Return { value: 0 },
    ];
    program.instruction_spans = vec![None; program.instructions.len()];
    program.main_entry_point = 0;

    let program = std::sync::Arc::new(program);

    let mut vm = RegoVM::new();
    vm.load_program(program);

    let relaxed_config = ExecutionTimerConfig {
        limit: Duration::from_millis(100),
        check_interval: NonZeroU32::new(1).unwrap(),
    };
    vm.set_execution_timer_config(Some(relaxed_config));

    let result = vm.execute();
    assert!(
        result.is_ok(),
        "expected successful execution, got {result:?}"
    );

    Ok(())
}

#[test]
fn vm_suspend_resume_excludes_suspended_time_from_limit() -> Result<()> {
    let _lock = LIMITS_TEST_LOCK.lock().unwrap();
    let _guard = install_fallback_config(Some(ExecutionTimerConfig {
        // Allow headroom for normal execution while still failing if suspended
        // time is included in the timer budget.
        limit: Duration::from_millis(500),
        check_interval: NonZeroU32::new(1).unwrap(),
    }));

    let mut program = Program::new();
    program.dispatch_window_size = 3;
    program.max_rule_window_size = 3;
    program.entry_points.insert("main".to_string(), 0);
    program.literals = vec![Value::from("id"), Value::from(1)];
    program.instructions = vec![
        Instruction::Load {
            dest: 0,
            literal_idx: 0,
        },
        Instruction::Load {
            dest: 1,
            literal_idx: 1,
        },
        Instruction::HostAwait {
            dest: 2,
            arg: 1,
            id: 0,
        },
        Instruction::Return { value: 2 },
    ];
    program.instruction_spans = vec![None; program.instructions.len()];
    program.main_entry_point = 0;

    let program = std::sync::Arc::new(program);
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);

    let _ = vm.execute()?;
    match vm.execution_state() {
        ExecutionState::Suspended { reason, .. } => {
            assert!(matches!(reason, SuspendReason::HostAwait { .. }));
        }
        other => panic!("expected suspension, got {other:?}"),
    }

    // Sleep longer than the limit; resume should still succeed if suspended time is excluded.
    sleep(Duration::from_secs(1));

    let resumed = vm.resume(Some(Value::from(42)))?;
    assert_eq!(resumed, Value::from(42));

    Ok(())
}

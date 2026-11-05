// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::rvm::instructions::ArrayCreateParams;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
use regorus::rvm::Instruction;
use regorus::Value;
use std::sync::Arc;

fn round_trip(program: &Program) -> anyhow::Result<Program> {
    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => Ok(program),
        DeserializationResult::Partial(_) => anyhow::bail!("program round trip was partial"),
    }
}

fn dag_program(depth: usize, comparison: Instruction, right_leaf: bool) -> Program {
    let mut program = Program::new();
    program.dispatch_window_size = 3;
    program.instructions = vec![
        Instruction::LoadTrue { dest: 0 },
        Instruction::LoadBool {
            dest: 1,
            value: right_leaf,
        },
    ];
    for dest in [0, 1] {
        program
            .instruction_data
            .array_create_params
            .push(ArrayCreateParams {
                dest,
                elements: vec![dest, dest],
            });
    }
    for _ in 0..depth {
        program
            .instructions
            .push(Instruction::ArrayCreate { params_index: 0 });
        program
            .instructions
            .push(Instruction::ArrayCreate { params_index: 1 });
    }
    program.instructions.push(comparison);
    program.instructions.push(Instruction::Return { value: 2 });
    program
}

#[test]
fn shared_array_comparisons_in_loaded_programs_and_both_modes() -> anyhow::Result<()> {
    let comparisons = [
        (
            Instruction::Eq {
                dest: 2,
                left: 0,
                right: 1,
            },
            true,
            false,
        ),
        (
            Instruction::Ne {
                dest: 2,
                left: 0,
                right: 1,
            },
            false,
            true,
        ),
        (
            Instruction::Lt {
                dest: 2,
                left: 0,
                right: 1,
            },
            false,
            false,
        ),
        (
            Instruction::Le {
                dest: 2,
                left: 0,
                right: 1,
            },
            true,
            false,
        ),
        (
            Instruction::Gt {
                dest: 2,
                left: 0,
                right: 1,
            },
            false,
            true,
        ),
        (
            Instruction::Ge {
                dest: 2,
                left: 0,
                right: 1,
            },
            true,
            true,
        ),
    ];
    // Deliberately bounded: scaling is asserted by unit-test operation counts,
    // not by risking a large fixture or imposing a timing threshold here.
    for depth in [4, 8, 12] {
        for (instruction, equal, unequal) in comparisons {
            for (right_leaf, expected) in [(true, equal), (false, unequal)] {
                let program = dag_program(depth, instruction, right_leaf);
                let program = Arc::new(round_trip(&program)?);
                for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                    let mut vm = RegoVM::new();
                    vm.load_program(program.clone());
                    vm.set_execution_mode(mode);
                    vm.set_max_instructions(program.instructions.len());
                    assert_eq!(vm.execute()?, Value::Bool(expected));
                    vm.set_max_instructions(program.instructions.len() - 1);
                    assert!(matches!(
                        vm.execute(),
                        Err(VmError::InstructionLimitExceeded { .. })
                    ));
                }
            }
        }
    }
    Ok(())
}

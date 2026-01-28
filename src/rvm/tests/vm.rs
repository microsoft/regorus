// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used,
    clippy::manual_assert,
    clippy::indexing_slicing,
    clippy::option_if_let_else,
    clippy::semicolon_if_nothing_returned,
    clippy::unseparated_literal_suffix,
    clippy::use_debug,
    clippy::unused_trait_names,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)] // VM tests assert/unwrap and use manual panics to validate scenarios

#[cfg(test)]
mod tests {
    use crate::rvm::tests::instruction_parser::{parse_instruction, parse_loop_mode};
    use crate::rvm::tests::test_utils::test_round_trip_serialization;
    use crate::utils::limits::ExecutionTimerConfig;
    use core::num::NonZeroU32;
    use core::time::Duration;
    #[derive(Debug, Clone, Deserialize, Serialize, Default)]
    struct RuleInfoSpec {
        rule_type: String,
        definitions: Vec<Vec<u16>>,
        #[serde(default)]
        default_rule_index: Option<u16>,
        #[serde(default)]
        default_literal_index: Option<u16>,
        #[serde(default)]
        destructuring_blocks: Option<Vec<Option<u16>>>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct DefaultRuleSpec {
        rule_name: String,
        default_value: crate::Value,
    }

    use crate::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
    use crate::test_utils::process_value;
    use crate::value::Value;
    use alloc::collections::{BTreeMap, VecDeque};
    use alloc::string::{String, ToString};
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use anyhow::Result;
    use serde::{Deserialize, Serialize};
    use std::fs;
    use test_generator::test_resources;

    extern crate alloc;
    extern crate std;

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct HostAwaitResponseSpec {
        id: crate::Value,
        #[serde(default)]
        value: Option<crate::Value>,
        #[serde(default)]
        values: Vec<crate::Value>,
    }

    fn default_vm_test_execution_timer_config() -> ExecutionTimerConfig {
        ExecutionTimerConfig {
            limit: Duration::from_secs(1),
            check_interval: NonZeroU32::new(100).unwrap_or(NonZeroU32::MIN),
        }
    }

    #[derive(Debug, Deserialize, Serialize)]
    struct VmTestCase {
        note: String,
        #[serde(default)]
        description: Option<String>,
        #[serde(default)]
        example_rego: Option<String>,
        #[serde(default)]
        data: Option<crate::Value>,
        #[serde(default)]
        input: Option<crate::Value>,
        literals: Vec<crate::Value>,
        #[serde(default)]
        rule_infos: Vec<RuleInfoSpec>,
        #[serde(default)]
        default_rules: Vec<DefaultRuleSpec>,
        #[serde(default)]
        rule_tree: Option<crate::Value>,
        #[serde(default)]
        instruction_params: Option<InstructionParamsSpec>,
        #[serde(default)]
        max_instructions: Option<usize>,
        #[serde(default)]
        host_await_responses: Option<Vec<HostAwaitResponseSpec>>,
        #[serde(default)]
        host_await_responses_run_to_completion: Option<Vec<HostAwaitResponseSpec>>,
        #[serde(default)]
        host_await_responses_suspendable: Option<Vec<HostAwaitResponseSpec>>,
        #[serde(default)]
        ignore_run_to_completion_hostawait_failure: bool,
        instructions: Vec<String>,
        #[serde(default, deserialize_with = "deserialize_optional_value")]
        want_result: Option<crate::Value>,
        #[serde(default)]
        want_error: Option<String>,
        #[serde(default, deserialize_with = "deserialize_optional_value")]
        want_result_strict: Option<crate::Value>,
        #[serde(default)]
        want_error_strict: Option<String>,
    }

    fn deserialize_optional_value<'de, D>(deserializer: D) -> Result<Option<crate::Value>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // If the field is present, always return Some, even if the value is null
        crate::Value::deserialize(deserializer).map(Some)
    }

    #[derive(Debug, Clone, Deserialize, Serialize, Default)]
    struct InstructionParamsSpec {
        #[serde(default)]
        loop_params: Vec<LoopStartParamsSpec>,
        #[serde(default)]
        call_params: Vec<CallParamsSpec>,
        #[serde(default)]
        builtin_call_params: Vec<BuiltinCallParamsSpec>,
        #[serde(default)]
        function_call_params: Vec<FunctionCallParamsSpec>,
        #[serde(default)]
        builtin_infos: Vec<BuiltinInfoSpec>,
        #[serde(default)]
        object_create_params: Vec<ObjectCreateParamsSpec>,
        #[serde(default)]
        array_create_params: Vec<ArrayCreateParamsSpec>,
        #[serde(default)]
        set_create_params: Vec<SetCreateParamsSpec>,
        #[serde(default)]
        virtual_data_document_lookup_params: Vec<VirtualDataDocumentLookupParamsSpec>,
        #[serde(default)]
        chained_index_params: Vec<ChainedIndexParamsSpec>,
        #[serde(default, alias = "comprehension_start_params")]
        comprehension_begin_params: Vec<ComprehensionBeginParamsSpec>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct LoopStartParamsSpec {
        mode: String,
        collection: u16,
        key_reg: u16,
        value_reg: u16,
        result_reg: u16,
        body_start: u16,
        loop_end: u16,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct CallParamsSpec {
        dest: u16,
        func: u16,
        args_start: u16,
        args_count: u16,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct BuiltinCallParamsSpec {
        dest: u16,
        builtin_index: u16,
        args: Vec<u16>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct FunctionCallParamsSpec {
        func: u16,
        dest: u16,
        args: Vec<u16>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct BuiltinInfoSpec {
        name: String,
        num_args: u16,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct ObjectCreateParamsSpec {
        dest: u16,
        template_literal_idx: u16,
        literal_key_fields: Vec<(u16, u16)>,
        fields: Vec<(u16, u16)>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct ArrayCreateParamsSpec {
        dest: u16,
        elements: Vec<u16>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct SetCreateParamsSpec {
        dest: u16,
        elements: Vec<u16>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct LiteralOrRegisterSpec {
        #[serde(default, alias = "literal")]
        literal_idx: Option<u16>,
        #[serde(default, alias = "reg")]
        register: Option<u16>,
    }

    impl LiteralOrRegisterSpec {
        fn into_literal_or_register(self) -> crate::rvm::instructions::LiteralOrRegister {
            if let Some(literal_idx) = self.literal_idx {
                crate::rvm::instructions::LiteralOrRegister::Literal(literal_idx)
            } else if let Some(register) = self.register {
                crate::rvm::instructions::LiteralOrRegister::Register(register.try_into().unwrap())
            } else {
                panic!("LiteralOrRegisterSpec must specify either literal_idx or register");
            }
        }
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct VirtualDataDocumentLookupParamsSpec {
        dest: u16,
        path_components: Vec<LiteralOrRegisterSpec>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct ChainedIndexParamsSpec {
        dest: u16,
        root: u16,
        path_components: Vec<LiteralOrRegisterSpec>,
    }

    #[derive(Debug, Clone, Deserialize, Serialize)]
    struct ComprehensionBeginParamsSpec {
        mode: String,
        collection_reg: u16,
        #[serde(default)]
        result_reg: Option<u16>,
        key_reg: u16,
        value_reg: u16,
        body_start: u16,
        comprehension_end: u16,
    }

    #[derive(Debug, Deserialize, Serialize)]
    struct VmTestSuite {
        cases: Vec<VmTestCase>,
    }

    /// Execute VM instructions directly from parsed instructions and literals
    #[allow(clippy::too_many_arguments)]
    fn execute_vm_instructions(
        instructions: Vec<crate::rvm::instructions::Instruction>,
        literals: Vec<Value>,
        rule_infos: Vec<RuleInfoSpec>,
        rule_tree: Option<Value>,
        instruction_params: Option<InstructionParamsSpec>,
        data: Option<Value>,
        input: Option<Value>,
        max_instructions: Option<usize>,
        host_await_responses: Option<Vec<HostAwaitResponseSpec>>,
        host_await_responses_run_to_completion: Option<Vec<HostAwaitResponseSpec>>,
        host_await_responses_suspendable: Option<Vec<HostAwaitResponseSpec>>,
        ignore_run_to_completion_hostawait_failure: bool,
        strict: bool,
    ) -> Result<Value> {
        let processed_data = if let Some(ref data_value) = data {
            Some(process_value(data_value)?)
        } else {
            None
        };

        let processed_input = if let Some(ref input_value) = input {
            Some(process_value(input_value)?)
        } else {
            None
        };

        let processed_rule_tree = if let Some(ref tree_value) = rule_tree {
            Some(process_value(tree_value)?)
        } else {
            None
        };

        let process_responses =
            |responses: Vec<HostAwaitResponseSpec>| -> Result<BTreeMap<Value, Vec<Value>>> {
                let mut processed: BTreeMap<Value, Vec<Value>> = BTreeMap::new();

                for spec in responses {
                    let identifier = process_value(&spec.id)?;
                    let mut values: Vec<Value> = Vec::new();

                    if let Some(single) = spec.value.as_ref() {
                        values.push(process_value(single)?);
                    }

                    for value in &spec.values {
                        values.push(process_value(value)?);
                    }

                    if values.is_empty() {
                        return Err(anyhow::anyhow!(
                            "HostAwait response specification for id {:?} has no values",
                            identifier
                        ));
                    }

                    processed.entry(identifier).or_default().extend(values);
                }

                Ok(processed)
            };

        let processed_host_responses = if let Some(responses) = host_await_responses {
            Some(process_responses(responses)?)
        } else {
            None
        };

        let processed_host_responses_run_to_completion =
            if let Some(responses) = host_await_responses_run_to_completion {
                Some(process_responses(responses)?)
            } else {
                processed_host_responses.clone()
            };

        let processed_host_responses_suspendable =
            if let Some(responses) = host_await_responses_suspendable {
                Some(process_responses(responses)?)
            } else {
                processed_host_responses.clone()
            };

        // Create a Program from instructions and literals
        let mut program = crate::rvm::program::Program::new();
        program.instructions = instructions;

        // Process literals through the value converter to handle special syntax like set!
        let mut processed_literals = Vec::new();
        for literal in &literals {
            processed_literals.push(process_value(literal)?);
        }
        program.literals = processed_literals;

        if let Some(tree) = processed_rule_tree {
            program.rule_tree = tree;
        } else {
            program.rule_tree = Value::new_object();
        }

        // Convert rule infos
        for rule_info_spec in rule_infos.iter() {
            use crate::rvm::program::{RuleInfo, RuleType};

            let rule_type = match rule_info_spec.rule_type.as_str() {
                "Complete" => RuleType::Complete,
                "PartialSet" => RuleType::PartialSet,
                "PartialObject" => RuleType::PartialObject,
                _ => {
                    return Err(anyhow::anyhow!(
                        "Unknown rule type: {}",
                        rule_info_spec.rule_type
                    ))
                }
            };

            // Convert Vec<Vec<u16>> to Vec<Vec<u32>>
            let definitions: Vec<Vec<u32>> = rule_info_spec
                .definitions
                .iter()
                .map(|def| def.iter().map(|&x| x as u32).collect())
                .collect();

            let mut destructuring_blocks: Vec<Option<u32>> = rule_info_spec
                .destructuring_blocks
                .clone()
                .map(|blocks| {
                    blocks
                        .into_iter()
                        .map(|entry| entry.map(|value| value as u32))
                        .collect()
                })
                .unwrap_or_else(|| alloc::vec![None; definitions.len()]);

            if destructuring_blocks.len() != definitions.len() {
                destructuring_blocks.resize(definitions.len(), None);
            }

            // For function calls, use result_reg 0; for other rules, use result_reg 1
            let result_reg = if instruction_params
                .as_ref()
                .is_some_and(|params| !params.function_call_params.is_empty())
            {
                0 // Function calls use register 0 as return register
            } else {
                1 // Regular rules use register 1
            };

            let rule_info = RuleInfo {
                name: String::from("test_rule"),
                rule_type,
                definitions: crate::Rc::new(definitions.clone()),
                function_info: None,
                default_literal_index: rule_info_spec.default_literal_index,
                result_reg,
                num_registers: 50, // Increased to accommodate test cases with higher register indices
                destructuring_blocks,
            };

            program.rule_infos.push(rule_info);
        }

        // Build instruction data from params specification
        if let Some(params_spec) = instruction_params {
            // Convert loop params
            for loop_param_spec in params_spec.loop_params {
                let mode = parse_loop_mode(&loop_param_spec.mode)?;
                let loop_params = crate::rvm::instructions::LoopStartParams {
                    mode,
                    collection: loop_param_spec.collection.try_into().unwrap(),
                    key_reg: loop_param_spec.key_reg.try_into().unwrap(),
                    value_reg: loop_param_spec.value_reg.try_into().unwrap(),
                    result_reg: loop_param_spec.result_reg.try_into().unwrap(),
                    body_start: loop_param_spec.body_start,
                    loop_end: loop_param_spec.loop_end,
                };
                program.add_loop_params(loop_params);
            }

            // Convert call params
            // Legacy call_params support removed - use builtin_call_params or function_call_params instead
            if !params_spec.call_params.is_empty() {
                // Legacy call parameters are no longer supported
                // Convert to BuiltinCall or FunctionCall instructions instead
                panic!("Legacy call_params are no longer supported. Use builtin_call_params or function_call_params instead.");
            }

            // Convert builtin info specs to program builtin info table
            for builtin_info_spec in params_spec.builtin_infos {
                let builtin_info = crate::rvm::program::BuiltinInfo {
                    name: builtin_info_spec.name,
                    num_args: builtin_info_spec.num_args,
                };
                program.add_builtin_info(builtin_info);
            }

            // Convert builtin call params
            for builtin_call_spec in params_spec.builtin_call_params {
                use crate::rvm::instructions::BuiltinCallParams;

                // Convert Vec<u16> to fixed array (unused slots are irrelevant due to num_args)
                let mut args_array = [0u8; 8];
                for (i, &arg) in builtin_call_spec.args.iter().enumerate() {
                    if i < 8 {
                        args_array[i] = arg.try_into().unwrap();
                    }
                }

                let builtin_call_params = BuiltinCallParams {
                    dest: builtin_call_spec.dest.try_into().unwrap(),
                    builtin_index: builtin_call_spec.builtin_index,
                    num_args: builtin_call_spec.args.len() as u8,
                    args: args_array,
                };
                program.add_builtin_call_params(builtin_call_params);
            }

            // Convert function call params
            for function_call_spec in params_spec.function_call_params {
                use crate::rvm::instructions::FunctionCallParams;

                // Convert Vec<u16> to fixed array (unused slots are irrelevant due to num_args)
                let mut args_array = [0u8; 8];
                for (i, &arg) in function_call_spec.args.iter().enumerate() {
                    if i < 8 {
                        args_array[i] = arg.try_into().unwrap();
                    }
                }

                let function_call_params = FunctionCallParams {
                    func_rule_index: function_call_spec.func,
                    dest: function_call_spec.dest.try_into().unwrap(),
                    num_args: function_call_spec.args.len() as u8,
                    args: args_array,
                };
                program.add_function_call_params(function_call_params);
            }

            // Convert object create params
            for object_create_spec in params_spec.object_create_params {
                use crate::rvm::instructions::ObjectCreateParams;

                let object_create_params = ObjectCreateParams {
                    dest: object_create_spec.dest.try_into().unwrap(),
                    template_literal_idx: object_create_spec.template_literal_idx,
                    literal_key_fields: object_create_spec
                        .literal_key_fields
                        .into_iter()
                        .map(|(k, v)| (k, v.try_into().unwrap()))
                        .collect(),
                    fields: object_create_spec
                        .fields
                        .into_iter()
                        .map(|(k, v)| (k.try_into().unwrap(), v.try_into().unwrap()))
                        .collect(),
                };
                program
                    .instruction_data
                    .add_object_create_params(object_create_params);
            }

            // Convert array create params
            for array_create_spec in params_spec.array_create_params {
                use crate::rvm::instructions::ArrayCreateParams;

                let array_create_params = ArrayCreateParams {
                    dest: array_create_spec.dest.try_into().unwrap(),
                    elements: array_create_spec
                        .elements
                        .into_iter()
                        .map(|reg| reg.try_into().unwrap())
                        .collect(),
                };
                program
                    .instruction_data
                    .add_array_create_params(array_create_params);
            }

            // Convert set create params
            for set_create_spec in params_spec.set_create_params {
                use crate::rvm::instructions::SetCreateParams;

                let set_create_params = SetCreateParams {
                    dest: set_create_spec.dest.try_into().unwrap(),
                    elements: set_create_spec
                        .elements
                        .into_iter()
                        .map(|reg| reg.try_into().unwrap())
                        .collect(),
                };
                program
                    .instruction_data
                    .add_set_create_params(set_create_params);
            }

            // Convert virtual data document lookup params
            for virtual_spec in params_spec.virtual_data_document_lookup_params {
                use crate::rvm::instructions::{
                    LiteralOrRegister, VirtualDataDocumentLookupParams,
                };

                let path_components: Vec<LiteralOrRegister> = virtual_spec
                    .path_components
                    .into_iter()
                    .map(|component| component.into_literal_or_register())
                    .collect();

                let params = VirtualDataDocumentLookupParams {
                    dest: virtual_spec.dest.try_into().unwrap(),
                    path_components,
                };

                program
                    .instruction_data
                    .add_virtual_data_document_lookup_params(params);
            }

            // Convert chained index params
            for chained_spec in params_spec.chained_index_params {
                use crate::rvm::instructions::{ChainedIndexParams, LiteralOrRegister};

                let path_components: Vec<LiteralOrRegister> = chained_spec
                    .path_components
                    .into_iter()
                    .map(|component| component.into_literal_or_register())
                    .collect();

                let params = ChainedIndexParams {
                    dest: chained_spec.dest.try_into().unwrap(),
                    root: chained_spec.root.try_into().unwrap(),
                    path_components,
                };

                program.instruction_data.add_chained_index_params(params);
            }

            // Convert comprehension start params
            for comprehension_spec in params_spec.comprehension_begin_params {
                use crate::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};

                let mode = match comprehension_spec.mode.as_str() {
                    "Array" => ComprehensionMode::Array,
                    "Set" => ComprehensionMode::Set,
                    "Object" => ComprehensionMode::Object,
                    _ => panic!("Invalid comprehension mode: {}", comprehension_spec.mode),
                };

                let comprehension_params = ComprehensionBeginParams {
                    mode,
                    collection_reg: comprehension_spec.collection_reg.try_into().unwrap(),
                    result_reg: comprehension_spec
                        .result_reg
                        .unwrap_or(comprehension_spec.collection_reg)
                        .try_into()
                        .unwrap(),
                    key_reg: comprehension_spec.key_reg.try_into().unwrap(),
                    value_reg: comprehension_spec.value_reg.try_into().unwrap(),
                    body_start: comprehension_spec.body_start,
                    comprehension_end: comprehension_spec.comprehension_end,
                };
                program
                    .instruction_data
                    .add_comprehension_begin_params(comprehension_params);
            }
        }

        program.main_entry_point = 0;

        // Set a reasonable default for register window size in VM tests
        // Most tests use registers 0-10, so we'll allocate 255 registers (u8 max)
        program.max_rule_window_size = 255;
        program.dispatch_window_size = 50;

        // Initialize resolved builtins if we have builtin info
        if !program.builtin_info_table.is_empty() {
            if let Err(e) = program.initialize_resolved_builtins() {
                return Err(anyhow::anyhow!(
                    "Failed to initialize resolved builtins: {}",
                    e
                ));
            }
        }

        // Ensure program artifacts survive binary round-tripping
        test_round_trip_serialization(&program)
            .map_err(|e| anyhow::anyhow!("Program serialization round-trip failed: {}", e))?;

        let program = Arc::new(program);

        let run_with_mode = |mode: ExecutionMode,
                             use_step_mode: bool,
                             host_responses_template: Option<BTreeMap<Value, Vec<Value>>>|
         -> Result<Result<Value>> {
            let mut vm = RegoVM::new();
            vm.set_execution_mode(mode);
            vm.set_step_mode(use_step_mode);
            vm.set_strict_builtin_errors(strict);
            vm.set_execution_timer_config(Some(default_vm_test_execution_timer_config()));

            if let Some(data_value) = processed_data.clone() {
                vm.set_data(data_value)?;
            }
            if let Some(input_value) = processed_input.clone() {
                vm.set_input(input_value);
            }

            if let Some(limit) = max_instructions {
                vm.set_max_instructions(limit);
            }

            if matches!(mode, ExecutionMode::RunToCompletion) {
                if let Some(responses) = host_responses_template.clone() {
                    vm.set_host_await_responses(responses);
                }
            }

            vm.load_program(program.clone());

            let mut response_map = host_responses_template.clone().map(|map| {
                map.into_iter()
                    .map(|(identifier, values)| (identifier, VecDeque::from(values)))
                    .collect::<BTreeMap<_, _>>()
            });

            let mut last_result = vm.execute().map_err(|e| anyhow::anyhow!("{}", e));

            loop {
                match vm.execution_state() {
                    ExecutionState::Completed { result } => {
                        return Ok(Ok(result.clone()));
                    }
                    ExecutionState::Error { error } => {
                        return Ok(Err(anyhow::anyhow!("{}", error)));
                    }
                    ExecutionState::Suspended { reason, .. } => {
                        if mode != ExecutionMode::Suspendable {
                            return Ok(Err(anyhow::anyhow!(
                                "Run-to-completion execution unexpectedly suspended: {:?}",
                                reason
                            )));
                        }

                        match reason {
                            SuspendReason::HostAwait {
                                dest, identifier, ..
                            } => {
                                let dest = *dest;
                                let identifier = identifier.clone();

                                let response = {
                                    let map = response_map.as_mut().ok_or_else(|| {
                                        anyhow::anyhow!(
                                            "{}",
                                            VmError::HostAwaitResponseMissing {
                                                dest,
                                                identifier: identifier.clone(),
                                                pc: 0,
                                            }
                                        )
                                    })?;

                                    let queue = map.get_mut(&identifier).ok_or_else(|| {
                                        anyhow::anyhow!(
                                            "{}",
                                            VmError::HostAwaitResponseMissing {
                                                dest,
                                                identifier: identifier.clone(),
                                                pc: 0,
                                            }
                                        )
                                    })?;

                                    let response = queue.pop_front().ok_or_else(|| {
                                        anyhow::anyhow!(
                                            "{}",
                                            VmError::HostAwaitResponseMissing {
                                                dest,
                                                identifier: identifier.clone(),
                                                pc: 0,
                                            }
                                        )
                                    })?;

                                    if queue.is_empty() {
                                        map.remove(&identifier);
                                    }

                                    response
                                };

                                last_result = vm
                                    .resume(Some(response))
                                    .map_err(|e| anyhow::anyhow!("{}", e));
                            }
                            SuspendReason::Step => {
                                if !use_step_mode {
                                    return Ok(Err(anyhow::anyhow!(
                                        "Suspendable execution unexpectedly suspended: {:?}",
                                        reason
                                    )));
                                }
                                last_result = vm.resume(None).map_err(|e| anyhow::anyhow!("{}", e));
                            }
                            _ => {
                                last_result = vm.resume(None).map_err(|e| anyhow::anyhow!("{}", e));
                            }
                        }
                    }
                    _ => match &last_result {
                        Ok(value) => return Ok(Ok(value.clone())),
                        Err(err) => return Ok(Err(anyhow::anyhow!("{}", err))),
                    },
                }
            }
        };

        let compare_results = |baseline_name: &str,
                               baseline: &Result<Value>,
                               other_name: &str,
                               other: &Result<Value>|
         -> Result<()> {
            match (baseline, other) {
                (Ok(expected), Ok(actual)) => {
                    if expected != actual {
                        return Err(anyhow::anyhow!(
                            "{} execution result {:?} differed from {} {:?}",
                            other_name,
                            actual,
                            baseline_name,
                            expected
                        ));
                    }
                    Ok(())
                }
                (Err(expected_err), Err(other_err)) => {
                    let expected_msg = expected_err.to_string();
                    let other_msg = other_err.to_string();
                    if expected_msg != other_msg {
                        return Err(anyhow::anyhow!(
                            "{} execution error '{}' differed from {} '{}'",
                            other_name,
                            other_msg,
                            baseline_name,
                            expected_msg
                        ));
                    }
                    Ok(())
                }
                (Ok(expected), Err(other_err)) => Err(anyhow::anyhow!(
                    "{} execution failed with '{}' while {} succeeded with {:?}",
                    other_name,
                    other_err,
                    baseline_name,
                    expected
                )),
                (Err(expected_err), Ok(actual)) => Err(anyhow::anyhow!(
                    "{} execution succeeded with {:?} while {} failed with '{}'",
                    other_name,
                    actual,
                    baseline_name,
                    expected_err
                )),
            }
        };

        let run_to_completion = run_with_mode(
            ExecutionMode::RunToCompletion,
            false,
            processed_host_responses_run_to_completion.clone(),
        )?;
        let suspendable = run_with_mode(
            ExecutionMode::Suspendable,
            false,
            processed_host_responses_suspendable.clone(),
        )?;
        let stepwise = run_with_mode(
            ExecutionMode::Suspendable,
            true,
            processed_host_responses_suspendable.clone(),
        )?;

        const HOST_AWAIT_RESPONSE_MISSING: &str = "HostAwait executed but no response provided";

        let ignore_run_to_completion = ignore_run_to_completion_hostawait_failure
            && matches!(
                &run_to_completion,
                Err(err) if err.to_string().contains(HOST_AWAIT_RESPONSE_MISSING)
            );

        if ignore_run_to_completion {
            compare_results("suspendable", &suspendable, "step-by-step", &stepwise)?;
            return suspendable;
        }

        compare_results(
            "run-to-completion",
            &run_to_completion,
            "suspendable",
            &suspendable,
        )?;
        compare_results(
            "run-to-completion",
            &run_to_completion,
            "step-by-step",
            &stepwise,
        )?;

        run_to_completion
    }

    fn run_vm_test_suite(file: &str) -> Result<()> {
        std::println!("Running VM test suite: {}", file);
        let yaml_content = fs::read_to_string(file)?;
        let test_suite: VmTestSuite = serde_yaml::from_str(&yaml_content)?;

        for test_case in test_suite.cases {
            std::println!("Running VM test case: {}", test_case.note);

            let instructions = test_case
                .instructions
                .iter()
                .map(|instruction_str| parse_instruction(instruction_str))
                .collect::<Result<Vec<_>>>()?;

            let ignore_hostawait_failure = test_case.ignore_run_to_completion_hostawait_failure;

            struct ModeExpectation<'a> {
                strict: bool,
                want_result: Option<&'a crate::Value>,
                want_error: Option<&'a String>,
            }

            let mut expectations = Vec::new();

            if test_case.want_result.is_some() || test_case.want_error.is_some() {
                expectations.push(ModeExpectation {
                    strict: false,
                    want_result: test_case.want_result.as_ref(),
                    want_error: test_case.want_error.as_ref(),
                });
            }

            if test_case.want_result_strict.is_some() || test_case.want_error_strict.is_some() {
                expectations.push(ModeExpectation {
                    strict: true,
                    want_result: test_case.want_result_strict.as_ref(),
                    want_error: test_case.want_error_strict.as_ref(),
                });
            }

            if expectations.is_empty() {
                panic!(
                    "Test case '{}' must specify expectations for at least one mode",
                    test_case.note
                );
            }

            for expectation in expectations {
                let mode_label = if expectation.strict {
                    "strict"
                } else {
                    "non-strict"
                };
                std::println!("  Mode: {}", mode_label);

                let execution_result = execute_vm_instructions(
                    instructions.clone(),
                    test_case.literals.clone(),
                    test_case.rule_infos.clone(),
                    test_case.rule_tree.clone(),
                    test_case.instruction_params.clone(),
                    test_case.data.clone(),
                    test_case.input.clone(),
                    test_case.max_instructions,
                    test_case.host_await_responses.clone(),
                    test_case.host_await_responses_run_to_completion.clone(),
                    test_case.host_await_responses_suspendable.clone(),
                    ignore_hostawait_failure,
                    expectation.strict,
                );

                if expectation.want_error.is_some() && expectation.want_result.is_some() {
                    panic!(
                        "Test case '{}' cannot specify both want_result and want_error for {} mode",
                        test_case.note, mode_label
                    );
                }

                if let Some(expected_error) = expectation.want_error {
                    match execution_result {
                        Err(e) => {
                            let error_msg = std::format!("{}", e);
                            if !error_msg.contains(expected_error) {
                                std::println!(
                                    "Test case '{}' failed ({} mode):",
                                    test_case.note,
                                    mode_label
                                );
                                std::println!("  Expected error containing: '{}'", expected_error);
                                std::println!("  Actual error: '{}'", error_msg);
                                panic!("VM test case failed: {}", test_case.note);
                            }
                        }
                        Ok(result) => {
                            std::println!(
                                "Test case '{}' failed ({} mode):",
                                test_case.note,
                                mode_label
                            );
                            std::println!("  Expected error containing: '{}'", expected_error);
                            std::println!("  But got successful result: {:?}", result);
                            panic!("VM test case failed: {}", test_case.note);
                        }
                    }
                } else if let Some(want_result) = expectation.want_result {
                    let expected_result = process_value(want_result)?;

                    let actual_result = match execution_result {
                        Ok(result) => result,
                        Err(e) => {
                            if std::format!("{}", e).contains("Assertion failed") {
                                Value::Undefined
                            } else {
                                return Err(e);
                            }
                        }
                    };

                    if actual_result != expected_result {
                        std::println!(
                            "Test case '{}' failed ({} mode):",
                            test_case.note,
                            mode_label
                        );
                        std::println!("  Expected: {:?}", expected_result);
                        std::println!("  Actual: {:?}", actual_result);
                        panic!("VM test case failed: {}", test_case.note);
                    }
                } else {
                    panic!(
                        "Test case '{}' must specify either want_result or want_error for {} mode",
                        test_case.note, mode_label
                    );
                }

                std::println!("  ✓ {} mode passed", mode_label);
            }

            std::println!("✓ Test case '{}' passed", test_case.note);
        }
        std::println!("✓ Test suite '{}' completed successfully", file);

        Ok(())
    }

    #[test_resources("tests/rvm/vm/suites/*.yaml")]
    fn run_vm_test_file(file: &str) {
        run_vm_test_suite(file).unwrap()
    }

    #[test_resources("tests/rvm/vm/suites/loops/*.yaml")]
    fn run_loop_test_file(file: &str) {
        run_vm_test_suite(file).unwrap()
    }
}

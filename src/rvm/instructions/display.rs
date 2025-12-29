// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use super::{Instruction, InstructionData, LiteralOrRegister};

impl Instruction {
    /// Get detailed display string with parameter resolution for debugging
    pub fn display_with_params(&self, instruction_data: &InstructionData) -> String {
        match *self {
            Instruction::LoopStart { params_index } => {
                instruction_data.get_loop_params(params_index).map_or_else(
                    || format!("LOOP_START P({}) [INVALID INDEX]", params_index),
                    |params| {
                        format!(
                            "LOOP_START {:?} R({}) R({}) R({}) R({}) {} {}",
                            params.mode,
                            params.collection,
                            params.key_reg,
                            params.value_reg,
                            params.result_reg,
                            params.body_start,
                            params.loop_end
                        )
                    },
                )
            }
            Instruction::BuiltinCall { params_index } => instruction_data
                .get_builtin_call_params(params_index)
                .map_or_else(
                    || format!("BUILTIN_CALL P({}) [INVALID INDEX]", params_index),
                    |params| {
                        let args_str = params
                            .arg_registers()
                            .iter()
                            .map(|&r| format!("R({})", r))
                            .collect::<Vec<_>>()
                            .join(" ");
                        format!(
                            "BUILTIN_CALL R({}) B({}) [{}]",
                            params.dest, params.builtin_index, args_str
                        )
                    },
                ),
            Instruction::HostAwait { dest, arg, id } => {
                format!("HOST_AWAIT R({}) R({}) R({})", dest, arg, id)
            }
            Instruction::FunctionCall { params_index } => instruction_data
                .get_function_call_params(params_index)
                .map_or_else(
                    || format!("FUNCTION_CALL P({}) [INVALID INDEX]", params_index),
                    |params| {
                        let args_str = params
                            .arg_registers()
                            .iter()
                            .map(|&r| format!("R({})", r))
                            .collect::<Vec<_>>()
                            .join(" ");
                        format!(
                            "FUNCTION_CALL R({}) RULE({}) [{}]",
                            params.dest, params.func_rule_index, args_str
                        )
                    },
                ),
            Instruction::ObjectCreate { params_index } => {
                instruction_data
                    .get_object_create_params(params_index)
                    .map_or_else(
                        || format!("OBJECT_CREATE P({}) [INVALID INDEX]", params_index),
                        |params| {
                            let mut field_parts = Vec::new();

                            // Add literal key fields
                            for &(literal_idx, value_reg) in params.literal_key_field_pairs() {
                                field_parts.push(format!("L({}):R({})", literal_idx, value_reg));
                            }

                            // Add non-literal key fields
                            for &(key_reg, value_reg) in params.field_pairs() {
                                field_parts.push(format!("R({}):R({})", key_reg, value_reg));
                            }

                            let fields_str = field_parts.join(" ");
                            format!(
                                "OBJECT_CREATE R({}) L({}) [{}]",
                                params.dest, params.template_literal_idx, fields_str
                            )
                        },
                    )
            }
            Instruction::VirtualDataDocumentLookup { params_index } => instruction_data
                .get_virtual_data_document_lookup_params(params_index)
                .map_or_else(
                    || {
                        format!(
                            "VIRTUAL_DATA_DOCUMENT_LOOKUP P({}) [INVALID INDEX]",
                            params_index
                        )
                    },
                    |params| {
                        let components_str = params
                            .path_components
                            .iter()
                            .map(|comp| match *comp {
                                LiteralOrRegister::Literal(idx) => format!("L({})", idx),
                                LiteralOrRegister::Register(reg) => format!("R({})", reg),
                            })
                            .collect::<Vec<_>>()
                            .join(".");
                        format!(
                            "VIRTUAL_DATA_DOCUMENT_LOOKUP R({}) [data.{}]",
                            params.dest, components_str
                        )
                    },
                ),
            Instruction::ComprehensionBegin { params_index } => instruction_data
                .get_comprehension_begin_params(params_index)
                .map_or_else(
                    || format!("COMPREHENSION_BEGIN P({}) [INVALID INDEX]", params_index),
                    |params| {
                        format!(
                            "COMPREHENSION_BEGIN {:?} R({}) R({}) R({}) {} {}",
                            params.mode,
                            params.collection_reg,
                            params.key_reg,
                            params.value_reg,
                            params.body_start,
                            params.comprehension_end
                        )
                    },
                ),
            _ => format!("{}", self),
        }
    }
}

impl core::fmt::Display for Instruction {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match *self {
            Instruction::Load { dest, literal_idx } => {
                format!("LOAD R({}) L({})", dest, literal_idx)
            }
            Instruction::LoadTrue { dest } => format!("LOAD_TRUE R({})", dest),
            Instruction::LoadFalse { dest } => format!("LOAD_FALSE R({})", dest),
            Instruction::LoadNull { dest } => format!("LOAD_NULL R({})", dest),
            Instruction::LoadBool { dest, value } => format!("LOAD_BOOL R({}) {}", dest, value),
            Instruction::LoadData { dest } => format!("LOAD_DATA R({})", dest),
            Instruction::LoadInput { dest } => format!("LOAD_INPUT R({})", dest),
            Instruction::Move { dest, src } => format!("MOVE R({}) R({})", dest, src),
            Instruction::Add { dest, left, right } => {
                format!("ADD R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Sub { dest, left, right } => {
                format!("SUB R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Mul { dest, left, right } => {
                format!("MUL R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Div { dest, left, right } => {
                format!("DIV R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Mod { dest, left, right } => {
                format!("MOD R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Eq { dest, left, right } => {
                format!("EQ R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Ne { dest, left, right } => {
                format!("NE R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Lt { dest, left, right } => {
                format!("LT R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Le { dest, left, right } => {
                format!("LE R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Gt { dest, left, right } => {
                format!("GT R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Ge { dest, left, right } => {
                format!("GE R({}) R({}) R({})", dest, left, right)
            }
            Instruction::And { dest, left, right } => {
                format!("AND R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Or { dest, left, right } => {
                format!("OR R({}) R({}) R({})", dest, left, right)
            }
            Instruction::Not { dest, operand } => {
                format!("NOT R({}) R({})", dest, operand)
            }
            Instruction::BuiltinCall { params_index } => {
                format!("BUILTIN_CALL P({})", params_index)
            }
            Instruction::HostAwait { dest, arg, id } => {
                format!("HOST_AWAIT R({}) R({}) R({})", dest, arg, id)
            }
            Instruction::FunctionCall { params_index } => {
                format!("FUNCTION_CALL P({})", params_index)
            }
            Instruction::Return { value } => format!("RETURN R({})", value),
            Instruction::ObjectSet { obj, key, value } => {
                format!("OBJECT_SET R({}) R({}) R({})", obj, key, value)
            }
            Instruction::ObjectCreate { params_index } => {
                format!("OBJECT_CREATE P({})", params_index)
            }
            Instruction::Index {
                dest,
                container,
                key,
            } => format!("INDEX R({}) R({}) R({})", dest, container, key),
            Instruction::IndexLiteral {
                dest,
                container,
                literal_idx,
            } => format!(
                "INDEX_LITERAL R({}) R({}) L({})",
                dest, container, literal_idx
            ),
            Instruction::ChainedIndex { params_index } => {
                format!("CHAINED_INDEX P({})", params_index)
            }
            Instruction::ArrayNew { dest } => format!("ARRAY_NEW R({})", dest),
            Instruction::ArrayPush { arr, value } => format!("ARRAY_PUSH R({}) R({})", arr, value),
            Instruction::ArrayCreate { params_index } => {
                format!("ARRAY_CREATE P({})", params_index)
            }
            Instruction::SetNew { dest } => format!("SET_NEW R({})", dest),
            Instruction::SetAdd { set, value } => format!("SET_ADD R({}) R({})", set, value),
            Instruction::SetCreate { params_index } => {
                format!("SET_CREATE P({})", params_index)
            }
            Instruction::Contains {
                dest,
                collection,
                value,
            } => format!("CONTAINS R({}) R({}) R({})", dest, collection, value),
            Instruction::Count { dest, collection } => {
                format!("COUNT R({}) R({})", dest, collection)
            }
            Instruction::AssertCondition { condition } => {
                format!("ASSERT_CONDITION R({})", condition)
            }
            Instruction::AssertNotUndefined { register } => {
                format!("ASSERT_NOT_UNDEFINED R({})", register)
            }
            Instruction::LoopStart { params_index } => {
                format!("LOOP_START P({})", params_index)
            }
            Instruction::LoopNext {
                body_start,
                loop_end,
            } => {
                format!("LOOP_NEXT {} {}", body_start, loop_end)
            }
            Instruction::CallRule { dest, rule_index } => {
                format!("CALL_RULE R({}) {}", dest, rule_index)
            }
            Instruction::VirtualDataDocumentLookup { params_index } => {
                format!("VIRTUAL_DATA_DOCUMENT_LOOKUP P({})", params_index)
            }
            Instruction::DestructuringSuccess {} => String::from("DESTRUCTURING_SUCCESS"),
            Instruction::RuleReturn {} => String::from("RULE_RETURN"),

            Instruction::RuleInit {
                result_reg,
                rule_index,
            } => {
                format!("RULE_INIT R({}) {}", result_reg, rule_index)
            }
            Instruction::Halt {} => String::from("HALT"),
            Instruction::ComprehensionBegin { params_index } => {
                format!("COMPREHENSION_BEGIN P({})", params_index)
            }
            Instruction::ComprehensionYield { value_reg, key_reg } => key_reg.as_ref().map_or_else(
                || format!("COMPREHENSION_YIELD R({})", value_reg),
                |k| format!("COMPREHENSION_YIELD R({}) R({})", k, value_reg),
            ),
            Instruction::ComprehensionEnd {} => String::from("COMPREHENSION_END"),
        };
        write!(f, "{}", text)
    }
}

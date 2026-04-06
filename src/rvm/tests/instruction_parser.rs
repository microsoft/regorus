// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::unwrap_used,
    clippy::arithmetic_side_effects,
    clippy::option_if_let_else,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)] // tests unwrap conversions and slice math for brevity

use crate::rvm::instructions::{GuardMode, Instruction, LogicalBlockMode, LoopMode, PolicyOp};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use anyhow::{anyhow, bail, Result};

/// Parse a textual instruction like "Load { dest: 0, literal_idx: 1 }"
pub fn parse_instruction(text: &str) -> Result<Instruction> {
    let text = text.trim();

    // Find the instruction name and parameters
    if let Some(brace_start) = text.find('{') {
        let name = text[..brace_start].trim();
        let params_text = &text[brace_start..];

        match name {
            "Load" => parse_load(params_text),
            "LoadTrue" => parse_load_true(params_text),
            "LoadFalse" => parse_load_false(params_text),
            "LoadNull" => parse_load_null(params_text),
            "LoadBool" => parse_load_bool(params_text),
            "LoadData" => parse_load_data(params_text),
            "LoadInput" => parse_load_input(params_text),
            "LoadContext" => parse_load_context(params_text),
            "LoadMetadata" => parse_load_metadata(params_text),
            "Move" => parse_move(params_text),
            "Add" => parse_add(params_text),
            "Sub" => parse_sub(params_text),
            "Mul" => parse_mul(params_text),
            "Div" => parse_div(params_text),
            "Mod" => parse_mod(params_text),
            "Eq" => parse_eq(params_text),
            "Ne" => parse_ne_instruction(params_text),
            "Lt" => parse_lt(params_text),
            "Le" => parse_le_instruction(params_text),
            "Gt" => parse_gt(params_text),
            "Ge" => parse_ge_instruction(params_text),
            "And" => parse_and(params_text),
            "Or" => parse_or(params_text),
            "Not" => parse_not(params_text),
            "Return" => parse_return(params_text),
            "RuleInit" => parse_rule_init(params_text),
            "RuleReturn" => parse_rule_return(params_text),
            "DestructuringSuccess" => parse_destructuring_success(params_text),
            "ObjectSet" => parse_object_set(params_text),
            "ObjectCreate" => parse_object_create(params_text),
            "Index" => parse_index(params_text),
            "IndexLiteral" => parse_index_literal(params_text),
            "ChainedIndex" => parse_chained_index(params_text),
            "ArrayNew" => parse_array_new(params_text),
            "ArrayCreate" => parse_array_create(params_text),
            "SetCreate" => parse_set_create(params_text),
            "ArrayPush" => parse_array_push(params_text),
            "ArrayPushDefined" => parse_array_push_defined(params_text),
            "SetNew" => parse_set_new(params_text),
            "SetAdd" => parse_set_add(params_text),
            "Contains" => parse_contains(params_text),
            "Count" => parse_count(params_text),
            "AssertEq" => parse_assert_eq(params_text),
            "AssertNot" => parse_guard(params_text, GuardMode::Not),
            "AssertCondition" => parse_guard(params_text, GuardMode::Condition),
            "AssertNotUndefined" => parse_guard(params_text, GuardMode::NotUndefined),
            "BuiltinCall" => parse_builtin_call(params_text),
            "FunctionCall" => parse_function_call(params_text),
            "CallRule" => parse_call_rule(params_text),
            "VirtualDataDocumentLookup" => parse_virtual_data_document_lookup(params_text),
            "HostAwait" => parse_host_await(params_text),
            "LoopStart" => parse_loop_start(params_text),
            "LoopNext" => parse_loop_next(params_text),
            "ComprehensionStart" => parse_comprehension_start(params_text),
            "ComprehensionAdd" => parse_comprehension_add(params_text),
            "ComprehensionBegin" => parse_comprehension_start(params_text),
            "ComprehensionYield" => parse_comprehension_add(params_text),
            "ReturnUndefinedIfNotTrue" => parse_return_undefined_if_not_true(params_text),
            "CoalesceUndefinedToNull" => parse_coalesce_undefined_to_null(params_text),
            // Azure Policy condition operators
            "PolicyEquals" => parse_policy_condition(params_text, PolicyOp::Equals),
            "PolicyNotEquals" => parse_policy_condition(params_text, PolicyOp::NotEquals),
            "PolicyGreater" => parse_policy_condition(params_text, PolicyOp::Greater),
            "PolicyGreaterOrEquals" => {
                parse_policy_condition(params_text, PolicyOp::GreaterOrEquals)
            }
            "PolicyLess" => parse_policy_condition(params_text, PolicyOp::Less),
            "PolicyLessOrEquals" => parse_policy_condition(params_text, PolicyOp::LessOrEquals),
            "PolicyIn" => parse_policy_condition(params_text, PolicyOp::In),
            "PolicyNotIn" => parse_policy_condition(params_text, PolicyOp::NotIn),
            "PolicyContains" => parse_policy_condition(params_text, PolicyOp::Contains),
            "PolicyNotContains" => parse_policy_condition(params_text, PolicyOp::NotContains),
            "PolicyContainsKey" => parse_policy_condition(params_text, PolicyOp::ContainsKey),
            "PolicyNotContainsKey" => parse_policy_condition(params_text, PolicyOp::NotContainsKey),
            "PolicyLike" => parse_policy_condition(params_text, PolicyOp::Like),
            "PolicyNotLike" => parse_policy_condition(params_text, PolicyOp::NotLike),
            "PolicyMatch" => parse_policy_condition(params_text, PolicyOp::Match),
            "PolicyNotMatch" => parse_policy_condition(params_text, PolicyOp::NotMatch),
            "PolicyMatchInsensitively" => {
                parse_policy_condition(params_text, PolicyOp::MatchInsensitively)
            }
            "PolicyNotMatchInsensitively" => {
                parse_policy_condition(params_text, PolicyOp::NotMatchInsensitively)
            }
            "PolicyExists" => parse_policy_condition(params_text, PolicyOp::Exists),
            "ValueConditionGuard" => parse_value_condition_guard(params_text),
            "PolicyNot" => parse_policy_not(params_text),
            // AllOf / AnyOf
            "AllOfStart" => parse_logical_block_start(params_text, LogicalBlockMode::AllOf),
            "AllOfNext" => parse_allof_next(params_text),
            "AllOfEnd" => parse_logical_block_end(params_text, LogicalBlockMode::AllOf),
            "AnyOfStart" => parse_logical_block_start(params_text, LogicalBlockMode::AnyOf),
            "AnyOfNext" => parse_anyof_next(params_text),
            "AnyOfEnd" => parse_logical_block_end(params_text, LogicalBlockMode::AnyOf),
            _ => bail!("Unknown instruction: {}", name),
        }
    } else {
        // Handle instructions without parameters (no braces)
        let name = text.trim();
        match name {
            "Halt" => Ok(Instruction::Halt {}),
            "RuleReturn" => Ok(Instruction::RuleReturn {}),
            "DestructuringSuccess" => Ok(Instruction::DestructuringSuccess {}),
            "ComprehensionEnd" => Ok(Instruction::ComprehensionEnd {}),
            _ => bail!("Unknown instruction: {}", name),
        }
    }
}

// Parameter parsing helpers
fn parse_params(text: &str) -> Result<Vec<(String, String)>> {
    if !text.starts_with('{') || !text.ends_with('}') {
        bail!("Parameters must be enclosed in braces");
    }

    let inner = &text[1..text.len() - 1];
    let mut params = Vec::new();
    let mut current = String::new();
    let in_value = false;
    let mut colon_pos = None;

    for ch in inner.chars() {
        match ch {
            ':' if !in_value => {
                colon_pos = Some(current.len());
                current.push(ch);
            }
            ',' if !in_value => {
                if let Some(pos) = colon_pos {
                    let key = current[..pos].trim().to_string();
                    let value = current[pos + 1..].trim().to_string();
                    params.push((key, value));
                    current.clear();
                    colon_pos = None;
                } else {
                    bail!("Invalid parameter format");
                }
            }
            _ => current.push(ch),
        }
    }

    // Handle the last parameter
    if !current.trim().is_empty() {
        if let Some(pos) = colon_pos {
            let key = current[..pos].trim().to_string();
            let value = current[pos + 1..].trim().to_string();
            params.push((key, value));
        } else {
            bail!("Invalid parameter format");
        }
    }

    Ok(params)
}

fn get_param_u16(params: &[(String, String)], name: &str) -> Result<u16> {
    for (key, value) in params {
        if key == name {
            return value
                .parse::<u16>()
                .map_err(|_| anyhow!("Invalid u16 value for {}: {}", name, value));
        }
    }
    bail!("Missing parameter: {}", name);
}

fn get_param_bool(params: &[(String, String)], name: &str) -> Result<bool> {
    for (key, value) in params {
        if key == name {
            return value
                .parse::<bool>()
                .map_err(|_| anyhow!("Invalid bool value for {}: {}", name, value));
        }
    }
    bail!("Missing parameter: {}", name);
}

pub fn parse_loop_mode(text: &str) -> Result<LoopMode> {
    match text {
        "Any" => Ok(LoopMode::Any),
        "Every" => Ok(LoopMode::Every),
        "ForEach" => Ok(LoopMode::ForEach),
        // Keep backwards compatibility for now
        "Existential" => Ok(LoopMode::Any),
        "Universal" => Ok(LoopMode::Every),
        "Collect" => Ok(LoopMode::ForEach),
        // Legacy comprehension modes now map to ForEach since we use dedicated comprehension instructions
        "ArrayComprehension" => Ok(LoopMode::ForEach),
        "SetComprehension" => Ok(LoopMode::ForEach),
        "ObjectComprehension" => Ok(LoopMode::ForEach),
        _ => bail!("Invalid loop mode: {}", text),
    }
}

// Individual instruction parsers
fn parse_load(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let literal_idx = get_param_u16(&params, "literal_idx")?;
    Ok(Instruction::Load {
        dest: dest.try_into().unwrap(),
        literal_idx,
    })
}

fn parse_move(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let src = get_param_u16(&params, "src")?;
    Ok(Instruction::Move {
        dest: dest.try_into().unwrap(),
        src: src.try_into().unwrap(),
    })
}

fn parse_add(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Add {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_sub(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Sub {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_mul(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Mul {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_div(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Div {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_eq(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Eq {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_ne_instruction(content: &str) -> Result<Instruction> {
    let params = parse_params(content)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Ne {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_lt(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Lt {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_le_instruction(content: &str) -> Result<Instruction> {
    let params = parse_params(content)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Le {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_gt(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Gt {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_ge_instruction(content: &str) -> Result<Instruction> {
    let params = parse_params(content)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Ge {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_return(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let value = get_param_u16(&params, "value")?;
    Ok(Instruction::Return {
        value: value.try_into().unwrap(),
    })
}

fn parse_rule_init(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let result_reg = get_param_u16(&params, "result_reg")?;
    let rule_index = get_param_u16(&params, "rule_index")?;
    Ok(Instruction::RuleInit {
        result_reg: result_reg.try_into().unwrap(),
        rule_index,
    })
}

fn parse_rule_return(params_text: &str) -> Result<Instruction> {
    let _params = parse_params(params_text)?;
    Ok(Instruction::RuleReturn {})
}

fn parse_destructuring_success(params_text: &str) -> Result<Instruction> {
    let _params = parse_params(params_text)?;
    Ok(Instruction::DestructuringSuccess {})
}

fn parse_object_set(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let obj = get_param_u16(&params, "obj")?;
    let key = get_param_u16(&params, "key")?;
    let value = get_param_u16(&params, "value")?;
    Ok(Instruction::ObjectSet {
        obj: obj.try_into().unwrap(),
        key: key.try_into().unwrap(),
        value: value.try_into().unwrap(),
    })
}

fn parse_object_create(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::ObjectCreate { params_index })
}

fn parse_index(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let container = get_param_u16(&params, "container")?;
    let key = get_param_u16(&params, "key")?;
    Ok(Instruction::Index {
        dest: dest.try_into().unwrap(),
        container: container.try_into().unwrap(),
        key: key.try_into().unwrap(),
    })
}

fn parse_index_literal(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let container = get_param_u16(&params, "container")?;
    let literal_idx = get_param_u16(&params, "literal_idx")?;
    Ok(Instruction::IndexLiteral {
        dest: dest.try_into().unwrap(),
        container: container.try_into().unwrap(),
        literal_idx,
    })
}

fn parse_chained_index(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::ChainedIndex { params_index })
}

fn parse_array_new(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::ArrayNew {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_array_push(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let arr = get_param_u16(&params, "arr")?;
    let value = get_param_u16(&params, "value")?;
    Ok(Instruction::ArrayPush {
        arr: arr.try_into().unwrap(),
        value: value.try_into().unwrap(),
    })
}

fn parse_array_push_defined(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let arr = get_param_u16(&params, "arr")?;
    let value = get_param_u16(&params, "value")?;
    Ok(Instruction::ArrayPushDefined {
        arr: arr.try_into().unwrap(),
        value: value.try_into().unwrap(),
    })
}

fn parse_array_create(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::ArrayCreate { params_index })
}

fn parse_set_create(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::SetCreate { params_index })
}

fn parse_set_new(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::SetNew {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_set_add(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let set = get_param_u16(&params, "set")?;
    let value = get_param_u16(&params, "value")?;
    Ok(Instruction::SetAdd {
        set: set.try_into().unwrap(),
        value: value.try_into().unwrap(),
    })
}

fn parse_contains(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let collection = get_param_u16(&params, "collection")?;
    let value = get_param_u16(&params, "value")?;
    Ok(Instruction::Contains {
        dest: dest.try_into().unwrap(),
        collection: collection.try_into().unwrap(),
        value: value.try_into().unwrap(),
    })
}

fn parse_count(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let collection = get_param_u16(&params, "collection")?;
    Ok(Instruction::Count {
        dest: dest.try_into().unwrap(),
        collection: collection.try_into().unwrap(),
    })
}

fn parse_assert_eq(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let left: u8 = get_param_u16(&params, "left")?.try_into().unwrap();
    let right: u8 = get_param_u16(&params, "right")?.try_into().unwrap();
    Ok(Instruction::AssertEq { left, right })
}

fn parse_guard(params_text: &str, mode: GuardMode) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    // Accept the original field name for each mode so YAML tests don't change.
    let register: u8 = match mode {
        GuardMode::Not => get_param_u16(&params, "operand")?,
        GuardMode::Condition => get_param_u16(&params, "condition")?,
        GuardMode::NotUndefined => get_param_u16(&params, "register")?,
    }
    .try_into()
    .unwrap();
    Ok(Instruction::Guard { register, mode })
}

fn parse_loop_start(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;

    // Get params_index parameter - this should be specified in the test
    let params_index = get_param_u16(&params, "params_index")?;

    Ok(Instruction::LoopStart { params_index })
}

fn parse_loop_next(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let body_start = get_param_u16(&params, "body_start")?;
    let loop_end = get_param_u16(&params, "loop_end")?;
    Ok(Instruction::LoopNext {
        body_start,
        loop_end,
    })
}

fn parse_load_true(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadTrue {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_load_false(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadFalse {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_load_null(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadNull {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_load_bool(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let value = get_param_bool(&params, "value")?;
    Ok(Instruction::LoadBool {
        dest: dest.try_into().unwrap(),
        value,
    })
}

fn parse_load_data(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadData {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_load_input(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadInput {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_load_context(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadContext {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_load_metadata(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    Ok(Instruction::LoadMetadata {
        dest: dest.try_into().unwrap(),
    })
}

fn parse_mod(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Mod {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_and(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::And {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_or(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let left = get_param_u16(&params, "left")?;
    let right = get_param_u16(&params, "right")?;
    Ok(Instruction::Or {
        dest: dest.try_into().unwrap(),
        left: left.try_into().unwrap(),
        right: right.try_into().unwrap(),
    })
}

fn parse_not(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let operand = get_param_u16(&params, "operand")?;
    Ok(Instruction::Not {
        dest: dest.try_into().unwrap(),
        operand: operand.try_into().unwrap(),
    })
}

fn parse_builtin_call(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::BuiltinCall { params_index })
}

fn parse_function_call(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::FunctionCall { params_index })
}

fn parse_call_rule(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let rule_index = get_param_u16(&params, "rule_index")?;
    Ok(Instruction::CallRule {
        dest: dest.try_into().unwrap(),
        rule_index,
    })
}

fn parse_virtual_data_document_lookup(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::VirtualDataDocumentLookup { params_index })
}

fn parse_host_await(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest = get_param_u16(&params, "dest")?;
    let arg = get_param_u16(&params, "arg")?;
    let id = get_param_u16(&params, "id")?;
    Ok(Instruction::HostAwait {
        dest: dest.try_into().unwrap(),
        arg: arg.try_into().unwrap(),
        id: id.try_into().unwrap(),
    })
}

fn parse_comprehension_start(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let params_index = get_param_u16(&params, "params_index")?;
    Ok(Instruction::ComprehensionBegin { params_index })
}

fn parse_comprehension_add(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let value_reg = get_param_u16(&params, "value_reg")?;
    let key_reg = if let Ok(key) = get_param_u16(&params, "key_reg") {
        Some(key.try_into().unwrap())
    } else {
        None
    };
    Ok(Instruction::ComprehensionYield {
        value_reg: value_reg.try_into().unwrap(),
        key_reg,
    })
}

fn parse_return_undefined_if_not_true(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let condition = get_param_u16(&params, "condition")?;
    Ok(Instruction::ReturnUndefinedIfNotTrue {
        condition: condition.try_into().unwrap(),
    })
}

fn parse_coalesce_undefined_to_null(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let register = get_param_u16(&params, "register")?;
    Ok(Instruction::CoalesceUndefinedToNull {
        register: register.try_into().unwrap(),
    })
}

/// Generic parser for PolicyCondition instructions with { dest, left, right } fields.
fn parse_policy_condition(params_text: &str, op: PolicyOp) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest: u8 = get_param_u16(&params, "dest")?.try_into().unwrap();
    let left: u8 = get_param_u16(&params, "left")?.try_into().unwrap();
    let right: u8 = get_param_u16(&params, "right")?.try_into().unwrap();
    Ok(Instruction::PolicyCondition {
        dest,
        left,
        right,
        op,
    })
}

fn parse_value_condition_guard(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest: u8 = get_param_u16(&params, "dest")?.try_into().unwrap();
    let value: u8 = get_param_u16(&params, "value")?.try_into().unwrap();
    let condition: u8 = get_param_u16(&params, "condition")?.try_into().unwrap();
    Ok(Instruction::PolicyCondition {
        dest,
        left: value,
        right: condition,
        op: PolicyOp::ValueConditionGuard,
    })
}

fn parse_policy_not(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let dest: u8 = get_param_u16(&params, "dest")?.try_into().unwrap();
    let operand: u8 = get_param_u16(&params, "operand")?.try_into().unwrap();
    Ok(Instruction::PolicyCondition {
        dest,
        left: operand,
        right: 0,
        op: PolicyOp::Not,
    })
}

fn parse_logical_block_start(params_text: &str, mode: LogicalBlockMode) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let result: u8 = get_param_u16(&params, "result")?.try_into().unwrap();
    let end_pc = get_param_u16(&params, "end_pc")?;
    Ok(Instruction::LogicalBlockStart {
        mode,
        result,
        end_pc,
    })
}

fn parse_allof_next(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let check: u8 = get_param_u16(&params, "check")?.try_into().unwrap();
    let result: u8 = get_param_u16(&params, "result")?.try_into().unwrap();
    let end_pc = get_param_u16(&params, "end_pc")?;
    Ok(Instruction::AllOfNext {
        check,
        result,
        end_pc,
    })
}

fn parse_logical_block_end(params_text: &str, mode: LogicalBlockMode) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let result: u8 = get_param_u16(&params, "result")?.try_into().unwrap();
    Ok(Instruction::LogicalBlockEnd { mode, result })
}

fn parse_anyof_next(params_text: &str) -> Result<Instruction> {
    let params = parse_params(params_text)?;
    let check: u8 = get_param_u16(&params, "check")?.try_into().unwrap();
    let result: u8 = get_param_u16(&params, "result")?.try_into().unwrap();
    let end_pc = get_param_u16(&params, "end_pc")?;
    Ok(Instruction::AnyOfNext {
        check,
        result,
        end_pc,
    })
}

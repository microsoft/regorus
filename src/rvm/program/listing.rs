// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::option_if_let_else)]

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use core::fmt::{self, Write as _};

use crate::rvm::{
    instructions::{Instruction, InstructionData, LoopMode},
    program::Program,
};

// Writing into a String via fmt never fails, so we intentionally ignore writeln! results.
fn push_line(buf: &mut String, args: fmt::Arguments) {
    let _ = buf.write_fmt(args);
    let _ = buf.write_char('\n');
}

/// Configuration for assembly listing output
#[derive(Debug, Clone)]
pub struct AssemblyListingConfig {
    /// Show instruction addresses
    pub show_addresses: bool,
    /// Show raw instruction bytes (if available)
    pub show_bytes: bool,
    /// Indent size for nested loops
    pub indent_size: usize,
    /// Maximum width for instruction column
    pub instruction_width: usize,
    /// Show literal values inline
    pub show_literal_values: bool,
    /// Column position for comments
    pub comment_column: usize,
}

impl Default for AssemblyListingConfig {
    fn default() -> Self {
        Self {
            show_addresses: true,
            show_bytes: false,
            indent_size: 4,
            instruction_width: 40,
            show_literal_values: true,
            comment_column: 50,
        }
    }
}

/// Generate annotated assembly listing for a compiled program
pub fn generate_assembly_listing(program: &Program, config: &AssemblyListingConfig) -> String {
    let mut output = String::new();
    let mut indent_level: usize = 0;
    let mut current_rule_index: Option<u16> = None;

    // Track active loops and comprehensions by their end addresses
    let mut active_ends: Vec<u16> = Vec::new();

    // Add header
    push_line(
        &mut output,
        format_args!(
            "; RVM Assembly - {} instructions, {} literals, {} builtins",
            program.instructions.len(),
            program.literals.len(),
            program.builtin_info_table.len()
        ),
    );

    // Add builtins table
    if !program.builtin_info_table.is_empty() {
        push_line(&mut output, format_args!(";"));
        push_line(&mut output, format_args!("; BUILTINS TABLE:"));
        for (idx, builtin_info) in program.builtin_info_table.iter().enumerate() {
            push_line(
                &mut output,
                format_args!(";   B{:2}: {}", idx, builtin_info.name),
            );
        }
    }

    // Add literals table
    if config.show_literal_values && !program.literals.is_empty() {
        push_line(&mut output, format_args!(";"));
        push_line(&mut output, format_args!("; LITERALS (JSON values):"));
        for (idx, literal) in program.literals.iter().enumerate() {
            let literal_json =
                serde_json::to_string(literal).unwrap_or_else(|_| "<invalid>".to_string());
            push_line(
                &mut output,
                format_args!(";   L{:2}: {}", idx, literal_json),
            );
        }
    }

    // Add rules table if available
    if !program.rule_infos.is_empty() {
        push_line(&mut output, format_args!(";"));
        push_line(&mut output, format_args!("; RULES TABLE:"));
        for (idx, rule_info) in program.rule_infos.iter().enumerate() {
            push_line(
                &mut output,
                format_args!(";   R{:2}: {}", idx, rule_info.name),
            );
        }
    }

    push_line(&mut output, format_args!(";"));

    for (pc, instruction) in program.instructions.iter().enumerate() {
        // Handle rule transitions and add gaps
        if let &Instruction::RuleInit { rule_index, .. } = instruction {
            // Add gap before new rule (except for the first rule)
            if current_rule_index.is_some() {
                push_line(&mut output, format_args!(""));
            }
            current_rule_index = Some(rule_index);

            // Add rule name prefix
            if let Some(rule_info) = program.rule_infos.get(usize::from(rule_index)) {
                push_line(
                    &mut output,
                    format_args!("; ===== RULE: {} =====", rule_info.name),
                );
            } else {
                push_line(
                    &mut output,
                    format_args!("; ===== RULE: rule_{} =====", rule_index),
                );
            }
        }

        // Check if current PC matches any active end addresses (loops, comprehensions, rules)
        let current_pc = u16::try_from(pc).unwrap_or(u16::MAX);
        while let Some(&end_addr) = active_ends.last() {
            if current_pc >= end_addr {
                active_ends.pop();
                indent_level = indent_level.saturating_sub(1);
            } else {
                break;
            }
        }

        // Handle explicit end instructions
        match *instruction {
            Instruction::LoopNext { .. } => {
                // LoopNext already handled by end address tracking above
            }
            Instruction::RuleReturn { .. } => {
                indent_level = indent_level.saturating_sub(1);
            }
            _ => {}
        }

        // Special case: Block end instructions should be indented at their block level (one level out)
        let effective_indent_level = match *instruction {
            Instruction::ComprehensionEnd {} => indent_level.saturating_sub(1),
            Instruction::LoopNext { .. } => indent_level.saturating_sub(1),
            _ => indent_level,
        };

        let indent = " ".repeat(effective_indent_level.saturating_mul(config.indent_size));

        // Format address
        let addr_str = if config.show_addresses {
            format!("{:03}: ", pc)
        } else {
            String::new()
        };

        // Format instruction with proper indentation and aligned comments
        let inst_str = format_instruction_readable(
            instruction,
            &indent,
            &program.instruction_data,
            program,
            config,
        );

        push_line(&mut output, format_args!("{}{}", addr_str, inst_str));

        // Increase indentation for loop/rule/comprehension starts and track their end addresses
        match *instruction {
            Instruction::LoopStart { params_index } => {
                if let Some(params) = program.instruction_data.get_loop_params(params_index) {
                    active_ends.push(params.loop_end);
                    indent_level = indent_level.saturating_add(1);
                }
            }
            Instruction::ComprehensionBegin { params_index } => {
                if let Some(params) = program
                    .instruction_data
                    .get_comprehension_begin_params(params_index)
                {
                    active_ends.push(params.comprehension_end);
                    indent_level = indent_level.saturating_add(1);
                }
            }
            Instruction::RuleInit { .. } => {
                indent_level = indent_level.saturating_add(1);
                // Note: Rules end with RuleReturn, not an address, so we don't track them here
            }
            _ => {}
        }
    }

    output
}

/// Helper function to align comments at a specific column
fn align_comment(base_text: &str, comment: &str, target_column: usize) -> String {
    let current_len = base_text.len();
    if current_len >= target_column {
        format!("{} ; {}", base_text, comment)
    } else {
        let padding = " ".repeat(target_column.saturating_sub(current_len));
        format!("{}{} ; {}", base_text, padding, comment)
    }
}

/// Format a single instruction with proper indentation and mathematical notation
fn format_instruction_readable(
    instruction: &Instruction,
    indent: &str,
    instruction_data: &InstructionData,
    program: &Program,
    config: &AssemblyListingConfig,
) -> String {
    match *instruction {
        Instruction::Load { dest, literal_idx } => {
            let base = format!("{}Load         r{} ← L{}", indent, dest, literal_idx);
            let comment = match program.literals.get(usize::from(literal_idx)) {
                Some(literal) => {
                    let literal_json =
                        serde_json::to_string(literal).unwrap_or_else(|_| "<invalid>".to_string());
                    format!("Load literal: {}", literal_json)
                }
                None => "Load literal: <invalid index>".to_string(),
            };
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::LoadTrue { dest } => {
            let base = format!("{}LoadTrue     r{} ← true", indent, dest);
            align_comment(&base, "Load boolean constant true", config.comment_column)
        }
        Instruction::LoadFalse { dest } => {
            let base = format!("{}LoadFalse    r{} ← false", indent, dest);
            align_comment(&base, "Load boolean constant false", config.comment_column)
        }
        Instruction::LoadNull { dest } => {
            let base = format!("{}LoadNull     r{} ← null", indent, dest);
            align_comment(&base, "Load null value", config.comment_column)
        }
        Instruction::LoadBool { dest, value } => {
            let base = format!("{}LoadBool     r{} ← {}", indent, dest, value);
            let comment = format!("Load boolean constant {}", value);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::LoadData { dest } => {
            let base = format!("{}LoadData     r{} ← data", indent, dest);
            align_comment(&base, "Load global data document", config.comment_column)
        }
        Instruction::LoadInput { dest } => {
            let base = format!("{}LoadInput    r{} ← input", indent, dest);
            align_comment(&base, "Load global input document", config.comment_column)
        }
        Instruction::Move { dest, src } => {
            let base = format!("{}Move         r{} ← r{}", indent, dest, src);
            let comment = format!("Copy value from r{} to r{}", src, dest);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Add { dest, left, right } => {
            let base = format!("{}Add          r{} ← r{} + r{}", indent, dest, left, right);
            let comment = format!("Arithmetic addition: r{} + r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Sub { dest, left, right } => {
            let base = format!("{}Sub          r{} ← r{} - r{}", indent, dest, left, right);
            let comment = format!("Arithmetic subtraction: r{} - r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Mul { dest, left, right } => {
            let base = format!("{}Mul          r{} ← r{} × r{}", indent, dest, left, right);
            let comment = format!("Arithmetic multiplication: r{} × r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Div { dest, left, right } => {
            let base = format!("{}Div          r{} ← r{} ÷ r{}", indent, dest, left, right);
            let comment = format!("Arithmetic division: r{} ÷ r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Mod { dest, left, right } => {
            let base = format!(
                "{}Mod          r{} ← r{} mod r{}",
                indent, dest, left, right
            );
            let comment = format!("Modulo operation: r{} mod r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Eq { dest, left, right } => {
            let base = format!(
                "{}Eq           r{} ← (r{} = r{})",
                indent, dest, left, right
            );
            let comment = format!("Equality test: r{} == r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Ne { dest, left, right } => {
            let base = format!(
                "{}Ne           r{} ← (r{} ≠ r{})",
                indent, dest, left, right
            );
            let comment = format!("Inequality test: r{} != r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Lt { dest, left, right } => {
            let base = format!(
                "{}Lt           r{} ← (r{} < r{})",
                indent, dest, left, right
            );
            let comment = format!("Less than comparison: r{} < r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Le { dest, left, right } => {
            let base = format!(
                "{}Le           r{} ← (r{} ≤ r{})",
                indent, dest, left, right
            );
            let comment = format!("Less or equal comparison: r{} <= r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Gt { dest, left, right } => {
            let base = format!(
                "{}Gt           r{} ← (r{} > r{})",
                indent, dest, left, right
            );
            let comment = format!("Greater than comparison: r{} > r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Ge { dest, left, right } => {
            let base = format!(
                "{}Ge           r{} ← (r{} ≥ r{})",
                indent, dest, left, right
            );
            let comment = format!("Greater or equal comparison: r{} >= r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::And { dest, left, right } => {
            let base = format!("{}And          r{} ← r{} ∧ r{}", indent, dest, left, right);
            let comment = format!("Logical AND: r{} && r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Or { dest, left, right } => {
            let base = format!("{}Or           r{} ← r{} ∨ r{}", indent, dest, left, right);
            let comment = format!("Logical OR: r{} || r{}", left, right);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Not { dest, operand } => {
            let base = format!("{}Not          r{} ← ¬r{}", indent, dest, operand);
            let comment = format!("Logical NOT: !r{}", operand);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::BuiltinCall { params_index } => {
            if let Some(params) = instruction_data.get_builtin_call_params(params_index) {
                let args_str = params
                    .arg_registers()
                    .iter()
                    .map(|&r| format!("r{}", r))
                    .collect::<Vec<_>>()
                    .join(", ");

                let builtin_name = program
                    .builtin_info_table
                    .get(usize::from(params.builtin_index))
                    .map(|info| info.name.as_str())
                    .unwrap_or("<invalid>");

                let base = format!(
                    "{}BuiltinCall  r{} ← {}({})",
                    indent, params.dest, builtin_name, args_str
                );
                let comment = format!(
                    "Call builtin '{}' (B{}) with {} args",
                    builtin_name, params.builtin_index, params.num_args
                );
                align_comment(&base, &comment, config.comment_column)
            } else {
                let base = format!("{}BuiltinCall  [INVALID P({})]", indent, params_index);
                align_comment(
                    &base,
                    "ERROR: Invalid builtin call parameters",
                    config.comment_column,
                )
            }
        }
        Instruction::FunctionCall { params_index } => {
            if let Some(params) = instruction_data.get_function_call_params(params_index) {
                let args_str = params
                    .arg_registers()
                    .iter()
                    .map(|&r| format!("r{}", r))
                    .collect::<Vec<_>>()
                    .join(", ");

                let func_name = program
                    .rule_infos
                    .get(usize::from(params.func_rule_index))
                    .map(|info| info.name.as_str())
                    .unwrap_or("<invalid>");

                let base = format!(
                    "{}FunctionCall r{} ← {}({})",
                    indent, params.dest, func_name, args_str
                );
                let comment = format!(
                    "Call function '{}' (R{}) with {} args",
                    func_name, params.func_rule_index, params.num_args
                );
                align_comment(&base, &comment, config.comment_column)
            } else {
                let base = format!("{}FunctionCall [INVALID P({})]", indent, params_index);
                align_comment(
                    &base,
                    "ERROR: Invalid function call parameters",
                    config.comment_column,
                )
            }
        }
        Instruction::HostAwait { dest, arg, id } => {
            let base = format!(
                "{}HostAwait    r{} ← await r{} (id r{})",
                indent, dest, arg, id
            );
            align_comment(
                &base,
                &format!(
                    "Suspend and request host result using r{} with identifier r{}",
                    arg, id
                ),
                config.comment_column,
            )
        }
        Instruction::Return { value } => {
            let base = format!("{}Return       return r{}", indent, value);
            let comment = format!("Return value from r{}", value);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::ObjectSet { obj, key, value } => {
            let base = format!("{}ObjectSet    r{}[r{}] ← r{}", indent, obj, key, value);
            let comment = format!("Set field r{}[r{}] = r{}", obj, key, value);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::ObjectCreate { params_index } => {
            let params = program
                .instruction_data
                .get_object_create_params(params_index);
            let base = format!(
                "{}ObjectCreate r{} ← {{...}}",
                indent,
                params.map_or(0, |p| p.dest)
            );
            let comment = match params {
                Some(p) => format!(
                    "Create object with {} fields (P{})",
                    p.field_count(),
                    params_index
                ),
                None => format!("Create object (P{} - INVALID)", params_index),
            };
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Index {
            dest,
            container,
            key,
        } => {
            let base = format!(
                "{}Index        r{} ← r{}[r{}]",
                indent, dest, container, key
            );
            let comment = format!("Index operation: get r{}[r{}]", container, key);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::IndexLiteral {
            dest,
            container,
            literal_idx,
        } => {
            let base = format!(
                "{}IndexLiteral r{} ← r{}[L{}]",
                indent, dest, container, literal_idx
            );
            let comment = match program.literals.get(usize::from(literal_idx)) {
                Some(literal) => {
                    let literal_json =
                        serde_json::to_string(literal).unwrap_or_else(|_| "<invalid>".to_string());
                    format!("Index with literal key: r{}[{}]", container, literal_json)
                }
                None => format!(
                    "Index with literal: r{}[L{}] (invalid index)",
                    container, literal_idx
                ),
            };
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::ArrayNew { dest } => {
            let base = format!("{}ArrayNew     r{} ← []", indent, dest);
            align_comment(&base, "Create new empty array", config.comment_column)
        }
        Instruction::ArrayPush { arr, value } => {
            let base = format!("{}ArrayPush    r{}.push(r{})", indent, arr, value);
            let comment = format!("Append r{} to array r{}", value, arr);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::ArrayCreate { params_index } => {
            if let Some(params) = instruction_data.get_array_create_params(params_index) {
                let elements = params
                    .element_registers()
                    .iter()
                    .map(|r| format!("r{}", r))
                    .collect::<Vec<_>>()
                    .join(", ");
                let base = format!("{}ArrayCreate  r{} ← [{}]", indent, params.dest, elements);
                let comment = format!(
                    "Create array from {} elements (undefined if any element is undefined)",
                    params.element_count()
                );
                align_comment(&base, &comment, config.comment_column)
            } else {
                format!("{}ArrayCreate  <invalid params P{}>", indent, params_index)
            }
        }
        Instruction::SetNew { dest } => {
            let base = format!("{}SetNew       r{} ← set()", indent, dest);
            align_comment(&base, "Create new empty set", config.comment_column)
        }
        Instruction::SetAdd { set, value } => {
            let base = format!("{}SetAdd       r{} ∪= r{}", indent, set, value);
            let comment = format!("Add r{} to set r{}", value, set);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::SetCreate { params_index } => {
            if let Some(params) = instruction_data.get_set_create_params(params_index) {
                let elements = params
                    .element_registers()
                    .iter()
                    .map(|r| format!("r{}", r))
                    .collect::<Vec<_>>()
                    .join(", ");
                let base = format!("{}SetCreate    r{} ← {{{}}}", indent, params.dest, elements);
                let comment = format!(
                    "Create set from {} elements (undefined if any element is undefined)",
                    params.element_count()
                );
                align_comment(&base, &comment, config.comment_column)
            } else {
                format!("{}SetCreate    <invalid params P{}>", indent, params_index)
            }
        }
        Instruction::Contains {
            dest,
            collection,
            value,
        } => {
            let base = format!(
                "{}Contains     r{} ← (r{} ∈ r{})",
                indent, dest, value, collection
            );
            let comment = format!("Membership test: r{} in r{}", value, collection);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::Count { dest, collection } => {
            let base = format!("{}Count        r{} ← count(r{})", indent, dest, collection);
            let comment = format!("Get count/length of collection r{}", collection);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::AssertCondition { condition } => {
            let base = format!("{}Assert       assert r{}", indent, condition);
            let comment = format!("Assert r{} is true (exit if false/undefined)", condition);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::AssertNotUndefined { register } => {
            let base = format!(
                "{}AssertNotUndefined assert_not_undefined r{}",
                indent, register
            );
            let comment = format!("Assert r{} is not undefined (exit if undefined)", register);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::LoopStart { params_index } => {
            if let Some(params) = instruction_data.get_loop_params(params_index) {
                let mode_str = match params.mode {
                    LoopMode::Any => "any",
                    LoopMode::Every => "every",
                    LoopMode::ForEach => "foreach",
                };
                let base = format!(
                    "{}LoopStart    {} r{},r{} in r{} → r{} {{",
                    indent,
                    mode_str,
                    params.key_reg,
                    params.value_reg,
                    params.collection,
                    params.result_reg
                );
                let comment = format!(
                    "{} loop over r{}, body: {}-{} (P{})",
                    mode_str, params.collection, params.body_start, params.loop_end, params_index
                );
                align_comment(&base, &comment, config.comment_column)
            } else {
                let base = format!("{}LoopStart    [INVALID P({})] {{", indent, params_index);
                align_comment(
                    &base,
                    "ERROR: Invalid loop parameters",
                    config.comment_column,
                )
            }
        }
        Instruction::LoopNext {
            body_start,
            loop_end,
        } => {
            let base = format!(
                "{}}} continue → {} or exit → {}",
                indent, body_start, loop_end
            );
            let comment = format!(
                "Next iteration or exit loop (body:{}-{})",
                body_start, loop_end
            );
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::CallRule { dest, rule_index } => {
            let rule_name = program
                .rule_infos
                .get(usize::from(rule_index))
                .map(|info| info.name.as_str())
                .unwrap_or("<invalid>");

            let base = format!("{}CallRule     r{} ← {}", indent, dest, rule_name);
            let comment = format!("Call rule '{}' (R{}) with caching", rule_name, rule_index);
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::RuleInit {
            result_reg,
            rule_index,
        } => {
            let rule_name = program
                .rule_infos
                .get(usize::from(rule_index))
                .map(|info| info.name.as_str())
                .unwrap_or("<invalid>");

            let base = format!("{}RuleInit     {} → r{} {{", indent, rule_name, result_reg);
            let comment = format!(
                "Initialize rule '{}' (R{}) evaluation",
                rule_name, rule_index
            );
            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::RuleReturn {} => {
            let base = format!("{}}} return from rule", indent);
            align_comment(&base, "End of rule evaluation", config.comment_column)
        }
        Instruction::ChainedIndex { params_index } => {
            let (base, comment) =
                if let Some(params) = instruction_data.get_chained_index_params(params_index) {
                    let chain_parts: Vec<String> = params
                        .path_components
                        .iter()
                        .map(|component| match *component {
                            crate::rvm::instructions::LiteralOrRegister::Literal(idx) => {
                                if let Some(literal) = program.literals.get(usize::from(idx)) {
                                    match *literal {
                                        crate::Value::String(ref s) => format!(".{}", s.as_ref()),
                                        ref other => format!(
                                            "[{}]",
                                            serde_json::to_string(other)
                                                .unwrap_or_else(|_| "?".to_string())
                                        ),
                                    }
                                } else {
                                    format!("[L{}?]", idx)
                                }
                            }
                            crate::rvm::instructions::LiteralOrRegister::Register(reg) => {
                                format!("[r{}]", reg)
                            }
                        })
                        .collect();

                    let chain_display = if chain_parts.is_empty() {
                        String::new()
                    } else {
                        format!(" r{}{}", params.root, chain_parts.join(""))
                    };

                    let base_str = format!(
                        "{}ChainedIndex r{} ← r{}{}",
                        indent, params.dest, params.root, chain_display
                    );
                    let comment_str = format!(
                        "Multi-level chained indexing: r{} → r{}",
                        params.root, params.dest
                    );
                    (base_str, comment_str)
                } else {
                    let base_str = format!("{}ChainedIndex chained_index", indent);
                    let comment_str = "Multi-level chained indexing (invalid params)".to_string();
                    (base_str, comment_str)
                };

            align_comment(&base, &comment, config.comment_column)
        }
        Instruction::VirtualDataDocumentLookup { .. } => {
            let base = format!(
                "{}VirtualDataDocumentLookup virtual_data_document_lookup",
                indent
            );
            align_comment(
                &base,
                "Lookup in data namespace virtual documents",
                config.comment_column,
            )
        }
        Instruction::DestructuringSuccess {} => {
            let base = format!("{}DestructuringSuccess ✓", indent);
            align_comment(
                &base,
                "Parameter destructuring validated",
                config.comment_column,
            )
        }
        Instruction::Halt {} => {
            let base = format!("{}Halt         halt", indent);
            align_comment(&base, "Stop execution", config.comment_column)
        }
        Instruction::ComprehensionBegin { params_index } => {
            if let Some(params) = instruction_data.get_comprehension_begin_params(params_index) {
                let mode_str = match params.mode {
                    crate::rvm::instructions::ComprehensionMode::Array => "array",
                    crate::rvm::instructions::ComprehensionMode::Set => "set",
                    crate::rvm::instructions::ComprehensionMode::Object => "object",
                };
                let (source_desc, result_desc) = if params.collection_reg == params.result_reg {
                    (
                        format!("r{}", params.collection_reg),
                        format!("r{}", params.result_reg),
                    )
                } else {
                    (
                        format!("r{} (src)", params.collection_reg),
                        format!("r{} (dst)", params.result_reg),
                    )
                };
                let base = format!(
                    "{}CompBegin   {} {} → {} k:{} v:{} {{",
                    indent, mode_str, source_desc, result_desc, params.key_reg, params.value_reg
                );
                let comment = format!(
                    "{} comprehension in r{}, body: {}-{} (P{})",
                    mode_str,
                    params.collection_reg,
                    params.body_start,
                    params.comprehension_end,
                    params_index
                );
                align_comment(&base, &comment, config.comment_column)
            } else {
                let base = format!("{}CompBegin   [INVALID P({})] {{", indent, params_index);
                align_comment(
                    &base,
                    "ERROR: Invalid comprehension parameters",
                    config.comment_column,
                )
            }
        }
        Instruction::ComprehensionYield { value_reg, key_reg } => {
            let base = match key_reg {
                Some(k) => format!("{}CompYield    r{} r{}", indent, k, value_reg),
                None => format!("{}CompYield    r{}", indent, value_reg),
            };
            align_comment(&base, "Yield value to comprehension", config.comment_column)
        }
        Instruction::ComprehensionEnd {} => {
            let base = format!("{}}} CompEnd", indent);
            align_comment(&base, "End comprehension block", config.comment_column)
        }
    }
}

/// Generate compact tabular assembly listing
pub fn generate_tabular_assembly_listing(
    program: &Program,
    _config: &AssemblyListingConfig,
) -> String {
    let mut output = String::new();
    let mut indent_level: usize = 0;

    // Add header
    push_line(&mut output, format_args!("; RVM Assembly (Tabular Format)"));
    push_line(
        &mut output,
        format_args!(
            "; {} instructions, {} literals",
            program.instructions.len(),
            program.literals.len()
        ),
    );
    push_line(&mut output, format_args!(";"));
    push_line(
        &mut output,
        format_args!("; PC  | Instruction  | Operation"),
    );
    push_line(
        &mut output,
        format_args!(";-----|--------------|----------"),
    );

    for (pc, instruction) in program.instructions.iter().enumerate() {
        // Handle loop indentation
        match *instruction {
            Instruction::LoopNext { .. } => {
                indent_level = indent_level.saturating_sub(1);
            }
            Instruction::RuleReturn { .. } => {
                indent_level = indent_level.saturating_sub(1);
            }
            _ => {}
        }

        let indent = " ".repeat(indent_level.saturating_mul(2)); // Smaller indent for tabular format

        // Format in tabular style
        let addr_str = format!("{:03}", pc);
        let inst_name = get_instruction_name(instruction);
        let operation =
            format_operation_compact(instruction, &indent, &program.instruction_data, program);

        push_line(
            &mut output,
            format_args!("{:>4} | {:12} | {}", addr_str, inst_name, operation),
        );

        // Increase indentation for loop/rule starts
        match *instruction {
            Instruction::LoopStart { .. } => {
                indent_level = indent_level.saturating_add(1);
            }
            Instruction::RuleInit { .. } => {
                indent_level = indent_level.saturating_add(1);
            }
            _ => {}
        }
    }

    output
}

const fn get_instruction_name(instruction: &Instruction) -> &'static str {
    match *instruction {
        Instruction::Load { .. } => "LOAD",
        Instruction::LoadTrue { .. } => "LOAD_TRUE",
        Instruction::LoadFalse { .. } => "LOAD_FALSE",
        Instruction::LoadNull { .. } => "LOAD_NULL",
        Instruction::LoadBool { .. } => "LOAD_BOOL",
        Instruction::LoadData { .. } => "LOAD_DATA",
        Instruction::LoadInput { .. } => "LOAD_INPUT",
        Instruction::Move { .. } => "MOVE",
        Instruction::Add { .. } => "ADD",
        Instruction::Sub { .. } => "SUB",
        Instruction::Mul { .. } => "MUL",
        Instruction::Div { .. } => "DIV",
        Instruction::Mod { .. } => "MOD",
        Instruction::Eq { .. } => "EQ",
        Instruction::Ne { .. } => "NE",
        Instruction::Lt { .. } => "LT",
        Instruction::Le { .. } => "LE",
        Instruction::Gt { .. } => "GT",
        Instruction::Ge { .. } => "GE",
        Instruction::And { .. } => "AND",
        Instruction::Or { .. } => "OR",
        Instruction::Not { .. } => "NOT",
        Instruction::BuiltinCall { .. } => "BUILTIN_CALL",
        Instruction::FunctionCall { .. } => "FUNC_CALL",
        Instruction::HostAwait { .. } => "HOST_AWAIT",
        Instruction::Return { .. } => "RETURN",
        Instruction::ObjectSet { .. } => "OBJ_SET",
        Instruction::ObjectCreate { .. } => "OBJ_CREATE",
        Instruction::Index { .. } => "INDEX",
        Instruction::IndexLiteral { .. } => "INDEX_LIT",
        Instruction::ArrayNew { .. } => "ARRAY_NEW",
        Instruction::ArrayPush { .. } => "ARRAY_PUSH",
        Instruction::ArrayCreate { .. } => "ARRAY_CREATE",
        Instruction::SetNew { .. } => "SET_NEW",
        Instruction::SetAdd { .. } => "SET_ADD",
        Instruction::SetCreate { .. } => "SET_CREATE",
        Instruction::Contains { .. } => "CONTAINS",
        Instruction::Count { .. } => "COUNT",
        Instruction::AssertCondition { .. } => "ASSERT",
        Instruction::AssertNotUndefined { .. } => "ASSERT_NOT_UNDEF",
        Instruction::LoopStart { .. } => "LOOP_START",
        Instruction::LoopNext { .. } => "LOOP_NEXT",
        Instruction::CallRule { .. } => "CALL_RULE",
        Instruction::RuleInit { .. } => "RULE_INIT",
        Instruction::RuleReturn { .. } => "RULE_RET",
        Instruction::DestructuringSuccess {} => "DESTRUCT_SUCCESS",
        Instruction::ChainedIndex { .. } => "CHAINED_INDEX",
        Instruction::VirtualDataDocumentLookup { .. } => "VIRTUAL_DATA_DOC_LOOKUP",
        Instruction::Halt {} => "HALT",
        Instruction::ComprehensionBegin { .. } => "COMP_BEGIN",
        Instruction::ComprehensionYield { .. } => "COMP_YIELD",
        Instruction::ComprehensionEnd {} => "COMP_END",
    }
}

fn format_operation_compact(
    instruction: &Instruction,
    indent: &str,
    instruction_data: &InstructionData,
    _program: &Program,
) -> String {
    match *instruction {
        Instruction::Load { dest, literal_idx } => {
            format!("{}r{} ← L{}", indent, dest, literal_idx)
        }
        Instruction::LoadInput { dest } => {
            format!("{}r{} ← input", indent, dest)
        }
        Instruction::LoadData { dest } => {
            format!("{}r{} ← data", indent, dest)
        }
        Instruction::Move { dest, src } => {
            format!("{}r{} ← r{}", indent, dest, src)
        }
        Instruction::Add { dest, left, right } => {
            format!("{}r{} ← r{} + r{}", indent, dest, left, right)
        }
        Instruction::Index {
            dest,
            container,
            key,
        } => {
            format!("{}r{} ← r{}[r{}]", indent, dest, container, key)
        }
        Instruction::IndexLiteral {
            dest,
            container,
            literal_idx,
        } => {
            format!("{}r{} ← r{}[L{}]", indent, dest, container, literal_idx)
        }
        Instruction::LoopStart { params_index } => {
            if let Some(params) = instruction_data.get_loop_params(params_index) {
                format!(
                    "{}loop r{} in r{} {{",
                    indent, params.value_reg, params.collection
                )
            } else {
                format!("{}loop P({}) {{", indent, params_index)
            }
        }
        Instruction::LoopNext { .. } => {
            format!("{}}}", indent)
        }
        Instruction::CallRule { dest, rule_index } => {
            format!("{}r{} ← rule_{}", indent, dest, rule_index)
        }
        Instruction::HostAwait { dest, arg, id } => {
            format!("{}await r{} → r{} (id r{})", indent, arg, dest, id)
        }
        Instruction::RuleInit {
            result_reg,
            rule_index,
        } => {
            format!("{}rule_{} → r{} {{", indent, rule_index, result_reg)
        }
        Instruction::RuleReturn {} => {
            format!("{}}}", indent)
        }
        Instruction::DestructuringSuccess {} => {
            format!("{}✓ destructuring validated", indent)
        }
        _ => {
            // For other instructions, use a simplified version
            format!(
                "{}{}",
                indent,
                instruction
                    .to_string()
                    .replace("R(", "r")
                    .replace(")", "")
                    .replace("L(", "L")
            )
        }
    }
}

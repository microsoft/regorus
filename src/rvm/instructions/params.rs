// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};

use super::types::{ComprehensionMode, LiteralOrRegister, LoopMode};

/// Loop parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoopStartParams {
    /// Loop mode (Existential/Universal/Comprehension types)
    pub mode: LoopMode,
    /// Register containing the collection to iterate over
    pub collection: u8,
    /// Register to store current key (same as value_reg if key not needed)
    pub key_reg: u8,
    /// Register to store current value
    pub value_reg: u8,
    /// Register to store final result
    pub result_reg: u8,
    /// Jump target for loop body start
    pub body_start: u16,
    /// Jump target for loop end
    pub loop_end: u16,
}

/// Builtin function call parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuiltinCallParams {
    /// Destination register to store the result
    pub dest: u8,
    /// Index into program's builtin_info_table
    pub builtin_index: u16,
    /// Number of arguments actually used
    pub num_args: u8,
    /// Argument register numbers (unused slots contain undefined values)
    pub args: [u8; 8],
}

impl BuiltinCallParams {
    /// Get the number of arguments actually used
    pub fn arg_count(&self) -> usize {
        usize::from(self.num_args)
    }

    /// Get argument register numbers as a slice
    pub fn arg_registers(&self) -> &[u8] {
        let count = usize::from(self.num_args).min(self.args.len());
        self.args.get(..count).unwrap_or(&[])
    }
}

/// Function rule call parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionCallParams {
    /// Destination register to store the result
    pub dest: u8,
    /// Rule index of the function to call
    pub func_rule_index: u16,
    /// Number of arguments actually used
    pub num_args: u8,
    /// Argument register numbers (unused slots contain undefined values)
    pub args: [u8; 8],
}

impl FunctionCallParams {
    /// Get the number of arguments actually used
    pub fn arg_count(&self) -> usize {
        usize::from(self.num_args)
    }

    /// Get argument register numbers as a slice
    pub fn arg_registers(&self) -> &[u8] {
        let count = usize::from(self.num_args).min(self.args.len());
        self.args.get(..count).unwrap_or(&[])
    }
}

/// Object creation parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObjectCreateParams {
    /// Destination register to store the result object
    pub dest: u8,
    /// Literal index of template object with all keys (undefined values)
    /// Always present - empty object if no literal keys
    pub template_literal_idx: u16,
    /// Fields with literal keys: (literal_key_index, value_register) in sorted order
    pub literal_key_fields: Vec<(u16, u8)>,
    /// Fields with non-literal keys: (key_register, value_register)
    pub fields: Vec<(u8, u8)>,
}

impl ObjectCreateParams {
    /// Get the total number of fields
    pub const fn field_count(&self) -> usize {
        self.literal_key_fields
            .len()
            .saturating_add(self.fields.len())
    }

    /// Get literal key field pairs as a slice
    pub fn literal_key_field_pairs(&self) -> &[(u16, u8)] {
        &self.literal_key_fields
    }

    /// Get non-literal key field pairs as a slice
    pub fn field_pairs(&self) -> &[(u8, u8)] {
        &self.fields
    }
}

/// Array creation parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArrayCreateParams {
    /// Destination register to store the result array
    pub dest: u8,
    /// Register numbers containing the element values
    pub elements: Vec<u8>,
}

impl ArrayCreateParams {
    /// Get the number of elements
    pub const fn element_count(&self) -> usize {
        self.elements.len()
    }

    /// Get element register numbers as a slice
    pub fn element_registers(&self) -> &[u8] {
        &self.elements
    }
}

/// Set creation parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SetCreateParams {
    /// Destination register to store the result set
    pub dest: u8,
    /// Register numbers containing the element values
    pub elements: Vec<u8>,
}

impl SetCreateParams {
    /// Get the number of elements
    pub const fn element_count(&self) -> usize {
        self.elements.len()
    }

    /// Get element register numbers as a slice
    pub fn element_registers(&self) -> &[u8] {
        &self.elements
    }
}

/// Virtual data document lookup parameters for data namespace access with rule evaluation
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VirtualDataDocumentLookupParams {
    /// Destination register to store the result
    pub dest: u8,
    /// Path components in order (e.g., for data.users[input.name].config)
    /// This would be [Literal("users"), Register(5), Literal("config")]
    /// where register 5 contains the value from input.name
    pub path_components: Vec<LiteralOrRegister>,
}

impl VirtualDataDocumentLookupParams {
    /// Get the number of path components
    pub const fn component_count(&self) -> usize {
        self.path_components.len()
    }

    /// Check if all components are literals (can be optimized at compile time)
    pub fn all_literals(&self) -> bool {
        self.path_components
            .iter()
            .all(|c| matches!(c, LiteralOrRegister::Literal(_)))
    }

    /// Get just the literal indices (for debugging/display)
    pub fn literal_indices(&self) -> Vec<u16> {
        self.path_components
            .iter()
            .filter_map(|c| match *c {
                LiteralOrRegister::Literal(idx) => Some(idx),
                _ => None,
            })
            .collect()
    }

    /// Get just the register numbers (for debugging/display)
    pub fn register_numbers(&self) -> Vec<u8> {
        self.path_components
            .iter()
            .filter_map(|c| match *c {
                LiteralOrRegister::Register(reg) => Some(reg),
                _ => None,
            })
            .collect()
    }
}

/// Chained index parameters for multi-level object access (input, locals, non-rule data paths)
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChainedIndexParams {
    /// Destination register to store the result
    pub dest: u8,
    /// Root register containing the base object (input, local var, data subset)
    pub root: u8,
    /// Path components to traverse from the root
    pub path_components: Vec<LiteralOrRegister>,
}

impl ChainedIndexParams {
    /// Get the number of path components
    pub const fn component_count(&self) -> usize {
        self.path_components.len()
    }

    /// Check if all components are literals (can be optimized)
    pub fn all_literals(&self) -> bool {
        self.path_components
            .iter()
            .all(|c| matches!(c, LiteralOrRegister::Literal(_)))
    }

    /// Get just the literal indices (for debugging/display)
    pub fn literal_indices(&self) -> Vec<u16> {
        self.path_components
            .iter()
            .filter_map(|c| match *c {
                LiteralOrRegister::Literal(idx) => Some(idx),
                _ => None,
            })
            .collect()
    }

    /// Get just the register numbers (for debugging/display)
    pub fn register_numbers(&self) -> Vec<u8> {
        self.path_components
            .iter()
            .filter_map(|c| match *c {
                LiteralOrRegister::Register(reg) => Some(reg),
                _ => None,
            })
            .collect()
    }
}

/// Comprehension parameters stored in program's instruction data table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComprehensionBeginParams {
    /// Type of comprehension being created
    pub mode: ComprehensionMode,
    /// Register containing the source collection to iterate over
    pub collection_reg: u8,
    /// Register to store the comprehension result collection
    /// If not specified separately, this will match collection_reg
    pub result_reg: u8,
    /// Register to store current iteration key
    pub key_reg: u8,
    /// Register to store current iteration value
    pub value_reg: u8,
    /// Jump target for comprehension body start
    pub body_start: u16,
    /// Jump target for comprehension end
    pub comprehension_end: u16,
}

/// Instruction data container for complex instruction parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstructionData {
    /// Loop parameter table for LoopStart instructions
    pub loop_params: Vec<LoopStartParams>,
    /// Builtin function call parameter table for BuiltinCall instructions
    pub builtin_call_params: Vec<BuiltinCallParams>,
    /// Function rule call parameter table for FunctionCall instructions
    pub function_call_params: Vec<FunctionCallParams>,
    /// Object creation parameter table for ObjectCreate instructions
    pub object_create_params: Vec<ObjectCreateParams>,
    /// Array creation parameter table for ArrayCreate instructions
    pub array_create_params: Vec<ArrayCreateParams>,
    /// Set creation parameter table for SetCreate instructions
    pub set_create_params: Vec<SetCreateParams>,
    /// Virtual data document lookup parameter table for VirtualDataDocumentLookup instructions
    pub virtual_data_document_lookup_params: Vec<VirtualDataDocumentLookupParams>,
    /// Chained index parameter table for ChainedIndex instructions
    pub chained_index_params: Vec<ChainedIndexParams>,
    /// Comprehension parameter table for ComprehensionBegin instructions
    pub comprehension_begin_params: Vec<ComprehensionBeginParams>,
}

impl InstructionData {
    fn ensure_u16_index(len: usize) -> u16 {
        debug_assert!(len <= usize::from(u16::MAX));
        u16::try_from(len).unwrap_or(u16::MAX)
    }

    /// Create a new empty instruction data container
    pub const fn new() -> Self {
        Self {
            loop_params: Vec::new(),
            builtin_call_params: Vec::new(),
            function_call_params: Vec::new(),
            object_create_params: Vec::new(),
            array_create_params: Vec::new(),
            set_create_params: Vec::new(),
            virtual_data_document_lookup_params: Vec::new(),
            chained_index_params: Vec::new(),
            comprehension_begin_params: Vec::new(),
        }
    }

    /// Add loop parameters and return the index
    pub fn add_loop_params(&mut self, params: LoopStartParams) -> u16 {
        let index = Self::ensure_u16_index(self.loop_params.len());
        self.loop_params.push(params);
        index
    }

    /// Add builtin call parameters and return the index
    pub fn add_builtin_call_params(&mut self, params: BuiltinCallParams) -> u16 {
        let index = Self::ensure_u16_index(self.builtin_call_params.len());
        self.builtin_call_params.push(params);
        index
    }

    /// Add function call parameters and return the index
    pub fn add_function_call_params(&mut self, params: FunctionCallParams) -> u16 {
        let index = Self::ensure_u16_index(self.function_call_params.len());
        self.function_call_params.push(params);
        index
    }

    /// Add object create parameters and return the index
    pub fn add_object_create_params(&mut self, params: ObjectCreateParams) -> u16 {
        let index = Self::ensure_u16_index(self.object_create_params.len());
        self.object_create_params.push(params);
        index
    }

    /// Add array create parameters and return the index
    pub fn add_array_create_params(&mut self, params: ArrayCreateParams) -> u16 {
        let index = Self::ensure_u16_index(self.array_create_params.len());
        self.array_create_params.push(params);
        index
    }

    /// Add set create parameters and return the index
    pub fn add_set_create_params(&mut self, params: SetCreateParams) -> u16 {
        let index = Self::ensure_u16_index(self.set_create_params.len());
        self.set_create_params.push(params);
        index
    }

    /// Get loop parameters by index
    pub fn get_loop_params(&self, index: u16) -> Option<&LoopStartParams> {
        self.loop_params.get(usize::from(index))
    }

    /// Get builtin call parameters by index
    pub fn get_builtin_call_params(&self, index: u16) -> Option<&BuiltinCallParams> {
        self.builtin_call_params.get(usize::from(index))
    }

    /// Get function call parameters by index
    pub fn get_function_call_params(&self, index: u16) -> Option<&FunctionCallParams> {
        self.function_call_params.get(usize::from(index))
    }

    /// Get object create parameters by index
    pub fn get_object_create_params(&self, index: u16) -> Option<&ObjectCreateParams> {
        self.object_create_params.get(usize::from(index))
    }

    /// Get array create parameters by index
    pub fn get_array_create_params(&self, index: u16) -> Option<&ArrayCreateParams> {
        self.array_create_params.get(usize::from(index))
    }

    /// Get set create parameters by index
    pub fn get_set_create_params(&self, index: u16) -> Option<&SetCreateParams> {
        self.set_create_params.get(usize::from(index))
    }

    /// Add virtual data document lookup parameters and return the index
    pub fn add_virtual_data_document_lookup_params(
        &mut self,
        params: VirtualDataDocumentLookupParams,
    ) -> u16 {
        let index = Self::ensure_u16_index(self.virtual_data_document_lookup_params.len());
        self.virtual_data_document_lookup_params.push(params);
        index
    }

    /// Get virtual data document lookup parameters by index
    pub fn get_virtual_data_document_lookup_params(
        &self,
        index: u16,
    ) -> Option<&VirtualDataDocumentLookupParams> {
        self.virtual_data_document_lookup_params
            .get(usize::from(index))
    }

    /// Add chained index parameters and return the index
    pub fn add_chained_index_params(&mut self, params: ChainedIndexParams) -> u16 {
        let index = Self::ensure_u16_index(self.chained_index_params.len());
        self.chained_index_params.push(params);
        index
    }

    /// Get chained index parameters by index
    pub fn get_chained_index_params(&self, index: u16) -> Option<&ChainedIndexParams> {
        self.chained_index_params.get(usize::from(index))
    }

    /// Get mutable reference to loop parameters by index
    pub fn get_loop_params_mut(&mut self, index: u16) -> Option<&mut LoopStartParams> {
        self.loop_params.get_mut(usize::from(index))
    }

    /// Add comprehension begin parameters and return the index
    pub fn add_comprehension_begin_params(&mut self, params: ComprehensionBeginParams) -> u16 {
        let index = Self::ensure_u16_index(self.comprehension_begin_params.len());
        self.comprehension_begin_params.push(params);
        index
    }

    /// Get comprehension begin parameters by index
    pub fn get_comprehension_begin_params(&self, index: u16) -> Option<&ComprehensionBeginParams> {
        self.comprehension_begin_params.get(usize::from(index))
    }

    /// Get mutable reference to comprehension begin parameters by index
    pub fn get_comprehension_begin_params_mut(
        &mut self,
        index: u16,
    ) -> Option<&mut ComprehensionBeginParams> {
        self.comprehension_begin_params.get_mut(usize::from(index))
    }
}

impl Default for InstructionData {
    fn default() -> Self {
        Self::new()
    }
}

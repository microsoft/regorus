// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::extensions::BuiltinExtensionTrait;
use crate::lexer::Span;
use crate::value::Value;

use anyhow::{anyhow, bail, Result};
use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_void};
use std::thread_local;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::boxed::Box;

// Define callback function type for FFI communication
pub type RegorusCallbackFn = extern "C" fn(payload: *const c_char, context: *mut c_void) -> *mut c_char;

// Thread-local storage for callbacks to avoid Send/Sync issues
thread_local! {
    pub static CALLBACK_MAP: RefCell<HashMap<String, (RegorusCallbackFn, *mut c_void)>> = RefCell::new(HashMap::new());
}

/// Utility function to convert from C string
fn from_c_str(name: &str, s: *const c_char) -> Result<String> {
    if s.is_null() {
        bail!("null pointer");
    }
    unsafe {
        CStr::from_ptr(s)
            .to_str()
            .map_err(|e| anyhow!("`{name}`: invalid utf8.\n{e}"))
            .map(|s| s.to_string())
    }
}

/// Register a callback function with a name and context
/// 
/// Returns true on success, false on failure
pub fn register_callback(
    name: *const c_char, 
    callback: RegorusCallbackFn, 
    context: *mut c_void
) -> bool {
    if name.is_null() {
        return false;
    }
    
    let name_str = match from_c_str("name", name) {
        Ok(s) => s,
        Err(_) => return false,
    };
    
    CALLBACK_MAP.with(|callbacks| {
        callbacks.borrow_mut().insert(name_str, (callback, context));
        true
    })
}

/// Unregister a callback function by name
/// 
/// Returns true on success, false on failure
pub fn unregister_callback(name: *const c_char) -> bool {
    if name.is_null() {
        return false;
    }
    
    let name_str = match from_c_str("name", name) {
        Ok(s) => s,
        Err(_) => return false,
    };
    
    CALLBACK_MAP.with(|callbacks| {
        callbacks.borrow_mut().remove(&name_str);
        true
    })
}

/// Register the invoke builtin function
#[cfg(feature = "rego-extensions")]
pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("invoke", (invoke, 2));
}

/// The invoke builtin function implementation
/// This function is a placeholder that will be replaced by the actual implementation
/// when the extension is enabled using Engine::enable_builtin_extension()
pub fn invoke(_span: &Span, _params: &[Ref<Expr>], _args: &[Value], _strict: bool) -> Result<Value> {
    bail!("invoke() called but no implementation has been registered. Call engine.enable_builtin_extension(\"invoke\", ...) first.");
}

/// Implementation of the invoke callback extension.
/// This handles calling into registered FFI callbacks.
#[derive(Debug, Clone)]
pub struct InvokeExtension;

impl BuiltinExtensionTrait for InvokeExtension {
    fn call(&self, mut params: Vec<Value>) -> Result<Value> {
        if params.len() != 2 {
            bail!("invoke requires exactly two parameters: function_name and payload");
        }
        
        let function_name = match params.remove(0) {
            Value::String(s) => s.as_ref().to_string(),
            _ => bail!("function_name must be a string"),
        };
        
        // Serialize the payload to JSON
        let payload = serde_json::to_string(&params.remove(0))
            .map_err(|e| anyhow!("Failed to serialize payload: {}", e))?;
        
        // Look up the callback function using thread_local storage
        let callback_option = CALLBACK_MAP.with(|callbacks| {
            callbacks.borrow().get(&function_name).cloned()
        });
        
        let (callback_fn, context) = match callback_option {
            Some(cb) => cb,
            None => bail!("No callback registered with name: {}", function_name),
        };
        
        // Convert payload to C string
        let payload_c_str = match CString::new(payload) {
            Ok(cs) => cs,
            Err(_) => bail!("Failed to convert payload to C string"),
        };
        
        // Call the orchestration function
        let result_ptr = callback_fn(payload_c_str.as_ptr(), context);
        
        if result_ptr.is_null() {
            return Ok(Value::Null);
        }
        
        // Convert the result back to a Value
        let result_str = unsafe {
            let result = CStr::from_ptr(result_ptr)
                .to_str()
                .map_err(|e| anyhow!("Invalid UTF-8 in callback result: {}", e))?
                .to_string();
                
            // Free the memory allocated by calling code
            let _ = CString::from_raw(result_ptr as *mut c_char);
            
            result
        };
        
        // Convert result string to Value
        Value::from_json_str(&result_str)
            .map_err(|e| anyhow!("Failed to parse callback result as JSON: {}", e))
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    
    fn clone_box(&self) -> Box<dyn BuiltinExtensionTrait> {
        Box::new(self.clone())
    }
}

/// Factory function for creating a new InvokeExtension
pub fn create_invoke_extension() -> Box<dyn BuiltinExtensionTrait> {
    Box::new(InvokeExtension)
}
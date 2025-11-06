// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, Result};
use regorus::Value;
use std::ffi::{c_char, c_void, CString};

use crate::common::{from_c_str, RegorusPointerType, RegorusResult, RegorusStatus};
use crate::engine::RegorusEngine;

// Helper to convert Value pointer
fn to_value_ref<'a>(ptr: *mut c_void) -> Result<&'a Value> {
    if ptr.is_null() {
        return Err(anyhow!("Null value pointer"));
    }
    Ok(unsafe { &*(ptr as *mut Value) })
}

fn to_value_mut<'a>(ptr: *mut c_void) -> Result<&'a mut Value> {
    if ptr.is_null() {
        return Err(anyhow!("Null value pointer"));
    }
    Ok(unsafe { &mut *(ptr as *mut Value) })
}

// Creation functions
#[no_mangle]
pub extern "C" fn regorus_value_create_null() -> RegorusResult {
    let value = Box::new(Value::Null);
    RegorusResult::ok_pointer(
        Box::into_raw(value) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_undefined() -> RegorusResult {
    let value = Box::new(Value::Undefined);
    RegorusResult::ok_pointer(
        Box::into_raw(value) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_bool(value: bool) -> RegorusResult {
    let val = Box::new(Value::Bool(value));
    RegorusResult::ok_pointer(
        Box::into_raw(val) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_int(value: i64) -> RegorusResult {
    let val = Box::new(Value::from(value));
    RegorusResult::ok_pointer(
        Box::into_raw(val) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_float(value: f64) -> RegorusResult {
    let val = Box::new(Value::from(value));
    RegorusResult::ok_pointer(
        Box::into_raw(val) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_string(s: *const c_char) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        let s = from_c_str(s)?;
        let val = Box::new(Value::from(s.as_str()));
        Ok(Box::into_raw(val) as *mut c_void)
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_value_create_array() -> RegorusResult {
    let val = Box::new(Value::new_array());
    RegorusResult::ok_pointer(
        Box::into_raw(val) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_object() -> RegorusResult {
    let val = Box::new(Value::new_object());
    RegorusResult::ok_pointer(
        Box::into_raw(val) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

#[no_mangle]
pub extern "C" fn regorus_value_create_set() -> RegorusResult {
    let val = Box::new(Value::new_set());
    RegorusResult::ok_pointer(
        Box::into_raw(val) as *mut c_void,
        RegorusPointerType::PointerValue,
    )
}

// JSON serialization
#[no_mangle]
pub extern "C" fn regorus_value_from_json(json: *const c_char) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        let json_str = from_c_str(json)?;
        let val = Box::new(Value::from_json_str(&json_str)?);
        Ok(Box::into_raw(val) as *mut c_void)
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_value_to_json(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<String> {
        let val = to_value_ref(value)?;
        val.to_json_str()
    }();

    match result {
        Ok(s) => {
            let c_str = CString::new(s).unwrap();
            RegorusResult::ok_string_raw(c_str.into_raw())
        }
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Type checking
#[no_mangle]
pub extern "C" fn regorus_value_is_null(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<bool> {
        let val = to_value_ref(value)?;
        Ok(matches!(val, Value::Null))
    }();

    match result {
        Ok(b) => RegorusResult::ok_bool(b),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_value_is_object(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<bool> {
        let val = to_value_ref(value)?;
        Ok(matches!(val, Value::Object(_)))
    }();

    match result {
        Ok(b) => RegorusResult::ok_bool(b),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_value_is_string(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<bool> {
        let val = to_value_ref(value)?;
        Ok(matches!(val, Value::String(_)))
    }();

    match result {
        Ok(b) => RegorusResult::ok_bool(b),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Typed value accessors
/// Get boolean value
#[no_mangle]
pub extern "C" fn regorus_value_as_bool(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<bool> {
        let val = to_value_ref(value)?;
        Ok(*val.as_bool()?)
    }();

    match result {
        Ok(b) => RegorusResult::ok_bool(b),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

/// Get integer value
#[no_mangle]
pub extern "C" fn regorus_value_as_i64(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<i64> {
        let val = to_value_ref(value)?;
        val.as_i64()
    }();

    match result {
        Ok(i) => RegorusResult::ok_int(i),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

/// Get string value (returns owned copy)
#[no_mangle]
pub extern "C" fn regorus_value_as_string(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<String> {
        let val = to_value_ref(value)?;
        Ok(val.as_string()?.to_string())
    }();

    match result {
        Ok(s) => RegorusResult::ok_string(s),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Object operations
#[no_mangle]
pub extern "C" fn regorus_value_object_insert(
    object: *mut c_void,
    key: *const c_char,
    value: *mut c_void,
) -> RegorusResult {
    let result = || -> Result<()> {
        let obj = to_value_mut(object)?;
        let key_str = from_c_str(key)?;
        let val = to_value_ref(value)?.clone();

        obj.as_object_mut()?
            .insert(Value::from(key_str.as_str()), val);

        Ok(())
    }();

    match result {
        Ok(_) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_value_object_get(
    object: *mut c_void,
    key: *const c_char,
) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        let obj = to_value_ref(object)?;
        let key_str = from_c_str(key)?;

        let map = obj.as_object()?;
        let key_val = Value::from(key_str.as_str());

        if let Some(val) = map.get(&key_val) {
            let cloned = Box::new(val.clone());
            Ok(Box::into_raw(cloned) as *mut c_void)
        } else {
            Err(anyhow!("Key not found: {}", key_str))
        }
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Array operations
/// Get the length of an array
#[no_mangle]
pub extern "C" fn regorus_value_array_len(array: *mut c_void) -> RegorusResult {
    let result = || -> Result<i64> {
        let arr = to_value_ref(array)?;
        let array_ref = arr.as_array()?;
        Ok(array_ref.len() as i64)
    }();

    match result {
        Ok(len) => RegorusResult::ok_int(len),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

/// Get an element from an array by index
#[no_mangle]
pub extern "C" fn regorus_value_array_get(array: *mut c_void, index: i64) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        let arr = to_value_ref(array)?;
        let array_ref = arr.as_array()?;

        if index < 0 || index >= array_ref.len() as i64 {
            return Err(anyhow!("Index out of bounds: {}", index));
        }

        let val = &array_ref[index as usize];
        let cloned = Box::new(val.clone());
        Ok(Box::into_raw(cloned) as *mut c_void)
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

/// Append a value to an array
#[no_mangle]
pub extern "C" fn regorus_value_array_push(
    array: *mut c_void,
    value: *mut c_void,
) -> RegorusResult {
    let result = || -> Result<()> {
        let arr = to_value_mut(array)?;
        let val = to_value_ref(value)?.clone();

        arr.as_array_mut()?.push(val);

        Ok(())
    }();

    match result {
        Ok(_) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

/// Insert a value into a set
#[no_mangle]
pub extern "C" fn regorus_value_set_insert(set: *mut c_void, value: *mut c_void) -> RegorusResult {
    let result = || -> Result<()> {
        let set_value = to_value_mut(set)?;
        let val = to_value_ref(value)?.clone();

        set_value.as_set_mut()?.insert(val);

        Ok(())
    }();

    match result {
        Ok(_) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Memory management
#[no_mangle]
pub extern "C" fn regorus_value_drop(value: *mut c_void) {
    if !value.is_null() {
        unsafe {
            let _ = Box::from_raw(value as *mut Value);
        }
    }
}

/// Clone a Value
#[no_mangle]
pub extern "C" fn regorus_value_clone(value: *mut c_void) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        if value.is_null() {
            return Err(anyhow!("Null value pointer"));
        }

        let val_ref = unsafe { &*(value as *mut Value) };
        let cloned = Box::new(val_ref.clone());
        Ok(Box::into_raw(cloned) as *mut c_void)
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Engine integration - Input/Data
#[no_mangle]
pub extern "C" fn regorus_engine_set_input_value(
    engine: *mut RegorusEngine,
    value: *mut c_void,
) -> RegorusResult {
    let result = || -> Result<()> {
        if engine.is_null() {
            return Err(anyhow!("Null engine pointer"));
        }

        let engine_ref = unsafe { &mut *engine };
        let val = to_value_ref(value)?.clone();

        engine_ref.engine.set_input(val);
        Ok(())
    }();

    match result {
        Ok(_) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_engine_add_data_value(
    engine: *mut RegorusEngine,
    value: *mut c_void,
) -> RegorusResult {
    let result = || -> Result<()> {
        if engine.is_null() {
            return Err(anyhow!("Null engine pointer"));
        }

        let engine_ref = unsafe { &mut *engine };
        let val = to_value_ref(value)?.clone();

        engine_ref.engine.add_data(val)?;
        Ok(())
    }();

    match result {
        Ok(_) => RegorusResult::ok_void(),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

// Engine integration - Eval (returns Value instead of JSON)
#[no_mangle]
pub extern "C" fn regorus_engine_eval_query_as_value(
    engine: *mut RegorusEngine,
    query: *const c_char,
) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        if engine.is_null() {
            return Err(anyhow!("Null engine pointer"));
        }

        let engine_ref = unsafe { &mut *engine };
        let query_str = from_c_str(query)?;

        // Convert QueryResults to Value by directly extracting values (no JSON conversion)
        let results = engine_ref.engine.eval_query(query_str, false)?;

        // Create a Value array to hold all result expressions
        let mut result_array = Vec::new();
        for result in results.result {
            let mut expr_array = Vec::new();
            for expr in result.expressions {
                expr_array.push(expr.value);
            }
            result_array.push(Value::from(expr_array));
        }

        let value = Box::new(Value::from(result_array));

        Ok(Box::into_raw(value) as *mut c_void)
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

#[no_mangle]
pub extern "C" fn regorus_engine_eval_rule_as_value(
    engine: *mut RegorusEngine,
    rule: *const c_char,
) -> RegorusResult {
    let result = || -> Result<*mut c_void> {
        if engine.is_null() {
            return Err(anyhow!("Null engine pointer"));
        }

        let engine_ref = unsafe { &mut *engine };
        let rule_str = from_c_str(rule)?;

        let value = Box::new(engine_ref.engine.eval_rule(rule_str)?);
        Ok(Box::into_raw(value) as *mut c_void)
    }();

    match result {
        Ok(ptr) => RegorusResult::ok_pointer(ptr, RegorusPointerType::PointerValue),
        Err(e) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{}", e)),
    }
}

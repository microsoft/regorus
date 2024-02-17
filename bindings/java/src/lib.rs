// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use jni::objects::{JClass, JObject, JString};
use jni::sys::{jlong, jstring};
use jni::JNIEnv;

use regorus::{Engine, Value};

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_newEngine(
    _env: JNIEnv,
    _class: JClass,
) -> jlong {
    let engine = Engine::new();
    Box::into_raw(Box::new(engine)) as jlong
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_addPolicy(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
    rego: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        let rego: String = env.get_string(&rego)?.into();
        engine.add_policy(path, rego)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_addPolicyFromFile(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        engine.add_policy_from_file(path)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_addDataJson(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    data: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let data: String = env.get_string(&data)?.into();
        engine.add_data_json(&data)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_addDataJsonFromFile(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        engine.add_data(Value::from_json_file(path)?)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_setInputJson(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    input: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let input: String = env.get_string(&input)?.into();
        engine.set_input_json(&input)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_setInputJsonFromFile(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        engine.set_input(Value::from_json_file(&path)?);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_evalQuery(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    query: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let query: String = env.get_string(&query)?.into();
        let results = engine.eval_query(query, false)?;
        let output = env.new_string(serde_json::to_string(&results)?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub unsafe extern "system" fn Java_com_microsoft_regorus_Engine_destroyEngine(
    _env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) {
    let _engine = Box::from_raw(engine_ptr as *mut Engine);
}

fn throw_err<T>(mut env: JNIEnv, mut f: impl FnMut(&mut JNIEnv) -> Result<T>) -> Result<T> {
    match f(&mut env) {
        Ok(val) => Ok(val),
        Err(err) => {
            env.throw(err.to_string())?;
            Err(err)
        }
    }
}

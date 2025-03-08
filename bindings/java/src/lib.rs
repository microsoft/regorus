// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use jni::objects::{JClass, JObject, JString};
use jni::sys::{jlong, jstring};
use jni::JNIEnv;

use regorus::{Engine, Value};

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeNewEngine(
    _env: JNIEnv,
    _class: JClass,
) -> jlong {
    let engine = Engine::new();
    Box::into_raw(Box::new(engine)) as jlong
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeClone(
    _env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jlong {
    let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
    let c = engine.clone();
    Box::into_raw(Box::new(c)) as jlong
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetRegoV0(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    enable: bool,
) {
    let _ = throw_err(env, |_env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        engine.set_rego_v0(enable);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeAddPolicy(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
    rego: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        let rego: String = env.get_string(&rego)?.into();
        let pkg = env.new_string(engine.add_policy(path, rego)?)?;
        Ok(pkg.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeAddPolicyFromFile(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        let pkg = env.new_string(engine.add_policy_from_file(path)?)?;
        Ok(pkg.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeGetPackages(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let packages = engine.get_packages()?;
        let packages_json = env.new_string(serde_json::to_string_pretty(&packages)?)?;
        Ok(packages_json.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeGetPolicies(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let policies = engine.get_policies_as_json()?;
        let policies_json = env.new_string(&policies)?;
        Ok(policies_json.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeClearData(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) {
    let _ = throw_err(env, |_env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        engine.clear_data();
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeAddDataJson(
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
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeAddDataJsonFromFile(
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
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetInputJson(
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
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetInputJsonFromFile(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = env.get_string(&path)?.into();
        engine.set_input(Value::from_json_file(path)?);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeEvalQuery(
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
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeEvalRule(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    rule: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let rule: String = env.get_string(&rule)?.into();
        let value = engine.eval_rule(rule)?;
        let output = env.new_string(value.to_json_str()?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetEnableCoverage(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    enable: bool,
) {
    let _ = throw_err(env, |_| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        engine.set_enable_coverage(enable);
        Ok(())
    });
}

#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeGetCoverageReport(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let report = engine.get_coverage_report()?;
        let output = env.new_string(serde_json::to_string_pretty(&report)?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeGetCoverageReportPretty(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let report = engine.get_coverage_report()?.to_string_pretty()?;
        let output = env.new_string(&report)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
#[cfg(feature = "coverage")]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeClearCoverageData(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) {
    let _ = throw_err(env, |_| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        engine.clear_coverage_data();
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetGatherPrints(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
    b: bool,
) {
    let _ = throw_err(env, |_| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        engine.set_gather_prints(b);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeTakePrints(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let prints = engine.take_prints()?;
        let output = env.new_string(serde_json::to_string_pretty(&prints)?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
#[cfg(feature = "ast")]
pub extern "system" fn Java_com_microsoft_regorus_Engine_getAstAsJson(
    env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let ast = engine.get_ast_as_json()?;
        let output = env.new_string(&ast)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeDestroyEngine(
    _env: JNIEnv,
    _class: JClass,
    engine_ptr: jlong,
) {
    unsafe {
        let _engine = Box::from_raw(engine_ptr as *mut Engine);
    }
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

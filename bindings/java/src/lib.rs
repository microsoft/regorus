// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use core::num::{NonZeroU32, NonZeroUsize};
use jni::objects::{JBooleanArray, JByteArray, JClass, JObject, JObjectArray, JString};
use jni::strings::JNIString;
use jni::sys::{jboolean, jbooleanArray, jbyteArray, jlong, jobjectArray, jstring};
use jni::{jni_str, Env, EnvUnowned, Outcome};

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{
    generate_assembly_listing, AssemblyListingConfig, DeserializationResult, Program as RvmProgram,
};
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{compile_policy_with_entrypoint, Engine, PolicyModule, Rc, Value};
use std::sync::Arc;

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeNewEngine(
    _env: EnvUnowned,
    _class: JClass,
) -> jlong {
    let engine = Engine::new();
    Box::into_raw(Box::new(engine)) as jlong
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeClone(
    _env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jlong {
    let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
    let c = engine.clone();
    Box::into_raw(Box::new(c)) as jlong
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetRegoV0(
    env: EnvUnowned,
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
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
    rego: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = path.try_to_string(env)?;
        let rego: String = rego.try_to_string(env)?;
        let pkg = JString::new(env, engine.add_policy(path, rego)?)?;
        Ok(pkg.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeAddPolicyFromFile(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = path.try_to_string(env)?;
        let pkg = JString::new(env, engine.add_policy_from_file(path)?)?;
        Ok(pkg.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeGetPackages(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let packages = engine.get_packages()?;
        let packages_json = JString::new(env, serde_json::to_string_pretty(&packages)?)?;
        Ok(packages_json.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeGetPolicies(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let policies = engine.get_policies_as_json()?;
        let policies_json = JString::new(env, &policies)?;
        Ok(policies_json.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeClearData(
    env: EnvUnowned,
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
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    data: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let data: String = data.try_to_string(env)?;
        engine.add_data_json(&data)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeAddDataJsonFromFile(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = path.try_to_string(env)?;
        engine.add_data(Value::from_json_file(path)?)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetInputJson(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    input: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let input: String = input.try_to_string(env)?;
        engine.set_input_json(&input)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetInputJsonFromFile(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    path: JString,
) {
    let _ = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let path: String = path.try_to_string(env)?;
        engine.set_input(Value::from_json_file(path)?);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeEvalQuery(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    query: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let query: String = query.try_to_string(env)?;
        let results = engine.eval_query(query, false)?;
        let output = JString::new(env, serde_json::to_string(&results)?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeEvalRule(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    rule: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let rule: String = rule.try_to_string(env)?;
        let value = engine.eval_rule(rule)?;
        let output = JString::new(env, value.to_json_str()?)?;
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
    env: EnvUnowned,
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
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let report = engine.get_coverage_report()?;
        let output = JString::new(env, serde_json::to_string_pretty(&report)?)?;
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
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let report = engine.get_coverage_report()?.to_string_pretty()?;
        let output = JString::new(env, &report)?;
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
    env: EnvUnowned,
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
    env: EnvUnowned,
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
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let prints = engine.take_prints()?;
        let output = JString::new(env, serde_json::to_string_pretty(&prints)?)?;
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
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let ast = engine.get_ast_as_json()?;
        let output = JString::new(env, &ast)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeSetPolicyLengthConfig(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    max_col: u32,
    max_file_bytes: jlong,
    max_lines: jlong,
) {
    let _ = throw_err(env, |_env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        engine.set_policy_length_config(regorus::PolicyLengthConfig {
            max_col: NonZeroU32::new(max_col)
                .ok_or_else(|| anyhow::anyhow!("maxCol must be non-zero"))?,
            max_file_bytes: NonZeroUsize::new(max_file_bytes as usize)
                .ok_or_else(|| anyhow::anyhow!("maxFileBytes must be non-zero"))?,
            max_lines: NonZeroUsize::new(max_lines as usize)
                .ok_or_else(|| anyhow::anyhow!("maxLines must be non-zero"))?,
        });
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeClearPolicyLengthConfig(
    _env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) {
    let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
    engine.clear_policy_length_config();
}

#[cfg(feature = "cache")]
#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_CacheConfig_nativeSetCacheConfig(
    _env: EnvUnowned,
    _class: JClass,
    regex: jlong,
    glob: jlong,
) {
    regorus::cache::configure(regorus::cache::Config {
        regex: if regex < 0 {
            0
        } else {
            usize::try_from(regex).unwrap_or(usize::MAX)
        },
        glob: if glob < 0 {
            0
        } else {
            usize::try_from(glob).unwrap_or(usize::MAX)
        },
    });
}

#[cfg(feature = "cache")]
#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_CacheConfig_nativeClearCache(
    _env: EnvUnowned,
    _class: JClass,
) {
    regorus::cache::clear();
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Engine_nativeDestroyEngine(
    _env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
) {
    unsafe {
        let _engine = Box::from_raw(engine_ptr as *mut Engine);
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Program_nativeCompileFromModules(
    env: EnvUnowned,
    _class: JClass,
    data_json: JString,
    module_ids: jobjectArray,
    module_contents: jobjectArray,
    entry_points: jobjectArray,
) -> jlong {
    let res = throw_err(env, |env| {
        let data_json: String = data_json.try_to_string(env)?;
        let data = Value::from_json_str(&data_json)?;

        let ids = get_string_array(env, module_ids)?;
        let contents = get_string_array(env, module_contents)?;
        if ids.len() != contents.len() {
            return Err(anyhow::anyhow!("module id/content length mismatch"));
        }

        let mut modules = Vec::with_capacity(ids.len());
        for (id, content) in ids.into_iter().zip(contents.into_iter()) {
            modules.push(PolicyModule {
                id: Rc::from(id.as_str()),
                content: Rc::from(content.as_str()),
            });
        }

        let entry_points_vec = get_string_array(env, entry_points)?;
        if entry_points_vec.is_empty() {
            return Err(anyhow::anyhow!(
                "entry_points must contain at least one entry"
            ));
        }
        let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();
        let entry_rule = entry_points_ref[0];

        let compiled = compile_policy_with_entrypoint(data, &modules, Rc::from(entry_rule))?;
        let program = Compiler::compile_from_policy(&compiled, &entry_points_ref)?;
        Ok(Box::into_raw(Box::new(program)) as jlong)
    });

    res.unwrap_or_default()
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Program_nativeCompileFromEngine(
    env: EnvUnowned,
    _class: JClass,
    engine_ptr: jlong,
    entry_points: jobjectArray,
) -> jlong {
    let res = throw_err(env, |env| {
        let engine = unsafe { &mut *(engine_ptr as *mut Engine) };
        let entry_points_vec = get_string_array(env, entry_points)?;
        if entry_points_vec.is_empty() {
            return Err(anyhow::anyhow!(
                "entry_points must contain at least one entry"
            ));
        }
        let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();
        let entry_rule = Rc::from(entry_points_ref[0]);
        let compiled = engine.compile_with_entrypoint(&entry_rule)?;
        let program = Compiler::compile_from_policy(&compiled, &entry_points_ref)?;
        Ok(Box::into_raw(Box::new(program)) as jlong)
    });

    res.unwrap_or_default()
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Program_nativeGenerateListing(
    env: EnvUnowned,
    _class: JClass,
    program_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let program = unsafe { &*(program_ptr as *mut Arc<RvmProgram>) };
        let listing =
            generate_assembly_listing(program.as_ref(), &AssemblyListingConfig::default());
        let output = JString::new(env, &listing)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Program_nativeSerializeBinary(
    env: EnvUnowned,
    _class: JClass,
    program_ptr: jlong,
) -> jbyteArray {
    let res = throw_err(env, |env| {
        let program = unsafe { &*(program_ptr as *mut Arc<RvmProgram>) };
        let bytes = program.serialize_binary().map_err(|e| anyhow::anyhow!(e))?;
        let array = env.byte_array_from_slice(&bytes)?;
        Ok(array.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
/// # Safety
///
/// The `data` and `is_partial` pointers must be valid JNI array references
/// for the duration of the call. They must come from the JVM for the current
/// thread and not be used after this function returns.
pub unsafe extern "system" fn Java_com_microsoft_regorus_Program_nativeDeserializeBinary(
    env: EnvUnowned,
    _class: JClass,
    data: jbyteArray,
    is_partial: jbooleanArray,
) -> jlong {
    let res = throw_err(env, |env| {
        if data.is_null() {
            return Err(anyhow::anyhow!("data must not be null"));
        }

        let data = unsafe { JByteArray::from_raw(env, data) };
        let bytes = env.convert_byte_array(&data)?;
        let (program, partial) =
            match RvmProgram::deserialize_binary(&bytes).map_err(|e| anyhow::anyhow!(e))? {
                DeserializationResult::Complete(program) => (program, false),
                DeserializationResult::Partial(program) => (program, true),
            };

        if !is_partial.is_null() {
            let is_partial = unsafe { JBooleanArray::from_raw(env, is_partial) };
            let len = is_partial.len(env)?;
            if len > 0 {
                let value: [jboolean; 1] = [partial];
                is_partial.set_region(env, 0, &value)?;
            }
        }

        Ok(Box::into_raw(Box::new(Arc::new(program))) as jlong)
    });

    res.unwrap_or_default()
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Program_nativeDrop(
    _env: EnvUnowned,
    _class: JClass,
    program_ptr: jlong,
) {
    unsafe {
        let _program = Box::from_raw(program_ptr as *mut Arc<RvmProgram>);
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeNew(
    _env: EnvUnowned,
    _class: JClass,
) -> jlong {
    let vm = RegoVM::new();
    Box::into_raw(Box::new(vm)) as jlong
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeLoadProgram(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
    program_ptr: jlong,
) {
    let _ = throw_err(env, |_env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let program = unsafe { &*(program_ptr as *mut Arc<RvmProgram>) };
        vm.load_program(program.clone());
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeSetDataJson(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
    data_json: JString,
) {
    let _ = throw_err(env, |env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let data_json: String = data_json.try_to_string(env)?;
        let data = Value::from_json_str(&data_json)?;
        vm.set_data(data)?;
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeSetInputJson(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
    input_json: JString,
) {
    let _ = throw_err(env, |env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let input_json: String = input_json.try_to_string(env)?;
        let input = Value::from_json_str(&input_json)?;
        vm.set_input(input);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeSetExecutionMode(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
    mode: u8,
) {
    let _ = throw_err(env, |_env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let mode = match mode {
            0 => ExecutionMode::RunToCompletion,
            1 => ExecutionMode::Suspendable,
            _ => return Err(anyhow::anyhow!("invalid execution mode")),
        };
        vm.set_execution_mode(mode);
        Ok(())
    });
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeExecute(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let result = vm.execute()?;
        let output = JString::new(env, result.to_json_str()?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeExecuteEntryPoint(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
    entry_point: JString,
) -> jstring {
    let res = throw_err(env, |env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let entry_point: String = entry_point.try_to_string(env)?;
        let result = vm.execute_entry_point_by_name(&entry_point)?;
        let output = JString::new(env, result.to_json_str()?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeResume(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
    resume_json: JString,
    has_value: bool,
) -> jstring {
    let res = throw_err(env, |env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let value = if has_value {
            let resume_json: String = resume_json.try_to_string(env)?;
            Some(Value::from_json_str(&resume_json)?)
        } else {
            None
        };
        let result = vm.resume(value)?;
        let output = JString::new(env, result.to_json_str()?)?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeGetExecutionState(
    env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
) -> jstring {
    let res = throw_err(env, |env| {
        let vm = unsafe { &mut *(vm_ptr as *mut RegoVM) };
        let output = JString::new(env, format!("{:?}", vm.execution_state()))?;
        Ok(output.into_raw())
    });

    match res {
        Ok(val) => val,
        Err(_) => JObject::null().into_raw(),
    }
}

#[no_mangle]
pub extern "system" fn Java_com_microsoft_regorus_Rvm_nativeDrop(
    _env: EnvUnowned,
    _class: JClass,
    vm_ptr: jlong,
) {
    unsafe {
        let _vm = Box::from_raw(vm_ptr as *mut RegoVM);
    }
}

fn throw_err<T>(mut env: EnvUnowned, f: impl FnOnce(&mut Env) -> Result<T>) -> Result<T> {
    let outcome = env.with_env(|env| -> Result<T> {
        match f(env) {
            Ok(val) => Ok(val),
            Err(err) => {
                let _ = env.throw_new(
                    jni_str!("java/lang/RuntimeException"),
                    JNIString::new(err.to_string()),
                );
                Err(err)
            }
        }
    });
    match outcome.into_outcome() {
        Outcome::Ok(val) => Ok(val),
        Outcome::Err(err) => Err(err),
        Outcome::Panic(payload) => std::panic::resume_unwind(payload),
    }
}

fn get_string_array(env: &mut Env, array: jobjectArray) -> Result<Vec<String>> {
    if array.is_null() {
        return Ok(Vec::new());
    }
    let array = unsafe { JObjectArray::<JObject>::from_raw(env, array) };
    let len = array.len(env)?;
    let mut values = Vec::with_capacity(len);
    for i in 0..len {
        let obj = array.get_element(env, i)?;
        let jstr = unsafe { JString::from_raw(env, obj.into_raw()) };
        let value: String = jstr.try_to_string(env)?;
        values.push(value);
    }
    Ok(values)
}

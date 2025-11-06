// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Runtime.InteropServices;

#pragma warning disable CS8500
#pragma warning disable CS8981

namespace Regorus.Internal
{
    /// <summary>
    /// Native FFI method declarations for Regorus.
    /// This file contains all P/Invoke declarations for the Regorus native library.
    /// </summary>
    internal static unsafe partial class API
    {
        private const string LibraryName = "regorus_ffi";

        #region Common Methods

        /// <summary>
        /// Drop a RegorusResult.
        /// output and error_message strings are not valid after drop.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_result_drop", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern void regorus_result_drop(RegorusResult result);

        #endregion

        #region Engine Methods

        /// <summary>
        /// Construct a new Engine.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_new", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusEngine* regorus_engine_new();

        /// <summary>
        /// Clone a RegorusEngine.
        /// To avoid having to parse same policy again, the engine can be cloned
        /// after policies and data have been added.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_clone", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusEngine* regorus_engine_clone(RegorusEngine* engine);

        /// <summary>
        /// Drop a RegorusEngine.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_drop", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern void regorus_engine_drop(RegorusEngine* engine);

        /// <summary>
        /// Add a policy.
        /// The policy is parsed into AST.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_policy
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_add_policy", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_policy(RegorusEngine* engine, byte* path, byte* rego);

        /// <summary>
        /// Add a policy from file.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_add_policy_from_file", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_policy_from_file(RegorusEngine* engine, byte* path);

        /// <summary>
        /// Add policy data.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_add_data_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_data_json(RegorusEngine* engine, byte* data);

        /// <summary>
        /// Get list of loaded Rego packages as JSON.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_packages
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_packages", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_packages(RegorusEngine* engine);

        /// <summary>
        /// Get list of policies as JSON.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_policies
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_policies", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_policies(RegorusEngine* engine);

        /// <summary>
        /// Add data from JSON file.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_add_data_from_json_file", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_data_from_json_file(RegorusEngine* engine, byte* path);

        /// <summary>
        /// Clear policy data.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_data
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_clear_data", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_clear_data(RegorusEngine* engine);

        /// <summary>
        /// Set input.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_input
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_input_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_input_json(RegorusEngine* engine, byte* input);

        /// <summary>
        /// Set input from JSON file.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_input_from_json_file", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_input_from_json_file(RegorusEngine* engine, byte* path);

        /// <summary>
        /// Evaluate query.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_query
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_eval_query", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_eval_query(RegorusEngine* engine, byte* query);

        /// <summary>
        /// Evaluate specified rule.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_rule
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_eval_rule", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_eval_rule(RegorusEngine* engine, byte* rule);

        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_input_value", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_input_value(RegorusEngine* engine, void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_engine_add_data_value", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_data_value(RegorusEngine* engine, void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_engine_eval_query_as_value", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_eval_query_as_value(RegorusEngine* engine, byte* query);

        [DllImport(LibraryName, EntryPoint = "regorus_engine_eval_rule_as_value", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_eval_rule_as_value(RegorusEngine* engine, byte* rule);

        /// <summary>
        /// Enable/disable coverage.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_enable_coverage
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_enable_coverage", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_enable_coverage(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool enable);

        /// <summary>
        /// Get coverage report.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_coverage_report
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_coverage_report", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_coverage_report(RegorusEngine* engine);

        /// <summary>
        /// Enable/disable strict builtin errors.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_strict_builtin_errors
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_strict_builtin_errors", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_strict_builtin_errors(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool strict);

        /// <summary>
        /// Get pretty printed coverage report.
        /// See https://docs.rs/regorus/latest/regorus/coverage/struct.Report.html#method.to_string_pretty
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_coverage_report_pretty", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_coverage_report_pretty(RegorusEngine* engine);

        /// <summary>
        /// Clear coverage data.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_coverage_data
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_clear_coverage_data", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_clear_coverage_data(RegorusEngine* engine);

        /// <summary>
        /// Whether to gather output of print statements.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_gather_prints
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_gather_prints", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_gather_prints(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool enable);

        /// <summary>
        /// Take all the gathered print statements.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.take_prints
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_take_prints", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_take_prints(RegorusEngine* engine);

        /// <summary>
        /// Get AST of policies.
        /// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_ast_as_json
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_ast_as_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_ast_as_json(RegorusEngine* engine);

        /// <summary>
        /// Gets the package names defined in each policy added to the engine.
        /// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_policy_package_names
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_policy_package_names", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_policy_package_names(RegorusEngine* engine);

        /// <summary>
        /// Gets the parameters defined in each policy added to the engine.
        /// See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_policy_parameters
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_get_policy_parameters", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_policy_parameters(RegorusEngine* engine);

        /// <summary>
        /// Enable/disable rego v1.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_rego_v0
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_set_rego_v0", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_rego_v0(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool enable);

        /// <summary>
        /// Compile a target-aware policy from the current engine state.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.compile_for_target
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_compile_for_target", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_compile_for_target(RegorusEngine* engine);

        /// <summary>
        /// Compile a policy with a specific entry point rule.
        /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.compile_with_entrypoint
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_engine_compile_with_entrypoint", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_compile_with_entrypoint(RegorusEngine* engine, byte* rule);

        #endregion

        #region Value Methods

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_null", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_null();

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_undefined", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_undefined();

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_bool", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_bool([MarshalAs(UnmanagedType.U1)] bool value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_int", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_int(long value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_float", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_float(double value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_string", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_string(byte* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_array", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_array();

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_object", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_object();

        [DllImport(LibraryName, EntryPoint = "regorus_value_create_set", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_create_set();

        [DllImport(LibraryName, EntryPoint = "regorus_value_from_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_from_json(byte* json);

        [DllImport(LibraryName, EntryPoint = "regorus_value_to_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_to_json(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_is_null", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_is_null(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_is_object", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_is_object(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_is_string", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_is_string(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_as_bool", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_as_bool(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_as_i64", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_as_i64(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_as_string", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_as_string(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_object_insert", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_object_insert(void* obj, byte* key, void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_object_get", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_object_get(void* obj, byte* key);

        [DllImport(LibraryName, EntryPoint = "regorus_value_array_len", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_array_len(void* array);

        [DllImport(LibraryName, EntryPoint = "regorus_value_array_get", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_array_get(void* array, long index);

    [DllImport(LibraryName, EntryPoint = "regorus_value_array_push", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
    internal static extern RegorusResult regorus_value_array_push(void* array, void* value);

    [DllImport(LibraryName, EntryPoint = "regorus_value_set_insert", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
    internal static extern RegorusResult regorus_value_set_insert(void* set, void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_clone", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_value_clone(void* value);

        [DllImport(LibraryName, EntryPoint = "regorus_value_drop", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern void regorus_value_drop(void* value);

        #endregion

        #region Compilation Methods

        /// <summary>
        /// Compiles a policy from data and modules with a specific entry point rule.
        /// This is a convenience function that wraps regorus::compile_policy_with_entrypoint.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_compile_policy_with_entrypoint", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_compile_policy_with_entrypoint(byte* data_json, RegorusPolicyModule* modules, UIntPtr modules_len, byte* entry_point_rule);

        /// <summary>
        /// Compiles a target-aware policy from data and modules.
        /// This is a convenience function that wraps regorus::compile_policy_for_target.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_compile_policy_for_target", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_compile_policy_for_target(byte* data_json, RegorusPolicyModule* modules, UIntPtr modules_len);

        #endregion

        #region Compiled Policy Methods

        /// <summary>
        /// Drop a RegorusCompiledPolicy.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_compiled_policy_drop", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern void regorus_compiled_policy_drop(RegorusCompiledPolicy* compiled_policy);

        /// <summary>
        /// Evaluate the compiled policy with the given input.
        /// For target policies, evaluates the target's effect rule.
        /// For regular policies, evaluates the originally compiled rule.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_compiled_policy_eval_with_input", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_compiled_policy_eval_with_input(RegorusCompiledPolicy* compiled_policy, byte* input);

        /// <summary>
        /// Get information about the compiled policy including metadata about modules,
        /// target configuration, and resource types.
        /// Returns a JSON-encoded PolicyInfo struct containing comprehensive
        /// information about the compiled policy such as module IDs, target name,
        /// applicable resource types, entry point rule, and parameters.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_compiled_policy_get_policy_info", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_compiled_policy_get_policy_info(RegorusCompiledPolicy* compiled_policy);

        #endregion

        #region Target Registry Methods

        /// <summary>
        /// Register a target from JSON definition.
        /// The target JSON should follow the target schema format.
        /// Once registered, the target can be referenced in Rego policies using __target__ rules.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_register_target_from_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_register_target_from_json(byte* target_json);

        /// <summary>
        /// Check if a target is registered.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_target_registry_contains", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_target_registry_contains(byte* name);

        /// <summary>
        /// Get a list of all registered target names as JSON array.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_target_registry_list_names", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_target_registry_list_names();

        /// <summary>
        /// Remove a target from the registry by name.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_target_registry_remove", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_target_registry_remove(byte* name);

        /// <summary>
        /// Clear all targets from the registry.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_target_registry_clear", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_target_registry_clear();

        /// <summary>
        /// Get the number of registered targets.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_target_registry_len", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_target_registry_len();

        /// <summary>
        /// Check if the target registry is empty.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_target_registry_is_empty", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_target_registry_is_empty();

        #endregion

        #region Resource Schema Registry Methods

        /// <summary>
        /// Register a resource schema from JSON with a given name.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_register", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_register(byte* name, byte* schema_json);

        /// <summary>
        /// Check if a resource schema with the given name exists.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_contains", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_contains(byte* name);

        /// <summary>
        /// Get the number of registered resource schemas.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_len", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_len();

        /// <summary>
        /// Check if the resource schema registry is empty.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_is_empty", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_is_empty();

        /// <summary>
        /// List all registered resource schema names as a JSON array.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_list_names", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_list_names();

        /// <summary>
        /// Remove a resource schema by name.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_remove", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_remove(byte* name);

        /// <summary>
        /// Clear all resource schemas from the registry.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_resource_schema_clear", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_resource_schema_clear();

        #endregion

        #region Effect Schema Registry Methods

        /// <summary>
        /// Register an effect schema from JSON with a given name.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_register", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_register(byte* name, byte* schema_json);

        /// <summary>
        /// Check if an effect schema with the given name exists.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_contains", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_contains(byte* name);

        /// <summary>
        /// Get the number of registered effect schemas.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_len", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_len();

        /// <summary>
        /// Check if the effect schema registry is empty.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_is_empty", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_is_empty();

        /// <summary>
        /// List all registered effect schema names as a JSON array.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_list_names", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_list_names();

        /// <summary>
        /// Remove an effect schema by name.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_remove", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_remove(byte* name);

        /// <summary>
        /// Clear all effect schemas from the registry.
        /// </summary>
        [DllImport(LibraryName, EntryPoint = "regorus_effect_schema_clear", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_effect_schema_clear();

        #endregion
    }

    #region Native Structures

    /// <summary>
    /// Type of data contained in RegorusResult.
    /// </summary>
    internal enum RegorusDataType : uint
    {
        /// <summary>
        /// No data / void.
        /// </summary>
        None,
        /// <summary>
        /// String data (output field is valid).
        /// </summary>
        String,
        /// <summary>
        /// Boolean data (bool_value field is valid).
        /// </summary>
        Boolean,
        /// <summary>
        /// Integer data (int_value field is valid).
        /// </summary>
        Integer,
        /// <summary>
        /// Pointer data (pointer_value field is valid).
        /// </summary>
        Pointer,
    }

    /// <summary>
    /// Type of pointer contained in RegorusResult.
    /// </summary>
    internal enum RegorusPointerType : uint
    {
        PointerNone,
        PointerValue,
        PointerCompiledPolicy,
    }

    /// <summary>
    /// Status of a call on RegorusEngine.
    /// </summary>
    internal enum RegorusStatus : uint
    {
        /// <summary>
        /// The operation was successful.
        /// </summary>
        Ok,
        /// <summary>
        /// The operation was unsuccessful.
        /// </summary>
        Error,
        /// <summary>
        /// Invalid data format provided.
        /// </summary>
        InvalidDataFormat,
        /// <summary>
        /// Invalid entrypoint rule specified.
        /// </summary>
        InvalidEntrypoint,
        /// <summary>
        /// Compilation failed.
        /// </summary>
        CompilationFailed,
        /// <summary>
        /// Invalid argument provided.
        /// </summary>
        InvalidArgument,
        /// <summary>
        /// Invalid module ID.
        /// </summary>
        InvalidModuleId,
        /// <summary>
        /// Invalid policy content.
        /// </summary>
        InvalidPolicy,
    }

    /// <summary>
    /// Result of a call on RegorusEngine.
    /// Must be freed using regorus_result_drop.
    /// </summary>
    [StructLayout(LayoutKind.Sequential)]
    internal unsafe partial struct RegorusResult
    {
        /// <summary>
        /// Status.
        /// </summary>
        public RegorusStatus status;
        /// <summary>
        /// Type of data contained in this result.
        /// </summary>
        public RegorusDataType data_type;
        /// <summary>
        /// String output produced by the call.
        /// Valid when data_type is String. Owned by Rust.
        /// </summary>
        public byte* output;
        /// <summary>
        /// Boolean value.
        /// Valid when data_type is Boolean.
        /// </summary>
        public bool bool_value;
        /// <summary>
        /// Integer value.
        /// Valid when data_type is Integer.
        /// </summary>
        public long int_value;
        /// <summary>
        /// Unsigned 64-bit integer value.
        /// Valid when data_type is Integer.
        /// </summary>
        public ulong u64_value;
        /// <summary>
        /// Pointer value.
        /// Valid when data_type is Pointer.
        /// </summary>
        public void* pointer_value;
        /// <summary>
        /// Type of pointer contained in pointer_value.
        /// </summary>
        public RegorusPointerType pointer_type;
        /// <summary>
        /// Errors produced by the call.
        /// Owned by Rust.
        /// </summary>
        public byte* error_message;
    }

    /// <summary>
    /// Wrapper for regorus::Engine.
    /// </summary>
    [StructLayout(LayoutKind.Sequential)]
    internal unsafe partial struct RegorusEngine
    {
    }

    /// <summary>
    /// Wrapper for regorus::CompiledPolicy.
    /// </summary>
    [StructLayout(LayoutKind.Sequential)]
    internal unsafe partial struct RegorusCompiledPolicy
    {
    }

    /// <summary>
    /// FFI wrapper for PolicyModule struct.
    /// </summary>
    [StructLayout(LayoutKind.Sequential)]
    internal unsafe partial struct RegorusPolicyModule
    {
        public byte* id;
        public byte* content;
    }

    #endregion
}

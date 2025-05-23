// <auto-generated>
// This code is generated by csbindgen.
// DON'T CHANGE THIS DIRECTLY.
// </auto-generated>
#pragma warning disable CS8500
#pragma warning disable CS8981
using System;
using System.Runtime.InteropServices;


namespace Regorus.Internal
{
    internal static unsafe partial class API
    {
        const string __DllName = "regorus_ffi";



        /// <summary>
        ///  Drop a `RegorusResult`.
        ///
        ///  `output` and `error_message` strings are not valid after drop.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_result_drop", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern void regorus_result_drop(RegorusResult r);

        /// <summary>
        ///  Construct a new Engine
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_new", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusEngine* regorus_engine_new();

        /// <summary>
        ///  Clone a [`RegorusEngine`]
        ///
        ///  To avoid having to parse same policy again, the engine can be cloned
        ///  after policies and data have been added.
        ///
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_clone", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusEngine* regorus_engine_clone(RegorusEngine* engine);

        [DllImport(__DllName, EntryPoint = "regorus_engine_drop", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern void regorus_engine_drop(RegorusEngine* engine);

        /// <summary>
        ///  Add a policy
        ///
        ///  The policy is parsed into AST.
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_policy
        ///
        ///  * `path`: A filename to be associated with the policy.
        ///  * `rego`: Rego policy.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_add_policy", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_policy(RegorusEngine* engine, byte* path, byte* rego);

        [DllImport(__DllName, EntryPoint = "regorus_engine_add_policy_from_file", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_policy_from_file(RegorusEngine* engine, byte* path);

        /// <summary>
        ///  Add policy data.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
        ///  * `data`: JSON encoded value to be used as policy data.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_add_data_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_data_json(RegorusEngine* engine, byte* data);

        /// <summary>
        ///  Get list of loaded Rego packages as JSON.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_packages
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_get_packages", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_packages(RegorusEngine* engine);

        /// <summary>
        ///  Get list of policies as JSON.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_policies
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_get_policies", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_policies(RegorusEngine* engine);

        [DllImport(__DllName, EntryPoint = "regorus_engine_add_data_from_json_file", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_add_data_from_json_file(RegorusEngine* engine, byte* path);

        /// <summary>
        ///  Clear policy data.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_data
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_clear_data", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_clear_data(RegorusEngine* engine);

        /// <summary>
        ///  Set input.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_input
        ///  * `input`: JSON encoded value to be used as input to query.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_set_input_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_input_json(RegorusEngine* engine, byte* input);

        [DllImport(__DllName, EntryPoint = "regorus_engine_set_input_from_json_file", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_input_from_json_file(RegorusEngine* engine, byte* path);

        /// <summary>
        ///  Evaluate query.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_query
        ///  * `query`: Rego expression to be evaluate.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_eval_query", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_eval_query(RegorusEngine* engine, byte* query);

        /// <summary>
        ///  Evaluate specified rule.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_rule
        ///  * `rule`: Path to the rule.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_eval_rule", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_eval_rule(RegorusEngine* engine, byte* rule);

        /// <summary>
        ///  Enable/disable coverage.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_enable_coverage
        ///  * `enable`: Whether to enable or disable coverage.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_set_enable_coverage", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_enable_coverage(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool enable);

        /// <summary>
        ///  Get coverage report.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_coverage_report
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_get_coverage_report", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_coverage_report(RegorusEngine* engine);

        /// <summary>
        ///  Enable/disable strict builtin errors.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_strict_builtin_errors
        ///  * `strict`: Whether to raise errors or return undefined on certain scenarios.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_set_strict_builtin_errors", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_strict_builtin_errors(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool strict);

        /// <summary>
        ///  Get pretty printed coverage report.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/coverage/struct.Report.html#method.to_string_pretty
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_get_coverage_report_pretty", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_coverage_report_pretty(RegorusEngine* engine);

        /// <summary>
        ///  Clear coverage data.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_coverage_data
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_clear_coverage_data", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_clear_coverage_data(RegorusEngine* engine);

        /// <summary>
        ///  Whether to gather output of print statements.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_gather_prints
        ///  * `enable`: Whether to enable or disable gathering print statements.
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_set_gather_prints", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_gather_prints(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool enable);

        /// <summary>
        ///  Take all the gathered print statements.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.take_prints
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_take_prints", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_take_prints(RegorusEngine* engine);

        /// <summary>
        ///  Get AST of policies.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/coverage/struct.Engine.html#method.get_ast_as_json
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_get_ast_as_json", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_get_ast_as_json(RegorusEngine* engine);

        /// <summary>
        ///  Enable/disable rego v1.
        ///
        ///  See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_rego_v0
        /// </summary>
        [DllImport(__DllName, EntryPoint = "regorus_engine_set_rego_v0", CallingConvention = CallingConvention.Cdecl, ExactSpelling = true)]
        internal static extern RegorusResult regorus_engine_set_rego_v0(RegorusEngine* engine, [MarshalAs(UnmanagedType.U1)] bool enable);


    }

    [StructLayout(LayoutKind.Sequential)]
    internal unsafe partial struct RegorusResult
    {
        public RegorusStatus status;
        public byte* output;
        public byte* error_message;
    }

    [StructLayout(LayoutKind.Sequential)]
    internal unsafe partial struct RegorusEngine
    {
    }


    internal enum RegorusStatus : uint
    {
        RegorusStatusOk,
        RegorusStatusError,
    }


}

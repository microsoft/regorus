// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text.Json;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Represents a compiled RVM program.
    /// </summary>
    public unsafe sealed class Program : SafeHandleWrapper
    {
        internal Program(RegorusProgramHandle handle)
            : base(handle, nameof(Program))
        {
        }

        /// <summary>
        /// Create an empty program.
        /// </summary>
        public static Program CreateEmpty()
        {
            return new Program(RegorusProgramHandle.Create());
        }

        /// <summary>
        /// Compile an RVM program from modules and entry points.
        /// </summary>
        public static Program CompileFromModules(string dataJson, IEnumerable<PolicyModule> modules, IEnumerable<string> entryPoints)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            if (entryPoints is null)
            {
                throw new ArgumentNullException(nameof(entryPoints));
            }

            return CompileFromModules(dataJson, modules.ToArray(), entryPoints.ToArray());
        }

        /// <summary>
        /// Compile an RVM program from modules and entry points.
        /// </summary>
        public static Program CompileFromModules(string dataJson, IReadOnlyList<PolicyModule> modules, IReadOnlyList<string> entryPoints)
        {
            return CompileFromModulesInner(dataJson, modules, entryPoints, hostAwaitBuiltins: null);
        }

        /// <summary>
        /// Compile an RVM program from an engine instance and entry points.
        /// </summary>
        public static Program CompileFromEngine(Engine engine, IEnumerable<string> entryPoints)
        {
            if (engine is null)
            {
                throw new ArgumentNullException(nameof(engine));
            }
            if (entryPoints is null)
            {
                throw new ArgumentNullException(nameof(entryPoints));
            }

            return CompileFromEngine(engine, entryPoints.ToArray());
        }

        /// <summary>
        /// Compile an RVM program from an engine instance and entry points.
        /// </summary>
        public static Program CompileFromEngine(Engine engine, IReadOnlyList<string> entryPoints)
        {
            if (engine is null)
            {
                throw new ArgumentNullException(nameof(engine));
            }

            if (entryPoints is null)
            {
                throw new ArgumentNullException(nameof(entryPoints));
            }

            if (entryPoints.Count == 0)
            {
                throw new ArgumentException("At least one entry point is required.", nameof(entryPoints));
            }

            using var pinnedEntryPoints = ModuleMarshalling.PinUtf8Strings(entryPoints);

            return engine.UseHandleForInterop(enginePtr =>
            {
                fixed (IntPtr* entryPtr = pinnedEntryPoints.Buffer)
                {
                    var result = API.regorus_engine_compile_program_with_entrypoints(
                        (RegorusEngine*)enginePtr,
                        (byte**)entryPtr,
                        (UIntPtr)pinnedEntryPoints.Length);

                    return GetProgramResult(result);
                }
            });
        }

        /// <summary>
        /// Compile an RVM program from modules, entry points, and registered host-awaitable builtins.
        /// </summary>
        /// <param name="hostAwaitBuiltins">Legacy name-only registrations; each call accepts one raw input value.</param>
        /// <remarks>
        /// This legacy path registers one-input calls and passes the raw input
        /// value to the host, including arrays and objects.
        /// </remarks>
        public static Program CompileFromModules(string dataJson, IReadOnlyList<PolicyModule> modules, IReadOnlyList<string> entryPoints, IReadOnlyList<HostAwaitBuiltin> hostAwaitBuiltins)
        {
            if (hostAwaitBuiltins is null)
            {
                throw new ArgumentNullException(nameof(hostAwaitBuiltins));
            }

            return CompileFromModulesInner(dataJson, modules, entryPoints, hostAwaitBuiltins);
        }

        /// <summary>
        /// Compile an RVM program using separate legacy raw-value and explicitly
        /// versioned packed-array host-await registrations.
        /// </summary>
        /// <param name="dataJson">JSON string containing static data for policy evaluation.</param>
        /// <param name="modules">Policy modules to compile.</param>
        /// <param name="entryPoints">Entry point rule paths.</param>
        /// <param name="legacyHostAwaitBuiltins">Legacy one-input registrations that pass raw values.</param>
        /// <param name="hostAwaitBuiltinsV2">Fixed-arity registrations that pass ordered arrays.</param>
        public static Program CompileFromModulesWithHostAwaitV2(
            string dataJson,
            IReadOnlyList<PolicyModule> modules,
            IReadOnlyList<string> entryPoints,
            IReadOnlyList<HostAwaitBuiltin> legacyHostAwaitBuiltins,
            IReadOnlyList<HostAwaitBuiltinV2> hostAwaitBuiltinsV2)
        {
            if (legacyHostAwaitBuiltins is null)
            {
                throw new ArgumentNullException(nameof(legacyHostAwaitBuiltins));
            }

            if (hostAwaitBuiltinsV2 is null)
            {
                throw new ArgumentNullException(nameof(hostAwaitBuiltinsV2));
            }

            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            if (entryPoints is null)
            {
                throw new ArgumentNullException(nameof(entryPoints));
            }

            if (entryPoints.Count == 0)
            {
                throw new ArgumentException("At least one entry point is required.", nameof(entryPoints));
            }

            using var pinnedModules = ModuleMarshalling.PinPolicyModules(modules);
            using var pinnedEntryPoints = ModuleMarshalling.PinUtf8Strings(entryPoints);
            using var pinnedLegacyBuiltins = ModuleMarshalling.PinHostAwaitBuiltins(legacyHostAwaitBuiltins);
            using var pinnedV2Builtins = ModuleMarshalling.PinHostAwaitBuiltinsV2(hostAwaitBuiltinsV2);

            return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
            {
                fixed (RegorusPolicyModule* modulesPtr = pinnedModules.Buffer)
                fixed (IntPtr* entryPtr = pinnedEntryPoints.Buffer)
                fixed (RegorusHostAwaitBuiltin* legacyBuiltinsPtr = pinnedLegacyBuiltins.Buffer)
                fixed (RegorusHostAwaitBuiltinV2* v2BuiltinsPtr = pinnedV2Builtins.Buffer)
                {
                    var result = API.regorus_program_compile_from_modules_with_host_await_v2(
                        (byte*)dataPtr,
                        modulesPtr,
                        (UIntPtr)pinnedModules.Length,
                        (byte**)entryPtr,
                        (UIntPtr)pinnedEntryPoints.Length,
                        legacyBuiltinsPtr,
                        (UIntPtr)pinnedLegacyBuiltins.Length,
                        (UIntPtr)sizeof(RegorusHostAwaitBuiltin),
                        v2BuiltinsPtr,
                        (UIntPtr)pinnedV2Builtins.Length,
                        (UIntPtr)sizeof(RegorusHostAwaitBuiltinV2));

                    return GetProgramResult(result);
                }
            });
        }

        private static Program CompileFromModulesInner(string dataJson, IReadOnlyList<PolicyModule> modules, IReadOnlyList<string> entryPoints, IReadOnlyList<HostAwaitBuiltin>? hostAwaitBuiltins)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            if (entryPoints is null)
            {
                throw new ArgumentNullException(nameof(entryPoints));
            }

            if (entryPoints.Count == 0)
            {
                throw new ArgumentException("At least one entry point is required.", nameof(entryPoints));
            }

            using var pinnedModules = ModuleMarshalling.PinPolicyModules(modules);
            using var pinnedEntryPoints = ModuleMarshalling.PinUtf8Strings(entryPoints);

            var hostAwaitBuiltinsOrEmpty = hostAwaitBuiltins ?? Array.Empty<HostAwaitBuiltin>();

            return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
            {
                fixed (RegorusPolicyModule* modulesPtr = pinnedModules.Buffer)
                fixed (IntPtr* entryPtr = pinnedEntryPoints.Buffer)
                {
                    RegorusResult result;
                    if (hostAwaitBuiltinsOrEmpty.Count == 0)
                    {
                        // No host-await builtins: use the original FFI entry point so an
                        // app updating only the managed package against an older native
                        // library (without the host-await symbol) stays binary-compatible
                        // instead of hitting EntryPointNotFoundException.
                        result = API.regorus_program_compile_from_modules(
                            (byte*)dataPtr,
                            modulesPtr,
                            (UIntPtr)pinnedModules.Length,
                            (byte**)entryPtr,
                            (UIntPtr)pinnedEntryPoints.Length);
                    }
                    else
                    {
                        using var pinnedBuiltins = ModuleMarshalling.PinHostAwaitBuiltins(hostAwaitBuiltinsOrEmpty);
                        fixed (RegorusHostAwaitBuiltin* builtinsPtr = pinnedBuiltins.Buffer)
                        {
                            result = API.regorus_program_compile_from_modules_with_host_await(
                                (byte*)dataPtr,
                                modulesPtr,
                                (UIntPtr)pinnedModules.Length,
                                (byte**)entryPtr,
                                (UIntPtr)pinnedEntryPoints.Length,
                                builtinsPtr,
                                (UIntPtr)pinnedBuiltins.Length,
                                (UIntPtr)sizeof(RegorusHostAwaitBuiltin));
                        }
                    }

                    return GetProgramResult(result);
                }
            });
        }

        /// <summary>
        /// Deserialize an RVM program from binary format.
        /// </summary>
        public static Program DeserializeBinary(byte[] data, out bool isPartial)
        {
            if (data is null)
            {
                throw new ArgumentNullException(nameof(data));
            }

            byte partialFlag = 0;
            fixed (byte* dataPtr = data)
            {
                var result = API.regorus_program_deserialize_binary(dataPtr, (UIntPtr)data.Length, &partialFlag);
                var program = GetProgramResult(result);
                isPartial = partialFlag != 0;
                return program;
            }
        }

        /// <summary>
        /// Serialize the program to binary format.
        /// </summary>
        public byte[] SerializeBinary()
        {
            return UseHandle(programPtr =>
            {
                var result = API.regorus_program_serialize_binary((RegorusProgram*)programPtr);
                return ExtractBuffer(result);
            });
        }

        /// <summary>
        /// Generate a readable assembly listing.
        /// </summary>
        public string? GenerateListing()
        {
            return UseHandle(programPtr =>
            {
                return CheckAndDropResult(API.regorus_program_generate_listing((RegorusProgram*)programPtr));
            });
        }

        /// <summary>
        /// Get the builtin names recorded in this program, in table order.
        /// Registered host-await builtins are not included.
        /// </summary>
        public IReadOnlyList<string> GetBuiltinNames()
        {
            return UseHandle(programPtr =>
            {
                var json = CheckAndDropResult(
                    API.regorus_program_get_builtin_names((RegorusProgram*)programPtr));
                if (json is null)
                {
                    throw new InvalidOperationException("Native library returned no builtin names.");
                }

                var names = JsonSerializer.Deserialize<string[]>(json);
                if (names is null || names.Any(name => name is null))
                {
                    throw new InvalidOperationException("Native library returned invalid builtin names.");
                }

                return Array.AsReadOnly(names);
            });
        }

        private static Program GetProgramResult(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                if (result.data_type != RegorusDataType.Pointer || result.pointer_value == null)
                {
                    throw new Exception("Expected program pointer but got different data type");
                }

                var handle = RegorusProgramHandle.FromPointer((IntPtr)result.pointer_value);
                return new Program(handle);
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        private static string? CheckAndDropResult(RegorusResult result)
        {
            return ResultHelpers.GetStringResult(result);
        }

        private static byte[] ExtractBuffer(RegorusResult result)
        {
            RegorusBuffer* buffer = null;
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                if (result.data_type != RegorusDataType.Pointer || result.pointer_value == null)
                {
                    throw new Exception("Expected buffer pointer but got different data type");
                }

                buffer = (RegorusBuffer*)result.pointer_value;
                var length = checked((int)buffer->len);
                var data = new byte[length];
                if (length > 0)
                {
                    Marshal.Copy((IntPtr)buffer->data, data, 0, length);
                }
                return data;
            }
            finally
            {
                if (buffer != null)
                {
                    API.regorus_buffer_drop(buffer);
                }
                API.regorus_result_drop(result);
            }
        }
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Represents a compiled RVM program.
    /// </summary>
    public unsafe sealed class Program : SafeHandleWrapper
    {
        private Program(RegorusProgramHandle handle)
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
            using var pinnedEntryPoints = ModuleMarshalling.PinEntryPoints(entryPoints);

            return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
            {
                fixed (RegorusPolicyModule* modulesPtr = pinnedModules.Buffer)
                fixed (IntPtr* entryPtr = pinnedEntryPoints.Buffer)
                {
                    var result = API.regorus_program_compile_from_modules(
                        (byte*)dataPtr,
                        modulesPtr,
                        (UIntPtr)pinnedModules.Length,
                        (byte**)entryPtr,
                        (UIntPtr)pinnedEntryPoints.Length);

                    return GetProgramResult(result);
                }
            });
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

            using var pinnedEntryPoints = ModuleMarshalling.PinEntryPoints(entryPoints);

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

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
    public unsafe sealed class Program : IDisposable
    {
        private RegorusProgramHandle? _handle;
        private int _isDisposed;

        private Program(RegorusProgramHandle handle)
        {
            _handle = handle ?? throw new ArgumentNullException(nameof(handle));
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
            var modulesArray = modules.ToArray();
            var entryPointsArray = entryPoints.ToArray();
            if (entryPointsArray.Length == 0)
            {
                throw new ArgumentException("At least one entry point is required.", nameof(entryPoints));
            }

            var nativeModules = new RegorusPolicyModule[modulesArray.Length];
            var pinnedStrings = new List<Utf8Marshaller.PinnedUtf8>(modulesArray.Length * 2 + entryPointsArray.Length);
            var entryPointers = new IntPtr[entryPointsArray.Length];

            try
            {
                for (int i = 0; i < modulesArray.Length; i++)
                {
                    var idPinned = Utf8Marshaller.Pin(modulesArray[i].Id);
                    var contentPinned = Utf8Marshaller.Pin(modulesArray[i].Content);
                    pinnedStrings.Add(idPinned);
                    pinnedStrings.Add(contentPinned);

                    nativeModules[i] = new RegorusPolicyModule
                    {
                        id = idPinned.Pointer,
                        content = contentPinned.Pointer
                    };
                }

                for (int i = 0; i < entryPointsArray.Length; i++)
                {
                    var entryPinned = Utf8Marshaller.Pin(entryPointsArray[i]);
                    pinnedStrings.Add(entryPinned);
                    entryPointers[i] = (IntPtr)entryPinned.Pointer;
                }

                return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
                {
                    fixed (RegorusPolicyModule* modulesPtr = nativeModules)
                    fixed (IntPtr* entryPtr = entryPointers)
                    {
                        var result = API.regorus_program_compile_from_modules(
                            (byte*)dataPtr,
                            modulesPtr,
                            (UIntPtr)modulesArray.Length,
                            (byte**)entryPtr,
                            (UIntPtr)entryPointsArray.Length);

                        return GetProgramResult(result);
                    }
                });
            }
            finally
            {
                foreach (var pinned in pinnedStrings)
                {
                    pinned.Dispose();
                }
            }
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

            var entryPointsArray = entryPoints.ToArray();
            if (entryPointsArray.Length == 0)
            {
                throw new ArgumentException("At least one entry point is required.", nameof(entryPoints));
            }

            var pinnedStrings = new List<Utf8Marshaller.PinnedUtf8>(entryPointsArray.Length);
            var entryPointers = new IntPtr[entryPointsArray.Length];
            try
            {
                for (int i = 0; i < entryPointsArray.Length; i++)
                {
                    var entryPinned = Utf8Marshaller.Pin(entryPointsArray[i]);
                    pinnedStrings.Add(entryPinned);
                    entryPointers[i] = (IntPtr)entryPinned.Pointer;
                }

                return engine.UseHandleForInterop(enginePtr =>
                {
                    fixed (IntPtr* entryPtr = entryPointers)
                    {
                        var result = API.regorus_engine_compile_program_with_entrypoints(
                            (RegorusEngine*)enginePtr,
                            (byte**)entryPtr,
                            (UIntPtr)entryPointsArray.Length);

                        return GetProgramResult(result);
                    }
                });
            }
            finally
            {
                foreach (var pinned in pinnedStrings)
                {
                    pinned.Dispose();
                }
            }
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
            ThrowIfDisposed();
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
            ThrowIfDisposed();
            return UseHandle(programPtr =>
            {
                return CheckAndDropResult(API.regorus_program_generate_listing((RegorusProgram*)programPtr));
            });
        }

        public void Dispose()
        {
            Dispose(disposing: true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing)
        {
            if (System.Threading.Interlocked.CompareExchange(ref _isDisposed, 1, 0) == 0)
            {
                _handle?.Dispose();
                _handle = null;
            }
        }

        private void ThrowIfDisposed()
        {
            if (_isDisposed != 0 || _handle is null || _handle.IsClosed)
            {
                throw new ObjectDisposedException(nameof(Program));
            }
        }

        internal RegorusProgramHandle GetHandleForUse()
        {
            var handle = _handle;
            if (handle is null || handle.IsClosed || handle.IsInvalid)
            {
                throw new ObjectDisposedException(nameof(Program));
            }
            return handle;
        }

        internal T UseHandle<T>(Func<IntPtr, T> func)
        {
            var handle = GetHandleForUse();
            bool addedRef = false;
            try
            {
                handle.DangerousAddRef(ref addedRef);
                var pointer = handle.DangerousGetHandle();
                if (pointer == IntPtr.Zero)
                {
                    throw new ObjectDisposedException(nameof(Program));
                }

                return func(pointer);
            }
            finally
            {
                if (addedRef)
                {
                    handle.DangerousRelease();
                }
            }
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
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type switch
                {
                    RegorusDataType.String => Utf8Marshaller.FromUtf8(result.output),
                    RegorusDataType.Boolean => result.bool_value.ToString().ToLowerInvariant(),
                    RegorusDataType.Integer => result.int_value.ToString(),
                    RegorusDataType.None => null,
                    _ => Utf8Marshaller.FromUtf8(result.output)
                };
            }
            finally
            {
                API.regorus_result_drop(result);
            }
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

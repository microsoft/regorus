// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Text;
using Regorus;

#nullable enable

namespace Regorus.Internal
{
    internal static class NativeUtf8
    {
        internal static byte[] GetNullTerminatedBytes(string value)
        {
            if (value is null)
            {
                throw new ArgumentNullException(nameof(value));
            }

            // Append a null terminator as expected by the native layer.
            var byteCount = Encoding.UTF8.GetByteCount(value);
            var buffer = new byte[byteCount + 1];
            Encoding.UTF8.GetBytes(value, 0, value.Length, buffer, 0);
            buffer[buffer.Length - 1] = 0;
            return buffer;
        }

        internal static string? PtrToString(IntPtr ptr)
        {
            if (ptr == IntPtr.Zero)
            {
                return null;
            }

#if NETSTANDARD2_1
            return Marshal.PtrToStringUTF8(ptr);
#else
            int length = 0;
            while (Marshal.ReadByte(ptr, length) != 0)
            {
                length++;
            }

            if (length == 0)
            {
                return string.Empty;
            }

            var buffer = new byte[length];
            Marshal.Copy(ptr, buffer, 0, length);
            return Encoding.UTF8.GetString(buffer);
#endif
        }
    }

    internal static unsafe class NativeResult
    {
        private static RegorusException BuildError(RegorusResult result)
        {
            var message = NativeUtf8.PtrToString(new IntPtr(result.error_message));
            return new RegorusException(message ?? "Regorus native call failed.");
        }

        internal static void EnsureSuccess(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    throw BuildError(result);
                }
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        internal static string? GetStringAndDrop(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    throw BuildError(result);
                }

                return NativeUtf8.PtrToString(new IntPtr(result.output));
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        internal static bool GetBoolAndDrop(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    throw BuildError(result);
                }

                return result.bool_value;
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        internal static long GetInt64AndDrop(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    throw BuildError(result);
                }

                return result.int_value;
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        internal static ulong GetUInt64AndDrop(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    throw BuildError(result);
                }

                return result.u64_value;
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        internal static IntPtr GetPointerAndDrop(RegorusResult result, RegorusPointerType expectedType)
        {
            if (result.status != RegorusStatus.Ok)
            {
                var error = BuildError(result);
                API.regorus_result_drop(result);
                throw error;
            }

            if (result.data_type != RegorusDataType.Pointer)
            {
                var error = new RegorusException($"Expected pointer result but received {result.data_type}.");
                API.regorus_result_drop(result);
                throw error;
            }

            if (expectedType != RegorusPointerType.PointerNone && result.pointer_type != expectedType)
            {
                var error = new RegorusException($"Unexpected pointer type {result.pointer_type}; expected {expectedType}.");
                API.regorus_result_drop(result);
                throw error;
            }

            var pointer = new IntPtr(result.pointer_value);

            // Prevent the native drop helper from freeing the pointer we are taking ownership of.
            result.pointer_value = null;
            result.pointer_type = RegorusPointerType.PointerNone;

            API.regorus_result_drop(result);
            return pointer;
        }
    }

    internal sealed unsafe class PinnedUtf8StringArray : IDisposable
    {
        private readonly GCHandle[] _stringHandles;
        private readonly GCHandle _arrayHandle;

        internal PinnedUtf8StringArray(IEnumerable<string>? values)
        {
            if (values is null)
            {
                _stringHandles = Array.Empty<GCHandle>();
                _arrayHandle = default;
                Length = 0;
                return;
            }

            var buffers = new List<byte[]>();
            foreach (var value in values)
            {
                if (value is null)
                {
                    throw new ArgumentNullException(nameof(values), "Field names cannot contain null entries.");
                }

                buffers.Add(NativeUtf8.GetNullTerminatedBytes(value));
            }

            _stringHandles = new GCHandle[buffers.Count];

            if (buffers.Count > 0)
            {
                var pointerArray = new IntPtr[buffers.Count];
                for (int i = 0; i < buffers.Count; i++)
                {
                    _stringHandles[i] = GCHandle.Alloc(buffers[i], GCHandleType.Pinned);
                    pointerArray[i] = _stringHandles[i].AddrOfPinnedObject();
                }

                _arrayHandle = GCHandle.Alloc(pointerArray, GCHandleType.Pinned);
                Length = buffers.Count;
            }
            else
            {
                _arrayHandle = default;
                Length = 0;
            }
        }

        internal byte** Pointer => _arrayHandle.IsAllocated ? (byte**)_arrayHandle.AddrOfPinnedObject().ToPointer() : null;

        internal UIntPtr LengthPtr => (UIntPtr)Length;

        internal int Length { get; }

        public void Dispose()
        {
            if (_arrayHandle.IsAllocated)
            {
                _arrayHandle.Free();
            }

            for (int i = 0; i < _stringHandles.Length; i++)
            {
                if (_stringHandles[i].IsAllocated)
                {
                    _stringHandles[i].Free();
                }
            }
        }
    }

    internal sealed unsafe class PinnedIntPtrArray : IDisposable
    {
        private readonly IntPtr[] _values;
        private readonly GCHandle _handle;

        internal PinnedIntPtrArray(IReadOnlyList<IntPtr>? values)
        {
            if (values is null || values.Count == 0)
            {
                _values = Array.Empty<IntPtr>();
                _handle = default;
                Length = 0;
                return;
            }

            _values = new IntPtr[values.Count];
            for (int i = 0; i < values.Count; i++)
            {
                _values[i] = values[i];
            }

            _handle = GCHandle.Alloc(_values, GCHandleType.Pinned);
            Length = _values.Length;
        }

        internal IntPtr* Pointer => _handle.IsAllocated ? (IntPtr*)_handle.AddrOfPinnedObject().ToPointer() : null;

        internal UIntPtr LengthPtr => (UIntPtr)Length;

        internal int Length { get; }

        public void Dispose()
        {
            if (_handle.IsAllocated)
            {
                _handle.Free();
            }
        }
    }
}

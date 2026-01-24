// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Buffers;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;

#nullable enable
namespace Regorus.Internal
{
    /// <summary>
    /// Helpers for marshaling managed strings to null-terminated UTF-8 buffers.
    /// Provides stack-based storage for short lived conversions and pooled backing
    /// for longer lived pinned buffers.
    /// </summary>
    internal static class Utf8Marshaller
    {
    // Mirrors BCL patterns (e.g., System.Text.Json encoding helpers) by stackalloc'ing
    // up to 512 bytes to cover common short strings while keeping the stack usage well
    // below typical per-frame limits; larger payloads fall back to pooled buffers.
    private const int StackAllocThreshold = 512;

        /// <summary>
        /// Represents a pooled and pinned UTF-8 buffer suitable for scenarios where
        /// the pointer must remain stable beyond the immediate call site (for example,
        /// when referenced by another buffer passed to native code).
        /// </summary>
        internal sealed class PinnedUtf8 : IDisposable
        {
            private GCHandle _handle;
            private byte[]? _buffer;
            private bool _disposed;

            internal unsafe PinnedUtf8(string value)
            {
                if (value is null)
                {
                    throw new ArgumentNullException(nameof(value));
                }

                var byteCount = Encoding.UTF8.GetByteCount(value);
                _buffer = ArrayPool<byte>.Shared.Rent(byteCount + 1);

                try
                {
                    var written = Encoding.UTF8.GetBytes(value, 0, value.Length, _buffer, 0);
                    _buffer[written] = 0;

                    _handle = GCHandle.Alloc(_buffer, GCHandleType.Pinned);
                    Pointer = (byte*)_handle.AddrOfPinnedObject();
                    Length = written + 1;
                }
                catch
                {
                    ArrayPool<byte>.Shared.Return(_buffer);
                    _buffer = null;
                    throw;
                }
            }

            internal unsafe byte* Pointer { get; }

            internal int Length { get; }

            public void Dispose()
            {
                if (_disposed)
                {
                    return;
                }

                if (_handle.IsAllocated)
                {
                    _handle.Free();
                }

                if (_buffer != null)
                {
                    ArrayPool<byte>.Shared.Return(_buffer);
                    _buffer = null;
                }

                _disposed = true;
            }
        }

        internal unsafe delegate void Utf8PointerAction(byte* pointer);

        internal static unsafe void WithUtf8(string value, Utf8PointerAction action)
        {
            if (action is null)
            {
                throw new ArgumentNullException(nameof(action));
            }

            WithUtf8<object?>(value, ptr =>
            {
                action((byte*)ptr);
                return null;
            });
        }

        internal static T WithUtf8<T>(string value, Func<IntPtr, T> func)
        {
            if (value is null)
            {
                throw new ArgumentNullException(nameof(value));
            }

            if (func is null)
            {
                throw new ArgumentNullException(nameof(func));
            }

            var byteCount = Encoding.UTF8.GetByteCount(value);
            var required = byteCount + 1;

            if (required <= StackAllocThreshold)
            {
                Span<byte> buffer = stackalloc byte[required];
                return Invoke(value, func, buffer, byteCount);
            }

            var rented = ArrayPool<byte>.Shared.Rent(required);
            try
            {
                Span<byte> buffer = rented;
                return Invoke(value, func, buffer, byteCount);
            }
            finally
            {
                ArrayPool<byte>.Shared.Return(rented);
            }
        }

        private static unsafe T Invoke<T>(string value, Func<IntPtr, T> func, Span<byte> buffer, int byteCount)
        {
            fixed (char* charPtr = value)
            fixed (byte* bytePtr = buffer)
            {
                var written = Encoding.UTF8.GetBytes(charPtr, value.Length, bytePtr, byteCount);
                bytePtr[written] = 0;
                return func((IntPtr)bytePtr);
            }
        }

        internal static PinnedUtf8 Pin(string value)
        {
            return new PinnedUtf8(value);
        }

        internal static unsafe string? FromUtf8(byte* pointer)
        {
            if (pointer is null)
            {
                return null;
            }

#if NETSTANDARD2_1
            return Marshal.PtrToStringUTF8((IntPtr)pointer);
#else
            var intPtr = (IntPtr)pointer;
            var length = 0;
            while (Marshal.ReadByte(intPtr, length) != 0)
            {
                length++;
            }

            if (length == 0)
            {
                return string.Empty;
            }

            var buffer = ArrayPool<byte>.Shared.Rent(length);
            try
            {
                Marshal.Copy(intPtr, buffer, 0, length);
                return Encoding.UTF8.GetString(buffer, 0, length);
            }
            finally
            {
                ArrayPool<byte>.Shared.Return(buffer);
            }
#endif
        }

        internal static string? FromUtf8(IntPtr pointer)
        {
            unsafe
            {
                return FromUtf8((byte*)pointer);
            }
        }
    }
}

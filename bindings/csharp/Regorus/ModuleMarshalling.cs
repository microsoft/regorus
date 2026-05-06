// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Buffers;
using System.Collections.Generic;
using Regorus;

#nullable enable

namespace Regorus.Internal
{
    internal static unsafe class ModuleMarshalling
    {
        internal sealed class PinnedPolicyModules : IDisposable
        {
            private readonly List<Utf8Marshaller.PinnedUtf8> _pins;
            private bool _disposed;

            internal PinnedPolicyModules(RegorusPolicyModule[] buffer, int length, List<Utf8Marshaller.PinnedUtf8> pins)
            {
                Buffer = buffer;
                Length = length;
                _pins = pins;
            }

            internal RegorusPolicyModule[] Buffer { get; }

            internal int Length { get; }

            public void Dispose()
            {
                if (_disposed)
                {
                    return;
                }

                foreach (var pin in _pins)
                {
                    pin.Dispose();
                }

                ArrayPool<RegorusPolicyModule>.Shared.Return(Buffer, clearArray: true);
                _disposed = true;
            }
        }

        internal sealed class PinnedUtf8Strings : IDisposable
        {
            private readonly List<Utf8Marshaller.PinnedUtf8> _pins;
            private bool _disposed;

            internal PinnedUtf8Strings(IntPtr[] buffer, int length, List<Utf8Marshaller.PinnedUtf8> pins)
            {
                Buffer = buffer;
                Length = length;
                _pins = pins;
            }

            internal IntPtr[] Buffer { get; }

            internal int Length { get; }

            public void Dispose()
            {
                if (_disposed)
                {
                    return;
                }

                foreach (var pin in _pins)
                {
                    pin.Dispose();
                }

                ArrayPool<IntPtr>.Shared.Return(Buffer, clearArray: true);
                _disposed = true;
            }
        }

        internal static PinnedPolicyModules PinPolicyModules(IReadOnlyList<PolicyModule> modules)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            var count = modules.Count;
            var buffer = ArrayPool<RegorusPolicyModule>.Shared.Rent(count);
            var pins = new List<Utf8Marshaller.PinnedUtf8>(count * 2);

            try
            {
                for (int i = 0; i < count; i++)
                {
                    var idPinned = Utf8Marshaller.Pin(modules[i].Id);
                    var contentPinned = Utf8Marshaller.Pin(modules[i].Content);
                    pins.Add(idPinned);
                    pins.Add(contentPinned);

                    buffer[i] = new RegorusPolicyModule
                    {
                        id = idPinned.Pointer,
                        content = contentPinned.Pointer
                    };
                }

                return new PinnedPolicyModules(buffer, count, pins);
            }
            catch
            {
                foreach (var pin in pins)
                {
                    pin.Dispose();
                }

                ArrayPool<RegorusPolicyModule>.Shared.Return(buffer, clearArray: true);
                throw;
            }
        }

        internal static PinnedUtf8Strings PinUtf8Strings(IReadOnlyList<string> values)
        {
            if (values is null)
            {
                throw new ArgumentNullException(nameof(values));
            }

            var count = values.Count;
            var buffer = ArrayPool<IntPtr>.Shared.Rent(count);
            var pins = new List<Utf8Marshaller.PinnedUtf8>(count);

            try
            {
                for (int i = 0; i < count; i++)
                {
                    var pinned = Utf8Marshaller.Pin(values[i]);
                    pins.Add(pinned);
                    buffer[i] = (IntPtr)pinned.Pointer;
                }

                return new PinnedUtf8Strings(buffer, count, pins);
            }
            catch
            {
                foreach (var pin in pins)
                {
                    pin.Dispose();
                }

                ArrayPool<IntPtr>.Shared.Return(buffer, clearArray: true);
                throw;
            }
        }

        internal sealed class PinnedHostAwaitBuiltins : IDisposable
        {
            private readonly List<Utf8Marshaller.PinnedUtf8> _pins;
            private bool _disposed;

            internal PinnedHostAwaitBuiltins(RegorusHostAwaitBuiltin[] buffer, int length, List<Utf8Marshaller.PinnedUtf8> pins)
            {
                Buffer = buffer;
                Length = length;
                _pins = pins;
            }

            internal RegorusHostAwaitBuiltin[] Buffer { get; }

            internal int Length { get; }

            public void Dispose()
            {
                if (_disposed)
                {
                    return;
                }

                foreach (var pin in _pins)
                {
                    pin.Dispose();
                }

                ArrayPool<RegorusHostAwaitBuiltin>.Shared.Return(Buffer, clearArray: true);
                _disposed = true;
            }
        }

        internal static PinnedHostAwaitBuiltins PinHostAwaitBuiltins(IReadOnlyList<HostAwaitBuiltin> builtins)
        {
            if (builtins is null)
            {
                throw new ArgumentNullException(nameof(builtins));
            }

            var count = builtins.Count;
            var buffer = ArrayPool<RegorusHostAwaitBuiltin>.Shared.Rent(count);
            var pins = new List<Utf8Marshaller.PinnedUtf8>(count);

            try
            {
                for (int i = 0; i < count; i++)
                {
                    var namePinned = Utf8Marshaller.Pin(builtins[i].Name);
                    pins.Add(namePinned);

                    buffer[i] = new RegorusHostAwaitBuiltin
                    {
                        name = namePinned.Pointer,
                        arg_count = (UIntPtr)builtins[i].ArgCount,
                    };
                }

                return new PinnedHostAwaitBuiltins(buffer, count, pins);
            }
            catch
            {
                foreach (var pin in pins)
                {
                    pin.Dispose();
                }

                ArrayPool<RegorusHostAwaitBuiltin>.Shared.Return(buffer, clearArray: true);
                throw;
            }
        }
    }
}

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

        internal sealed class PinnedEntryPoints : IDisposable
        {
            private readonly List<Utf8Marshaller.PinnedUtf8> _pins;
            private bool _disposed;

            internal PinnedEntryPoints(IntPtr[] buffer, int length, List<Utf8Marshaller.PinnedUtf8> pins)
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

        internal static PinnedEntryPoints PinEntryPoints(IReadOnlyList<string> entryPoints)
        {
            if (entryPoints is null)
            {
                throw new ArgumentNullException(nameof(entryPoints));
            }

            var count = entryPoints.Count;
            var buffer = ArrayPool<IntPtr>.Shared.Rent(count);
            var pins = new List<Utf8Marshaller.PinnedUtf8>(count);

            try
            {
                for (int i = 0; i < count; i++)
                {
                    var entryPinned = Utf8Marshaller.Pin(entryPoints[i]);
                    pins.Add(entryPinned);
                    buffer[i] = (IntPtr)entryPinned.Pointer;
                }

                return new PinnedEntryPoints(buffer, count, pins);
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
    }
}

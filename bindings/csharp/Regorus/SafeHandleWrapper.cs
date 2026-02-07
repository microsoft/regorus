// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Runtime.InteropServices;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Base class for native handle wrappers that coordinates handle usage and disposal.
    ///
    /// Behavior summary:
    /// - UseHandle: blocks Dispose while running; throws ObjectDisposedException if disposal has started or the handle is invalid.
    /// - Dispose: marks disposing and blocks new calls; waits briefly for in-flight calls to finish, then defers native release to the last exiting call if needed.
    /// - Handles are never exposed directly; derived classes can only work through UseHandle helpers.
    ///
    /// Concurrency model:
    /// - _state tracks lifecycle transitions (Active -> DisposeRequested -> Released).
    /// - HandleGate tracks in-flight operations and enforces the "no new calls after Dispose" rule.
    /// - SafeHandle is pinned per call via DangerousAddRef to prevent use-after-free while native work runs.
    /// - If Dispose times out, the last in-flight caller performs the release to avoid leaks.
    /// </summary>
    public abstract class SafeHandleWrapper : IDisposable
    {
        private static readonly TimeSpan DefaultDisposeTimeout = TimeSpan.FromMilliseconds(50);
        private const int StateActive = 0;
        private const int StateDisposeRequested = 1;
        private const int StateReleased = 2;
        private readonly HandleGate _gate;
        private readonly string _ownerName;
        private int _state;
        private SafeHandle? _handle;

        protected SafeHandleWrapper(SafeHandle handle, string ownerName)
        {
            // Cache ownership info and initialize the gate before any use to avoid racing disposal.
            _handle = handle ?? throw new ArgumentNullException(nameof(handle));
            _ownerName = ownerName ?? throw new ArgumentNullException(nameof(ownerName));
            _gate = new HandleGate(ownerName);
            // Default to a very short wait when in-flight calls exist; release is deferred to the last caller if needed.
        }

        protected void UseHandle(Action<IntPtr> action)
        {
            // Reuse the generic path to keep add/ref/release in one place.
            UseHandle<object?>(ptr =>
            {
                action(ptr);
                return null;
            });
        }

        protected T UseHandle<T>(Func<IntPtr, T> func)
        {
            // Fast reject if dispose was requested.
            if (System.Threading.Volatile.Read(ref _state) != StateActive)
            {
                throw new ObjectDisposedException(_ownerName);
            }

            // Enter gate so Dispose waits for in-flight native calls.
            _gate.Enter();
            bool addedRef = false;
            SafeHandle? handle = null;
            try
            {
                // Race: Dispose could begin after Enter; GetHandleForUse validates the handle again.
                handle = GetHandleForUse();
                // DangerousAddRef pins the SafeHandle so Dispose cannot close it mid-call.
                handle.DangerousAddRef(ref addedRef);
                var pointer = handle.DangerousGetHandle();
                // Validate pointer after AddRef in case handle became invalid between checks.
                if (pointer == IntPtr.Zero)
                {
                    throw new ObjectDisposedException(_ownerName);
                }

                return func(pointer);
            }
            finally
            {
                // Always release the DangerousAddRef to avoid leaking the native handle.
                if (addedRef)
                {
                    handle?.DangerousRelease();
                }

                // Leave gate so Dispose can proceed when the last caller exits.
                var idle = _gate.Exit();
                // Race: Dispose may have timed out while we were in-flight.
                // The last exiting caller performs the native release to avoid leaks.
                if (idle && System.Threading.Volatile.Read(ref _state) == StateDisposeRequested)
                {
                    TryReleaseHandle();
                }
            }
        }

        internal T UseHandleForInterop<T>(Func<IntPtr, T> func)
        {
            // Explicit alias for interop-specific call sites.
            return UseHandle(func);
        }

        internal void UseHandleForInterop(Action<IntPtr> action)
        {
            // Explicit alias for interop-specific call sites.
            UseHandle(action);
        }

        private void ThrowIfDisposed()
        {
            // Fast check for dispose state so callers fail deterministically.
            if (System.Threading.Volatile.Read(ref _state) != StateActive)
            {
                throw new ObjectDisposedException(_ownerName);
            }

            // Validate the underlying SafeHandle is still usable; avoids races with release.
            var handle = _handle;
            if (handle is null || handle.IsClosed || handle.IsInvalid)
            {
                throw new ObjectDisposedException(_ownerName);
            }
        }

        private SafeHandle GetHandleForUse()
        {
            // Centralized gate for derived classes to grab the handle safely.
            // This is a second line of defense in case disposal began after the initial state check.
            var handle = _handle;
            if (handle is null || handle.IsClosed || handle.IsInvalid)
            {
                throw new ObjectDisposedException(_ownerName);
            }
            return handle;
        }

        public void Dispose()
        {
            // Only the first caller runs disposal; others become no-ops.
            if (System.Threading.Interlocked.CompareExchange(ref _state, StateDisposeRequested, StateActive) == StateActive)
            {
                // Block new calls and wait briefly if there are in-flight operations.
                var completed = _gate.TryBeginDispose(DefaultDisposeTimeout, out var hadActive);
                if (completed)
                {
                    // Either no active calls or they drained within the short timeout.
                    TryReleaseHandle();
                }
                else
                {
                    // Defer release to the last in-flight caller to avoid leaks without blocking indefinitely.
                    // Race: if the last in-flight caller already exited, there will be no Exit() to trigger release.
                    // Re-check active state and release immediately in that case.
                    if (!hadActive || _gate.IsIdle)
                    {
                        TryReleaseHandle();
                    }
                }
            }

            GC.SuppressFinalize(this);
        }

        private void TryReleaseHandle()
        {
            if (System.Threading.Interlocked.CompareExchange(ref _state, StateReleased, StateDisposeRequested) != StateDisposeRequested)
            {
                return;
            }

            // Once released, no caller should be able to observe a valid handle.
            // SafeHandle.Dispose closes the native resource; null to prevent reuse after dispose.
            _handle?.Dispose();
            _handle = null;
            // Release the wait handle resources after disposal completes.
            _gate.Dispose();
        }

        /// <summary>
        /// Tracks in-flight operations and coordinates disposal.
        /// </summary>
        private sealed class HandleGate : IDisposable
        {
            private readonly string _ownerName;
            private readonly System.Threading.ManualResetEventSlim _idle = new(initialState: true);
            private int _active;
            private int _disposing;

            internal HandleGate(string ownerName)
            {
                _ownerName = ownerName;
            }

            internal void Enter()
            {
                // If disposal already started, reject new work immediately.
                if (System.Threading.Volatile.Read(ref _disposing) != 0)
                {
                    ThrowDisposed();
                }

                // Track active callers; first one resets idle event.
                var active = System.Threading.Interlocked.Increment(ref _active);
                if (active == 1)
                {
                    _idle.Reset();
                }

                // Re-check disposing to handle races where Dispose began after increment.
                if (System.Threading.Volatile.Read(ref _disposing) != 0)
                {
                    Exit();
                    ThrowDisposed();
                }
            }

            internal bool Exit()
            {
                // Last caller signals idle so Dispose can continue.
                if (System.Threading.Interlocked.Decrement(ref _active) == 0)
                {
                    _idle.Set();
                    return true;
                }

                return false;
            }

            internal bool IsIdle => System.Threading.Volatile.Read(ref _active) == 0;

            internal bool TryBeginDispose(TimeSpan timeout, out bool hadActive)
            {
                // Set disposing flag once; subsequent calls treat as already disposing.
                if (System.Threading.Interlocked.Exchange(ref _disposing, 1) != 0)
                {
                    hadActive = System.Threading.Volatile.Read(ref _active) != 0;
                    return true;
                }

                hadActive = System.Threading.Volatile.Read(ref _active) != 0;
                if (!hadActive)
                {
                    // No in-flight callers; disposal can proceed without waiting.
                    return true;
                }

                // Wait for active callers to drain; optional timeout avoids blocking forever.
                if (timeout == System.Threading.Timeout.InfiniteTimeSpan)
                {
                    _idle.Wait();
                    return true;
                }

                // Race note: callers may finish between the timeout decision and Wait call; Wait handles that safely.
                return _idle.Wait(timeout);
            }

            private void ThrowDisposed()
            {
                throw new ObjectDisposedException(_ownerName);
            }

            public void Dispose()
            {
                _idle.Dispose();
            }
        }
    }
}

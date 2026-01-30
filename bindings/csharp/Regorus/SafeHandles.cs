// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Runtime.InteropServices;
using Microsoft.Win32.SafeHandles;

#nullable enable
namespace Regorus
{
    internal sealed class RegorusEngineHandle : SafeHandleZeroOrMinusOneIsInvalid
    {
        private RegorusEngineHandle() : base(ownsHandle: true)
        {
        }

        internal static RegorusEngineHandle Create()
        {
            unsafe
            {
                var raw = Internal.API.regorus_engine_new();
                if (raw is null)
                {
                    throw new InvalidOperationException("Failed to create Regorus engine.");
                }

                var handle = new RegorusEngineHandle();
                handle.SetHandle((IntPtr)raw);
                return handle;
            }
        }

        internal static RegorusEngineHandle FromPointer(IntPtr pointer)
        {
            if (pointer == IntPtr.Zero)
            {
                throw new ArgumentException("Pointer cannot be zero.", nameof(pointer));
            }

            var handle = new RegorusEngineHandle();
            handle.SetHandle(pointer);
            return handle;
        }

        protected override bool ReleaseHandle()
        {
            if (!IsInvalid && !IsClosed)
            {
                unsafe
                {
                    Internal.API.regorus_engine_drop((Internal.RegorusEngine*)handle);
                }
                SetHandle(IntPtr.Zero);
            }
            return true;
        }
    }

    internal sealed class RegorusCompiledPolicyHandle : SafeHandleZeroOrMinusOneIsInvalid
    {
        private RegorusCompiledPolicyHandle() : base(ownsHandle: true)
        {
        }

        internal static RegorusCompiledPolicyHandle FromPointer(IntPtr pointer)
        {
            if (pointer == IntPtr.Zero)
            {
                throw new ArgumentException("Pointer cannot be zero.", nameof(pointer));
            }

            var handle = new RegorusCompiledPolicyHandle();
            handle.SetHandle(pointer);
            return handle;
        }

        protected override bool ReleaseHandle()
        {
            if (!IsInvalid && !IsClosed)
            {
                unsafe
                {
                    Internal.API.regorus_compiled_policy_drop((Internal.RegorusCompiledPolicy*)handle);
                }
                SetHandle(IntPtr.Zero);
            }
            return true;
        }
    }

    internal sealed class RegorusProgramHandle : SafeHandleZeroOrMinusOneIsInvalid
    {
        private RegorusProgramHandle() : base(ownsHandle: true)
        {
        }

        internal static RegorusProgramHandle Create()
        {
            unsafe
            {
                var raw = Internal.API.regorus_program_new();
                if (raw is null)
                {
                    throw new InvalidOperationException("Failed to create Regorus program.");
                }

                var handle = new RegorusProgramHandle();
                handle.SetHandle((IntPtr)raw);
                return handle;
            }
        }

        internal static RegorusProgramHandle FromPointer(IntPtr pointer)
        {
            if (pointer == IntPtr.Zero)
            {
                throw new ArgumentException("Pointer cannot be zero.", nameof(pointer));
            }

            var handle = new RegorusProgramHandle();
            handle.SetHandle(pointer);
            return handle;
        }

        protected override bool ReleaseHandle()
        {
            if (!IsInvalid && !IsClosed)
            {
                unsafe
                {
                    Internal.API.regorus_program_drop((Internal.RegorusProgram*)handle);
                }
                SetHandle(IntPtr.Zero);
            }
            return true;
        }
    }

    internal sealed class RegorusRvmHandle : SafeHandleZeroOrMinusOneIsInvalid
    {
        private RegorusRvmHandle() : base(ownsHandle: true)
        {
        }

        internal static RegorusRvmHandle Create()
        {
            unsafe
            {
                var raw = Internal.API.regorus_rvm_new();
                if (raw is null)
                {
                    throw new InvalidOperationException("Failed to create Regorus RVM.");
                }

                var handle = new RegorusRvmHandle();
                handle.SetHandle((IntPtr)raw);
                return handle;
            }
        }

        internal static RegorusRvmHandle FromPointer(IntPtr pointer)
        {
            if (pointer == IntPtr.Zero)
            {
                throw new ArgumentException("Pointer cannot be zero.", nameof(pointer));
            }

            var handle = new RegorusRvmHandle();
            handle.SetHandle(pointer);
            return handle;
        }

        protected override bool ReleaseHandle()
        {
            if (!IsInvalid && !IsClosed)
            {
                unsafe
                {
                    Internal.API.regorus_rvm_drop((Internal.RegorusRvm*)handle);
                }
                SetHandle(IntPtr.Zero);
            }
            return true;
        }
    }
}

#if REGORUS_FFI_TEST_HOOKS
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Runtime.InteropServices;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus.Internal;

namespace Regorus.Tests;

[TestClass]
public sealed class PanicGuardTests
{
    [TestInitialize]
    public void Initialize()
    {
        API.regorus_engine_test_reset_poison();
    }

    [TestCleanup]
    public void Cleanup()
    {
        API.regorus_engine_test_reset_poison();
    }

    [TestMethod]
    public void Panic_produces_invalid_operation_exception()
    {
        var panic = Assert.ThrowsException<InvalidOperationException>(TriggerPanic);
        StringAssert.Contains(panic.Message, "panicked", "panic message should capture payload");
    }

    [TestMethod]
    public void Poison_flag_blocks_subsequent_calls()
    {
        _ = Assert.ThrowsException<InvalidOperationException>(TriggerPanic);
        var poisoned = Assert.ThrowsException<InvalidOperationException>(TriggerPanic);
        StringAssert.Contains(poisoned.Message, "poisoned", "poisoned message should explain guard state");
    }

    private static unsafe void TriggerPanic()
    {
        var result = API.regorus_engine_test_trigger_panic();
        try
        {
            if (result.status == RegorusStatus.Ok)
            {
                return;
            }

            var message = PtrToStringUtf8((IntPtr)result.error_message);
            throw result.status.CreateException(message);
        }
        finally
        {
            API.regorus_result_drop(result);
        }
    }

    private static string? PtrToStringUtf8(IntPtr ptr)
    {
#if NETSTANDARD2_1
        return Marshal.PtrToStringUTF8(ptr);
#else
        if (ptr == IntPtr.Zero)
        {
            return null;
        }

        var len = 0;
        while (Marshal.ReadByte(ptr, len) != 0)
        {
            len++;
        }

        var buffer = new byte[len];
        Marshal.Copy(ptr, buffer, 0, buffer.Length);
        return System.Text.Encoding.UTF8.GetString(buffer);
#endif
    }
}

#endif

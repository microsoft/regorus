// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Runtime.InteropServices;
using System.Text;
using System.Collections.Generic;
using System.Text.Json;


#nullable enable
namespace Regorus
{
    /// <summary>
    /// Delegate for callback functions that can be invoked from Rego policies
    /// </summary>
    /// <param name="payload">Deserialized JSON object containing the payload from Rego</param>
    /// <returns>Object that will be serialized to JSON and converted to a Rego value</returns>
    public delegate object RegoCallback(object payload);
    
    public unsafe sealed class Engine : System.IDisposable
    {
        private Regorus.Internal.RegorusEngine* E;
        // Detect redundant Dispose() calls in a thread-safe manner.
        // _isDisposed == 0 means Dispose(bool) has not been called yet.
        // _isDisposed == 1 means Dispose(bool) has been already called.
        private int isDisposed;
        
        // Store callback delegates to prevent garbage collection
        private readonly Dictionary<string, GCHandle> callbackHandles = new Dictionary<string, GCHandle>();
        
        // Store user callbacks
        private readonly Dictionary<string, RegoCallback> callbacks = new Dictionary<string, RegoCallback>();

        // JSON serialization options
        private static readonly JsonSerializerOptions JsonOptions = new JsonSerializerOptions
        {
            PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
            WriteIndented = false
        };

        public Engine()
        {
            E = Regorus.Internal.API.regorus_engine_new();
        }

        public void Dispose()
        {
            Dispose(disposing: true);

            // This object will be cleaned up by the Dispose method.
            // Therefore, call GC.SuppressFinalize to
            // take this object off the finalization queue
            // and prevent finalization code for this object
            // from executing a second time.
            GC.SuppressFinalize(this);
        }

        // Dispose(bool disposing) executes in two distinct scenarios.
        // If disposing equals true, the method has been called directly
        // or indirectly by a user's code. Managed and unmanaged resources
        // can be disposed.
        // If disposing equals false, the method has been called by the
        // runtime from inside the finalizer and you should not reference
        // other objects. Only unmanaged resources can be disposed.
        void Dispose(bool disposing)
        {
            // In case _isDisposed is 0, atomically set it to 1.
            // Enter the branch only if the original value is 0.
            if (System.Threading.Interlocked.CompareExchange(ref isDisposed, 1, 0) == 0)
            {
                // If disposing equals true, dispose all managed
                // and unmanaged resources.
                if (disposing)
                {
                    // Unregister all callbacks
                    foreach (var name in new List<string>(callbackHandles.Keys))
                    {
                        UnregisterCallback(name);
                    }
                }

                // Call the appropriate methods to clean up
                // unmanaged resources here.
                // If disposing is false,
                // only the following code is executed.
                if (E != null)
                {
                    Regorus.Internal.API.regorus_engine_drop(E);
                    E = null;
                }

            }
        }

        // Use C# finalizer syntax for finalization code.
        // This finalizer will run only if the Dispose method
        // does not get called.
        ~Engine() => Dispose(disposing: false);

        // Helper for implementing Clone
        private Engine(Internal.RegorusEngine* engine)
        {
            this.E = engine;
        }

        public Engine Clone() => new(Internal.API.regorus_engine_clone(E));

        byte[] NullTerminatedUTF8Bytes(string s)
        {
            return Encoding.UTF8.GetBytes(s + char.MinValue);
        }

        public string? AddPolicy(string path, string rego)
        {
            var pathBytes = NullTerminatedUTF8Bytes(path);
            var regoBytes = NullTerminatedUTF8Bytes(rego);


            fixed (byte* pathPtr = pathBytes)
            {
                fixed (byte* regoPtr = regoBytes)
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_policy(E, pathPtr, regoPtr));
                }
            }

        }

        public void SetRegoV0(bool enable)
        {
            CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_rego_v0(E, enable));
        }

        public string? AddPolicyFromFile(string path)
        {
            var pathBytes = NullTerminatedUTF8Bytes(path);
            fixed (byte* pathPtr = pathBytes)
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_policy_from_file(E, pathPtr));
            }

        }

        public void AddDataJson(string data)
        {
            var dataBytes = NullTerminatedUTF8Bytes(data);
            fixed (byte* dataPtr = dataBytes)
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_data_json(E, dataPtr));
            }

        }

        public void AddDataFromJsonFile(string path)
        {
            var pathBytes = NullTerminatedUTF8Bytes(path);
            fixed (byte* pathPtr = pathBytes)
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_data_from_json_file(E, pathPtr));
            }

        }

        public void SetInputJson(string input)
        {
            var inputBytes = NullTerminatedUTF8Bytes(input);
            fixed (byte* inputPtr = inputBytes)
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_input_json(E, inputPtr));
            }
        }

        public void SetInputFromJsonFile(string path)
        {
            var pathBytes = NullTerminatedUTF8Bytes(path);
            fixed (byte* pathPtr = pathBytes)
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_input_from_json_file(E, pathPtr));
            }
        }

        public string? EvalQuery(string query)
        {
            var queryBytes = NullTerminatedUTF8Bytes(query);
            fixed (byte* queryPtr = queryBytes)
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_query(E, queryPtr));
            }
        }

        public string? EvalRule(string rule)
        {
            var ruleBytes = NullTerminatedUTF8Bytes(rule);
            fixed (byte* rulePtr = ruleBytes)
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_query(E, rulePtr));
            }
        }

        public void SetEnableCoverage(bool enable)
        {
            CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_enable_coverage(E, enable));
        }

        public void ClearCoverageData()
        {
            CheckAndDropResult(Regorus.Internal.API.regorus_engine_clear_coverage_data(E));
        }

        public string? GetCoverageReport()
        {
            return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_coverage_report(E));
        }

        public string? GetCoverageReportPretty()
        {
            return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_coverage_report_pretty(E));
        }

        public void SetGatherPrints(bool enable)
        {
            CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_gather_prints(E, enable));
        }

        public string? TakePrints()
        {
            return CheckAndDropResult(Regorus.Internal.API.regorus_engine_take_prints(E));
        }

        /// <summary>
        /// Enable a builtin extension by name
        /// </summary>
        /// <param name="name">The name of the builtin extension to enable</param>
        /// <returns>True if the operation succeeded, otherwise false</returns>
        public bool EnableBuiltinExtension(string name)
        {
            try
            {
                var nameBytes = NullTerminatedUTF8Bytes(name);
                fixed (byte* namePtr = nameBytes)
                {
                    CheckAndDropResult(Internal.API.regorus_engine_enable_builtin_extension(E, namePtr));
                    return true;
                }
            }
            catch
            {
                return false;
            }
        }

        /// <summary>
        /// Enable the invoke capability to allow Rego policies to call registered callbacks
        /// </summary>
        /// <returns>True if the operation succeeded, otherwise false</returns>
        public bool EnableInvoke()
        {
            return EnableBuiltinExtension("invoke");
        }

        // Generate a closure that wraps the user's callback function
        private static Internal.RegorusCallbackDelegate GenerateRegorusCallback(RegoCallback callback)
        {
            return delegate (byte* payloadPtr, void* contextPtr)
            {
                try
                {
                    // Convert the payload to a string
#if NETSTANDARD2_1
                    var payload = Marshal.PtrToStringUTF8(new IntPtr(payloadPtr));
#else
                    var payload = StringFromUTF8Raw(new IntPtr(payloadPtr));
#endif
                    if (payload == null)
                    {
                        return null;
                    }
                    
                    // Deserialize the payload to an object
                    var payloadObject = JsonSerializer.Deserialize<object>(payload, JsonOptions);
                    if (payloadObject == null)
                    {
                        return null;
                    }
                    
                    // Call the user's callback function
                    var result = callback(payloadObject);
                    
                    if (result == null)
                    {
                        return null;
                    }
                    
                    // Always serialize the result to JSON, even if it's a string
                    string jsonResult = JsonSerializer.Serialize(result, JsonOptions);
                    
                    // Convert the result back to a C string that Rust will free
#if NETSTANDARD2_1
                    return (byte*)Marshal.StringToCoTaskMemUTF8(jsonResult).ToPointer();
#else
                    return StringToCoTaskMemUTF8Raw(jsonResult);
#endif
                }
                catch
                {
                    return null;
                }
            };
        }

        // Helper for .NET Standard 2.0 to convert string to UTF8 allocated memory
        private static byte* StringToCoTaskMemUTF8Raw(string str)
        {
            if (str == null)
                return null;

            var bytes = Encoding.UTF8.GetBytes(str);
            var ptr = Marshal.AllocCoTaskMem(bytes.Length + 1);
            Marshal.Copy(bytes, 0, ptr, bytes.Length);
            Marshal.WriteByte(ptr, bytes.Length, 0);
            return (byte*)ptr.ToPointer();
        }

        // Helper for .NET Standard 2.0 to convert UTF8 to string
        private static string StringFromUTF8Raw(IntPtr ptr)
        {
            if (ptr == IntPtr.Zero)
                return null;

            int len = 0;
            while (Marshal.ReadByte(ptr, len) != 0) { ++len; }
            byte[] buffer = new byte[len];
            Marshal.Copy(ptr, buffer, 0, buffer.Length);
            return Encoding.UTF8.GetString(buffer);
        }

        public bool RegisterCallback(string name, RegoCallback callback)
        {
            if (string.IsNullOrEmpty(name) || callback == null)
            {
                return false;
            }
            
            // Store the callback in our dictionary
            callbacks[name] = callback;
            
            // Generate a closure for this callback
            var callbackDelegate = GenerateRegorusCallback(callback);
            
            // Create a GCHandle to prevent garbage collection
            var handle = GCHandle.Alloc(callbackDelegate);
            callbackHandles[name] = handle;
            
            // Register the callback with the native code
            var nameBytes = NullTerminatedUTF8Bytes(name);
            fixed (byte* namePtr = nameBytes)
            {
                var result = Internal.API.regorus_register_callback(namePtr, callbackDelegate, (void*)IntPtr.Zero);
                return result == Internal.RegorusStatus.RegorusStatusOk;
            }
        }
        
        /// <summary>
        /// Unregister a previously registered callback function
        /// </summary>
        /// <param name="name">Name of the callback function to unregister</param>
        /// <returns>True if unregistration succeeded, otherwise false</returns>
        public bool UnregisterCallback(string name)
        {
            if (string.IsNullOrEmpty(name))
            {
                return false;
            }
            
            // Remove the callback from our dictionary
            callbacks.Remove(name);
            
            // Unregister the callback from the native code
            var nameBytes = NullTerminatedUTF8Bytes(name);
            fixed (byte* namePtr = nameBytes)
            {
                var result = Internal.API.regorus_unregister_callback(namePtr);
                
                // Free the GCHandle if we have it
                if (callbackHandles.TryGetValue(name, out var handle))
                {
                    handle.Free();
                    callbackHandles.Remove(name);
                }
                
                return result == Internal.RegorusStatus.RegorusStatusOk;
            }
        }

        string? StringFromUTF8(IntPtr ptr)
        {

#if NETSTANDARD2_1
				return System.Runtime.InteropServices.Marshal.PtrToStringUTF8(ptr);
#else
            int len = 0;
            while (Marshal.ReadByte(ptr, len) != 0) { ++len; }
            byte[] buffer = new byte[len];
            Marshal.Copy(ptr, buffer, 0, buffer.Length);
            return Encoding.UTF8.GetString(buffer);
#endif
        }

        string? CheckAndDropResult(Regorus.Internal.RegorusResult result)
        {
            if (result.status != Regorus.Internal.RegorusStatus.RegorusStatusOk)
            {
                var message = StringFromUTF8((IntPtr)result.error_message);
                var ex = new Exception(message);
                Regorus.Internal.API.regorus_result_drop(result);
                throw ex;
            }

            var resultString = "";
            if (result.output is not null)
            {
                resultString = StringFromUTF8((IntPtr)result.output);
            }
            Regorus.Internal.API.regorus_result_drop(result);
            return resultString;
        }
    }
}

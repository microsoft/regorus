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
        private readonly Dictionary<string, (Internal.RegorusCallbackDelegate Delegate, GCHandle Handle)> callbackDelegates 
            = new Dictionary<string, (Internal.RegorusCallbackDelegate, GCHandle)>();
        
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
                    foreach (var name in new List<string>(callbackDelegates.Keys))
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
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_rule(E, rulePtr));
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

        // Generic callback handler that routes to the appropriate user-provided callback
        private static unsafe byte* CallbackHandler(byte* payloadPtr, void* contextPtr)
        {
            try
            {
                // Context pointer contains the engine instance and callback name
                var context = GCHandle.FromIntPtr(new IntPtr(contextPtr));
                var contextData = (CallbackContext)context.Target!;
                
                if (contextData == null || contextData.Engine == null)
                {
                    return null;
                }
                
                // Convert the payload to a string
                var payload = Marshal.PtrToStringUTF8(new IntPtr(payloadPtr));
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
                
                // Get the user callback
                if (!contextData.Engine.callbacks.TryGetValue(contextData.CallbackName, out var callback))
                {
                    return null;
                }
                
                // Call the user callback
                var result = callback(payloadObject);
                
                if (result == null)
                {
                    return null;
                }
                
                // Always serialize the result to JSON, even if it's a string
                string jsonResult = JsonSerializer.Serialize(result, JsonOptions);
                
                // Convert the result back to a C string that Rust will free
                return (byte*)Marshal.StringToCoTaskMemUTF8(jsonResult).ToPointer();
            }
            catch
            {
                return null;
            }
        }
        
        private class CallbackContext
        {
            public Engine Engine { get; set; }
            public string CallbackName { get; set; }
            
            public CallbackContext(Engine engine, string name)
            {
                Engine = engine;
                CallbackName = name;
            }
        }
        
        /// <summary>
        /// Register a callback function that can be invoked from Rego policies
        /// </summary>
        /// <param name="name">Name of the callback function to register</param>
        /// <param name="callback">Callback function to be invoked</param>
        /// <returns>True if registration succeeded, otherwise false</returns>
        public bool RegisterCallback(string name, RegoCallback callback)
        {
            if (string.IsNullOrEmpty(name) || callback == null)
            {
                return false;
            }
            
            // Store the callback in our dictionary
            callbacks[name] = callback;
            
            // Create a context object and GCHandle
            var contextData = new CallbackContext(this, name);
            var contextHandle = GCHandle.Alloc(contextData);
            var contextPtr = GCHandle.ToIntPtr(contextHandle);
            
            // Create a delegate for the callback handler
            var callbackDelegate = new Internal.RegorusCallbackDelegate(CallbackHandler);
            
            // Store the delegate to prevent garbage collection
            callbackDelegates[name] = (callbackDelegate, contextHandle);
            
            // Register the callback with the native code
            var nameBytes = NullTerminatedUTF8Bytes(name);
            fixed (byte* namePtr = nameBytes)
            {
                var result = Internal.API.regorus_register_callback(namePtr, callbackDelegate, (void*)contextPtr);
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
                if (callbackDelegates.TryGetValue(name, out var delegateInfo))
                {
                    delegateInfo.Handle.Free();
                    callbackDelegates.Remove(name);
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

#r "../Regorus/bin/Debug/netstandard2.1/Regorus.dll"
// No direct reference to regorus_ffi.dll as it's a native DLL
#r "nuget: Newtonsoft.Json, 13.0.2"
#r "nuget: System.Data.Common, 4.3.0"

// Create a new engine
var engine = new Regorus.Engine();

// Enable the invoke extension
bool enableResult = engine.EnableInvoke();
Console.WriteLine($"Invoke extension enabled: {enableResult}");

// Register a callback function
bool registerResult = engine.RegisterCallback("test_callback", payload => {
    Console.WriteLine($"Called with payload: {payload}");
    
    if (payload is System.Text.Json.JsonElement jsonElement)
    {
        // Access properties from JsonElement
        var testValue = jsonElement.GetProperty("value").GetInt32();
        
        // Return a response object that will be serialized to JSON
        return new Dictionary<string, object>
        {
            ["value"] = testValue * 2,
            ["message"] = "Processing complete"
        };
    }
    
    return null;
});

Console.WriteLine($"Callback registration result: {registerResult}");

// Add a policy that uses the callback
engine.AddPolicy("example.rego", @"
package example

import future.keywords.if

double_value := invoke(""test_callback"", {""value"": 42}).value
");

// Evaluate query
var result = engine.EvalQuery("data.example.double_value");
Console.WriteLine($"Result: {result}");

// Unregister the callback when done
engine.UnregisterCallback("test_callback");

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus;
using YamlDotNet.Serialization;

namespace Regorus.Tests;

[TestClass]
public class RbacEngineTests
{
    public TestContext? TestContext { get; set; }

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = false
    };

    private const string BaseContextJson = """
{
  "principal": {
  "id": "user-1",
  "principal_type": "User",
  "custom_security_attributes": {
    "department": "eng",
    "levels": ["L1", "L2"]
  }
  },
  "resource": {
  "id": "/subscriptions/s1",
  "resource_type": "Microsoft.Storage/storageAccounts",
  "scope": "/subscriptions/s1",
  "attributes": {
    "owner": "alice",
    "tags": ["a", "b"],
    "count": 5,
    "enabled": false,
    "ip": "10.0.0.5",
    "guid": "a1b2c3d4-0000-0000-0000-000000000000"
  }
  },
  "request": {
  "action": "Microsoft.Storage/storageAccounts/read",
  "data_action": "Microsoft.Storage/storageAccounts/read",
  "attributes": {
    "owner": "alice",
    "text": "HelloWorld",
    "tags": ["prod", "gold"],
    "count": 10,
    "ratio": 2.5,
    "enabled": true,
    "ip": "10.0.0.8",
    "guid": "A1B2C3D4-0000-0000-0000-000000000000",
    "time": "12:30:15",
    "date": "2023-05-01T12:00:00Z",
    "numbers": [1, 2, 3],
    "letters": ["a", "b"]
  }
  },
  "environment": {
  "is_private_link": false,
  "private_endpoint": null,
  "subnet": null,
  "utc_now": "2023-05-01T12:00:00Z"
  },
  "action": "Microsoft.Storage/storageAccounts/read",
  "suboperation": "sub/read"
}
""";

    [TestMethod]
    public void Rbac_engine_evaluates_all_yaml_cases()
    {
        var cases = LoadEvalTestCases().ToList();
        Assert.IsTrue(cases.Count > 0, "No RBAC test cases were loaded.");

        foreach (var testCase in cases)
        {
            TestContext?.WriteLine($"RBAC case: {testCase.Name} -> {testCase.Condition}");
            var context = BuildBaseContext();
            if (testCase.Context != null)
            {
                ApplyOverrides(context, testCase.Context);
            }

            var contextJson = context.ToJsonString(JsonOptions);
            var result = RbacEngine.EvaluateCondition(testCase.Condition, contextJson);

            Assert.AreEqual(
              testCase.Expected,
              result,
              $"RBAC test '{testCase.Name}' failed for condition '{testCase.Condition}'.");
        }
    }

    private static JsonObject BuildBaseContext()
    {
        var node = JsonNode.Parse(BaseContextJson) as JsonObject;
        if (node is null)
        {
            throw new InvalidOperationException("Failed to parse base context JSON.");
        }

        return node;
    }

    private static void ApplyOverrides(JsonObject context, EvalContextOverrides overrides)
    {
        var principal = (JsonObject?)context["principal"]
          ?? throw new InvalidOperationException("Missing principal section.");
        var resource = (JsonObject?)context["resource"]
          ?? throw new InvalidOperationException("Missing resource section.");
        var request = (JsonObject?)context["request"]
          ?? throw new InvalidOperationException("Missing request section.");
        var environment = (JsonObject?)context["environment"]
          ?? throw new InvalidOperationException("Missing environment section.");

        if (!string.IsNullOrEmpty(overrides.Action))
        {
            context["action"] = overrides.Action;
        }

        if (!string.IsNullOrEmpty(overrides.Suboperation))
        {
            context["suboperation"] = overrides.Suboperation;
        }

        if (!string.IsNullOrEmpty(overrides.RequestAction))
        {
            request["action"] = overrides.RequestAction;
        }

        if (!string.IsNullOrEmpty(overrides.DataAction))
        {
            request["data_action"] = overrides.DataAction;
        }

        if (!string.IsNullOrEmpty(overrides.PrincipalId))
        {
            principal["id"] = overrides.PrincipalId;
        }

        if (!string.IsNullOrEmpty(overrides.PrincipalType))
        {
            principal["principal_type"] = overrides.PrincipalType;
        }

        if (!string.IsNullOrEmpty(overrides.ResourceId))
        {
            resource["id"] = overrides.ResourceId;
        }

        if (!string.IsNullOrEmpty(overrides.ResourceType))
        {
            resource["resource_type"] = overrides.ResourceType;
        }

        if (!string.IsNullOrEmpty(overrides.ResourceScope))
        {
            resource["scope"] = overrides.ResourceScope;
        }

        if (overrides.RequestAttributes != null)
        {
            request["attributes"] = ConvertToJsonNode(overrides.RequestAttributes);
        }

        if (overrides.ResourceAttributes != null)
        {
            resource["attributes"] = ConvertToJsonNode(overrides.ResourceAttributes);
        }

        if (overrides.PrincipalCustomSecurityAttributes != null)
        {
            principal["custom_security_attributes"] = ConvertToJsonNode(overrides.PrincipalCustomSecurityAttributes);
        }

        if (overrides.Environment != null)
        {
            if (overrides.Environment.IsPrivateLink.HasValue)
            {
                environment["is_private_link"] = overrides.Environment.IsPrivateLink.Value;
            }

            if (!string.IsNullOrEmpty(overrides.Environment.PrivateEndpoint))
            {
                environment["private_endpoint"] = overrides.Environment.PrivateEndpoint;
            }

            if (!string.IsNullOrEmpty(overrides.Environment.Subnet))
            {
                environment["subnet"] = overrides.Environment.Subnet;
            }

            if (!string.IsNullOrEmpty(overrides.Environment.UtcNow))
            {
                environment["utc_now"] = overrides.Environment.UtcNow;
            }
        }
    }

    private static IEnumerable<EvalTestCase> LoadEvalTestCases()
    {
        var baseDir = Path.Combine(AppContext.BaseDirectory, "test_cases");
        if (!Directory.Exists(baseDir))
        {
            throw new DirectoryNotFoundException($"RBAC test case directory not found: {baseDir}");
        }

        var deserializer = new DeserializerBuilder()
          .IgnoreUnmatchedProperties()
          .Build();

        var files = Directory.EnumerateFiles(baseDir, "*.yaml")
          .OrderBy(path => path, StringComparer.OrdinalIgnoreCase);

        foreach (var file in files)
        {
            var yaml = File.ReadAllText(file);
            var suite = deserializer.Deserialize<EvalTestSuite>(yaml);
            if (suite?.TestCases is null)
            {
                continue;
            }

            foreach (var testCase in suite.TestCases)
            {
                yield return testCase;
            }
        }
    }

    private static JsonNode? ConvertToJsonNode(object? value)
    {
        if (value is null)
        {
            return null;
        }

        switch (value)
        {
            case JsonNode node:
                return node;
            case string text:
                return JsonValue.Create(text);
            case bool boolean:
                return JsonValue.Create(boolean);
            case int intValue:
                return JsonValue.Create(intValue);
            case long longValue:
                return JsonValue.Create(longValue);
            case double doubleValue:
                return JsonValue.Create(doubleValue);
            case float floatValue:
                return JsonValue.Create(floatValue);
            case decimal decimalValue:
                return JsonValue.Create(decimalValue);
            case DateTime dateTime:
                return JsonValue.Create(dateTime.ToString("O"));
            case IDictionary dictionary:
                {
                    var obj = new JsonObject();
                    foreach (DictionaryEntry entry in dictionary)
                    {
                        var key = entry.Key?.ToString() ?? string.Empty;
                        obj[key] = ConvertToJsonNode(entry.Value);
                    }
                    return obj;
                }
            case IEnumerable enumerable:
                {
                    if (value is string)
                    {
                        return JsonValue.Create(value.ToString());
                    }

                    var array = new JsonArray();
                    foreach (var item in enumerable)
                    {
                        array.Add(ConvertToJsonNode(item));
                    }
                    return array;
                }
            default:
                return JsonValue.Create(value.ToString());
        }
    }

    private sealed class EvalTestSuite
    {
        [YamlMember(Alias = "test_cases")]
        public List<EvalTestCase> TestCases { get; set; } = new();
    }

    private sealed class EvalTestCase
    {
        [YamlMember(Alias = "name")]
        public string Name { get; set; } = string.Empty;

        [YamlMember(Alias = "condition")]
        public string Condition { get; set; } = string.Empty;

        [YamlMember(Alias = "expected")]
        public bool Expected { get; set; }

        [YamlMember(Alias = "context")]
        public EvalContextOverrides? Context { get; set; }
    }

    private sealed class EvalContextOverrides
    {
        [YamlMember(Alias = "action")]
        public string? Action { get; set; }

        [YamlMember(Alias = "suboperation")]
        public string? Suboperation { get; set; }

        [YamlMember(Alias = "request_action")]
        public string? RequestAction { get; set; }

        [YamlMember(Alias = "data_action")]
        public string? DataAction { get; set; }

        [YamlMember(Alias = "principal_id")]
        public string? PrincipalId { get; set; }

        [YamlMember(Alias = "principal_type")]
        public string? PrincipalType { get; set; }

        [YamlMember(Alias = "resource_id")]
        public string? ResourceId { get; set; }

        [YamlMember(Alias = "resource_type")]
        public string? ResourceType { get; set; }

        [YamlMember(Alias = "resource_scope")]
        public string? ResourceScope { get; set; }

        [YamlMember(Alias = "request_attributes")]
        public object? RequestAttributes { get; set; }

        [YamlMember(Alias = "resource_attributes")]
        public object? ResourceAttributes { get; set; }

        [YamlMember(Alias = "principal_custom_security_attributes")]
        public object? PrincipalCustomSecurityAttributes { get; set; }

        [YamlMember(Alias = "environment")]
        public EvalEnvironmentOverrides? Environment { get; set; }
    }

    private sealed class EvalEnvironmentOverrides
    {
        [YamlMember(Alias = "is_private_link")]
        public bool? IsPrivateLink { get; set; }

        [YamlMember(Alias = "private_endpoint")]
        public string? PrivateEndpoint { get; set; }

        [YamlMember(Alias = "subnet")]
        public string? Subnet { get; set; }

        [YamlMember(Alias = "utc_now")]
        public string? UtcNow { get; set; }
    }
}

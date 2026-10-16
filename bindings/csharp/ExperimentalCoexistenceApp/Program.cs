using ExperimentalEngine = Regorus.Experimental.Engine;
using StandardEngine = Regorus.Engine;
using System.Text.Json;

const string policy = """
package experimental
import rego.v1

allow if {
    input.enabled == true
}
""";

if (typeof(StandardEngine).GetMethod("SetExplanationSettings") is not null)
{
    throw new InvalidOperationException("Standard Regorus unexpectedly exposes explanation APIs.");
}
if (typeof(ExperimentalEngine).GetMethod("SetExplanationSettings") is null)
{
    throw new InvalidOperationException("Experimental Regorus does not expose explanation APIs.");
}

using (var standard = new StandardEngine())
{
    standard.AddPolicy("coexistence.rego", policy);
    standard.SetInputJson("""{"enabled":true}""");
    if (standard.EvalRule("data.experimental.allow") != "true")
    {
        throw new InvalidOperationException("Standard Regorus returned an unexpected result.");
    }
}

using (var experimental = new ExperimentalEngine())
{
    experimental.AddPolicy("coexistence.rego", policy);
    experimental.SetExplanationSettings(enabled: true);
    experimental.SetInputJson("""{"enabled":true}""");
    if (experimental.EvalRule("data.experimental.allow") != "true")
    {
        throw new InvalidOperationException("Experimental Regorus returned an unexpected result.");
    }

    var reportJson = experimental.TakeCausalityReport();
    if (string.IsNullOrWhiteSpace(reportJson))
    {
        throw new InvalidOperationException("Experimental Regorus did not return a causality report.");
    }
    using var report = JsonDocument.Parse(reportJson);
    if (!report.RootElement.TryGetProperty("query_result", out var queryResult) ||
        queryResult.ValueKind != JsonValueKind.True)
    {
        throw new InvalidOperationException("Experimental Regorus report did not preserve the true query result.");
    }
    if (!report.RootElement.TryGetProperty("rules", out var rules) ||
        rules.ValueKind != JsonValueKind.Array ||
        rules.GetArrayLength() == 0)
    {
        throw new InvalidOperationException("Experimental Regorus report contained no evaluated rules.");
    }
}

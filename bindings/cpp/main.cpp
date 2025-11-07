#include <iostream>
#include "regorus.hpp"

void example()
{
    // Create engine
    regorus::Engine engine;

    engine.set_rego_v0(true);
    engine.set_enable_coverage(true);

    // Add policies.
    engine.add_policy("objects.rego", R"(package objects

rect := {`width`: 2, "height": 4}
cube := {"width": 3, `height`: 4, "depth": 5}
a := 42
b := false
c := null
d := {"a": a, "x": [b, c]}
index := 1
shapes := [rect, cube]
names := ["prod", `smoke1`, "dev"]
sites := [{"name": "prod"}, {"name": names[index]}, {"name": "dev"}]
e := {
    a: "foo",
    "three": c,
    names[2]: b,
    "four": d,
}
f := e["dev"])");

    // Add data.
    engine.add_data_json(R"({
    "one": {
        "bar": "Foo",
        "baz": 5,
        "be": true,
        "bop": 23.4
    },
    "two": {
        "bar": "Bar",
        "baz": 12.3,
        "be": false,
        "bop": 42
    }
})");

    engine.add_data_json(R"({
    "three": {
        "bar": "Baz",
        "baz": 15,
        "be": true,
        "bop": 4.23
    }
})");

    // Set input.
    engine.set_input_json(R"({
    "a": 10,
    "b": "20",
    "c": 30.0,
    "d": true
})");

    // Eval query.
    auto result = engine.eval_query("[data.one, input.b, data.objects.sites[1]] = x");
    if (result)
    {
        std::cout << result.output() << std::endl;
    }
    else
    {
        std::cerr << result.error() << std::endl;
    }

    // Print coverage report
    auto result1 = engine.get_coverage_report_pretty();
    if (result1)
    {
        std::cout << result1.output() << std::endl;
    }
    else
    {
        std::cerr << result1.error() << std::endl;
    }
}

int main()
{

    // Create engine.
    regorus::Engine engine;
    engine.set_rego_v0(true);

    // Load policies.
    const char *policies[] = {
        "../../../tests/aci/framework.rego",
        "../../../tests/aci/policy.rego",
        "../../../tests/aci/api.rego",
    };

    // Add policies and data.
    for (auto policy : policies)
    {
        auto result = engine.add_policy_from_file(policy);
        if (!result)
        {
            std::cerr << result.error() << std::endl;
            return -1;
        }
        std::cout << "Loaded package " << result.output() << std::endl;
    }
    {
        auto result = engine.add_data_from_json_file("../../../tests/aci/data.json");
        if (!result)
        {
            std::cerr << result.error() << std::endl;
            return -1;
        }
    }

    // Set input and eval rule.
    {
        auto result = engine.set_input_from_json_file("../../../tests/aci/input.json");
        if (!result)
        {
            std::cerr << result.error() << std::endl;
            return -1;
        }
    }
    auto result = engine.eval_rule("data.framework.mount_overlay");
    if (!result)
    {
        std::cerr << result.error() << std::endl;
        return -1;
    }

    std::cout << result.output() << std::endl;

    example();

    // Value API demonstration using the existing engine
    std::cout << "\n=== Value API Demo ===" << std::endl;

    // Evaluate mount_overlay rule and get result as Value (not JSON)
    std::cout << "Evaluating data.framework.mount_overlay using eval_rule_as_value:" << std::endl;
    auto value_result = engine.eval_rule_as_value("data.framework.mount_overlay");

    if (!value_result)
    {
        std::cerr << "Value eval failed: " << value_result.error() << std::endl;
        return -1;
    }

    // Get the Value - this is the policy result structure
    auto policy_value = value_result.value();

    std::cout << "\n=== Navigating Value ===" << std::endl;

    // The result is an object with "allowed" and "metadata" fields
    if (policy_value.is_object())
    {
        std::cout << "✓ Policy result is an object" << std::endl;

        // Get the "allowed" field directly as a Value and extract as bool
        auto allowed_value = policy_value.object_get("allowed");
        std::cout << "\n1. Navigate to 'allowed' field (using typed API):" << std::endl;
        bool allowed = allowed_value.as_bool();
        std::cout << "   Type: bool" << std::endl;
        std::cout << "   Value: " << (allowed ? "true" : "false") << std::endl;

        // Get the "metadata" array
        auto metadata_value = policy_value.object_get("metadata");
        std::cout << "\n2. Navigate to 'metadata' array:" << std::endl;

        auto metadata_len = metadata_value.array_len();
        std::cout << "   Array length: " << metadata_len << std::endl;

        // Navigate through array elements using typed API
        for (int64_t i = 0; i < metadata_len && i < 2; i++)
        { // Show first 2 items
            std::cout << "\n   Metadata[" << i << "] (navigated with typed API):" << std::endl;
            auto item = metadata_value.array_get(i);

            if (item.is_object())
            {
                std::cout << "     Type: object" << std::endl;

                // Get the "action" field as string
                auto action = item.object_get("action");
                std::cout << "     action (string): \"" << action.as_string() << "\"" << std::endl;

                // Get the "key" field as string
                auto key = item.object_get("key");
                std::cout << "     key (string): \"" << key.as_string() << "\"" << std::endl;

                // Get the "name" field as string
                auto name = item.object_get("name");
                std::cout << "     name (string): \"" << name.as_string() << "\"" << std::endl;

                // Navigate deeper into "value" field
                auto value_field = item.object_get("value");

                // Check the type and extract accordingly
                if (i == 1)
                { // Second item has a boolean value
                    std::cout << "     value (bool): " << (value_field.as_bool() ? "true" : "false") << std::endl;
                }
                else
                {
                    // First item has an array - just report the type
                    std::cout << "     value: <array with " << value_field.array_len() << " elements>" << std::endl;
                }
            }
        }

        std::cout << "\n✓ Successfully navigated nested array/object structure using Value API" << std::endl;
    }

    std::cout << "\n✓ Value API demo completed successfully!" << std::endl;
}

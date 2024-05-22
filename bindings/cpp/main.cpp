#include <iostream>
#include "regorus.hpp"

void example()
{
    // Create engine
    regorus::Engine engine;

    engine.set_enable_coverage(true);
    
    // Add policies.
    engine.add_policy("objects.rego",R"(package objects

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
    if (result) {
	std::cout<<result.output()<<std::endl;
    } else {
	std::cerr<<result.error()<<std::endl;
    }

    // Print coverage report
    auto result1 = engine.get_coverage_report_pretty();
    if (result1) {
	std::cout<<result1.output()<<std::endl;
    } else {
	std::cerr<<result1.error()<<std::endl;
    }
}

int main() {

    // Create engine.
    regorus::Engine engine;


    // Load policies.
    const char* policies[] = {
	"../../../tests/aci/framework.rego",
	"../../../tests/aci/policy.rego",
	"../../../tests/aci/api.rego",
    };

    // Add policies and data.
    for (auto policy : policies) {
	auto result = engine.add_policy_from_file(policy);
	if (!result) {
	    std::cerr<<result.error()<<std::endl;
	    return -1;
	}
	std::cout<<"Loaded package "<<result.output()<< std::endl;
    }
    {
	auto result = engine.add_data_from_json_file("../../../tests/aci/data.json");
	if (!result) {
	    std::cerr<<result.error()<<std::endl;
	    return -1;
	}
    }

    // Set input and eval rule.
    {
	auto result = engine.set_input_from_json_file("../../../tests/aci/input.json");
	if (!result) {
	    std::cerr<<result.error()<<std::endl;
	    return -1;
	}
    }
    auto result = engine.eval_rule("data.framework.mount_overlay");
    if (!result) {
	std::cerr<<result.error()<<std::endl;
	return -1;
    }

    std::cout<<result.output()<<std::endl;

    example();
}

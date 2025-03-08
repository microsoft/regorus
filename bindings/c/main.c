#include <stdio.h>
#include "regorus.h"

int main() {
    // Create engine.
    RegorusEngine* engine = regorus_engine_new();
    RegorusResult r;

    // Turn on rego v0 since policy uses v0.
    r = regorus_engine_set_rego_v0(engine, true);
    if (r.status != RegorusStatusOk)
	goto error;

    // Load policies.
    r = regorus_engine_add_policy_from_file(engine, "../../../tests/aci/framework.rego");
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    r = regorus_engine_add_policy_from_file(engine, "../../../tests/aci/api.rego");
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);
    
    r = regorus_engine_add_policy_from_file(engine, "../../../tests/aci/policy.rego");
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    // Add data
    r = regorus_engine_add_data_from_json_file(engine, "../../../tests/aci/data.json");
    if (r.status != RegorusStatusOk)
	goto error;
    regorus_result_drop(r);

    // Set input
    r = regorus_engine_set_input_from_json_file(engine, "../../../tests/aci/input.json");
    if (r.status != RegorusStatusOk)
	goto error;
    regorus_result_drop(r);

    // Eval rule.
    r = regorus_engine_eval_query(engine, "data.framework.mount_overlay");
    if (r.status != RegorusStatusOk)
	goto error;

    // Print output
    printf("%s\n", r.output);
    regorus_result_drop(r);
    
    // Free the engine.
    regorus_engine_drop(engine);

    // Create another engine.
    engine = regorus_engine_new();

    r = regorus_engine_add_policy(
	engine,
	"test.rego",
	"package test\n"
	"x = 1\n"
	"message = `Hello`"
	);

    // Evaluate rule.
    if (r.status != RegorusStatusOk)
	goto error;

    r = regorus_engine_set_enable_coverage(engine, true);
    regorus_result_drop(r);
    
    r = regorus_engine_eval_query(engine, "data.test.message");
    if (r.status != RegorusStatusOk)
	goto error;

    // Print output
    printf("%s\n", r.output);
    regorus_result_drop(r);
	
    // Print pretty coverage report.
    r = regorus_engine_get_coverage_report_pretty(engine);
    if (r.status != RegorusStatusOk)
	goto error;

    printf("%s\n", r.output);
    regorus_result_drop(r);
    
    // Free the engine.
    regorus_engine_drop(engine);
    
    return 0;
    
error:
    printf("%s", r.error_message);
    regorus_result_drop(r);
    regorus_engine_drop(engine);
	
    return 1;
}

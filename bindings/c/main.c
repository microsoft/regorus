#include <stdio.h>
#include "regorus.h"

int main() {
    // Create engine.
    RegorusEngine* engine = regorus_engine_new();
    RegorusResult r;

    // Load policies.
    r = regorus_engine_add_policy_from_file(engine, "../../../tests/aci/framework.rego");
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded policy %s\n", r.output);
    regorus_result_drop(r);

    r = regorus_engine_add_policy_from_file(engine, "../../../tests/aci/api.rego");
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded policy %s\n", r.output);
    regorus_result_drop(r);
    
    r = regorus_engine_add_policy_from_file(engine, "../../../tests/aci/policy.rego");
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded policy %s\n", r.output);
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

    // Eval query
    r = regorus_engine_eval_query(engine, "data.framework.mount_overlay=x");
    if (r.status != RegorusStatusOk)
	goto error;

    // Print output
    printf("%s", r.output);
    regorus_result_drop(r);
    
    
    // Free the engine.
    regorus_engine_drop(engine);

    return 0;
error:
    printf("%s", r.error_message);
	
    return 1;
}

#include <stdio.h>
#include "regorus.h"


// Regorus has been built for no_std and cannot access files.
char*  file_to_string(const char* file) {
    char * buffer = 0;
    long length;
    FILE * f = fopen (file, "rb");

    if (f)
    {
	fseek (f, 0, SEEK_END);
	length = ftell (f);
	fseek (f, 0, SEEK_SET);
	buffer = malloc (length + 1);
	buffer[length] = '\0';
	if (buffer)
	{
	    fread (buffer, 1, length, f);
	}
	fclose (f);
    }

    return buffer;
}

// If regorus is built with custom-allocator, then provide implementation.
uint8_t* regorus_aligned_alloc(size_t alignment, size_t size) {
    return aligned_alloc(alignment, size);
}

void regorus_free(uint8_t* ptr) {
    free(ptr);
}


int main() {
    // Create engine.
    RegorusEngine* engine = regorus_engine_new();
    RegorusResult r;
    char* buffer = NULL;

    // Load policies.
    r = regorus_engine_add_policy(engine, "framework.rego", (buffer = file_to_string("../../../tests/aci/framework.rego")));
    free(buffer);
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    r = regorus_engine_add_policy(engine, "api.rego", (buffer = file_to_string("../../../tests/aci/api.rego")));
    free(buffer);
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    r = regorus_engine_add_policy(engine, "policy.rego", (buffer = file_to_string("../../../tests/aci/policy.rego")));
    free(buffer);
    if (r.status != RegorusStatusOk)
	goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    // Add data
    r = regorus_engine_add_data_json(engine, (buffer = file_to_string("../../../tests/aci/data.json")));
    free(buffer);
    if (r.status != RegorusStatusOk)
	goto error;
    regorus_result_drop(r);

    // Set input
    r = regorus_engine_set_input_json(engine, (buffer = file_to_string("../../../tests/aci/input.json")));
    free(buffer);
    if (r.status != RegorusStatusOk)
	goto error;
    regorus_result_drop(r);

    // Eval rule.
    r = regorus_engine_eval_rule(engine, "data.framework.mount_overlay");
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

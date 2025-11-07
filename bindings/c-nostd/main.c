#include <stdio.h>
#include <stdlib.h>
#if defined(_WIN32)
#include <malloc.h>
#endif
#include "regorus.h"

// Regorus has been built for no_std and cannot access files.
char *file_to_string(const char *file)
{
    char *buffer = 0;
    long length;
    FILE *f = fopen(file, "rb");

    if (f)
    {
        fseek(f, 0, SEEK_END);
        length = ftell(f);
        fseek(f, 0, SEEK_SET);
        buffer = malloc(length + 1);
        buffer[length] = '\0';
        if (buffer)
        {
            fread(buffer, 1, length, f);
        }
        fclose(f);
    }

    return buffer;
}

// If regorus is built with custom-allocator, then provide implementation.
uint8_t *regorus_aligned_alloc(size_t alignment, size_t size)
{
    // Aligned allocations must respect platform quirks: Windows offers
    // _aligned_malloc/_aligned_free, while macOS/Linux reject aligned_alloc
    // calls when size is not a multiple of alignment, so we rely on
    // posix_memalign for the no_std build.
#if defined(_WIN32)
    return (uint8_t *)_aligned_malloc(size, alignment);
#else
    void *ptr = NULL;
    // posix_memalign requires alignment to be at least sizeof(void*)
    // and a power of two; normalize here so small requests succeed.
    if (alignment < sizeof(void *))
    {
        alignment = sizeof(void *);
    }

    if (posix_memalign(&ptr, alignment, size) != 0)
    {
        return NULL;
    }
    return (uint8_t *)ptr;
#endif
}

void regorus_free(uint8_t *ptr)
{
#if defined(_WIN32)
    _aligned_free(ptr);
#else
    free(ptr);
#endif
}

int main()
{
    // Create engine.
    RegorusEngine *engine = regorus_engine_new();
    RegorusResult r;
    char *buffer = NULL;

    // Turn on rego v0 since policy uses v0.
    r = regorus_engine_set_rego_v0(engine, true);
    if (r.status != Ok)
        goto error;

    // Load policies.
    r = regorus_engine_add_policy(engine, "framework.rego", (buffer = file_to_string("../../../tests/aci/framework.rego")));
    free(buffer);
    if (r.status != Ok)
        goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    r = regorus_engine_add_policy(engine, "api.rego", (buffer = file_to_string("../../../tests/aci/api.rego")));
    free(buffer);
    if (r.status != Ok)
        goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    r = regorus_engine_add_policy(engine, "policy.rego", (buffer = file_to_string("../../../tests/aci/policy.rego")));
    free(buffer);
    if (r.status != Ok)
        goto error;
    printf("Loaded package %s\n", r.output);
    regorus_result_drop(r);

    // Add data
    r = regorus_engine_add_data_json(engine, (buffer = file_to_string("../../../tests/aci/data.json")));
    free(buffer);
    if (r.status != Ok)
        goto error;
    regorus_result_drop(r);

    // Set input
    r = regorus_engine_set_input_json(engine, (buffer = file_to_string("../../../tests/aci/input.json")));
    free(buffer);
    if (r.status != Ok)
        goto error;
    regorus_result_drop(r);

    // Eval rule.
    r = regorus_engine_eval_rule(engine, "data.framework.mount_overlay");
    if (r.status != Ok)
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

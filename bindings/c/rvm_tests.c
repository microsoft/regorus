// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include "regorus.h"

static int assert_ok(RegorusResult r, const char* message) {
    if (r.status != Ok) {
        fprintf(stderr, "%s: %s\n", message, r.error_message ? r.error_message : "(no error)");
        return 0;
    }
    return 1;
}

static int test_registered_host_await_wide_stride(void) {
    typedef struct WiderHostAwaitBuiltin {
        RegorusHostAwaitBuiltin prefix;
        uintptr_t trailing;
    } WiderHostAwaitBuiltin;

    if (offsetof(RegorusHostAwaitBuiltin, name) != 0 ||
        offsetof(RegorusHostAwaitBuiltin, arg_count) != sizeof(const char*) ||
        sizeof(RegorusHostAwaitBuiltin) != sizeof(const char*) + sizeof(uintptr_t) ||
        sizeof(WiderHostAwaitBuiltin) <= sizeof(RegorusHostAwaitBuiltin)) {
        fprintf(stderr, "unexpected registered HostAwait ABI layout\n");
        return 1;
    }

    const char* module_text =
        "package demo\n"
        "import rego.v1\n"
        "result := echo(input.left, input.right)\n";
    const char* expected_argument =
        "[\n"
        "  \"first\",\n"
        "  {\n"
        "    \"nested\": [\n"
        "      2\n"
        "    ]\n"
        "  }\n"
        "]";
    RegorusPolicyModule module = {"registered_host_await_stride.rego", module_text};
    const char* entry_points[] = {"data.demo.result"};
    WiderHostAwaitBuiltin builtins[] = {
        {{"unused", 0}, 0},
        {{"echo", 2}, 0},
    };

    RegorusResult result = regorus_program_compile_from_modules_with_host_await(
        "{}",
        &module,
        1,
        entry_points,
        1,
        &builtins[0].prefix,
        2,
        sizeof(WiderHostAwaitBuiltin));
    bool result_valid = true;
    RegorusProgram* program = NULL;
    RegorusRvm* vm = NULL;
    int exit_code = 1;

    if (!assert_ok(result, "compile registered HostAwait with wider stride")) {
        goto Cleanup;
    }
    program = (RegorusProgram*)result.pointer_value;
    regorus_result_drop(result);
    result_valid = false;
    if (!program) {
        fprintf(stderr, "registered HostAwait compile returned no program\n");
        goto Cleanup;
    }

    vm = regorus_rvm_new();
    if (!vm) {
        fprintf(stderr, "failed to allocate registered HostAwait VM\n");
        goto Cleanup;
    }
    result = regorus_rvm_set_execution_mode(vm, 1);
    result_valid = true;
    if (!assert_ok(result, "set registered HostAwait execution mode")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_load_program(vm, program);
    result_valid = true;
    if (!assert_ok(result, "load registered HostAwait program")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_set_input(vm, "{\"left\":\"first\",\"right\":{\"nested\":[2]}}");
    result_valid = true;
    if (!assert_ok(result, "set registered HostAwait input")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_execute(vm);
    result_valid = true;
    if (!assert_ok(result, "execute registered HostAwait program")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_get_host_await_identifier(vm);
    result_valid = true;
    if (!assert_ok(result, "get registered HostAwait identifier")) {
        goto Cleanup;
    }
    if (!result.output || strcmp(result.output, "echo") != 0) {
        fprintf(stderr, "unexpected registered HostAwait identifier: %s\n",
            result.output ? result.output : "(null)");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_get_host_await_argument(vm);
    result_valid = true;
    if (!assert_ok(result, "get registered HostAwait argument")) {
        goto Cleanup;
    }
    if (!result.output || strcmp(result.output, expected_argument) != 0) {
        fprintf(stderr, "unexpected registered HostAwait argument: %s\n",
            result.output ? result.output : "(null)");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_resume(vm, "123", true);
    result_valid = true;
    if (!assert_ok(result, "resume registered HostAwait program")) {
        goto Cleanup;
    }
    if (!result.output || strcmp(result.output, "123") != 0) {
        fprintf(stderr, "unexpected registered HostAwait result: %s\n",
            result.output ? result.output : "(null)");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    printf("Registered HostAwait wide-stride C ABI test passed.\n");
    exit_code = 0;

Cleanup:
    if (result_valid) {
        regorus_result_drop(result);
    }
    if (vm) {
        regorus_rvm_drop(vm);
    }
    if (program) {
        regorus_program_drop(program);
    }
    return exit_code;
}

int main() {
    RegorusResult result = {0};
    bool result_valid = false;
    RegorusProgram* program = NULL;
    RegorusBuffer* buffer = NULL;
    RegorusProgram* program2 = NULL;
    RegorusProgram* empty_program = NULL;
    RegorusRvm* vm = NULL;
    RegorusProgram* host_program = NULL;
    RegorusRvm* host_vm = NULL;
    bool is_partial = false;
    int exit_code = 1;

    const char* data_json =
        "{"
        "  \"roles\": {"
        "    \"alice\": [\"admin\", \"reader\"]"
        "  }"
        "}";
    const char* input_json =
        "{"
        "  \"user\": \"alice\","
        "  \"actions\": [\"read\"]"
        "}";
    const char* module_text =
        "package demo\n"
        "default allow = false\n"
        "allow if {\n"
        "  input.user == \"alice\"\n"
        "  some role in data.roles[input.user]\n"
        "  role == \"admin\"\n"
        "  count(input.actions) > 0\n"
        "}\n";

    const char* host_data_json = "{}";
    const char* host_input_json = "{\"account\":{\"id\":\"acct-1\",\"active\":true}}";
    const char* host_module_text =
        "package demo\n"
        "import rego.v1\n"
        "default allow := false\n"
        "allow if {\n"
        "  input.account.active == true\n"
        "  details := __builtin_host_await(input.account.id, \"account\")\n"
        "  details.tier == \"gold\"\n"
        "}\n";

    RegorusPolicyModule module;
    module.id = "demo.rego";
    module.content = module_text;

    const char* entry_points[] = {"data.demo.allow"};
    printf("Rego policy:\n%s\n", module_text);
    printf("Compiling program from modules...\n");
    result = regorus_program_compile_from_modules(
        data_json,
        &module,
        1,
        entry_points,
        1
    );
    result_valid = true;
    if (!assert_ok(result, "compile program")) {
        goto Cleanup;
    }
    program = (RegorusProgram*)result.pointer_value;
    regorus_result_drop(result);
    result_valid = false;

    printf("Reading compiled builtin names...\n");
    result = regorus_program_get_builtin_names(program);
    result_valid = true;
    if (!assert_ok(result, "get compiled builtin names")) {
        goto Cleanup;
    }
    if (!result.output || strcmp(result.output, "[\"count\"]") != 0) {
        fprintf(stderr, "unexpected builtin names: %s\n", result.output ? result.output : "(null)");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_program_get_builtin_names(NULL);
    result_valid = true;
    if (result.status == Ok || !result.error_message) {
        fprintf(stderr, "null program should return an explicit error\n");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    empty_program = regorus_program_new();
    if (!empty_program) {
        fprintf(stderr, "failed to allocate empty program\n");
        goto Cleanup;
    }
    result = regorus_program_get_builtin_names(empty_program);
    result_valid = true;
    if (!assert_ok(result, "get empty program builtin names")) {
        goto Cleanup;
    }
    if (!result.output || strcmp(result.output, "[]") != 0) {
        fprintf(stderr, "unexpected empty program builtin names: %s\n", result.output ? result.output : "(null)");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    printf("Generating assembly listing...\n");
    result = regorus_program_generate_listing(program);
    result_valid = true;
    if (!assert_ok(result, "generate listing")) {
        goto Cleanup;
    }
    printf("Assembly listing:\n%s\n", result.output ? result.output : "(null)");
    regorus_result_drop(result);
    result_valid = false;

    printf("Serializing program...\n");
    result = regorus_program_serialize_binary(program);
    result_valid = true;
    if (!assert_ok(result, "serialize program")) {
        goto Cleanup;
    }
    buffer = (RegorusBuffer*)result.pointer_value;
    regorus_result_drop(result);
    result_valid = false;

    printf("Deserializing program (%zu bytes)...\n", buffer->len);
    result = regorus_program_deserialize_binary(
        buffer->data,
        buffer->len,
        &is_partial
    );
    result_valid = true;
    if (!assert_ok(result, "deserialize program")) {
        goto Cleanup;
    }

    if (is_partial) {
        fprintf(stderr, "deserialized program marked partial\n");
        goto Cleanup;
    }

    program2 = (RegorusProgram*)result.pointer_value;
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_program_get_builtin_names(program2);
    result_valid = true;
    if (!assert_ok(result, "get deserialized program builtin names")) {
        goto Cleanup;
    }
    if (!result.output || strcmp(result.output, "[\"count\"]") != 0) {
        fprintf(stderr, "unexpected deserialized builtin names: %s\n", result.output ? result.output : "(null)");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    printf("Creating VM...\n");
    vm = regorus_rvm_new();
    if (!vm) {
        fprintf(stderr, "failed to allocate VM\n");
        goto Cleanup;
    }

    printf("Loading program into VM...\n");
    result = regorus_rvm_load_program(vm, program2);
    result_valid = true;
    if (!assert_ok(result, "load program")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    printf("Setting data...\n");
    result = regorus_rvm_set_data(vm, data_json);
    result_valid = true;
    if (!assert_ok(result, "set data")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    printf("Setting input...\n");
    result = regorus_rvm_set_input(vm, input_json);
    result_valid = true;
    if (!assert_ok(result, "set input")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    printf("Executing entry point...\n");
    result = regorus_rvm_execute(vm);
    result_valid = true;
    if (!assert_ok(result, "execute")) {
        goto Cleanup;
    }

        printf("Execution result (data.demo.allow): %s\n",
            result.output ? result.output : "(null)");
        printf("Decision: user=alice action=read -> allow=%s\n",
            result.output ? result.output : "(null)");
    if (!result.output || strcmp(result.output, "true") != 0) {
        fprintf(stderr, "unexpected result: %s\n", result.output);
        goto Cleanup;
    }

    printf("\n--- HostAwait example (suspendable execution) ---\n");
    RegorusPolicyModule host_module;
    host_module.id = "host_await.rego";
    host_module.content = host_module_text;

    const char* host_entry_points[] = {"data.demo.allow"};
    result = regorus_program_compile_from_modules(
        host_data_json,
        &host_module,
        1,
        host_entry_points,
        1
    );
    result_valid = true;
    if (!assert_ok(result, "compile host await program")) {
        goto Cleanup;
    }
    host_program = (RegorusProgram*)result.pointer_value;
    regorus_result_drop(result);
    result_valid = false;

    host_vm = regorus_rvm_new();
    if (!host_vm) {
        fprintf(stderr, "failed to allocate host await VM\n");
        goto Cleanup;
    }

    result = regorus_rvm_set_execution_mode(host_vm, 1);
    result_valid = true;
    if (!assert_ok(result, "set execution mode")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_load_program(host_vm, host_program);
    result_valid = true;
    if (!assert_ok(result, "load host await program")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_set_data(host_vm, host_data_json);
    result_valid = true;
    if (!assert_ok(result, "set host data")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_set_input(host_vm, host_input_json);
    result_valid = true;
    if (!assert_ok(result, "set host input")) {
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_execute(host_vm);
    result_valid = true;
    if (!assert_ok(result, "execute host await")) {
        goto Cleanup;
    }
    printf("HostAwait initial result: %s\n", result.output ? result.output : "(null)");
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_get_execution_state(host_vm);
    result_valid = true;
    if (!assert_ok(result, "get execution state")) {
        goto Cleanup;
    }
    printf("Execution state: %s\n", result.output ? result.output : "(null)");
    regorus_result_drop(result);
    result_valid = false;

    result = regorus_rvm_resume(host_vm, "{\"tier\":\"gold\"}", true);
    result_valid = true;
    if (!assert_ok(result, "resume host await")) {
        goto Cleanup;
    }
    printf("HostAwait resumed result: %s\n", result.output ? result.output : "(null)");

    if (!result.output || strcmp(result.output, "true") != 0) {
        fprintf(stderr, "unexpected host await result\n");
        goto Cleanup;
    }
    regorus_result_drop(result);
    result_valid = false;

    if (test_registered_host_await_wide_stride() != 0) {
        goto Cleanup;
    }

    exit_code = 0;

Cleanup:
    if (result_valid) {
        regorus_result_drop(result);
    }
    if (host_vm) {
        regorus_rvm_drop(host_vm);
    }
    if (host_program) {
        regorus_program_drop(host_program);
    }
    if (vm) {
        regorus_rvm_drop(vm);
    }
    if (program2) {
        regorus_program_drop(program2);
    }
    if (buffer) {
        regorus_buffer_drop(buffer);
    }
    if (program) {
        regorus_program_drop(program);
    }
    if (empty_program) {
        regorus_program_drop(empty_program);
    }
    return exit_code;
}

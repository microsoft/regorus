// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#include <iostream>
#include <cstddef>
#include <cstdint>
#include <string>
#include <memory>
#include "regorus.hpp"

struct WiderHostAwaitBuiltinV2 {
    RegorusHostAwaitBuiltinV2 prefix;
    std::uintptr_t trailing;
};

static_assert(offsetof(RegorusHostAwaitBuiltin, name) == 0);
static_assert(sizeof(RegorusHostAwaitBuiltin) == sizeof(const char*));
static_assert(offsetof(RegorusHostAwaitBuiltinV2, name) == 0);
static_assert(offsetof(RegorusHostAwaitBuiltinV2, arg_count) == sizeof(const char*));
static_assert(sizeof(WiderHostAwaitBuiltinV2) > sizeof(RegorusHostAwaitBuiltinV2));
static_assert(sizeof(WiderHostAwaitBuiltinV2) % alignof(RegorusHostAwaitBuiltinV2) == 0);

static bool expect_ffi_ok(RegorusResult result, const char* operation, const char* expected_output = nullptr) {
    bool success = result.status == RegorusStatus::Ok;
    if (!success) {
        std::cerr << operation << ": "
                  << (result.error_message ? result.error_message : "(no error)") << std::endl;
    } else if (expected_output &&
               (!result.output || std::string(result.output) != expected_output)) {
        std::cerr << operation << " returned unexpected output: "
                  << (result.output ? result.output : "(null)") << std::endl;
        success = false;
    }
    regorus_result_drop(result);
    return success;
}

static bool test_registered_host_await_wide_stride() {
    const char* module_text =
        "package demo\n"
        "import rego.v1\n"
        "result := echo(input.left, input.right)\n";
    RegorusPolicyModule module{"registered_host_await_stride.rego", module_text};
    const char* entry_points[] = {"data.demo.result"};
    WiderHostAwaitBuiltinV2 builtins[] = {
        {{"unused", 0}, 0},
        {{"echo", 2}, 0},
    };

    RegorusResult compile_result = regorus_program_compile_from_modules_with_host_await_v2(
        "{}",
        &module,
        1,
        entry_points,
        1,
        nullptr,
        0,
        sizeof(RegorusHostAwaitBuiltin),
        reinterpret_cast<const RegorusHostAwaitBuiltinV2*>(builtins),
        2,
        sizeof(WiderHostAwaitBuiltinV2));
    if (compile_result.status != RegorusStatus::Ok || !compile_result.pointer_value) {
        std::cerr << "compile registered HostAwait with wider stride: "
                  << (compile_result.error_message ? compile_result.error_message : "(no program)")
                  << std::endl;
        regorus_result_drop(compile_result);
        return false;
    }
    auto* program_pointer = static_cast<RegorusProgram*>(compile_result.pointer_value);
    regorus_result_drop(compile_result);
    std::unique_ptr<RegorusProgram, decltype(&regorus_program_drop)> program(
        program_pointer, &regorus_program_drop);

    std::unique_ptr<RegorusRvm, decltype(&regorus_rvm_drop)> vm(
        regorus_rvm_new(), &regorus_rvm_drop);
    if (!program || !vm) {
        std::cerr << "failed to allocate registered HostAwait handles" << std::endl;
        return false;
    }

    if (!expect_ffi_ok(regorus_rvm_set_execution_mode(vm.get(), 1),
                       "set registered HostAwait execution mode") ||
        !expect_ffi_ok(regorus_rvm_load_program(vm.get(), program.get()),
                       "load registered HostAwait program") ||
        !expect_ffi_ok(regorus_rvm_set_input(
                           vm.get(),
                           "{\"left\":\"first\",\"right\":{\"nested\":[2]}}"),
                       "set registered HostAwait input") ||
        !expect_ffi_ok(regorus_rvm_execute(vm.get()), "execute registered HostAwait program") ||
        !expect_ffi_ok(regorus_rvm_get_host_await_identifier(vm.get()),
                       "get registered HostAwait identifier",
                       "echo") ||
        !expect_ffi_ok(regorus_rvm_get_host_await_argument(vm.get()),
                       "get registered HostAwait argument",
                       R"json([
  "first",
  {
    "nested": [
      2
    ]
  }
])json") ||
        !expect_ffi_ok(regorus_rvm_resume(vm.get(), "123", true),
                       "resume registered HostAwait program",
                       "123")) {
        return false;
    }

    std::cout << "Registered HostAwait v2 wide-stride C++ ABI test passed." << std::endl;
    return true;
}

static bool test_legacy_host_await_raw_array() {
    const char* module_text =
        "package demo\n"
        "import rego.v1\n"
        "result := echo([1, 2])\n";
    RegorusPolicyModule module{"legacy_host_await.rego", module_text};
    const char* entry_points[] = {"data.demo.result"};
    RegorusHostAwaitBuiltin builtin{"echo"};

    RegorusResult compile_result = regorus_program_compile_from_modules_with_host_await(
        "{}",
        &module,
        1,
        entry_points,
        1,
        &builtin,
        1,
        sizeof(builtin));
    if (compile_result.status != RegorusStatus::Ok || !compile_result.pointer_value) {
        std::cerr << "compile legacy name-only HostAwait: "
                  << (compile_result.error_message ? compile_result.error_message : "(no program)")
                  << std::endl;
        regorus_result_drop(compile_result);
        return false;
    }
    auto* program_pointer = static_cast<RegorusProgram*>(compile_result.pointer_value);
    regorus_result_drop(compile_result);
    std::unique_ptr<RegorusProgram, decltype(&regorus_program_drop)> program(
        program_pointer, &regorus_program_drop);
    std::unique_ptr<RegorusRvm, decltype(&regorus_rvm_drop)> vm(
        regorus_rvm_new(), &regorus_rvm_drop);
    if (!program || !vm) {
        std::cerr << "failed to allocate legacy HostAwait handles" << std::endl;
        return false;
    }

    if (!expect_ffi_ok(regorus_rvm_set_execution_mode(vm.get(), 1),
                       "set legacy HostAwait execution mode") ||
        !expect_ffi_ok(regorus_rvm_load_program(vm.get(), program.get()),
                       "load legacy HostAwait program") ||
        !expect_ffi_ok(regorus_rvm_execute(vm.get()),
                       "execute legacy HostAwait program") ||
        !expect_ffi_ok(regorus_rvm_get_host_await_argument(vm.get()),
                       "get legacy HostAwait argument",
                       "[\n  1,\n  2\n]")) {
        return false;
    }

    std::cout << "Legacy name-only HostAwait C++ ABI test passed." << std::endl;
    return true;
}

int main() {
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
    std::cout << "Rego policy:\n" << module_text << std::endl;
    std::cout << "Compiling program from modules..." << std::endl;
    auto program_result = regorus::Program::compile_from_modules(
        data_json,
        &module,
        1,
        entry_points,
        1
    );
    if (!program_result) {
        std::cerr << "compile program (modules): " << program_result.error() << std::endl;
        return 1;
    }

    regorus::Program program = program_result.program();

    std::cout << "Generating assembly listing..." << std::endl;
    auto listing_result = program.generate_listing();
    if (!listing_result) {
        std::cerr << "generate listing: " << listing_result.error() << std::endl;
        return 1;
    }
    std::cout << "Assembly listing:\n" << listing_result.output() << std::endl;

    std::cout << "Serializing program..." << std::endl;
    auto serialize_result = program.serialize_binary();
    if (!serialize_result) {
        std::cerr << "serialize program: " << serialize_result.error() << std::endl;
        return 1;
    }

    regorus::Buffer buffer(reinterpret_cast<RegorusBuffer*>(serialize_result.pointer()));
    bool is_partial = false;
    std::cout << "Deserializing program (" << buffer.size() << " bytes)..." << std::endl;
    auto deserialize_result = regorus::Program::deserialize_binary(
        buffer.data(),
        buffer.size(),
        &is_partial
    );
    if (!deserialize_result) {
        std::cerr << "deserialize program: " << deserialize_result.error() << std::endl;
        return 1;
    }

    if (is_partial) {
        std::cerr << "deserialized program marked partial" << std::endl;
        return 1;
    }

    regorus::Program program2 = deserialize_result.program();

    {
        std::cout << "Creating VM..." << std::endl;
        regorus::Rvm vm;
        auto load_result = vm.load_program(program2);
        if (!load_result) {
            std::cerr << "load program: " << load_result.error() << std::endl;
            return 1;
        }

        std::cout << "Setting data..." << std::endl;
        auto data_result = vm.set_data(data_json);
        if (!data_result) {
            std::cerr << "set data: " << data_result.error() << std::endl;
            return 1;
        }

        std::cout << "Setting input..." << std::endl;
        auto input_result = vm.set_input(input_json);
        if (!input_result) {
            std::cerr << "set input: " << input_result.error() << std::endl;
            return 1;
        }

        std::cout << "Executing entry point..." << std::endl;
        auto exec_result = vm.execute();
        if (!exec_result) {
            std::cerr << "execute: " << exec_result.error() << std::endl;
            return 1;
        }

        std::cout << "Execution result (data.demo.allow): " << exec_result.output() << std::endl;
        std::cout << "Decision: user=alice action=read -> allow=" << exec_result.output() << std::endl;
        if (std::string(exec_result.output()) != "true") {
            std::cerr << "unexpected result: " << exec_result.output() << std::endl;
            return 1;
        }
    }

    regorus::Engine engine;
    std::cout << "Compiling program from engine..." << std::endl;
    auto add_policy_result = engine.add_policy("demo.rego", module_text);
    if (!add_policy_result) {
        std::cerr << "engine add policy: " << add_policy_result.error() << std::endl;
        return 1;
    }

    auto engine_program_result = regorus::Program::compile_from_engine(
        engine.raw(),
        entry_points,
        1
    );
    if (!engine_program_result) {
        std::cerr << "compile program (engine): " << engine_program_result.error() << std::endl;
        return 1;
    }

    regorus::Program engine_program = engine_program_result.program();

    regorus::Rvm engine_vm;
    auto engine_load_result = engine_vm.load_program(engine_program);
    if (!engine_load_result) {
        std::cerr << "engine load program: " << engine_load_result.error() << std::endl;
        return 1;
    }

    std::cout << "Setting engine data..." << std::endl;
    auto engine_data_result = engine_vm.set_data(data_json);
    if (!engine_data_result) {
        std::cerr << "engine set data: " << engine_data_result.error() << std::endl;
        return 1;
    }

    std::cout << "Setting engine input..." << std::endl;
    auto engine_input_result = engine_vm.set_input(input_json);
    if (!engine_input_result) {
        std::cerr << "engine set input: " << engine_input_result.error() << std::endl;
        return 1;
    }

    std::cout << "Executing engine entry point..." << std::endl;
    auto engine_exec_result = engine_vm.execute();
    if (!engine_exec_result) {
        std::cerr << "engine execute: " << engine_exec_result.error() << std::endl;
        return 1;
    }

    std::cout << "Engine execution result (data.demo.allow): " << engine_exec_result.output() << std::endl;
    std::cout << "Decision: user=alice action=read -> allow=" << engine_exec_result.output() << std::endl;
    if (std::string(engine_exec_result.output()) != "true") {
        std::cerr << "unexpected engine result: " << engine_exec_result.output() << std::endl;
        return 1;
    }

    std::cout << "\n--- HostAwait example (suspendable execution) ---" << std::endl;
    RegorusPolicyModule host_module;
    host_module.id = "host_await.rego";
    host_module.content = host_module_text;
    const char* host_entry_points[] = {"data.demo.allow"};

    auto host_program_result = regorus::Program::compile_from_modules(
        host_data_json,
        &host_module,
        1,
        host_entry_points,
        1
    );
    if (!host_program_result) {
        std::cerr << "compile host await program: " << host_program_result.error() << std::endl;
        return 1;
    }

    regorus::Program host_program = host_program_result.program();
    regorus::Rvm host_vm;
    auto host_mode_result = host_vm.set_execution_mode(1);
    if (!host_mode_result) {
        std::cerr << "set execution mode: " << host_mode_result.error() << std::endl;
        return 1;
    }

    auto host_load_result = host_vm.load_program(host_program);
    if (!host_load_result) {
        std::cerr << "load host await program: " << host_load_result.error() << std::endl;
        return 1;
    }

    auto host_data_result = host_vm.set_data(host_data_json);
    if (!host_data_result) {
        std::cerr << "set host data: " << host_data_result.error() << std::endl;
        return 1;
    }

    auto host_input_result = host_vm.set_input(host_input_json);
    if (!host_input_result) {
        std::cerr << "set host input: " << host_input_result.error() << std::endl;
        return 1;
    }

    auto host_exec_result = host_vm.execute();
    if (!host_exec_result) {
        std::cerr << "execute host await: " << host_exec_result.error() << std::endl;
        return 1;
    }
    std::cout << "HostAwait initial result: " << host_exec_result.output() << std::endl;

    auto host_state_result = host_vm.get_execution_state();
    if (!host_state_result) {
        std::cerr << "get execution state: " << host_state_result.error() << std::endl;
        return 1;
    }
    std::cout << "Execution state: " << host_state_result.output() << std::endl;

    auto host_resume_result = host_vm.resume("{\"tier\":\"gold\"}", true);
    if (!host_resume_result) {
        std::cerr << "resume host await: " << host_resume_result.error() << std::endl;
        return 1;
    }
    std::cout << "HostAwait resumed result: " << host_resume_result.output() << std::endl;
    if (std::string(host_resume_result.output()) != "true") {
        std::cerr << "unexpected host await result: " << host_resume_result.output() << std::endl;
        return 1;
    }

    if (!test_registered_host_await_wide_stride()) {
        return 1;
    }
    if (!test_legacy_host_await_raw_array()) {
        return 1;
    }

    return 0;
}

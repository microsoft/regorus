#ifndef REGORUS_WRAPPER_HPP
#define REGORUS_WRAPPER_HPP

#include <cstddef>
#include <cstdint>
#include <memory>
#include <variant>

#include "regorus.ffi.hpp"

namespace regorus {

	class Buffer;
	class Program;

	class Result {
	public:

	operator bool() const { return result.status == RegorusStatus::Ok; }
	bool operator !() const { return result.status != RegorusStatus::Ok; }

	const char* output() const {
	    if (*this && result.output) {
		return result.output;
	    } else {
		return "";
	    }
	}
	
	const char* error() const {
	    if (!*this && result.error_message) {
		return result.error_message;
	    } else {
		return "";
	    }
	}

	void* pointer() const {
	    return result.pointer_value;
	}

	Program program() const;
	Buffer buffer() const;

	Result(RegorusResult r) : result(r) {}
	Result(Result&& other) noexcept : result(other.result) {
	    other.result.output = nullptr;
	    other.result.error_message = nullptr;
	    other.result.pointer_value = nullptr;
	}
	Result& operator=(Result&& other) noexcept {
	    if (this != &other) {
		regorus_result_drop(result);
		result = other.result;
		other.result.output = nullptr;
		other.result.error_message = nullptr;
		other.result.pointer_value = nullptr;
	    }
	    return *this;
	}

	~Result() {
	    regorus_result_drop(result);
	}
	
    private:
	RegorusResult result;

    private:
	Result(const Result&) = delete;
	Result& operator=(const Result&) = delete;

    };
    
    class Engine {
    public:
	Engine() : Engine(regorus_engine_new()) {}

	std::unique_ptr<Engine> clone() const {
	    return std::unique_ptr<Engine>(new Engine(regorus_engine_clone(engine)));
	}

	Result set_rego_v0(bool enable) {
		return Result(regorus_engine_set_rego_v0(engine, enable));
	}

	Result add_policy(const char* path, const char* policy) {
	    return Result(regorus_engine_add_policy(engine, path, policy));
	}
	
	Result add_policy_from_file(const char* path) {
	    return Result(regorus_engine_add_policy_from_file(engine, path));
	}
	
	Result add_data_json(const char* data) {
	    return Result(regorus_engine_add_data_json(engine, data));
	}
	
	Result add_data_from_json_file(const char* path) {
	    return Result(regorus_engine_add_data_from_json_file(engine, path));
	}
	
	Result set_input_json(const char* input) {
	    return Result(regorus_engine_set_input_json(engine, input));
	}
	
	Result set_input_from_json_file(const char* path) {
	    return Result(regorus_engine_set_input_from_json_file(engine, path));
	}

	Result eval_query(const char* query) {
	    return Result(regorus_engine_eval_query(engine, query));
	}
	
	Result eval_rule(const char* rule) {
	    return Result(regorus_engine_eval_rule(engine, rule));
	}
	
	Result set_enable_coverage(bool enable) {
	    return Result(regorus_engine_set_enable_coverage(engine, enable));
	}
	
	Result clear_coverage_data() {
            return Result(regorus_engine_clear_coverage_data(engine));
	}
	
	Result get_coverage_report() {
            return Result(regorus_engine_get_coverage_report(engine));
	}
	
	Result get_coverage_report_pretty() {
            return Result(regorus_engine_get_coverage_report_pretty(engine));
	}
	
	~Engine() {
	    regorus_engine_drop(engine);
	}

	RegorusEngine* raw() const {
	    return engine;
	}
	    
	
    private:
	RegorusEngine* engine;
    private:
	Engine(RegorusEngine* e) : engine(e) {}
	Engine(const Engine&) = delete;
	Engine(Engine&&) = delete;
	Engine& operator=(const Engine&) = delete;
    };

    class CompiledPolicy {
    public:
	explicit CompiledPolicy(RegorusCompiledPolicy* p) : policy(p) {}

	Result eval_with_input(const char* input_json) {
	    return Result(regorus_compiled_policy_eval_with_input(policy, input_json));
	}

	Result get_policy_info() {
	    return Result(regorus_compiled_policy_get_policy_info(policy));
	}

	RegorusCompiledPolicy* raw() const {
	    return policy;
	}

	~CompiledPolicy() {
	    if (policy) {
		regorus_compiled_policy_drop(policy);
	    }
	}

    private:
	RegorusCompiledPolicy* policy;
	CompiledPolicy(const CompiledPolicy&) = delete;
	CompiledPolicy(CompiledPolicy&&) = delete;
	CompiledPolicy& operator=(const CompiledPolicy&) = delete;
    };

    class Buffer {
    public:
	Buffer() : buffer(nullptr) {}
	explicit Buffer(RegorusBuffer* b) : buffer(b) {}

	const std::uint8_t* data() const {
	    return buffer ? buffer->data : nullptr;
	}

	size_t size() const {
	    return buffer ? buffer->len : 0;
	}

	RegorusBuffer* raw() const {
	    return buffer;
	}

	~Buffer() {
	    if (buffer) {
		regorus_buffer_drop(buffer);
	    }
	}

    private:
	RegorusBuffer* buffer;
	Buffer(const Buffer&) = delete;
	Buffer(Buffer&&) = delete;
	Buffer& operator=(const Buffer&) = delete;
    };

    class Program {
    public:
	Program() : program(regorus_program_new()) {}
	explicit Program(RegorusProgram* p) : program(p) {}

	static Result compile_from_policy(
	    RegorusCompiledPolicy* compiled_policy,
	    const char* const* entry_points,
	    size_t entry_points_len
	) {
	    return Result(regorus_program_compile_from_policy(
		compiled_policy,
		entry_points,
		entry_points_len
	    ));
	}

	static Result compile_from_modules(
	    const char* data_json,
	    const RegorusPolicyModule* modules,
	    size_t modules_len,
	    const char* const* entry_points,
	    size_t entry_points_len
	) {
	    return Result(regorus_program_compile_from_modules(
		data_json,
		modules,
		modules_len,
		entry_points,
		entry_points_len
	    ));
	}

	static Result compile_from_engine(
	    RegorusEngine* engine,
	    const char* const* entry_points,
	    size_t entry_points_len
	) {
	    return Result(regorus_engine_compile_program_with_entrypoints(
		engine,
		entry_points,
		entry_points_len
	    ));
	}

	Result serialize_binary() const {
	    return Result(regorus_program_serialize_binary(program));
	}

	static Result deserialize_binary(
	    const std::uint8_t* data,
	    size_t len,
	    bool* is_partial
	) {
	    return Result(regorus_program_deserialize_binary(data, len, is_partial));
	}

	Result generate_listing() const {
	    return Result(regorus_program_generate_listing(program));
	}

	Result generate_tabular_listing() const {
	    return Result(regorus_program_generate_tabular_listing(program));
	}

	RegorusProgram* raw() const {
	    return program;
	}

	~Program() {
	    if (program) {
		regorus_program_drop(program);
	    }
	}

    private:
	RegorusProgram* program;
	Program(const Program&) = delete;
	Program(Program&&) = delete;
	Program& operator=(const Program&) = delete;
    };

	inline Program Result::program() const {
	return Program(reinterpret_cast<RegorusProgram*>(result.pointer_value));
	}

	inline Buffer Result::buffer() const {
	return Buffer(reinterpret_cast<RegorusBuffer*>(result.pointer_value));
	}

    class Rvm {
    public:
	Rvm() : vm(regorus_rvm_new()) {}
	explicit Rvm(RegorusRvm* v) : vm(v) {}

	static Result create_with_policy(RegorusCompiledPolicy* compiled_policy) {
	    return Result(regorus_rvm_new_with_policy(compiled_policy));
	}

	Result load_program(const Program& program) {
	    return Result(regorus_rvm_load_program(vm, program.raw()));
	}

	Result set_data(const char* data_json) {
	    return Result(regorus_rvm_set_data(vm, data_json));
	}

	Result set_input(const char* input_json) {
	    return Result(regorus_rvm_set_input(vm, input_json));
	}

	Result set_max_instructions(size_t max_instructions) {
	    return Result(regorus_rvm_set_max_instructions(vm, max_instructions));
	}

	Result set_strict_builtin_errors(bool strict) {
	    return Result(regorus_rvm_set_strict_builtin_errors(vm, strict));
	}

	Result set_execution_mode(std::uint8_t mode) {
	    return Result(regorus_rvm_set_execution_mode(vm, mode));
	}

	Result set_step_mode(bool enabled) {
	    return Result(regorus_rvm_set_step_mode(vm, enabled));
	}

	Result set_execution_timer_config(bool has_config, RegorusExecutionTimerConfig config) {
	    return Result(regorus_rvm_set_execution_timer_config(vm, has_config, config));
	}

	Result execute() {
	    return Result(regorus_rvm_execute(vm));
	}

	Result execute_entry_point_by_name(const char* entry_point) {
	    return Result(regorus_rvm_execute_entry_point_by_name(vm, entry_point));
	}

	Result execute_entry_point_by_index(size_t index) {
	    return Result(regorus_rvm_execute_entry_point_by_index(vm, index));
	}

	Result resume(const char* resume_value_json, bool has_value) {
	    return Result(regorus_rvm_resume(vm, resume_value_json, has_value));
	}

	Result get_execution_state() {
	    return Result(regorus_rvm_get_execution_state(vm));
	}

	RegorusRvm* raw() const {
	    return vm;
	}

	~Rvm() {
	    if (vm) {
		regorus_rvm_drop(vm);
	    }
	}

    private:
	RegorusRvm* vm;
	Rvm(const Rvm&) = delete;
	Rvm(Rvm&&) = delete;
	Rvm& operator=(const Rvm&) = delete;
    };

    inline Result compile_policy_with_entrypoint(
	const char* data_json,
	const RegorusPolicyModule* modules,
	size_t modules_len,
	const char* entry_point
    ) {
	return Result(regorus_compile_policy_with_entrypoint(
	    data_json,
	    modules,
	    modules_len,
	    entry_point
	));
    }
}

#endif // REGORUS_WRAPPER_HPP

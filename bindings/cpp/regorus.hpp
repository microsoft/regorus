#ifndef REGORUS_WRAPPER_HPP
#define REGORUS_WRAPPER_HPP

#include <memory>
#include <variant>

#include "regorus.ffi.hpp"

namespace regorus {

    class Result {
    public:

	operator bool() const { return result.status == RegorusStatus::RegorusStatusOk; }
	bool operator !() const { return result.status != RegorusStatus::RegorusStatusOk; }

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

	~Result() {
	    regorus_result_drop(result);
	}
	
    private:
	friend class Engine;
	RegorusResult result;

	Result(RegorusResult r) : result(r) {}	
    private:
	Result(const Result&) = delete;
	Result(Result&&) = delete;
	Result& operator=(const Result&) = delete;

    };
    
    class Engine {
    public:
	Engine() : Engine(regorus_engine_new()) {}

	std::unique_ptr<Engine> clone() const {
	    return std::unique_ptr<Engine>(new Engine(regorus_engine_clone(engine)));
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
	
	~Engine() {
	    regorus_engine_drop(engine);
	}
	    
	
    private:
	RegorusEngine* engine;
    private:
	Engine(RegorusEngine* e) : engine(e) {}
	Engine(const Engine&) = delete;
	Engine(Engine&&) = delete;
	Engine& operator=(const Engine&) = delete;
    };
}

#endif // REGORUS_WRAPPER_HPP

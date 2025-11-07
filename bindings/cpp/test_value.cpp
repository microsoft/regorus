// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#include <cassert>
#include <iostream>
#include <string>

#include "regorus_value.hpp"

using regorus::RegorusException;
using regorus::Value;

namespace {

void test_scalar_roundtrip() {
    Value truthy = Value::Bool(true);
    assert(truthy.as_bool());

    Value answer = Value::Int(42);
    assert(answer.as_i64() == 42);

    Value greeting = Value::String("hello");
    assert(greeting.is_string());
    assert(greeting.as_string() == "hello");
}

void test_object_access() {
    Value obj = Value::Object();
    obj.object_insert("flag", Value::Bool(false));
    obj.object_insert("answer", Value::Int(42));

    Value flag = obj.object_get("flag");
    Value answer = obj.object_get("answer");

    assert(flag.as_bool() == false);
    assert(answer.as_i64() == 42);

    // Mutations should not change JSON representation unexpectedly.
    std::string json = obj.to_json();
    assert(json.find("flag") != std::string::npos);
    assert(json.find("answer") != std::string::npos);
}

void test_array_helpers() {
    Value array = Value::FromJson(R"([1, 2, 3])");
    assert(array.array_len() == 3);

    Value first = array.array_get(0);
    Value third = array.array_get(2);

    assert(first.as_i64() == 1);
    assert(third.as_i64() == 3);
}

void test_clone() {
    Value original = Value::FromJson(R"({"nested": [true, false]})");
    Value copy = original.clone();

    assert(original.to_json() == copy.to_json());
    assert(original.get_ptr() != copy.get_ptr());
}

} // namespace

int main() {
    try {
        test_scalar_roundtrip();
        test_object_access();
        test_array_helpers();
        test_clone();
    } catch (const RegorusException& ex) {
        std::cerr << "regorus exception: " << ex.what() << '\n';
        return 1;
    } catch (const std::exception& ex) {
        std::cerr << "unexpected std::exception: " << ex.what() << '\n';
        return 1;
    }

    std::cout << "regorus_value.hpp smoke tests passed" << std::endl;
    return 0;
}

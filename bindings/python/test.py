# Copyright (c) Microsoft Corporation.
# Licensed under the MIT License.
import regorus
import sys

if hasattr(sys.stdout, "reconfigure"):
  sys.stdout.reconfigure(encoding="utf-8")

# Create engine
engine = regorus.Engine()

engine.set_rego_v0(True)

# Load policies
pkg = engine.add_policy_from_file('../../tests/aci/framework.rego')
print(' Loaded package %s' % pkg)

pkg = engine.add_policy_from_file('../../tests/aci/api.rego')
print(' Loaded package %s' % pkg)

pkg = engine.add_policy_from_file('../../tests/aci/policy.rego')
print(' Loaded package %s' % pkg)

# Add policy data
data = {
  "metadata": {
    "devices": {
      "/run/layers/p0-layer0": "1b80f120dbd88e4355d6241b519c3e25290215c469516b49dece9cf07175a766",
      "/run/layers/p0-layer1": "e769d7487cc314d3ee748a4440805317c19262c7acd2fdbdb0d47d2e4613a15c",
      "/run/layers/p0-layer2": "eb36921e1f82af46dfe248ef8f1b3afb6a5230a64181d960d10237a08cd73c79",
      "/run/layers/p0-layer3": "41d64cdeb347bf236b4c13b7403b633ff11f1cf94dbc7cf881a44d6da88c5156",
      "/run/layers/p0-layer4": "4dedae42847c704da891a28c25d32201a1ae440bce2aecccfa8e6f03b97a6a6c",
      "/run/layers/p0-layer5": "fe84c9d5bfddd07a2624d00333cf13c1a9c941f3a261f13ead44fc6a93bc0e7a"
    }
  }
}
engine.add_data(data)

# Set input
input = {
  "containerID": "container0",
  "layerPaths": [
    "/run/layers/p0-layer0",
    "/run/layers/p0-layer1",
    "/run/layers/p0-layer2",
    "/run/layers/p0-layer3",
    "/run/layers/p0-layer4",
    "/run/layers/p0-layer5"
  ],
  "target": "/run/gcs/c/container0/rootfs"
}
engine.set_input(input)

# Eval query
results = engine.eval_query('data.framework.mount_overlay=x')

# Print results
print(results['result'][0])

# Eval query as json
results_json = engine.eval_query_as_json('data.framework.mount_overlay=x')
print(results_json)

# Eval rule
v = engine.eval_rule('data.framework.mount_overlay')
print(v)

# Eval rule as json
v = engine.eval_rule_as_json('data.framework.mount_overlay')
print(v)

# Enable coverage
engine.set_enable_coverage(True)
engine.eval_rule('data.framework.mount_overlay')

# Print coverage
report_json = engine.get_coverage_report_as_json()
print(report_json)

# Pretty coverage report
report = engine.get_coverage_report_pretty()
print(report)

# Clone engine
engine1 = engine.clone()


# Clear coverage data
engine.clear_coverage_data();

print(engine1.get_coverage_report_pretty())

# Enable gathering prints
engine1.set_gather_prints(True)

# Gather prints
engine1.eval_query('print("Hello")')
ps = engine1.take_prints()
print(ps)

# RVM regular example
policy = """
package demo
import rego.v1

default allow := false

allow if {
  input.user == "alice"
  input.active == true
}
"""
def run_regular_example():
  module = ("demo.rego", policy)
  program = regorus.Program.compile_from_modules(
    "{}",
    [module],
    ["data.demo.allow"],
  )

  print(program.generate_listing())

  binary = program.serialize_binary()
  program, is_partial = regorus.Program.deserialize_binary(binary)
  if is_partial:
    raise RuntimeError("Deserialized program marked partial")

  vm = regorus.Rvm()
  vm.load_program(program)
  vm.set_input_json('{"user":"alice","active":true}')
  print(vm.execute())

run_regular_example()

# RVM HostAwait example
policy = """
package demo
import rego.v1

default allow := false

allow if {
  input.account.active == true
  details := __builtin_host_await(input.account.id, "account")
  details.tier == "gold"
}
"""
def run_host_await_example():
  module = ("await.rego", policy)
  program = regorus.Program.compile_from_modules(
    "{}",
    [module],
    ["data.demo.allow"],
  )

  vm = regorus.Rvm()
  vm.set_execution_mode(1)
  vm.load_program(program)
  vm.set_input_json('{"account":{"id":"acct-1","active":true}}')
  vm.execute()
  print(vm.get_execution_state())
  print(vm.resume('{"tier":"gold"}'))

run_host_await_example()

def test_extension_execution():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        result := greeting(a, b) if {
          a := data.a
          b := data.b
        }
        """)

    def custom_function(arg1, arg2):
        return f"{arg1}, {arg2}!"
    rego.add_extension("greeting", 2, custom_function)

    rego.add_data({"a": "Hello", "b": "World"})
    result = rego.eval_rule("data.demo.result")
    assert result == "Hello, World!", f"Unexpected result: {result}"

test_extension_execution()

def test_extension_wrong_arity():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        result := greeting(a, b) if {
          a := data.a
          b := data.b
        }
        """)

    def custom_function(arg1, arg2):
        return f"{arg1}, {arg2}!"

    rego.add_extension("greeting", 3, custom_function)
    rego.add_data({"a": "Hello", "b": "World"})

    try:
        rego.eval_rule("data.demo.result")
    except RuntimeError as ex:
        assert "error: incorrect number of parameters supplied to extension" in str(str(ex)) 
    else:
        assert False, "exception not thrown"

test_extension_wrong_arity()

def test_extension_raises_exception():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        result := greeting(a, b) if {
          a := data.a
          b := data.b
        }
        """)

    def custom_function(arg1, arg2):
        raise RuntimeError("unknown error")

    rego.add_extension("greeting", 2, custom_function)
    rego.add_data({"a": "Hello", "b": "World"})

    try:
        rego.eval_rule("data.demo.result")
    except RuntimeError as ex:
        assert "error: extension 'greeting' raises Python error: RuntimeError: unknown error" in str(ex) 
    else:
        assert False, "exception not thrown"

test_extension_raises_exception()


def test_extension_zero_arg():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        result := greeting()
        """)

    def custom_function():
        return "Hello, World!"

    rego.add_extension("greeting", 0, custom_function)
    rego.add_data({"a": "Hello", "b": "World"})

    result = rego.eval_rule("data.demo.result")
    assert result == "Hello, World!", f"Unexpected result: {result}"

test_extension_zero_arg()

def test_extension_non_callable():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        result := greeting()
        """)

    try:
        rego.add_extension("greeting", 0, 123)
    except RuntimeError as ex:
        assert "extension 'greeting' must be callable" in str(ex)
    else:
        assert False, "exception not thrown"

test_extension_non_callable()


def test_extension_duplicate():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        result := greeting()
        """)

    def custom_function1(arg1, arg2):
        return f"{arg1}, {arg2}!"
    def custom_function2(arg1, arg2):
        return f"{arg1}, {arg2}!"

    rego.add_extension("greeting", 0, custom_function1)

    try:
        rego.add_extension("greeting", 0, custom_function2)
    except RuntimeError as ex:
        assert "extension already added" in str(ex)
    else:
        assert False, "exception not thrown"

test_extension_duplicate()


def test_extension_types():
    rego = regorus.Engine()
    rego.add_policy("demo",
        """
        package demo

        i := custom.triple(10)
        f := custom.triple(2.5)
        b1 := custom.negate(true)
        b2 := custom.negate(false)

        a := custom.first([true, null, 1])
        b := custom.first([null, null, 1])
        c := custom.first([null, null, null])

        object := custom.modify_object({"a": 1, "b": 2})
        list := custom.modify_list([3, 4])
        set := custom.modify_set({5, 6})
        """)

    def triple(n):
        return n*3

    def negate(b):
        return not b

    def first(lst):
        for i in lst:
            if i is not None:
                return i
        return None

    def modify_object(object):
        assert isinstance(object, dict)
        return {k: v*2 for k, v in object.items()}

    def modify_list(lst):
        assert isinstance(lst, list)
        return [x*2 for x in lst]

    def modify_set(st):
        assert isinstance(st, set)
        return {x*2 for x in st}

    rego.add_extension("custom.triple", 1, triple)
    rego.add_extension("custom.negate", 1, negate)
    rego.add_extension("custom.first", 1, first)
    rego.add_extension("custom.modify_object", 1, modify_object)
    rego.add_extension("custom.modify_list", 1, modify_list)
    rego.add_extension("custom.modify_set", 1, modify_set)

    i = rego.eval_rule("data.demo.i")
    assert i == 30, f"Unexpected result for 'i': {i}"

    f = rego.eval_rule("data.demo.f")
    assert f == 7.5, f"Unexpected result for 'f': {f}"

    b1 = rego.eval_rule("data.demo.b1")
    assert b1 == False, f"Unexpected result for 'b1': {b1}"

    b2 = rego.eval_rule("data.demo.b2")
    assert b2 == True, f"Unexpected result for 'b2': {b2}"

    a = rego.eval_rule("data.demo.a")
    assert a == True, f"Unexpected result for 'a': {a}"

    b = rego.eval_rule("data.demo.b")
    assert b == 1, f"Unexpected result for 'b': {b}"

    c = rego.eval_rule("data.demo.c")
    assert c is None, f"Unexpected result for 'c': {c}"

    obj = rego.eval_rule("data.demo.object")
    assert obj == {"a": 2, "b": 4}, f"Unexpected object: {obj}"

    lst = rego.eval_rule("data.demo.list")
    assert lst == [6, 8], f"Unexpected list: {lst}"

    st = rego.eval_rule("data.demo.set")
    assert st == {10, 12}, f"Unexpected lst: {st}"

test_extension_types()

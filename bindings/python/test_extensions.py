# Copyright (c) Microsoft Corporation.
# Licensed under the MIT License.
import json
import pytest
import regorus
import subprocess
import sys

TEST_EXT_NAME = "Microsoft.Azure.ActiveDirectory.AADSSHLoginForLinux"


def test_native_conversion_roundtrips():
    subprocess.run(
        [
            sys.executable,
            "-c",
            "import threading\n"
            "from concurrent.futures import ThreadPoolExecutor\n"
            "from test_extensions import _check_native_conversion\n"
            "threading.stack_size(1_500_000)\n"
            "with ThreadPoolExecutor(max_workers=1) as pool:\n"
            "    pool.submit(_check_native_conversion).result()\n",
        ],
        check=True,
        timeout=30,
    )


def _check_native_conversion():
    from collections import UserDict, UserList

    engine = regorus.Engine()
    engine.add_policy(
        "conversion.rego",
        "package conversion\nanswer := input\nwrapped := [input]\nsize := count(input)",
    )
    for container in [[], {}, UserList(), UserDict()]:
        if isinstance(container, (dict, UserDict)):
            container["value"] = container
        else:
            container.append(container)
        with pytest.raises(ValueError, match="cyclic native value"):
            engine.set_input(container)

    left = []
    right = {"left": left}
    left.append(right)
    with pytest.raises(ValueError, match="cyclic native value"):
        engine.set_input(right)

    shared = {"value": (1, 2)}
    engine.set_input([shared, shared])
    assert engine.eval_rule("data.conversion.answer") == [
        {"value": [1, 2]}, {"value": [1, 2]}
    ]
    for depth in [32, 33]:
        value = None
        for _ in range(depth):
            value = [value]
        if depth == 32:
            engine.set_input(value)
            assert engine.eval_rule("data.conversion.answer") == value
            with pytest.raises(RuntimeError, match="nesting limit"):
                engine.eval_rule("data.conversion.wrapped")
        else:
            with pytest.raises(ValueError, match="nesting limit"):
                engine.set_input(value)
        engine.set_input([7])
        assert engine.eval_rule("data.conversion.answer") == [7]

    key = 0
    for _ in range(31):
        key = (key,)
    engine.set_input({key: True})
    assert engine.eval_rule("data.conversion.size") == 1
    with pytest.raises(ValueError, match="nesting limit"):
        engine.set_input({(key,): True})


@pytest.fixture(name="engine", scope="function")
def engine_fixture():
    """
    Fixture to handle creation and cleanup of a default policy engine.
    New engine is created for each test case.
    """
    engine = regorus.Engine()
    engine.add_policy_from_file('../../examples/extension_list/agent_extension_policy.rego')
    yield engine


@pytest.mark.parametrize("value", [float("nan"), float("inf"), float("-inf")])
def test_native_input_rejects_non_finite_numbers(value):
    engine = regorus.Engine()

    with pytest.raises(ValueError, match="not valid Rego numbers"):
        engine.set_input({"value": value})


@pytest.mark.parametrize("value", [float("nan"), float("inf"), float("-inf")])
def test_native_data_rejects_non_finite_numbers(value):
    engine = regorus.Engine()

    with pytest.raises(ValueError, match="not valid Rego numbers"):
        engine.add_data({"value": value})


@pytest.fixture(name="input_data")
def input_data_fixture():
    """
    Fixture to handle creation and cleanup of a default input data.
    New input data is created for each test case.
    """
    input_data = {
        "extensions": {
            TEST_EXT_NAME: {
                "signingInfo": {
                    "extensionSigned": False
                }
            }
        }
    }
    input_json = json.dumps(input_data)
    yield input_json


@pytest.fixture(name="default_data")
def default_data_fixture():
    """Fixture for default data"""
    data_json = {
        "azureGuestAgentPolicy": {
            "policyVersion": "0.1.0",
            "signingRules": {
                "extensionSigned": False
            },
            "allowListOnly": False
        }
    }
    data_json = json.dumps(data_json)
    yield data_json


def test_default_data_json(engine, input_data):
    """Test the default data in json format for extension policy."""
    data_json = {
        "azureGuestAgentPolicy": {
            "policyVersion": "0.1.0",
            "signingRules": {
                "extensionSigned": False
            },
            "allowListOnly": False
        }
    }
    data_json = json.dumps(data_json)
    engine.add_data_json(data_json)
    engine.set_input_json(input_data)
    # Eval query
    results = engine.eval_query('data.agent_extension_policy')
    assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][TEST_EXT_NAME]['downloadAllowed']


def test_default_data_file(engine, input_data):
    """Test the default data in file format for extension policy."""
    data_default_path = "../../examples/extension_list/agent-extension-default-data.json"
    engine.add_data_from_json_file(data_default_path)
    engine.set_input_json(input_data)
    # Eval query
    results = engine.eval_query('data.agent_extension_policy')
    assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][TEST_EXT_NAME]['downloadAllowed']


def test_allow_all(engine, input_data):
    """Test the policy engine with allow all policy."""
    data_json = {
        "azureGuestAgentPolicy": {
            "policyVersion": "0.1.0",
            "signingRules": {
                "extensionSigned": False
            },
            "allowListOnly": False
        }
    }
    data_json = json.dumps(data_json)
    engine.add_data_json(data_json)
    engine.set_input_json(input_data)
    # Eval query
    results = engine.eval_query('data.agent_extension_policy')
    assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][TEST_EXT_NAME]['downloadAllowed']


def test_name_only_input(engine, default_data):
    """Test input with only the extension name."""
    input_data = {
        "extensions": {
            TEST_EXT_NAME: {
            }
        }
    }
    input_json = json.dumps(input_data)
    engine.add_data_json(default_data)
    engine.set_input_json(input_json)
    # Eval query
    results = engine.eval_query('data.agent_extension_policy')
    assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][TEST_EXT_NAME]['downloadAllowed']


@pytest.mark.parametrize("input_signed, extension_signed", [
    (True, True),
    (True, False),
    (False, True),
    (False, False)
])
def test_extension_signed_rule(engine, input_signed, extension_signed):
    """
    Test extension signing rule. Engine should be able to handle
    both signed and unsigned extensions, with extensionSigned rule set
    to either true or false.
    """
    data_json = {
        "azureGuestAgentPolicy": {
            "policyVersion": "0.1.0",
            "signingRules": {
                "extensionSigned": extension_signed
            },
            "allowListOnly": False
        }
    }
    input_data = {
        "extensions": {
            TEST_EXT_NAME: {
                "signingInfo": {
                    "extensionSigned": input_signed
                }
            }
        }
    }
    data_json = json.dumps(data_json)
    input_data = json.dumps(input_data)
    engine.add_data_json(data_json)
    engine.set_input_json(input_data)
    # Eval query
    results = engine.eval_query('data.agent_extension_policy')

    # assert results
    if extension_signed:
        assert results['result'][0]['expressions'][0]['value']['extensions_validated'][TEST_EXT_NAME]['signingValidated'] == input_signed
    else:
        assert results['result'][0]['expressions'][0]['value']['extensions_validated'][TEST_EXT_NAME]['signingValidated']
    assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][TEST_EXT_NAME]['downloadAllowed']


@pytest.mark.parametrize("ext_allowed, allow_rule", [
    (True, True),
    (True, False),
    (False, True),
    (False, False)
])
def test_allowlist_rule(engine, ext_allowed, allow_rule):
    """
    Test allowListOnly rule. Engine should be able to handle
    both allowed and disallowed extensions, with allowListOnly rule
    set to either true or false.
    """
    if ext_allowed:
        ext_name = TEST_EXT_NAME
    else:
        ext_name = "random_disallowed_extension"

    input_json = {
        "extensions": {
            ext_name: {
                "signingInfo": {
                    "extensionSigned": False
                }
            }
        }
    }
    data_json = {
        "azureGuestAgentPolicy": {
            "signingRules": {
                "extensionSigned": False
            },
            "allowListOnly": allow_rule
        },
        "azureGuestExtensionsPolicy": {
            "Microsoft.CPlat.Core.RunCommandLinux": {
            },
            TEST_EXT_NAME: {
            }
        }
    }
    input_json = json.dumps(input_json)
    data_json = json.dumps(data_json)
    engine.add_data_json(data_json)
    engine.set_input_json(input_json)
    # Eval query
    results = engine.eval_query('data.agent_extension_policy')
    if allow_rule:
        assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][ext_name]['downloadAllowed'] == ext_allowed
    else:
        assert results['result'][0]['expressions'][0]['value']['extensions_to_download'][ext_name]['downloadAllowed']

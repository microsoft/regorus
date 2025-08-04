// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

namespace Regorus.Tests;

using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Text.Json.Nodes;

[TestClass]
public class RegorusTests
{
    [TestMethod]
    public void Basic_evaluation_succeeds()
    {
        using var engine = new Engine();
        engine.AddPolicy(
            "test.rego",
            "package test\nx = 1\nmessage = `Hello`");

        var result = engine.EvalRule("data.test.message");

        Assert.AreEqual("\"Hello\"", result);
    }

    [TestMethod]
    public void Evaluation_using_file_policies_succeeds()
    {
        using var engine = new Engine();
        engine.SetRegoV0(true);

        // Load policies and data.
        engine.AddPolicyFromFile("tests/aci/framework.rego");
        engine.AddPolicyFromFile("tests/aci/api.rego");
        engine.AddPolicyFromFile("tests/aci/policy.rego");
        engine.AddDataFromJsonFile("tests/aci/data.json");

        // Set input and eval rule.
        engine.SetInputFromJsonFile("tests/aci/input.json");
        var result = engine.EvalRule("data.framework.mount_overlay");

        var expected = """
{
  "allowed": true,
  "metadata": [
    {
      "action": "add",
      "key": "container0",
      "name": "matches",
      "value": [
        {
          "allow_elevated": true,
          "allow_stdio_access": false,
          "capabilities": {
            "ambient": [
              "CAP_SYS_ADMIN"
            ],
            "bounding": [
              "CAP_SYS_ADMIN"
            ],
            "effective": [
              "CAP_SYS_ADMIN"
            ],
            "inheritable": [
              "CAP_SYS_ADMIN"
            ],
            "permitted": [
              "CAP_SYS_ADMIN"
            ]
          },
          "command": [
            "rustc",
            "--help"
          ],
          "env_rules": [
            {
              "pattern": "PATH=/usr/local/cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
              "required": true,
              "strategy": "string"
            },
            {
              "pattern": "RUSTUP_HOME=/usr/local/rustup",
              "required": true,
              "strategy": "string"
            },
            {
              "pattern": "CARGO_HOME=/usr/local/cargo",
              "required": true,
              "strategy": "string"
            },
            {
              "pattern": "RUST_VERSION=1.52.1",
              "required": true,
              "strategy": "string"
            },
            {
              "pattern": "TERM=xterm",
              "required": false,
              "strategy": "string"
            },
            {
              "pattern": "PREFIX_.+=.+",
              "required": false,
              "strategy": "re2"
            }
          ],
          "exec_processes": [
            {
              "command": [
                "top"
              ],
              "signals": []
            }
          ],
          "layers": [
            "fe84c9d5bfddd07a2624d00333cf13c1a9c941f3a261f13ead44fc6a93bc0e7a",
            "4dedae42847c704da891a28c25d32201a1ae440bce2aecccfa8e6f03b97a6a6c",
            "41d64cdeb347bf236b4c13b7403b633ff11f1cf94dbc7cf881a44d6da88c5156",
            "eb36921e1f82af46dfe248ef8f1b3afb6a5230a64181d960d10237a08cd73c79",
            "e769d7487cc314d3ee748a4440805317c19262c7acd2fdbdb0d47d2e4613a15c",
            "1b80f120dbd88e4355d6241b519c3e25290215c469516b49dece9cf07175a766"
          ],
          "mounts": [
            {
              "destination": "/container/path/one",
              "options": [
                "rbind",
                "rshared",
                "rw"
              ],
              "source": "sandbox:///host/path/one",
              "type": "bind"
            },
            {
              "destination": "/container/path/two",
              "options": [
                "rbind",
                "rshared",
                "ro"
              ],
              "source": "sandbox:///host/path/two",
              "type": "bind"
            }
          ],
          "no_new_privileges": true,
          "seccomp_profile_sha256": "",
          "signals": [],
          "user": {
            "group_idnames": [
              {
                "pattern": "",
                "strategy": "any"
              }
            ],
            "umask": "0022",
            "user_idname": {
              "pattern": "",
              "strategy": "any"
            }
          },
          "working_dir": "/home/user"
        }
      ]
    },
    {
      "action": "add",
      "key": "/run/gcs/c/container0/rootfs",
      "name": "overlayTargets",
      "value": true
    }
  ]
}
""";

        Assert.IsTrue(JsonNode.DeepEquals(JsonNode.Parse(expected), JsonNode.Parse(result!)), $"Actual: {result}");
    }

    [TestMethod]
    public void GetPolicyPackageNames_succeeds()
    {
        using var engine = new Engine();
        engine.AddPolicy(
            "test.rego",
            "package test\nx = 1\nmessage = `Hello`");

        engine.AddPolicy(
            "test.rego",
            "package test.nested.name\nx = 1\nmessage = `Hello`");

        var result = engine.GetPolicyPackageNames();

        var packageNames = JsonNode.Parse(result!);

        Assert.AreEqual("test", packageNames![0]["package_name"].ToString());
        Assert.AreEqual("test.nested.name", packageNames![1]["package_name"].ToString());
    }

    [TestMethod]
    public void GetPolicyParameters_succeeds()
    {
        using var engine = new Engine();
        engine.AddPolicy(
            "test.rego",
            "package test\n default parameters.a = 5\nparameters.b = 10\nx = 1\nmessage = `Hello`");

        var result = engine.GetPolicyParameters();

        var parameters = JsonNode.Parse(result!);

        Assert.AreEqual(1, parameters![0]["parameters"].AsArray().Count);
        Assert.AreEqual(1, parameters![0]["modifiers"].AsArray().Count);

        Assert.AreEqual("a", parameters![0]["parameters"][0]["name"].ToString());
        Assert.AreEqual("b", parameters![0]["modifiers"][0]["name"].ToString());
    }
}
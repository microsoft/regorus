// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

import com.microsoft.regorus.Engine;
import com.microsoft.regorus.PolicyModule;
import com.microsoft.regorus.Program;
import com.microsoft.regorus.Rvm;

public class Test {

    public static void main(String[] args) {
        try (Engine engine = new Engine()) {
            String pkg = engine.addPolicy(
                    "hello.rego",
                    "package test\nx=1\nmessage = concat(\", \", [input.message, data.message])"
            );
            System.out.println("Loaded package " + pkg);

            engine.addDataJson("{\"message\":\"World!\"}");
            engine.setInputJson("{\"message\":\"Hello\"}");

            // Evaluate query.
            String resJson = engine.evalQuery("data.test.message");
            System.out.println(resJson);

            // Enable coverage.
            engine.setEnableCoverage(true);

            // Evaluate rule.
            String valueJson = engine.evalRule("data.test.message");
            System.out.println(valueJson);

            String coverageJson = engine.getCoverageReport();
            System.out.println(coverageJson);

            System.out.println(engine.getCoverageReportPretty());

            String packagesJson = engine.getPackages();
            System.out.println(packagesJson);

            String policiesJson = engine.getPolicies();
            System.out.println(policiesJson);

            engine.setRegoV0(true);
            engine.addPolicy(
                    "world.rego",
                    "package world\nx { true }"
            );
        }

                String regularPolicy = String.join("\n",
                                "package demo",
                                "import rego.v1",
                                "",
                                "default allow := false",
                                "",
                                "allow if {",
                                "  input.user == \"alice\"",
                                "  input.active == true",
                                "}"
                );
                String regularInput = "{\"user\":\"alice\",\"active\":true}";

                {
                    PolicyModule module = new PolicyModule("demo.rego", regularPolicy);
                    Program program = Program.compileFromModules("{}", new PolicyModule[]{module}, new String[]{"data.demo.allow"});
                    System.out.println("RVM listing:\n" + program.generateListing());

                    byte[] binary = program.serializeBinary();
                    program.close();

                    boolean[] isPartial = new boolean[1];
                    Program rehydrated = Program.deserializeBinary(binary, isPartial);
                    if (isPartial[0]) {
                        throw new IllegalStateException("Deserialized program marked partial");
                    }

                    try (Rvm vm = new Rvm()) {
                        vm.loadProgram(rehydrated);
                        vm.setInputJson(regularInput);
                        String result = vm.execute();
                        System.out.println("RVM regular result: " + result);
                    }
                    rehydrated.close();
                }

                String awaitPolicy = String.join("\n",
                                "package demo",
                                "import rego.v1",
                                "",
                                "default allow := false",
                                "",
                                "allow if {",
                                "  input.account.active == true",
                                "  details := __builtin_host_await(input.account.id, \"account\")",
                                "  details.tier == \"gold\"",
                                "}"
                );
                String awaitInput = "{\"account\":{\"id\":\"acct-1\",\"active\":true}}";

                {
                    PolicyModule module = new PolicyModule("await.rego", awaitPolicy);
                    Program program = Program.compileFromModules("{}", new PolicyModule[]{module}, new String[]{"data.demo.allow"});
                    try (Rvm vm = new Rvm()) {
                        vm.setExecutionMode((byte) 1);
                        vm.loadProgram(program);
                        vm.setInputJson(awaitInput);
                        vm.execute();
                        System.out.println("HostAwait state: " + vm.getExecutionState());
                        String resumed = vm.resume("{\"tier\":\"gold\"}");
                        System.out.println("HostAwait result: " + resumed);
                    }
                    program.close();
                }
    }
}

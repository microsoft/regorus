// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

import com.microsoft.regorus.Engine;

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
        }
    }
}

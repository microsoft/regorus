// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

import com.microsoft.regorus.Engine;

public class Test {
    public static void main(String[] args) {
        try (Engine engine = new Engine()) {
            engine.addPolicy(
                "hello.rego",
                "package test\nmessage = concat(\", \", [input.message, data.message])"
            );
            engine.addDataJson("{\"message\":\"World!\"}");
            engine.setInputJson("{\"message\":\"Hello\"}");
            String resJson = engine.evalQuery("data.test.message");

            System.out.println(resJson);
        }
    }
}

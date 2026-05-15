/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/
package com.microsoft.regorus;

import java.util.Map;
import java.util.ArrayList;
import junit.framework.TestCase;
import junit.framework.Assert;
import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

public class EngineTest extends TestCase
{
    public void test_engine()
    {
        String resJson;
        try (Engine engine = new Engine()) {
            engine.addPolicy(
                "hello.rego",
                "package test\nmessage = concat(\", \", [input.message, data.message])"
            );
            engine.addDataJson("{\"message\":\"World!\"}");
            engine.prepare();
            engine.setInputJson("{\"message\":\"Hello\"}");
            resJson = engine.evalQuery("data.test.message");

            try (Engine template = engine.clone()) {
                template.setInputJson("{\"message\":\"Hi\"}");
                String templateResJson = template.evalQuery("data.test.message");
                Map templateRes = new Gson().fromJson(templateResJson, Map.class);
                ArrayList templateResults = (ArrayList) templateRes.get("result");
                ArrayList templateExpressions = (ArrayList) ((Map) templateResults.get(0)).get("expressions");
                Map templateExpression = (Map) templateExpressions.get(0);
                Assert.assertEquals("Hi, World!", templateExpression.get("value"));
            }
        }

        Gson gson = new Gson();
        Map res = gson.fromJson(resJson, Map.class);
        ArrayList results = (ArrayList) res.get("result");
        ArrayList expressions = (ArrayList) ((Map) results.get(0)).get("expressions");
        Map expression = (Map) expressions.get(0);
        Assert.assertEquals("Hello, World!", expression.get("value"));
    }

    public void test_closed_engine_operations_throw()
    {
        Engine engine = new Engine();
        engine.close();

        try {
            engine.prepare();
            fail("prepare should fail on closed engine");
        } catch (IllegalStateException expected) {
        }

        try {
            engine.clone();
            fail("clone should fail on closed engine");
        } catch (IllegalStateException expected) {
        }

        try {
            engine.evalQuery("data");
            fail("evalQuery should fail on closed engine");
        } catch (IllegalStateException expected) {
        }
    }
}

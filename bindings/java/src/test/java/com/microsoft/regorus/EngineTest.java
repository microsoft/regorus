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
            engine.setInputJson("{\"message\":\"Hello\"}");
            resJson = engine.evalQuery("data.test.message");
        }

        Gson gson = new Gson();
        Map res = gson.fromJson(resJson, Map.class);
        ArrayList results = (ArrayList) res.get("result");
        ArrayList expressions = (ArrayList) ((Map) results.get(0)).get("expressions");
        Map expression = (Map) expressions.get(0);
        Assert.assertEquals("Hello, World!", expression.get("value"));
    }
}

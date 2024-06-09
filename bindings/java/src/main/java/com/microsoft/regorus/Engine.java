/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/

package com.microsoft.regorus;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Regorus Engine.
 */
public class Engine implements AutoCloseable, Cloneable {
    // Methods exposed from Rust side, you can run
    // `javac -h . src/main/java/com/microsoft/regorus/Engine.java` to update
    // expected native header at `bindings/java/com_microsoft_regorus_Engine.h`
    // if you update the native API.
    private static native long nativeNewEngine();
    private static native long nativeClone(long enginePtr);
    private static native String nativeAddPolicy(long enginePtr, String path, String rego);
    private static native String nativeAddPolicyFromFile(long enginePtr, String path);
    private static native String nativeGetPackages(long enginePtr);
    private static native String nativeGetPolicies(long enginePtr);
    private static native void nativeClearData(long enginePtr);
    private static native void nativeAddDataJson(long enginePtr, String data);
    private static native void nativeAddDataJsonFromFile(long enginePtr, String path);
    private static native void nativeSetInputJson(long enginePtr, String input);
    private static native void nativeSetInputJsonFromFile(long enginePtr, String path);
    private static native String nativeEvalQuery(long enginePtr, String query);
    private static native String nativeEvalRule(long enginePtr, String qrule);
    private static native void nativeSetEnableCoverage(long enginePtr, boolean enable);
    private static native String nativeGetCoverageReport(long enginePtr);
    private static native String nativeGetCoverageReportPretty(long enginePtr);
    private static native void nativeClearCoverageData(long enginePtr);
    private static native void nativeSetGatherPrints(long enginePtr, boolean b);
    private static native String nativeTakePrints(long enginePtr);
    private static native void nativeDestroyEngine(long enginePtr);

    // Pointer to Engine allocated on Rust's heap, all native methods works on
    // engine expects this pointer. It is free'd in `close` method.
    private final long enginePtr;

    /**
     * Creates a new Regorus Engine.
     */
    public Engine() {
        enginePtr = nativeNewEngine();
    }

    
    Engine(long ptr) {
	enginePtr = ptr;
    }

    /**
     * Efficiently clones an Engine.
     */
    public Engine clone() {
	return new Engine(nativeClone(enginePtr));
    }
    
    /**
     * Adds an inline Rego policy.
     * 
     * @param filename Filename of this Rego policy.
     * @param rego     Rego policy.
     * 
     * @return Rego package defined in the policy.
     */
    public String addPolicy(String filename, String rego) {
        return nativeAddPolicy(enginePtr, filename, rego);
    }

    /**
     * Adds a Rego policy from given path.
     * 
     * @param path Path of the Rego policy.
     * 
     * @return Rego package defined in the policy.
     */
    public String addPolicyFromFile(String path) {
        return nativeAddPolicyFromFile(enginePtr, path);
    }

    /**
     * Get list of loaded Rego packages.
     * 
     * @return List of Rego packages as a JSON array of strings.
     */
    public String getPackages() {
        return nativeGetPackages(enginePtr);
    }
    
    /**
     * Get list of loaded policies.
     * 
     * @return List of Rego policies as a JSON array of sources.
     */
    public String getPolicies() {
        return nativeGetPolicies(enginePtr);
    }
    
    /**
     * Clears the data  document.
     */
    public void clearData() {
        nativeClearData(enginePtr);
    }

    /**
     * Adds inline data document from given JSON. 
     * The specified data document is merged into existing data document.
     * It will throw an error if new data conflicts with the existing document.
     * 
     * Example:
     *  addDataJson("[]") - Throws as it's not an object.
     *  addDataJson('{"a": 1}') - Fine
     *  addDataJson('{"b": 2}') - Fine, now {"a": 1, "b": 2}
     *  addDataJson('{"b": 3}') - Throws as `b` conflicts.
     * 
     * @see clearData
     * 
     * @throws RuntimeException If data conflicts with the existing document 
     *                          or data is not an object.
     * 
     * @param data Inline data document.
     */
    public void addDataJson(String data) throws RuntimeException {
        nativeAddDataJson(enginePtr, data);
    }

    /**
     * Adds data document from given JSON file. 
     * The specified data document is merged into existing data document.
     * It will throw an error if new data conflicts with the existing document.
     * 
     * @see addDataJson
     * @see clearData
     * 
     * @throws RuntimeException If data conflicts with the existing document 
     *                          or data is not an object.
     * 
     * @param path Path to JSON data document.
     */
    public void addDataJsonFromFile(String path) throws RuntimeException {
        nativeAddDataJsonFromFile(enginePtr, path);
    }

    /**
     * Sets inline JSON input.
     * 
     * @param input inline JSON input.
     */
    public void setInputJson(String input) {
        nativeSetInputJson(enginePtr, input);
    }

    /**
     * Sets JSON input from given path.
     * 
     * @param path Path to JSON input.
     */
    public void setInputJsonFromFile(String path) {
        nativeSetInputJsonFromFile(enginePtr, path);
    }

    /**
     * Evaluates given Rego query and returns a JSON string as a result.
     * 
     * @param query The Rego query.
     * 
     * @return Query results as a JSON string.
     */
    public String evalQuery(String query) {
        return nativeEvalQuery(enginePtr, query);
    }
    
    /**
     * Evaluates given Rego rule and returns a JSON string as a result.
     * 
     * @param rule Path of the  Rego rule.
     * 
     * @return Value of the rule as a JSON string.
     */
    public String evalRule(String rule) {
        return nativeEvalRule(enginePtr, rule);
    }
    
    /**
     * Enable/disable coverage.
     * 
     * @param enable Whether to enable coverage or not.
     * 
     */
    public void setEnableCoverage(boolean enable) {
        nativeSetEnableCoverage(enginePtr, enable);
    }
    
    /**
     * Clear coverage data.
     * 
     */
    public void clearCoverageData() {
        nativeClearCoverageData(enginePtr);
    }
    
    /**
     * Get coverage report as json string.
     * 
     */
    public String getCoverageReport() {
        return nativeGetCoverageReport(enginePtr);
    }
    
    /**
     * Get coverage report as ANSI color coded string.
     * 
     */
    public String getCoverageReportPretty() {
        return nativeGetCoverageReportPretty(enginePtr);
    }
    
    /**
     * Enable/disable gathering prints.
     * 
     * @param b Whether to gather prints or not.
     * 
     */
    public void setGatherPrints(boolean b) {
        nativeSetGatherPrints(enginePtr, b);
    }
    
    /**
     * Take gathered prints.
     * 
     */
    public String takePrints() {
        return nativeTakePrints(enginePtr);
    }

    
    @Override
    public void close() {
        nativeDestroyEngine(enginePtr);
    }

    // Loading native library from JAR is adapted from:
    // https://github.com/apache/opendal/blob/93e5f65bbf30df2fed4bdd95bb0685c73c6418c2/bindings/java/src/main/java/org/apache/opendal/NativeLibrary.java
    // https://github.com/apache/opendal/blob/93e5f65bbf30df2fed4bdd95bb0685c73c6418c2/bindings/java/src/main/java/org/apache/opendal/Environment.java
    static {
        // Build a Rust target triple, like: 'aarch64-unknown-linux-gnu'.
        final StringBuilder targetTripleBuilder = new StringBuilder();

        final String arch = System.getProperty("os.arch").toLowerCase();
        if (arch.equals("aarch64")) {
            targetTripleBuilder.append("aarch64");
        } else {
            targetTripleBuilder.append("x86_64");
        }
        targetTripleBuilder.append("-");

        final String os = System.getProperty("os.name").toLowerCase();
        if (os.startsWith("windows")) {
            targetTripleBuilder.append("pc-windows-msvc");
        } else if (os.startsWith("mac")) {
            targetTripleBuilder.append("apple-darwin");
        } else {
            targetTripleBuilder.append("unknown-linux-gnu");
        }

        loadNativeLibrary(targetTripleBuilder.toString());
    }

    private static void loadNativeLibrary(String targetTriple) {
        try {
            // try dynamic library - the search path can be configured via "-Djava.library.path"
            System.loadLibrary("regorus_java");
            return;
        } catch (UnsatisfiedLinkError ignore) {
            // ignore - try from classpath
        }

        // Native libraries will be bundles into JARs like: 
        // `aarch64-apple-darwin/libregorus_java.dylib`
        final String libraryName = System.mapLibraryName("regorus_java");
        final String libraryPath = "/" + targetTriple + "/" + libraryName;

        try (final InputStream is = Engine.class.getResourceAsStream(libraryPath)) {
            if (is == null) {
                throw new RuntimeException("Cannot find " + libraryPath + "\nSee https://github.com/microsoft/regorus/tree/main/bindings/java for help.");
            }
            final int dot = libraryPath.indexOf('.');
            final File tmpFile = File.createTempFile(libraryPath.substring(0, dot), libraryPath.substring(dot));
            tmpFile.deleteOnExit();
            Files.copy(is, tmpFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
            System.load(tmpFile.getAbsolutePath());
        } catch (IOException exception) {
            throw new RuntimeException(exception);
        }
    }
}

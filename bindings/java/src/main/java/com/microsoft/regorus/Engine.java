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

public class Engine implements AutoCloseable {
    // Methods exposed from Rust side, you can run
    // `javac -h . src/main/java/com/microsoft/regorus/Engine.java` to update
    // expected native header at `bindings/java/com_microsoft_regorus_Engine.h`
    // if you update the native API.
    private static native long newEngine();
    private static native void addPolicy(long enginePtr, String path, String rego);
    private static native void addPolicyFromFile(long enginePtr, String path);
    private static native void addDataJson(long enginePtr, String data);
    private static native void addDataJsonFromFile(long enginePtr, String path);
    private static native void setInputJson(long enginePtr, String input);
    private static native void setInputJsonFromFile(long enginePtr, String path);
    private static native String evalQuery(long enginePtr, String query);
    private static native void destroyEngine(long enginePtr);

    // Pointer to Engine allocated on Rust's heap, all native methods works on
    // engine expects this pointer. It is free'd in `close` method.
    private final long enginePtr;

    public Engine() {
        enginePtr = newEngine();
    }

    public void pubAddPolicy(String path, String rego) {
        addPolicy(enginePtr, path, rego);
    }

    public void pubAddDataJson(String path) {
        addDataJson(enginePtr, path);
    }

    public void pubSetInputJson(String path) {
        setInputJson(enginePtr, path);
    }

    public String pubEvalQuery(String path) {
        return evalQuery(enginePtr, path);
    }
    
    @Override
    public void close() {
        destroyEngine(enginePtr);
    }

    // Loading native library from jar is adapted from:
    // https://github.com/apache/opendal/blob/93e5f65bbf30df2fed4bdd95bb0685c73c6418c2/bindings/java/src/main/java/org/apache/opendal/NativeLibrary.java
    // https://github.com/apache/opendal/blob/93e5f65bbf30df2fed4bdd95bb0685c73c6418c2/bindings/java/src/main/java/org/apache/opendal/Environment.java
    private static final String classifier;
    static {
        final StringBuilder classifierBuilder = new StringBuilder();
        final String os = System.getProperty("os.name").toLowerCase();
        if (os.startsWith("windows")) {
            classifierBuilder.append("windows");
        } else if (os.startsWith("mac")) {
            classifierBuilder.append("osx");
        } else {
            classifierBuilder.append("linux");
        }
        classifierBuilder.append("-");
        final String arch = System.getProperty("os.arch").toLowerCase();
        if (arch.equals("aarch64")) {
            classifierBuilder.append("aarch_64");
        } else {
            classifierBuilder.append("x86_64");
        }
        classifier = classifierBuilder.toString();

        loadNativeLibrary();
    }

    private static void loadNativeLibrary() {
        try {
            // try dynamic library - the search path can be configured via "-Djava.library.path"
            System.loadLibrary("regorus_java");
            return;
        } catch (UnsatisfiedLinkError ignore) {
            // ignore - try from classpath
        }

        final String libraryPath = bundledLibraryPath();
        try (final InputStream is = Engine.class.getResourceAsStream(libraryPath)) {
            if (is == null) {
                throw new RuntimeException("cannot find " + libraryPath);
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

    private static String bundledLibraryPath() {
        final String libraryName = System.mapLibraryName("regorus_java");
        return "/native/" + classifier + "/" + libraryName;
    }
}

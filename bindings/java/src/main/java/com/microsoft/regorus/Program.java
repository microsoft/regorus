/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/

package com.microsoft.regorus;

/**
 * Represents a compiled RVM program.
 */
public final class Program implements AutoCloseable {
    private static native long nativeCompileFromModules(
            String dataJson,
            String[] moduleIds,
            String[] moduleContents,
            String[] entryPoints);

    private static native long nativeCompileFromEngine(long enginePtr, String[] entryPoints);
    private static native String nativeGenerateListing(long programPtr);
    private static native byte[] nativeSerializeBinary(long programPtr);
    private static native long nativeDeserializeBinary(byte[] data, boolean[] isPartial);
    private static native void nativeDrop(long programPtr);

    private final long programPtr;

    Program(long ptr) {
        this.programPtr = ptr;
    }

    /**
     * Compile a program from modules and entry points.
     *
     * @param dataJson JSON document to merge as static data.
     * @param modules Policy modules to compile.
     * @param entryPoints Entry point rule paths.
     * @return Compiled program instance.
     */
    public static Program compileFromModules(String dataJson, PolicyModule[] modules, String[] entryPoints) {
        String[] ids = new String[modules.length];
        String[] contents = new String[modules.length];
        for (int i = 0; i < modules.length; i++) {
            ids[i] = modules[i].id;
            contents[i] = modules[i].content;
        }
        long ptr = nativeCompileFromModules(dataJson, ids, contents, entryPoints);
        return new Program(ptr);
    }

    /**
     * Compile a program from an engine and entry points.
     *
     * @param engine Engine with loaded policies.
     * @param entryPoints Entry point rule paths.
     * @return Compiled program instance.
     */
    public static Program compileFromEngine(Engine engine, String[] entryPoints) {
        long ptr = nativeCompileFromEngine(engine.getPtr(), entryPoints);
        return new Program(ptr);
    }

    /**
     * Generate a readable assembly listing.
     *
     * @return Listing text.
     */
    public String generateListing() {
        return nativeGenerateListing(programPtr);
    }

    /**
     * Serialize the program to binary format.
     *
     * @return Serialized bytes.
     */
    public byte[] serializeBinary() {
        return nativeSerializeBinary(programPtr);
    }

    /**
     * Deserialize a program from binary format.
     *
     * @param data Serialized program bytes.
     * @param isPartial Optional array to receive the partial flag (index 0). Only
     *                  blobs of a legacy format version, or a program whose builtins
     *                  this build cannot resolve, come back partial; a blob of the
     *                  current format version that does not decode is rejected.
     * @return Deserialized program instance.
     * @throws RuntimeException if the blob is rejected (corrupt section, truncated
     *                          tail, over-limit table, unsupported future version).
     */
    public static Program deserializeBinary(byte[] data, boolean[] isPartial) {
        if (data == null || data.length == 0) {
            throw new IllegalArgumentException("data must not be empty");
        }
        long ptr = nativeDeserializeBinary(data, isPartial);
        if (ptr == 0) {
            // The native shim reports a rejected blob by throwing and returning 0; never wrap a
            // null handle into a Program that would evaluate an empty instruction table.
            throw new IllegalStateException("regorus: could not deserialize program blob");
        }
        return new Program(ptr);
    }

    long getPtr() {
        return programPtr;
    }

    @Override
    public void close() {
        nativeDrop(programPtr);
    }
}

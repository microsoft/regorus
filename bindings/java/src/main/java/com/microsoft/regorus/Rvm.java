/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/

package com.microsoft.regorus;

/**
 * Wrapper for the Regorus RVM runtime.
 */
public final class Rvm implements AutoCloseable {
    private static native long nativeNew();
    private static native void nativeDrop(long vmPtr);
    private static native void nativeLoadProgram(long vmPtr, long programPtr);
    private static native void nativeSetDataJson(long vmPtr, String dataJson);
    private static native void nativeSetInputJson(long vmPtr, String inputJson);
    private static native void nativeSetExecutionMode(long vmPtr, byte mode);
    private static native String nativeExecute(long vmPtr);
    private static native String nativeExecuteEntryPoint(long vmPtr, String entryPoint);
    private static native String nativeResume(long vmPtr, String resumeJson, boolean hasValue);
    private static native String nativeGetExecutionState(long vmPtr);

    private final long vmPtr;

    /**
     * Create a new RVM instance.
     */
    public Rvm() {
        this.vmPtr = nativeNew();
    }

    /**
     * Load a program into the VM.
     *
     * @param program Compiled program.
     */
    public void loadProgram(Program program) {
        nativeLoadProgram(vmPtr, program.getPtr());
    }

    /**
     * Set data JSON for the VM.
     *
     * @param dataJson JSON data document.
     */
    public void setDataJson(String dataJson) {
        nativeSetDataJson(vmPtr, dataJson);
    }

    /**
     * Set input JSON for the VM.
     *
     * @param inputJson JSON input document.
     */
    public void setInputJson(String inputJson) {
        nativeSetInputJson(vmPtr, inputJson);
    }

    /**
     * Set execution mode (0 = run-to-completion, 1 = suspendable).
     *
     * @param mode Execution mode.
     */
    public void setExecutionMode(byte mode) {
        nativeSetExecutionMode(vmPtr, mode);
    }

    /**
     * Execute the program.
     *
     * @return JSON result string.
     */
    public String execute() {
        return nativeExecute(vmPtr);
    }

    /**
     * Execute a named entry point.
     *
     * @param entryPoint Entry point rule path.
     * @return JSON result string.
     */
    public String executeEntryPoint(String entryPoint) {
        return nativeExecuteEntryPoint(vmPtr, entryPoint);
    }

    /**
     * Resume execution with an optional JSON value.
     *
     * @param resumeJson JSON value to resume with, or null for no value.
     * @return JSON result string.
     */
    public String resume(String resumeJson) {
        return nativeResume(vmPtr, resumeJson, resumeJson != null);
    }

    /**
     * Get the current execution state.
     *
     * @return Execution state string.
     */
    public String getExecutionState() {
        return nativeGetExecutionState(vmPtr);
    }

    @Override
    public void close() {
        nativeDrop(vmPtr);
    }
}

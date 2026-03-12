/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/

package com.microsoft.regorus;

/**
 * Policy source length limits enforced when loading policy files.
 *
 * All values must be positive (non-zero).
 */
public final class PolicyLengthConfig {
    /**
     * Maximum column width per line (default: 1024).
     */
    public final int maxCol;

    /**
     * Maximum policy file size in bytes (default: 1 MiB).
     */
    public final long maxFileBytes;

    /**
     * Maximum number of lines per policy file (default: 20000).
     */
    public final long maxLines;

    /**
     * Create a new policy length configuration.
     *
     * @param maxCol Maximum column width per line.
     * @param maxFileBytes Maximum policy file size in bytes.
     * @param maxLines Maximum number of lines per policy file.
     */
    public PolicyLengthConfig(int maxCol, long maxFileBytes, long maxLines) {
        if (maxCol <= 0) {
            throw new IllegalArgumentException("maxCol must be positive");
        }
        if (maxFileBytes <= 0) {
            throw new IllegalArgumentException("maxFileBytes must be positive");
        }
        if (maxLines <= 0) {
            throw new IllegalArgumentException("maxLines must be positive");
        }
        this.maxCol = maxCol;
        this.maxFileBytes = maxFileBytes;
        this.maxLines = maxLines;
    }
}

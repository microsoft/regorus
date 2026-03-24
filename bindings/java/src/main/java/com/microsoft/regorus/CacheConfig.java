/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/

package com.microsoft.regorus;

/**
 * Global configuration for compiled pattern caches used by regex and glob builtins.
 *
 * <p>Capacity of 0 disables the corresponding cache.
 */
public final class CacheConfig {

    static {
        System.loadLibrary("regorus_java");
    }

    private static native void nativeSetCacheConfig(long regex, long glob);
    private static native void nativeClearCache();

    /**
     * Maximum cached compiled regex patterns (default 256).
     */
    public final long regex;

    /**
     * Maximum cached compiled glob matchers (default 128).
     */
    public final long glob;

    /**
     * Create a new cache configuration.
     *
     * @param regex Maximum cached compiled regex patterns (0 = disabled).
     * @param glob Maximum cached compiled glob matchers (0 = disabled).
     */
    public CacheConfig(long regex, long glob) {
        if (regex < 0) {
            throw new IllegalArgumentException("regex must be non-negative");
        }
        if (glob < 0) {
            throw new IllegalArgumentException("glob must be non-negative");
        }
        this.regex = regex;
        this.glob = glob;
    }

    /**
     * Apply this cache configuration globally.
     */
    public static void configure(CacheConfig config) {
        nativeSetCacheConfig(config.regex, config.glob);
    }

    /**
     * Clear all entries from every pattern cache.
     */
    public static void clear() {
        nativeClearCache();
    }
}

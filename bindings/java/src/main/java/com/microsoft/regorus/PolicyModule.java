/**
 * Copyright (c) Microsoft Corporation.
 * Licensed under the MIT License.
 **/

package com.microsoft.regorus;

/**
 * Represents a Rego module used for RVM program compilation.
 */
public final class PolicyModule {
    /**
     * Module identifier or filename.
     */
    public final String id;

    /**
     * Rego policy content.
     */
    public final String content;

    /**
     * Create a new policy module.
     *
     * @param id Module identifier or filename.
     * @param content Rego policy content.
     */
    public PolicyModule(String id, String content) {
        this.id = id;
        this.content = content;
    }
}

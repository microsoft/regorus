// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Text.Json;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Provides static methods for managing the global target registry.
    /// Targets define resource types and their associated schemas for Azure Policy evaluation.
    /// </summary>
    public static unsafe class TargetRegistry
    {
        /// <summary>
        /// Register a target from JSON definition.
        /// The target JSON should follow the target schema format.
        /// Once registered, the target can be referenced in Rego policies using `__target__` rules.
        /// </summary>
        /// <param name="targetJson">JSON encoded target definition</param>
        /// <exception cref="Exception">Thrown when target registration fails</exception>
        public static void RegisterFromJson(string targetJson)
        {
            Utf8Marshaller.WithUtf8(targetJson, targetPtr =>
            {
                unsafe
                {
                    ResultHelpers.GetStringResult(Internal.API.regorus_register_target_from_json((byte*)targetPtr));
                }
            });
        }

        /// <summary>
        /// Check if a target is registered.
        /// </summary>
        /// <param name="name">Name of the target to check</param>
        /// <returns>True if the target is registered, false otherwise</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool Contains(string name)
        {
            return Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                unsafe
                {
                    var result = Internal.API.regorus_target_registry_contains((byte*)namePtr);
                    return ResultHelpers.GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Get a list of all registered target names.
        /// </summary>
        /// <returns>JSON array of target names</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static string ListNames()
        {
            return ResultHelpers.GetStringResult(Internal.API.regorus_target_registry_list_names()) ?? "[]";
        }

        /// <summary>
        /// Get a list of all registered target names as managed strings.
        /// </summary>
        public static IReadOnlyList<string> GetNames()
        {
            var json = ListNames();
            return JsonSerializer.Deserialize<string[]>(json) ?? Array.Empty<string>();
        }

        /// <summary>
        /// Remove a target from the registry by name.
        /// </summary>
        /// <param name="name">The target name to remove</param>
        /// <returns>True if the target was removed, false if it wasn't found</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool Remove(string name)
        {
            return Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                unsafe
                {
                    var result = Internal.API.regorus_target_registry_remove((byte*)namePtr);
                    return ResultHelpers.GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Clear all targets from the registry.
        /// </summary>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static void Clear()
        {
            ResultHelpers.GetStringResult(Internal.API.regorus_target_registry_clear());
        }

        /// <summary>
        /// Get the number of registered targets.
        /// </summary>
        /// <returns>The number of registered targets</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static long Count
        {
            get
            {
                var result = Internal.API.regorus_target_registry_len();
                return ResultHelpers.GetIntResult(result);
            }
        }
        /// <summary>
        /// Check if the target registry is empty.
        /// </summary>
        /// <returns>True if the registry is empty, false otherwise</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool IsEmpty
        {
            get
            {
                var result = Internal.API.regorus_target_registry_is_empty();
                return ResultHelpers.GetBoolResult(result);
            }
        }
    }
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
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
                    CheckAndDropResult(Internal.API.regorus_register_target_from_json((byte*)targetPtr));
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
                    return GetBoolResult(result);
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
            return CheckAndDropResult(Internal.API.regorus_target_registry_list_names()) ?? "[]";
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
                    return GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Clear all targets from the registry.
        /// </summary>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static void Clear()
        {
            CheckAndDropResult(Internal.API.regorus_target_registry_clear());
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
                return GetIntResult(result);
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
                return GetBoolResult(result);
            }
        }

        private static string? CheckAndDropResult(Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Internal.RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type switch
                {
                    Internal.RegorusDataType.String => Utf8Marshaller.FromUtf8(result.output),
                    Internal.RegorusDataType.Boolean => result.bool_value.ToString().ToLowerInvariant(),
                    Internal.RegorusDataType.Integer => result.int_value.ToString(),
                    Internal.RegorusDataType.None => null,
                    _ => Utf8Marshaller.FromUtf8(result.output)
                };
            }
            finally
            {
                Internal.API.regorus_result_drop(result);
            }
        }

        private static bool GetBoolResult(Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Internal.RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type == Internal.RegorusDataType.Boolean ? result.bool_value : false;
            }
            finally
            {
                Internal.API.regorus_result_drop(result);
            }
        }

        private static long GetIntResult(Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Internal.RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type == Internal.RegorusDataType.Integer ? result.int_value : 0;
            }
            finally
            {
                Internal.API.regorus_result_drop(result);
            }
        }
    }
}

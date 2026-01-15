// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Provides static methods for managing the global resource schema registry.
    /// Resource schemas define the structure and validation rules for Azure Policy resources.
    /// </summary>
    public static unsafe class SchemaRegistry
    {
        /// <summary>
        /// Register a resource schema from JSON with a given name.
        /// </summary>
        /// <param name="name">Name to register the schema under</param>
        /// <param name="schemaJson">JSON string representing the schema</param>
        /// <exception cref="Exception">Thrown when schema registration fails</exception>
        public static void RegisterResource(string name, string schemaJson)
        {
            Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                Utf8Marshaller.WithUtf8(schemaJson, schemaPtr =>
                {
                    unsafe
                    {
                        CheckAndDropResult(Internal.API.regorus_resource_schema_register((byte*)namePtr, (byte*)schemaPtr));
                    }
                });
            });
        }

        /// <summary>
        /// Check if a resource schema with the given name exists.
        /// </summary>
        /// <param name="name">Name of the schema to check</param>
        /// <returns>True if the schema exists, false otherwise</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool ContainsResource(string name)
        {
            return Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                unsafe
                {
                    var result = Internal.API.regorus_resource_schema_contains((byte*)namePtr);
                    return GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Get the number of registered resource schemas.
        /// </summary>
        /// <returns>The number of registered resource schemas</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static long ResourceCount
        {
            get
            {
                var result = Internal.API.regorus_resource_schema_len();
                return GetIntResult(result);
            }
        }

        /// <summary>
        /// Check if the resource schema registry is empty.
        /// </summary>
        /// <returns>True if the registry is empty, false otherwise</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool IsResourceRegistryEmpty
        {
            get
            {
                var result = Internal.API.regorus_resource_schema_is_empty();
                return GetBoolResult(result);
            }
        }

        /// <summary>
        /// List all registered resource schema names.
        /// </summary>
        /// <returns>JSON array of schema names</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static string ListResourceNames()
        {
            return CheckAndDropResult(Internal.API.regorus_resource_schema_list_names()) ?? "[]";
        }

        /// <summary>
        /// Remove a resource schema by name.
        /// </summary>
        /// <param name="name">Name of the schema to remove</param>
        /// <returns>True if the schema was removed, false if it wasn't found</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool RemoveResource(string name)
        {
            return Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                unsafe
                {
                    var result = Internal.API.regorus_resource_schema_remove((byte*)namePtr);
                    return GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Clear all resource schemas from the registry.
        /// </summary>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static void ClearResources()
        {
            CheckAndDropResult(Internal.API.regorus_resource_schema_clear());
        }

        /// <summary>
        /// Register an effect schema from JSON with a given name.
        /// </summary>
        /// <param name="name">Name to register the schema under</param>
        /// <param name="schemaJson">JSON string representing the schema</param>
        /// <exception cref="Exception">Thrown when schema registration fails</exception>
        public static void RegisterEffect(string name, string schemaJson)
        {
            Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                Utf8Marshaller.WithUtf8(schemaJson, schemaPtr =>
                {
                    unsafe
                    {
                        CheckAndDropResult(Internal.API.regorus_effect_schema_register((byte*)namePtr, (byte*)schemaPtr));
                    }
                });
            });
        }

        /// <summary>
        /// Check if an effect schema with the given name exists.
        /// </summary>
        /// <param name="name">Name of the schema to check</param>
        /// <returns>True if the schema exists, false otherwise</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool ContainsEffect(string name)
        {
            return Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                unsafe
                {
                    var result = Internal.API.regorus_effect_schema_contains((byte*)namePtr);
                    return GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Get the number of registered effect schemas.
        /// </summary>
        /// <returns>The number of registered effect schemas</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static long EffectCount
        {
            get
            {
                var result = Internal.API.regorus_effect_schema_len();
                return GetIntResult(result);
            }
        }

        /// <summary>
        /// Check if the effect schema registry is empty.
        /// </summary>
        /// <returns>True if the registry is empty, false otherwise</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool IsEffectRegistryEmpty
        {
            get
            {
                var result = Internal.API.regorus_effect_schema_is_empty();
                return GetBoolResult(result);
            }
        }

        /// <summary>
        /// List all registered effect schema names.
        /// </summary>
        /// <returns>JSON array of schema names</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static string ListEffectNames()
        {
            return CheckAndDropResult(Internal.API.regorus_effect_schema_list_names()) ?? "[]";
        }

        /// <summary>
        /// Remove an effect schema by name.
        /// </summary>
        /// <param name="name">Name of the schema to remove</param>
        /// <returns>True if the schema was removed, false if it wasn't found</returns>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static bool RemoveEffect(string name)
        {
            return Utf8Marshaller.WithUtf8(name, namePtr =>
            {
                unsafe
                {
                    var result = Internal.API.regorus_effect_schema_remove((byte*)namePtr);
                    return GetBoolResult(result);
                }
            });
        }

        /// <summary>
        /// Clear all effect schemas from the registry.
        /// </summary>
        /// <exception cref="Exception">Thrown when the operation fails</exception>
        public static void ClearEffects()
        {
            CheckAndDropResult(Internal.API.regorus_effect_schema_clear());
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

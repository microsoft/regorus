// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Provides helpers for evaluating Azure RBAC condition expressions.
    /// </summary>
    public static unsafe class RbacEngine
    {
        /// <summary>
        /// Evaluate an Azure RBAC condition expression against a JSON evaluation context.
        /// </summary>
        /// <param name="condition">Azure RBAC condition expression.</param>
        /// <param name="contextJson">JSON encoded EvaluationContext.</param>
        /// <returns>True if the condition evaluates to true; otherwise false.</returns>
        /// <exception cref="Exception">Thrown when evaluation fails.</exception>
        public static bool EvaluateCondition(string condition, string contextJson)
        {
            if (condition is null)
            {
                throw new ArgumentNullException(nameof(condition));
            }

            if (contextJson is null)
            {
                throw new ArgumentNullException(nameof(contextJson));
            }

            return Utf8Marshaller.WithUtf8(condition, conditionPtr =>
                Utf8Marshaller.WithUtf8(contextJson, contextPtr =>
                {
                    unsafe
                    {
                        var result = Internal.API.regorus_rbac_engine_eval_condition((byte*)conditionPtr, (byte*)contextPtr);
                        return ResultHelpers.GetBoolResult(result);
                    }
                }));
        }
    }
}

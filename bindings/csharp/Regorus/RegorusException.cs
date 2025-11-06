// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

#nullable enable

namespace Regorus
{
	/// <summary>
	/// Represents errors originating from the native Regorus runtime.
	/// </summary>
	public sealed class RegorusException : Exception
	{
		public RegorusException()
		{
		}

		public RegorusException(string message)
			: base(message)
		{
		}

		public RegorusException(string message, Exception innerException)
			: base(message, innerException)
		{
		}
	}
}

// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Threading;
using Regorus.Internal;

#nullable enable

namespace Regorus
{
	/// <summary>
	/// Managed wrapper for the native regorus::Value type.
	/// Instances own the underlying native value and must be disposed when no longer needed.
	/// </summary>
	public sealed unsafe class Value : IDisposable
	{
		private RegorusValueHandle? _handle;
		private int _isDisposed;

		private Value(RegorusValueHandle handle)
		{
			_handle = handle ?? throw new ArgumentNullException(nameof(handle));
		}

		internal static Value FromHandle(IntPtr handle) => new Value(RegorusValueHandle.FromPointer(handle));

		private RegorusValueHandle GetHandleForUse()
		{
			var handle = _handle;
			if (handle is null || handle.IsClosed || handle.IsInvalid)
			{
				throw new ObjectDisposedException(nameof(Value));
			}

			return handle;
		}

		private void UseHandle(Action<IntPtr> action)
		{
			UseHandle<object?>(handlePtr =>
			{
				action(handlePtr);
				return null;
			});
		}

		private T UseHandle<T>(Func<IntPtr, T> func)
		{
			var handle = GetHandleForUse();
			bool addedRef = false;
			try
			{
				handle.DangerousAddRef(ref addedRef);
				var pointer = handle.DangerousGetHandle();
				if (pointer == IntPtr.Zero)
				{
					throw new ObjectDisposedException(nameof(Value));
				}

				return func(pointer);
			}
			finally
			{
				if (addedRef)
				{
					handle.DangerousRelease();
				}
			}
		}

		internal void WithHandle(Action<IntPtr> action) => UseHandle(action);

		internal T WithHandle<T>(Func<IntPtr, T> func) => UseHandle(func);

		public static Value Null()
		{
			var result = Internal.API.regorus_value_create_null();
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value Undefined()
		{
			var result = Internal.API.regorus_value_create_undefined();
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value Bool(bool value)
		{
			var result = Internal.API.regorus_value_create_bool(value);
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value Int(long value)
		{
			var result = Internal.API.regorus_value_create_int(value);
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value Float(double value)
		{
			var result = Internal.API.regorus_value_create_float(value);
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value String(string value)
		{
			if (value is null)
			{
				throw new ArgumentNullException(nameof(value));
			}

			var bytes = NativeUtf8.GetNullTerminatedBytes(value);
			fixed (byte* ptr = bytes)
			{
				var result = Internal.API.regorus_value_create_string(ptr);
				var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
				return new Value(RegorusValueHandle.FromPointer(pointer));
			}
		}

		public static Value Array()
		{
			var result = Internal.API.regorus_value_create_array();
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value Object()
		{
			var result = Internal.API.regorus_value_create_object();
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value Set()
		{
			var result = Internal.API.regorus_value_create_set();
			var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
			return new Value(RegorusValueHandle.FromPointer(pointer));
		}

		public static Value FromJson(string json)
		{
			if (json is null)
			{
				throw new ArgumentNullException(nameof(json));
			}

			var bytes = NativeUtf8.GetNullTerminatedBytes(json);
			fixed (byte* ptr = bytes)
			{
				var result = Internal.API.regorus_value_from_json(ptr);
				var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
				return new Value(RegorusValueHandle.FromPointer(pointer));
			}
		}

		public Value Clone()
		{
			return UseHandle(handlePtr =>
			{
				var result = Internal.API.regorus_value_clone((void*)handlePtr);
				var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
				return new Value(RegorusValueHandle.FromPointer(pointer));
			});
		}

		public string ToJson()
		{
			return UseHandle(handlePtr =>
			{
				var result = Internal.API.regorus_value_to_json((void*)handlePtr);
				return NativeResult.GetStringAndDrop(result) ?? string.Empty;
			});
		}

		public bool IsNull
		{
			get
			{
				return UseHandle(handlePtr =>
				{
					return NativeResult.GetBoolAndDrop(Internal.API.regorus_value_is_null((void*)handlePtr));
				});
			}
		}

		public bool IsObject
		{
			get
			{
				return UseHandle(handlePtr =>
				{
					return NativeResult.GetBoolAndDrop(Internal.API.regorus_value_is_object((void*)handlePtr));
				});
			}
		}

		public bool IsString
		{
			get
			{
				return UseHandle(handlePtr =>
				{
					return NativeResult.GetBoolAndDrop(Internal.API.regorus_value_is_string((void*)handlePtr));
				});
			}
		}

		public bool AsBool()
		{
			return UseHandle(handlePtr =>
			{
				return NativeResult.GetBoolAndDrop(Internal.API.regorus_value_as_bool((void*)handlePtr));
			});
		}

		public long AsInt64()
		{
			return UseHandle(handlePtr =>
			{
				return NativeResult.GetInt64AndDrop(Internal.API.regorus_value_as_i64((void*)handlePtr));
			});
		}

		public string AsString()
		{
			return UseHandle(handlePtr =>
			{
				return NativeResult.GetStringAndDrop(Internal.API.regorus_value_as_string((void*)handlePtr)) ?? string.Empty;
			});
		}

		public long ArrayLength()
		{
			return UseHandle(handlePtr =>
			{
				return NativeResult.GetInt64AndDrop(Internal.API.regorus_value_array_len((void*)handlePtr));
			});
		}

		public Value ArrayGet(long index)
		{
			return UseHandle(handlePtr =>
			{
				var result = Internal.API.regorus_value_array_get((void*)handlePtr, index);
				var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
				return new Value(RegorusValueHandle.FromPointer(pointer));
			});
		}

		public void ArrayAppend(Value value)
		{
			if (value is null)
			{
				throw new ArgumentNullException(nameof(value));
			}

			value.WithHandle(valuePtr =>
			{
				UseHandle(handlePtr =>
				{
					NativeResult.EnsureSuccess(Internal.API.regorus_value_array_push((void*)handlePtr, (void*)valuePtr));
				});
			});
		}

		public void ObjectInsert(string key, Value value)
		{
			if (key is null)
			{
				throw new ArgumentNullException(nameof(key));
			}
			if (value is null)
			{
				throw new ArgumentNullException(nameof(value));
			}

			var keyBytes = NativeUtf8.GetNullTerminatedBytes(key);
			value.WithHandle(valuePtr =>
			{
				UseHandle(handlePtr =>
				{
					fixed (byte* keyPtr = keyBytes)
					{
						NativeResult.EnsureSuccess(Internal.API.regorus_value_object_insert((void*)handlePtr, keyPtr, (void*)valuePtr));
					}
				});
			});
		}

		public void SetInsert(Value value)
		{
			if (value is null)
			{
				throw new ArgumentNullException(nameof(value));
			}

			value.WithHandle(valuePtr =>
			{
				UseHandle(handlePtr =>
				{
					NativeResult.EnsureSuccess(Internal.API.regorus_value_set_insert((void*)handlePtr, (void*)valuePtr));
				});
			});
		}

		public Value ObjectGet(string key)
		{
			if (key is null)
			{
				throw new ArgumentNullException(nameof(key));
			}

			var keyBytes = NativeUtf8.GetNullTerminatedBytes(key);
			return UseHandle(handlePtr =>
			{
				fixed (byte* keyPtr = keyBytes)
				{
					var result = Internal.API.regorus_value_object_get((void*)handlePtr, keyPtr);
					var pointer = NativeResult.GetPointerAndDrop(result, RegorusPointerType.PointerValue);
					return new Value(RegorusValueHandle.FromPointer(pointer));
				}
			});
		}

		public void Dispose()
		{
			Dispose(disposing: true);
			GC.SuppressFinalize(this);
		}

		private void Dispose(bool disposing)
		{
			if (Interlocked.CompareExchange(ref _isDisposed, 1, 0) == 0)
			{
				_handle?.Dispose();
				_handle = null;
			}
		}

		~Value()
		{
			Dispose(disposing: false);
		}
	}
}

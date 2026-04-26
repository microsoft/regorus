<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: FFI Boundary

Deep knowledge about regorus's foreign function interface and multi-language
binding architecture. Read this before modifying `bindings/` or the core
library's public API.

## Architecture

```
                    regorus (Rust core library)
                              │
                    bindings/ffi/ (base FFI crate)
                              │
        ┌────────┬────────┬───┴───┬────────┬────────┐
        │        │        │       │        │        │
     C/C++    C#/NuGet  Java   Python   Ruby    WASM
   (cbindgen) (csbindgen)(jni-rs)(PyO3) (magnus)(wasm-pack)
     CMake    MSBuild    Maven  maturin bundler  npm
```

The FFI crate (`bindings/ffi/`) is the **security boundary**. Rust's compiler
guarantees do not extend across it.

## Opaque Handle Pattern

All Rust objects are exposed to C as opaque pointers:

```rust
// Rust side
pub struct RegorusEngine {
    engine: Handle<::regorus::Engine>,  // Rc<RefCell<>> or Arc<RwLock<>>
}

#[no_mangle]
pub extern "C" fn regorus_engine_new() -> *mut RegorusEngine {
    Box::into_raw(Box::new(RegorusEngine::new(engine)))
}

#[no_mangle]
pub extern "C" fn regorus_engine_drop(engine: *mut RegorusEngine) {
    if let Ok(e) = to_ref(engine) {
        unsafe { let _ = Box::from_raw(ptr::from_mut(e)); }
    }
}
```

**Invariant:** Every `Box::into_raw()` must have a corresponding `Box::from_raw()`
in a drop function. Missing drops = memory leaks.

## Null Pointer Validation

Every pointer parameter is validated at the FFI boundary:

```rust
pub(crate) fn to_ref<'a, T>(t: *mut T) -> Result<&'a mut T> {
    unsafe { t.as_mut().ok_or_else(|| anyhow!("null pointer")) }
}

pub(crate) fn from_c_str(s: *const c_char) -> Result<String> {
    if s.is_null() { bail!("null pointer"); }
    unsafe { CStr::from_ptr(s).to_str().map_err(|e| anyhow!("invalid utf8: {e}")).map(|s| s.to_string()) }
}
```

**Invariant:** No FFI function may dereference a pointer without checking for null.

## Contention Detection

The FFI handle uses configurable locking (`bindings/ffi/src/lock.rs`):

| Feature flags | Handle type | Cost | Safety |
|---------------|-------------|------|--------|
| `std` + `contention_checks` | `Arc<RwLock<T>>` | Higher | Detects concurrent access |
| `std` only | `Rc<RefCell<T>>` | Lower | Single-thread assumption |
| `no_std` | `Rc<RefCell<T>>` | Lowest | Single-thread only |

The contention error message explicitly tells users to clone:
> "regorus engine handle is already in use; clone the engine before sharing across threads"

## Panic Containment and Poisoning

**Every FFI entry point wraps in `with_unwind_guard()`** which:

1. Checks if engine is already poisoned → return `RegorusStatus::Poisoned`
2. Installs a temporary panic hook to capture backtrace
3. Calls `panic::catch_unwind()` around the function body
4. If panic caught → permanently poisons engine via `AtomicBool`
5. Returns `RegorusStatus::Panic` with the captured backtrace

**Once poisoned, the engine is PERMANENTLY dead.** All subsequent calls return
`RegorusStatus::Poisoned`. There is no recovery. This is intentional — after a
panic, internal state may be corrupt.

## Result Encoding

All FFI functions return `RegorusResult`:

```c
typedef struct {
    RegorusStatus status;        // Ok, Error, Panic, Poisoned, ...
    RegorusDataType data_type;   // None, String, Boolean, Integer, Pointer
    char* output;                // Owned by Rust — caller MUST call regorus_result_drop()
    bool bool_value;
    long long int_value;
    void* pointer_value;
    char* error_message;         // Owned by Rust — freed by regorus_result_drop()
} RegorusResult;
```

**CRITICAL:** String ownership transfers to C via `CString::into_raw()`. If the
caller doesn't call `regorus_result_drop()`, memory leaks.

## Binary Buffer Pattern

For binary data (serialized programs), `RegorusBuffer` transfers Vec ownership:

```rust
pub struct RegorusBuffer {
    pub data: *mut u8,
    pub len: usize,
    pub capacity: usize,
}
```

Created via `RegorusBuffer::from_vec()` (which `mem::forget()`s the Vec),
freed via `regorus_buffer_drop()` (which reconstructs and drops the Vec).

## Language-Specific Binding Patterns

### C — Raw FFI
No wrapper. Manual `regorus_result_drop()` and `regorus_engine_drop()` calls.
Error handling via status code checks.

### C++ — RAII
`regorus.hpp` wraps with:
- `Result` class: move-only, destructor calls `regorus_result_drop()`
- `Engine` class: destructor calls `regorus_engine_drop()`
- Copy prevention via deleted copy constructor/assignment

### C# — SafeHandle with HandleGate
Most sophisticated wrapper:
- `SafeHandle` integrates with .NET finalizer
- `HandleGate` tracks in-flight operations
- `DangerousAddRef()`/`DangerousRelease()` pins handle during native calls
- Dispose waits up to 50ms for in-flight calls to drain
- Thread-safe concurrent access tracking

### Java — AutoCloseable + JNI
- Stores opaque `long` pointer (64-bit address)
- `AutoCloseable` for `try-with-resources` blocks
- `close()` calls `nativeDestroyEngine()`

### Python — PyO3 Direct Embedding
- `#[pyclass(unsendable)]` embeds Rust Engine in Python object
- Python GC owns the object, Rust `Drop` is automatic
- No separate FFI layer — PyO3 marshals directly

### Go — cgo
- Stores `*C.RegorusEngine` opaque pointer
- `defer` for cleanup ordering
- Manual CString conversion with `C.CString()`/`C.free()`

### Ruby — Magnus Native Extension
- Rust struct wrapped as Ruby class
- Ruby GC manages lifecycle via finalizer

### WASM — wasm-pack
- Compiled to WebAssembly, exposed via JavaScript bindings
- No pointer management — WASM linear memory handles it

## Custom Allocator Support

The FFI crate supports host-provided allocators:

```rust
#[cfg(feature = "custom_allocator")]
extern "C" {
    fn regorus_aligned_alloc(alignment: usize, size: usize) -> *mut u8;
    fn regorus_free(ptr: *mut u8);
}
```

This allows C#/JVM/Go hosts to provide their own allocator, which is important
for memory tracking and limit enforcement in managed runtimes.

## Impact of Core API Changes

When changing the core library's public API:

1. **Every binding must be updated** — 9 language targets
2. **FFI function signature changes** require updating:
   - `bindings/ffi/src/engine.rs` (or relevant FFI module)
   - C/C++ headers (auto-generated by cbindgen, but verify)
   - C# P/Invoke declarations
   - Java JNI native method declarations
   - Go cgo function declarations
   - WASM bindings
3. **Run `cargo xtask test-all-bindings`** to verify all targets
4. **New public methods** need FFI wrappers, documentation in all languages
5. **Behavioral changes** may need binding-level test updates

## Security Considerations

- The FFI boundary is where type safety ends — validate everything
- Pointer arithmetic for array parameters must check bounds carefully
- String encoding (UTF-8 vs platform) must be validated at the boundary
- Panic containment prevents Rust panics from unwinding into C/C++
- Poisoning prevents use-after-panic of potentially corrupt state
- Memory ownership must be crystal clear — who allocates, who frees

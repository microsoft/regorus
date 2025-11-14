# RVM Instruction Set Reference

This reference captures every opcode emitted by the compiler and executed by
`RegoVM`. Each instruction is defined in `src/rvm/instructions/mod.rs` and
implemented by the dispatcher tree in `src/rvm/vm/dispatch.rs` plus specialised
submodules (`arithmetic.rs`, `loops.rs`, `functions.rs`, `rules.rs`,
`comprehension.rs`, `virtual_data.rs`).

Use this guide to understand operand semantics, parameter tables, and runtime
side effects.

---

## Reading the tables

- **Operands**: registers (`rX`), literals (`litY`), parameter indices (`pZ`) and
  immediate values.
- **Parameters**: links into `InstructionData` (`src/rvm/instructions/params.rs`).
  The compiler stores complex metadata here; instructions reference it by index.
- **Outcome**: mentioned in prose where relevant (`Continue`, `Return`, `Break`,
  `Suspend`).

---

## Load and Move instructions

| Mnemonic   | Operands                    | Behaviour                                            |
| :--------- | :-------------------------- | :--------------------------------------------------- |
| `Load`     | `dest=rD, literal_idx=litN` | Copies literal `N` into register `D`.                |
| `LoadTrue` | `dest=rD`                   | Stores boolean `true`.                               |
| `LoadFalse`| `dest=rD`                   | Stores boolean `false`.                              |
| `LoadNull` | `dest=rD`                   | Stores `Value::Null`.                                |
| `LoadBool` | `dest=rD, value`            | Stores inline boolean literal.                       |
| `LoadData` | `dest=rD`                   | Stores the VM's `data` value.                        |
| `LoadInput`| `dest=rD`                   | Stores the VM's `input` value.                       |
| `Move`     | `dest=rD, src=rS`           | Copies register `S` into register `D`.               |

Out-of-range literal indices raise `VmError::LiteralIndexOutOfBounds`. Registers
must have been allocated by the current frame.

---

## Arithmetic and comparison instructions

| Mnemonic | Operands                | Behaviour                                                     |
| :------- | :---------------------- | :------------------------------------------------------------ |
| `Add`    | `dest, left, right`     | Numeric addition; undefined operands trigger loop condition checks. |
| `Sub`    | `dest, left, right`     | Numeric subtraction.                                          |
| `Mul`    | `dest, left, right`     | Numeric multiplication.                                       |
| `Div`    | `dest, left, right`     | Numeric division with runtime checks (division by zero errors). |
| `Mod`    | `dest, left, right`     | Modulo.                                                       |
| `Eq`     | `dest, left, right`     | Equality comparison resulting in `Value::Bool`.               |
| `Ne`     | `dest, left, right`     | Inequality.                                                   |
| `Lt`/`Le`/`Gt`/`Ge` | `dest, left, right` | Ordering comparisons.                                         |
| `And`    | `dest, left, right`     | Logical conjunction (truthiness semantics).                   |
| `Or`     | `dest, left, right`     | Logical disjunction.                                          |
| `Not`    | `dest, operand`         | Logical negation.                                             |
| `AssertCondition` | `condition`    | Fails current loop/rule when the condition is falsey.         |
| `AssertNotUndefined` | `register`  | Fails when register holds `Value::Undefined`.                 |

`handle_condition` routes through `loops.rs` to propagate failures to loop and
comprehension contexts. Outside loops it aborts the current rule.

---

## Collection and indexing instructions

| Mnemonic                   | Operands / Params             | Behaviour                                                   |
| :------------------------- | :---------------------------- | :---------------------------------------------------------- |
| `ObjectSet`                | `obj, key, value`             | Mutates object in `obj` with key/value from registers.      |
| `ObjectCreate`             | `params_index=pN`             | Builds object from literal template and register entries.   |
| `ArrayNew`                 | `dest`                        | Creates empty array.                                        |
| `ArrayPush`                | `arr, value`                  | Appends to array.                                           |
| `ArrayCreate`              | `params_index=pN`             | Builds array from register list; undefined element ⇒ result undefined. |
| `SetNew`                   | `dest`                        | Creates empty set.                                          |
| `SetAdd`                   | `set, value`                  | Adds element to set.                                        |
| `SetCreate`                | `params_index=pN`             | Builds set from register list; undefined element ⇒ result undefined. |
| `Index`                    | `dest, container, key`        | Indexes container with runtime key.                         |
| `IndexLiteral`             | `dest, container, literal_idx`| Indexes container using literal stored in program.          |
| `ChainedIndex`             | `params_index=pN`             | Resolves multi-hop path from root register.                 |
| `Contains`                 | `dest, collection, value`     | Checks membership; returns `Value::Bool`.                   |
| `Count`                    | `dest, collection`            | Returns length or `Value::Undefined` for unsupported types. |
| `VirtualDataDocumentLookup`| `params_index=pN`             | Evaluates `data` path, invoking rules lazily.               |

Parameter structures:

- `ObjectCreateParams` reuses arrays of literal key/value pairs and register
  pairs. Literal keys must be sorted to match template order.
- `ArrayCreateParams` and `SetCreateParams` store register lists. The VM checks
  all referenced registers for `Value::Undefined` before constructing the
  collection.
- `VirtualDataDocumentLookupParams` and `ChainedIndexParams` encode `Vec<LiteralOrRegister>`
  path components. `LiteralOrRegister` is defined in `src/rvm/instructions/types.rs`.

---

## Loop instructions

Loops use dedicated parameter tables (`LoopStartParams`) and the `LoopMode`
enum.

| Mnemonic    | Operands / Params        | Behaviour                                                      |
| :---------- | :----------------------- | :------------------------------------------------------------- |
| `LoopStart` | `params_index=pN`        | Initialises loop context and decides first body iteration.     |
| `LoopNext`  | `body_start`, `loop_end` | Finalises iteration, updates accumulators, advances to next element. |

`LoopMode` values:

- `Any`: succeed on first passing iteration, short-circuit on success.
- `Every`: fail on first failing iteration.
- `ForEach`: evaluate all iterations, typically for comprehensions or complete
  rules.

`LoopStartParams` fields:

- `collection`: source register.
- `key_reg` / `value_reg`: iteration registers (for arrays, key is index).
- `result_reg`: accumulator storing loop outcome (`bool` for quantifiers).
- `body_start` / `loop_end`: PCs identifying loop boundaries.

The dispatcher converts `LoopStartParams` into a VM-specific `LoopParams` used by
both execution modes. In suspendable mode, loops own their own `ExecutionFrame`.

---

## Comprehension instructions

| Mnemonic             | Operands / Params       | Behaviour                                          |
| :------------------- | :---------------------- | :------------------------------------------------- |
| `ComprehensionBegin` | `params_index=pN`       | Allocates collection builder and iteration context. |
| `ComprehensionYield` | `value_reg`, `key_reg?` | Emits value (and optional key) into builder.        |
| `ComprehensionEnd`   | —                       | Finalises collection and stores result.             |

`ComprehensionBeginParams` captures:

- `mode: ComprehensionMode` (Set, Array, Object)
- `collection_reg`: source register for iteration
- `result_reg`: register that will hold the final collection
- `key_reg` / `value_reg`: iteration registers
- `body_start` / `comprehension_end`: branch targets

Comprehensions manage their own stack (`ComprehensionContext`) to maintain
ordering guarantees (arrays), uniqueness (sets) or key/value pairing (objects).

---

## Call and return instructions

| Mnemonic              | Operands / Params         | Behaviour                                       |
| :-------------------- | :------------------------ | :---------------------------------------------- |
| `BuiltinCall`         | `params_index=pN`         | Invokes builtin via resolved function pointer.  |
| `FunctionCall`        | `params_index=pN`         | Invokes function rule.                           |
| `CallRule`            | `dest, rule_index`        | Requests rule evaluation with caching.           |
| `RuleInit`            | `result_reg, rule_index`  | Prepares rule accumulator and cache state.       |
| `Return`              | `value_reg`               | Returns value from current function body.        |
| `RuleReturn`          | —                         | Finalises rule evaluation frame.                 |
| `DestructuringSuccess`| —                         | Signals successful destructuring, breaks rule block. |

Parameter tables:

- `BuiltinCallParams` / `FunctionCallParams` store destination register, index
  into builtin table / rule index, argument count and up to eight argument
  register numbers.
- The VM dynamically resizes registers when a callee requires a larger window
  using program metadata (`max_rule_window_size`).

---

## Host interaction

| Mnemonic   | Operands          | Behaviour                                |
| :--------- | :---------------- | :--------------------------------------- |
| `HostAwait`| `dest, arg, id`   | Yields control to host with payload value. |

- Run-to-completion: consumes a response from `host_await_responses` keyed by
  the identifier register. Missing responses raise `VmError::HostAwaitResponseMissing`.
- Suspendable: emits `InstructionOutcome::Suspend` with `SuspendReason::HostAwait`.
  The host must resume with a value that will be written into `dest`.

---

## Halt instruction

| Mnemonic | Behaviour                         | Notes |
| :------- | :-------------------------------- | :---- |
| `Halt`   | Terminates execution immediately. | Used during debugging or emitted for guard rails. |

When encountered during run-to-completion execution, `Halt` returns the current
value in register `0`.

---

## Parameter data overview

`InstructionData` (`src/rvm/instructions/params.rs`) collects all complex
parameter types. Each `add_*` method returns a `u16` index suitable for storing
inside instructions. The VM retrieves tables via `get_*` accessors.

| Struct                   | Field                                     | Purpose                                                                    |
| :----------------------- | :---------------------------------------- | :------------------------------------------------------------------------- |
| `LoopStartParams`        | `mode`                                    | Loop semantics (`Any`, `Every`, `ForEach`).                                |
|                          | `collection`                              | Register holding the iterable collection.                                 |
|                          | `key_reg` / `value_reg`                   | Registers populated with the current key/value each iteration.             |
|                          | `result_reg`                              | Accumulator for loop outcome (`bool` for quantifiers).                     |
|                          | `body_start` / `loop_end`                 | Instruction pointers delimiting the loop body and exit.                    |
| `BuiltinCallParams`      | `dest`                                    | Register that receives the builtin result.                                 |
|                          | `builtin_index`                           | Slot into `builtin_info_table` for dispatch.                               |
|                          | `num_args`                                | Count of argument registers actually populated.                            |
|                          | `args[8]`                                 | Up to eight registers supplying builtin arguments.                         |
| `FunctionCallParams`     | `dest`                                    | Register that receives the function rule result.                           |
|                          | `func_rule_index`                         | Rule index for the target function definition.                             |
|                          | `num_args`                                | Number of argument registers provided.                                     |
|                          | `args[8]`                                 | Argument register numbers (unused slots ignored).                          |
| `ObjectCreateParams`     | `dest`                                    | Destination register for the constructed object.                           |
|                          | `template_literal_idx`                    | Literal template containing all expected keys.                             |
|                          | `literal_key_fields: Vec<(u16, u8)>`      | Mapping of literal-key indices to value registers.                         |
|                          | `fields: Vec<(u8, u8)>`                   | Dynamic key/value register pairs for non-literal keys.                     |
| `ArrayCreateParams`      | `dest`                                    | Destination register for the array literal.                               |
|                          | `elements: Vec<u8>`                       | Registers providing array elements (order preserved).                      |
| `SetCreateParams`        | `dest`                                    | Destination register for the set literal.                                 |
|                          | `elements: Vec<u8>`                       | Registers providing set members (duplicates dropped at runtime).           |
| `VirtualDataDocumentLookupParams` | `dest`                           | Destination register for lookup result.                                   |
|                          | `path_components: Vec<LiteralOrRegister>` | Ordered path traversal steps; mix of literals and register-based keys.     |
| `ChainedIndexParams`     | `dest`                                    | Destination register for resolved value.                                   |
|                          | `root`                                    | Register containing the root object/collection.                            |
|                          | `path_components: Vec<LiteralOrRegister>` | Path components applied relative to the root register.                     |
| `ComprehensionBeginParams` | `mode`                                  | Comprehension output type (array, set, object).                            |
|                          | `collection_reg`                          | Source collection register for iteration.                                  |
|                          | `result_reg`                              | Register receiving the final collection.                                   |
|                          | `key_reg` / `value_reg`                   | Iteration registers (keys optional for arrays/sets).                       |
|                          | `body_start` / `comprehension_end`        | Instruction pointers framing comprehension body and exit.                  |

All parameter structs derive `Serialize`/`Deserialize` and can be stored inside
artifacts. Some contain `Vec` fields; the compiler is responsible for ensuring
indices remain valid and stable across serialization boundaries.

---


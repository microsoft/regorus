/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.RVM.State
import Regorus.Value.Canonical
import Regorus.Value.Truth

/-!
# Core RVM small-step semantics

`step` is the total executable transition function.  A running state either
executes its current instruction, enters a terminal state, or records an
explicit error; terminal states are fixed points.  `Step` is the corresponding
proof-facing relation.

Arithmetic is strict in `Undefined`.  This phase uses exact rational
arithmetic, reports division by zero explicitly, and requires integral modulo
operands.  The full Rust VM's configurable non-strict arithmetic-error mode is
deferred.
-/

namespace Regorus.RVM

open Regorus

private def advance (state : VMState) : VMState :=
  { state with pc := state.pc + 1 }

private def writeAndAdvance (state : VMState) (dest : Reg) (value : Value) :
    Except VMError VMState :=
  match writeRegister state dest value with
  | .ok state' => .ok (advance state')
  | .error error => .error error

private def readRegisters (state : VMState) : List Reg → Except VMError (List Value)
  | [] => .ok []
  | register :: registers => do
      let value ← readRegister state register
      let values ← readRegisters state registers
      pure (value :: values)

private def strictLift₂
    (operation : Value → Value → Except VMError Value)
    (left right : Value) : Except VMError Value :=
  match left, right with
  | .Undefined, _ | _, .Undefined =>
      .ok (Regorus.lift₂ (fun _ _ => .Undefined) left right)
  | _, _ => operation left right

private def evalAdd : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Number left, .Number right => .ok (.Number (left + right))
    | _, _ => .error (.TypeMismatch "Add expects two numbers")

private def evalSub : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Number left, .Number right => .ok (.Number (left - right))
    | .Set left, .Set right =>
        .ok (Value.mkSet (left.filter fun value => value ∉ right))
    | _, _ => .error (.TypeMismatch "Sub expects two numbers or two sets")

private def evalMul : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Number left, .Number right => .ok (.Number (left * right))
    | _, _ => .error (.TypeMismatch "Mul expects two numbers")

private def evalDiv : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Number left, .Number right =>
        match RegoNumber.div? left right with
        | some quotient => .ok (.Number quotient)
        | none => .error .DivisionByZero
    | _, _ => .error (.TypeMismatch "Div expects two numbers")

private def evalMod : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Number left, .Number right =>
        match left.toInt?, right.toInt? with
        | some _, some 0 => .error .DivisionByZero
        | some leftInt, some rightInt =>
            .ok (.Number (RegoNumber.ofInt (Int.tmod leftInt rightInt)))
        | _, _ => .error .NonIntegralModulo
    | _, _ => .error (.TypeMismatch "Mod expects two numbers")

private def evalEq : Value → Value → Except VMError Value :=
  strictLift₂ fun left right => .ok (.Bool (decide (left = right)))

private def evalNe : Value → Value → Except VMError Value :=
  strictLift₂ fun left right => .ok (.Bool (decide (left ≠ right)))

/-- Ordered comparisons in the modeled strict mode reject operands of
different value kinds instead of falling back to heterogeneous ordering. -/
private def requireSameKind
    (left right : Value) (result : Bool) : Except VMError Value :=
  if left.kindRank = right.kindRank then
    .ok (.Bool result)
  else
    .error (.TypeMismatch "cannot compare values of different types")

private def evalLt : Value → Value → Except VMError Value :=
  strictLift₂ fun left right =>
    requireSameKind left right (decide (Value.compareValue left right = .lt))

private def evalLe : Value → Value → Except VMError Value :=
  strictLift₂ fun left right =>
    requireSameKind left right (decide (Value.compareValue left right ≠ .gt))

private def evalGt : Value → Value → Except VMError Value :=
  strictLift₂ fun left right =>
    requireSameKind left right (decide (Value.compareValue left right = .gt))

private def evalGe : Value → Value → Except VMError Value :=
  strictLift₂ fun left right =>
    requireSameKind left right (decide (Value.compareValue left right ≠ .lt))

/-- Strict-mode `And`/`Or` accept Boolean operands only; the Rust VM's
`to_bool` helper additionally coerces `Null` in non-strict mode only, which
this phase does not model (see the module docstring). -/
private def evalAnd : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Bool left, .Bool right => .ok (.Bool (left && right))
    | _, _ => .error (.TypeMismatch "And expects two booleans")

private def evalOr : Value → Value → Except VMError Value :=
  strictLift₂ fun
    | .Bool left, .Bool right => .ok (.Bool (left || right))
    | _, _ => .error (.TypeMismatch "Or expects two booleans")

private def executeBinary
    (operation : Value → Value → Except VMError Value)
    (state : VMState) (dest left right : Reg) : Except VMError VMState := do
  let leftValue ← readRegister state left
  let rightValue ← readRegister state right
  let result ← operation leftValue rightValue
  writeAndAdvance state dest result

private def indexValue (container key : Value) : Value :=
  match container with
  | .Object fields =>
      match fields.find? fun field => field.1 == key with
      | some field => field.2
      | none => .Undefined
  | .Set elements =>
      if key ∈ elements then key else .Undefined
  | .Array elements =>
      match key with
      | .Number number =>
          match number.toInt? with
          | some index =>
              if 0 ≤ index then
                (elements.get? index.toNat).getD .Undefined
              else
                .Undefined
          | none => .Undefined
      | _ => .Undefined
  | _ => .Undefined

private def containsValue (collection value : Value) : Value :=
  .Bool <| match collection with
    | .Set elements | .Array elements => value ∈ elements
    | .Object fields => fields.any fun field => field.2 == value
    | _ => false

private def countValue : Value → Value
  | .Array elements | .Set elements =>
      .Number (RegoNumber.ofInt (Int.ofNat elements.length))
  | .Object fields =>
      .Number (RegoNumber.ofInt (Int.ofNat fields.length))
  | _ => .Undefined

private def readLiteralFields
    (state : VMState) :
    List (LiteralIdx × Reg) → Except VMError (List (Value × Value))
  | [] => .ok []
  | (literalIdx, valueReg) :: fields => do
      let key ← readLiteral state literalIdx
      let value ← readRegister state valueReg
      let rest ← readLiteralFields state fields
      pure ((key, value) :: rest)

private def readDynamicFields
    (state : VMState) : List (Reg × Reg) → Except VMError (List (Value × Value))
  | [] => .ok []
  | (keyReg, valueReg) :: fields => do
      let key ← readRegister state keyReg
      let value ← readRegister state valueReg
      let rest ← readDynamicFields state fields
      pure ((key, value) :: rest)

private def hasUndefinedField (fields : List (Value × Value)) : Bool :=
  fields.any fun field =>
    field.1 == Value.Undefined || field.2 == Value.Undefined

private def executeObjectCreate
    (state : VMState) (paramsIndex : ParamIdx) : Except VMError VMState := do
  let params ←
    match state.program.instructionData.objectCreateParams.get? paramsIndex with
    | some params => .ok params
    | none => .error (.ParameterIndexOutOfBounds "objectCreateParams" paramsIndex)
  let literalFields ← readLiteralFields state params.literalKeyFields
  let fields ← readDynamicFields state params.fields
  if hasUndefinedField literalFields || hasUndefinedField fields then
    writeAndAdvance state params.dest .Undefined
  else
    let template ← readLiteral state params.templateLiteralIdx
    match template with
    | .Object entries =>
        writeAndAdvance state params.dest
          (Value.mkObject (entries ++ literalFields ++ fields))
    | _ => .error (.TypeMismatch "ObjectCreate template must be an object")

private def executeArrayCreate
    (state : VMState) (paramsIndex : ParamIdx) : Except VMError VMState := do
  let params ←
    match state.program.instructionData.arrayCreateParams.get? paramsIndex with
    | some params => .ok params
    | none => .error (.ParameterIndexOutOfBounds "arrayCreateParams" paramsIndex)
  let values ← readRegisters state params.elements
  if Value.Undefined ∈ values then
    writeAndAdvance state params.dest .Undefined
  else
    writeAndAdvance state params.dest (.Array values)

private def executeSetCreate
    (state : VMState) (paramsIndex : ParamIdx) : Except VMError VMState := do
  let params ←
    match state.program.instructionData.setCreateParams.get? paramsIndex with
    | some params => .ok params
    | none => .error (.ParameterIndexOutOfBounds "setCreateParams" paramsIndex)
  let values ← readRegisters state params.elements
  if Value.Undefined ∈ values then
    writeAndAdvance state params.dest .Undefined
  else
    writeAndAdvance state params.dest (Value.mkSet values)

/-- Execute one already-fetched instruction. -/
def executeInstruction (instruction : Instruction) (state : VMState) :
    Except VMError VMState := do
  match instruction with
  | .Load dest literalIdx =>
      let value ← readLiteral state literalIdx
      writeAndAdvance state dest value
  | .LoadTrue dest => writeAndAdvance state dest (.Bool true)
  | .LoadFalse dest => writeAndAdvance state dest (.Bool false)
  | .LoadNull dest => writeAndAdvance state dest .Null
  | .LoadBool dest value => writeAndAdvance state dest (.Bool value)
  | .LoadData dest => writeAndAdvance state dest state.data
  | .LoadInput dest => writeAndAdvance state dest state.input
  | .Move dest src =>
      let value ← readRegister state src
      writeAndAdvance state dest value
  | .Add dest left right => executeBinary evalAdd state dest left right
  | .Sub dest left right => executeBinary evalSub state dest left right
  | .Mul dest left right => executeBinary evalMul state dest left right
  | .Div dest left right => executeBinary evalDiv state dest left right
  | .Mod dest left right => executeBinary evalMod state dest left right
  | .Eq dest left right => executeBinary evalEq state dest left right
  | .Ne dest left right => executeBinary evalNe state dest left right
  | .Lt dest left right => executeBinary evalLt state dest left right
  | .Le dest left right => executeBinary evalLe state dest left right
  | .Gt dest left right => executeBinary evalGt state dest left right
  | .Ge dest left right => executeBinary evalGe state dest left right
  | .And dest left right => executeBinary evalAnd state dest left right
  | .Or dest left right => executeBinary evalOr state dest left right
  | .Not dest operand =>
      let value ← readRegister state operand
      writeAndAdvance state dest (Regorus.notRvm value)
  | .Guard register .Condition =>
      let value ← readRegister state register
      if Regorus.guardCondition value then
        pure (advance state)
      else
        .error .AssertionFailed
  | .Guard register .NotUndefined =>
      let value ← readRegister state register
      if Regorus.guardNotUndefined value then
        pure (advance state)
      else
        .error .AssertionFailed
  | .Guard register .Not =>
      let value ← readRegister state register
      if Regorus.isTruthy (Regorus.notRvm value) then
        pure (advance state)
      else
        .error .AssertionFailed
  | .ObjectSet obj key value =>
      let keyValue ← readRegister state key
      let fieldValue ← readRegister state value
      let objectValue ← readRegister state obj
      match objectValue with
      | .Object fields =>
          writeAndAdvance state obj
            (Value.mkObject (fields ++ [(keyValue, fieldValue)]))
      | _ => .error (.TypeMismatch "ObjectSet expects an object")
  | .ObjectCreate paramsIndex => executeObjectCreate state paramsIndex
  | .ArrayNew dest => writeAndAdvance state dest (.Array [])
  | .ArrayPush arr value =>
      let element ← readRegister state value
      let arrayValue ← readRegister state arr
      match arrayValue with
      | .Array elements =>
          writeAndAdvance state arr (.Array (elements ++ [element]))
      | _ => .error (.TypeMismatch "ArrayPush expects an array")
  | .ArrayCreate paramsIndex => executeArrayCreate state paramsIndex
  | .SetNew dest => writeAndAdvance state dest (Value.mkSet [])
  | .SetAdd set value =>
      let element ← readRegister state value
      let setValue ← readRegister state set
      match setValue with
      | .Set elements =>
          writeAndAdvance state set (Value.mkSet (element :: elements))
      | _ => .error (.TypeMismatch "SetAdd expects a set")
  | .SetCreate paramsIndex => executeSetCreate state paramsIndex
  | .Index dest container key =>
      let containerValue ← readRegister state container
      let keyValue ← readRegister state key
      writeAndAdvance state dest (indexValue containerValue keyValue)
  | .IndexLiteral dest container literalIdx =>
      let containerValue ← readRegister state container
      let keyValue ← readLiteral state literalIdx
      writeAndAdvance state dest (indexValue containerValue keyValue)
  | .Contains dest collection value =>
      let collectionValue ← readRegister state collection
      let soughtValue ← readRegister state value
      writeAndAdvance state dest (containsValue collectionValue soughtValue)
  | .Count dest collection =>
      let collectionValue ← readRegister state collection
      writeAndAdvance state dest (countValue collectionValue)
  | .Return value =>
      let result ← readRegister state value
      pure { state with status := .Returned result }
  | .Halt =>
      let result ← readRegister state 0
      pure { state with status := .Halted result }
  | other => .error (.Unimplemented (reprStr other))

/--
Execute one small step.  Errors are data in the resulting state, and terminal
states are fixed points, making the function total.
-/
def step (state : VMState) : VMState :=
  match state.status with
  | .Running =>
      match fetchInstruction state with
      | .error error => { state with status := .Error error }
      | .ok instruction =>
          match executeInstruction instruction state with
          | .ok state' => state'
          | .error error => { state with status := .Error error }
  | _ => state

/-- Relational presentation of the executable one-step transition. -/
inductive Step : VMState → VMState → Prop where
  | execute {before after : VMState} (result : step before = after) :
      Step before after

theorem step_iff_Step (before after : VMState) :
    Step before after ↔ step before = after := by
  constructor
  · intro transition
    cases transition with
    | execute result => exact result
  · exact Step.execute

theorem Step.deterministic {before after₁ after₂ : VMState}
    (first : Step before after₁) (second : Step before after₂) :
    after₁ = after₂ := by
  rw [step_iff_Step] at first second
  exact first.symm.trans second

private theorem getElem?_set_ne
    (registers : List Value) (dest other : Reg) (value : Value)
    (different : other ≠ dest) :
    (registers.set dest value)[other]? = registers[other]? := by
  rw [List.getElem?_set]
  simp [Ne.symm different]

theorem writeAndAdvance_frame
    {state state' : VMState} {dest other : Reg} {value : Value}
    (written : writeAndAdvance state dest value = .ok state')
    (different : other ≠ dest) :
    state'.registers[other]? = state.registers[other]? := by
  by_cases inBounds : dest < state.registers.length
  · simp [writeAndAdvance, writeRegister, inBounds] at written
    rw [← written]
    exact getElem?_set_ne state.registers dest other value different
  · simp [writeAndAdvance, writeRegister, inBounds] at written

theorem executeInstruction_load_frame
    {state state' : VMState} {dest other : Reg} {literalIdx : LiteralIdx}
    (executed : executeInstruction (.Load dest literalIdx) state = .ok state')
    (different : other ≠ dest) :
    state'.registers[other]? = state.registers[other]? := by
  cases literalRead : readLiteral state literalIdx with
  | error error =>
      simp [executeInstruction, literalRead, Bind.bind, Except.bind] at executed
  | ok value =>
      rw [show executeInstruction (.Load dest literalIdx) state =
        writeAndAdvance state dest value by
          simp [executeInstruction, literalRead, Bind.bind, Except.bind]] at executed
      exact writeAndAdvance_frame executed different

theorem executeInstruction_move_frame
    {state state' : VMState} {dest src other : Reg}
    (executed : executeInstruction (.Move dest src) state = .ok state')
    (different : other ≠ dest) :
    state'.registers[other]? = state.registers[other]? := by
  cases sourceRead : readRegister state src with
  | error error =>
      simp [executeInstruction, sourceRead, Bind.bind, Except.bind] at executed
  | ok value =>
      rw [show executeInstruction (.Move dest src) state =
        writeAndAdvance state dest value by
          simp [executeInstruction, sourceRead, Bind.bind, Except.bind]] at executed
      exact writeAndAdvance_frame executed different

private theorem executeBinary_frame
    (operation : Value → Value → Except VMError Value)
    {state state' : VMState} {dest left right other : Reg}
    (executed : executeBinary operation state dest left right = .ok state')
    (different : other ≠ dest) :
    state'.registers[other]? = state.registers[other]? := by
  cases leftRead : readRegister state left with
  | error error =>
      simp [executeBinary, leftRead, Bind.bind, Except.bind] at executed
  | ok leftValue =>
      cases rightRead : readRegister state right with
      | error error =>
          simp [executeBinary, leftRead, rightRead, Bind.bind, Except.bind] at executed
      | ok rightValue =>
          cases operationResult : operation leftValue rightValue with
          | error error =>
              simp [executeBinary, leftRead, rightRead, operationResult,
                Bind.bind, Except.bind] at executed
          | ok result =>
              rw [show executeBinary operation state dest left right =
                writeAndAdvance state dest result by
                  simp [executeBinary, leftRead, rightRead, operationResult,
                    Bind.bind, Except.bind]] at executed
              exact writeAndAdvance_frame executed different

theorem executeInstruction_add_frame
    {state state' : VMState} {dest left right other : Reg}
    (executed : executeInstruction (.Add dest left right) state = .ok state')
    (different : other ≠ dest) :
    state'.registers[other]? = state.registers[other]? := by
  exact executeBinary_frame evalAdd (by simpa [executeInstruction] using executed)
    different

theorem executeInstruction_add_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Add dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined := by
  rcases rightBound with ⟨rightValue, rightValueEq⟩
  have leftRead : readRegister state left = .ok .Undefined := by
    simp [readRegister, leftBottom]
  have rightRead : readRegister state right = .ok rightValue := by
    simp [readRegister, rightValueEq]
  have operationResult : evalAdd .Undefined rightValue = .ok .Undefined := by
    simp [evalAdd, strictLift₂]
  have result :
      writeAndAdvance state dest .Undefined = .ok state' := by
    simpa [executeInstruction, executeBinary, leftRead, rightRead,
      operationResult, Bind.bind, Except.bind] using executed
  have inBounds : dest < state.registers.length := by
    by_contra outOfBounds
    have errorResult :
        writeAndAdvance state dest .Undefined =
          .error (.RegisterOutOfBounds dest) := by
      simp [writeAndAdvance, writeRegister, outOfBounds]
    rw [errorResult] at result
    contradiction
  have stateEq :
      advance { state with registers := state.registers.set dest .Undefined } =
        state' := by
    simpa [writeAndAdvance, writeRegister, inBounds] using result
  rw [← stateEq]
  change (state.registers.set dest .Undefined)[dest]? = some .Undefined
  rw [List.getElem?_set]
  simp [inBounds]

theorem executeInstruction_binary_left_undefined
    (operation : Value → Value → Except VMError Value)
    (bottom : ∀ value, operation .Undefined value = .ok .Undefined)
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeBinary operation state dest left right = .ok state') :
    state'.registers[dest]? = some .Undefined := by
  rcases rightBound with ⟨rightValue, rightValueEq⟩
  have leftRead : readRegister state left = .ok .Undefined := by
    simp [readRegister, leftBottom]
  have rightRead : readRegister state right = .ok rightValue := by
    simp [readRegister, rightValueEq]
  have result :
      writeAndAdvance state dest .Undefined = .ok state' := by
    simpa [executeBinary, leftRead, rightRead, bottom rightValue,
      Bind.bind, Except.bind] using executed
  have inBounds : dest < state.registers.length := by
    by_contra outOfBounds
    have errorResult :
        writeAndAdvance state dest .Undefined =
          .error (.RegisterOutOfBounds dest) := by
      simp [writeAndAdvance, writeRegister, outOfBounds]
    rw [errorResult] at result
    contradiction
  have stateEq :
      advance { state with registers := state.registers.set dest .Undefined } =
        state' := by
    simpa [writeAndAdvance, writeRegister, inBounds] using result
  rw [← stateEq]
  change (state.registers.set dest .Undefined)[dest]? = some .Undefined
  rw [List.getElem?_set]
  simp [inBounds]

theorem executeInstruction_sub_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Sub dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalSub
    (by intro value; simp [evalSub, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_mul_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Mul dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalMul
    (by intro value; simp [evalMul, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_div_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Div dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalDiv
    (by intro value; simp [evalDiv, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_mod_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Mod dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalMod
    (by intro value; simp [evalMod, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_eq_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Eq dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalEq
    (by intro value; simp [evalEq, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_ne_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Ne dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalNe
    (by intro value; simp [evalNe, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_lt_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Lt dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalLt
    (by intro value; simp [evalLt, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_le_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Le dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalLe
    (by intro value; simp [evalLe, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_gt_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Gt dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalGt
    (by intro value; simp [evalGt, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_ge_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Ge dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalGe
    (by intro value; simp [evalGe, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_and_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.And dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalAnd
    (by intro value; simp [evalAnd, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

theorem executeInstruction_or_left_undefined
    {state state' : VMState} {dest left right : Reg}
    (leftBottom : state.registers[left]? = some .Undefined)
    (rightBound : ∃ value, state.registers[right]? = some value)
    (executed : executeInstruction (.Or dest left right) state = .ok state') :
    state'.registers[dest]? = some .Undefined :=
  executeInstruction_binary_left_undefined evalOr
    (by intro value; simp [evalOr, strictLift₂])
    leftBottom rightBound (by simpa [executeInstruction] using executed)

end Regorus.RVM

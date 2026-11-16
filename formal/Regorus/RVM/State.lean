/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.RVM.Program

/-!
# Core RVM state

The Rust VM has additional frame, loop, comprehension, cache, suspension, and
resource-accounting state.  Those components are intentionally absent here:
this state is the complete state needed by the non-control-flow phase-one
instruction subset.

Rust exposes several specialized register/type errors.  The phase-one model
keeps bounds failures precise and consolidates collection and arithmetic type
failures under `TypeMismatch`.
-/

namespace Regorus.RVM

inductive VMError where
  | RegisterOutOfBounds (register : Reg)
  | LiteralIndexOutOfBounds (index : LiteralIdx)
  | ParameterIndexOutOfBounds (table : String) (index : ParamIdx)
  | ProgramCounterOutOfBounds (pc : PC)
  | TypeMismatch (expected : String)
  | DivisionByZero
  | NonIntegralModulo
  | AssertionFailed
  | Unimplemented (instruction : String)
  deriving Repr, DecidableEq

inductive VMStatus where
  | Running
  | Halted (value : Regorus.Value)
  | Returned (value : Regorus.Value)
  | Error (error : VMError)
  | Stuck (reason : String)
  deriving Repr, DecidableEq

structure VMState where
  registers : List Regorus.Value
  pc : PC
  program : Program
  data : Regorus.Value
  input : Regorus.Value
  status : VMStatus := .Running
  deriving Repr

def readRegister (state : VMState) (register : Reg) :
    Except VMError Regorus.Value :=
  match state.registers.get? register with
  | some value => .ok value
  | none => .error (.RegisterOutOfBounds register)

def writeRegister (state : VMState) (register : Reg) (value : Regorus.Value) :
    Except VMError VMState :=
  if register < state.registers.length then
    .ok { state with registers := state.registers.set register value }
  else
    .error (.RegisterOutOfBounds register)

def readLiteral (state : VMState) (index : LiteralIdx) :
    Except VMError Regorus.Value :=
  match state.program.literals.get? index with
  | some value => .ok value
  | none => .error (.LiteralIndexOutOfBounds index)

def fetchInstruction (state : VMState) : Except VMError Instruction :=
  match state.program.instructions.get? state.pc with
  | some instruction => .ok instruction
  | none => .error (.ProgramCounterOutOfBounds state.pc)

end Regorus.RVM

/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.RVM.Bytecode
import Regorus.Value.Value

/-!
# Executable RVM program

This is the executable phase-one projection of Rust's `Program`.  It retains
the instruction stream, literal pool, relevant instruction parameter tables,
and entry points.  Rule metadata, builtin dispatch, source spans, compiler
metadata, virtual-data caches, register-window sizing, and serialization flags
are deferred until their instructions enter the formalized subset.
-/

namespace Regorus.RVM

structure Program where
  instructions : List Instruction := []
  literals : List Regorus.Value := []
  instructionData : InstructionData := {}
  entryPoints : List (String × PC) := []
  mainEntryPoint : PC := 0
  deriving Repr

end Regorus.RVM

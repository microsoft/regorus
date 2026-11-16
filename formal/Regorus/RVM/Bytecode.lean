/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

/-!
# RVM bytecode

The instruction constructors mirror `src/rvm/instructions/mod.rs` as of the
RVM phase-one model.  Register and table indices use mathematical naturals
rather than the Rust representation widths (`u8` and `u16`); program
well-formedness will impose those finite bounds in a later phase.

Only the object, array, and set creation parameter tables are represented
below.  The remaining parameter-bearing instructions are retained with their
real table index operand, but their parameter records and semantics are
deliberately deferred.
-/

namespace Regorus.RVM

abbrev Reg := Nat
abbrev PC := Nat
abbrev LiteralIdx := Nat
abbrev ParamIdx := Nat
abbrev RuleIdx := Nat

inductive LoopMode where
  | Any
  | Every
  | ForEach
  deriving Repr, DecidableEq

inductive ComprehensionMode where
  | Set
  | Array
  | Object
  deriving Repr, DecidableEq

inductive GuardMode where
  | Not
  | Condition
  | NotUndefined
  deriving Repr, DecidableEq

inductive PolicyOp where
  | Equals
  | NotEquals
  | Greater
  | GreaterOrEquals
  | Less
  | LessOrEquals
  | In
  | NotIn
  | Contains
  | NotContains
  | ContainsKey
  | NotContainsKey
  | Like
  | NotLike
  | Match
  | NotMatch
  | MatchInsensitively
  | NotMatchInsensitively
  | Exists
  | ValueConditionGuard
  | Not
  deriving Repr, DecidableEq

inductive LogicalBlockMode where
  | AllOf
  | AnyOf
  deriving Repr, DecidableEq

inductive LiteralOrRegister where
  | Literal (index : LiteralIdx)
  | Register (register : Reg)
  deriving Repr, DecidableEq

/--
The full current Rust opcode enum.  Constructors outside the phase-one core
retain their actual immediate operands so programs can be represented
faithfully even though `step` reports them as unimplemented.
-/
inductive Instruction where
  | Load (dest : Reg) (literalIdx : LiteralIdx)
  | LoadTrue (dest : Reg)
  | LoadFalse (dest : Reg)
  | LoadNull (dest : Reg)
  | LoadBool (dest : Reg) (value : Bool)
  | LoadData (dest : Reg)
  | LoadInput (dest : Reg)
  | LoadContext (dest : Reg)
  | LoadMetadata (dest : Reg)
  | Move (dest src : Reg)
  | Add (dest left right : Reg)
  | Sub (dest left right : Reg)
  | Mul (dest left right : Reg)
  | Div (dest left right : Reg)
  | Mod (dest left right : Reg)
  | Eq (dest left right : Reg)
  | Ne (dest left right : Reg)
  | Lt (dest left right : Reg)
  | Le (dest left right : Reg)
  | Gt (dest left right : Reg)
  | Ge (dest left right : Reg)
  | And (dest left right : Reg)
  | Or (dest left right : Reg)
  | Not (dest operand : Reg)
  | BuiltinCall (paramsIndex : ParamIdx)
  | HostAwait (dest arg id : Reg)
  | FunctionCall (paramsIndex : ParamIdx)
  | Return (value : Reg)
  | ObjectSet (obj key value : Reg)
  | ObjectCreate (paramsIndex : ParamIdx)
  | Index (dest container key : Reg)
  | IndexLiteral (dest container : Reg) (literalIdx : LiteralIdx)
  | ChainedIndex (paramsIndex : ParamIdx)
  | ArrayNew (dest : Reg)
  | ArrayPush (arr value : Reg)
  | ArrayPushDefined (arr value : Reg)
  | ArrayCreate (paramsIndex : ParamIdx)
  | SetNew (dest : Reg)
  | SetAdd (set value : Reg)
  | SetCreate (paramsIndex : ParamIdx)
  | Contains (dest collection value : Reg)
  | Count (dest collection : Reg)
  | AssertEq (left right : Reg)
  | Guard (register : Reg) (mode : GuardMode)
  | ReturnUndefinedIfNotTrue (condition : Reg)
  | CoalesceUndefinedToNull (register : Reg)
  | LoopStart (paramsIndex : ParamIdx)
  | LoopNext (bodyStart loopEnd : PC)
  | CallRule (dest : Reg) (ruleIndex : RuleIdx)
  | RuleInit (resultReg : Reg) (ruleIndex : RuleIdx)
  | VirtualDataDocumentLookup (paramsIndex : ParamIdx)
  | DestructuringSuccess
  | RuleReturn
  | Halt
  | ComprehensionBegin (paramsIndex : ParamIdx)
  | ComprehensionYield (valueReg : Reg) (keyReg : Option Reg)
  | ComprehensionEnd
  | PolicyCondition (dest left right : Reg) (op : PolicyOp)
  | LogicalBlockStart (mode : LogicalBlockMode) (result : Reg) (endPC : PC)
  | AllOfNext (check result : Reg) (endPC : PC)
  | AnyOfNext (check result : Reg) (endPC : PC)
  | LogicalBlockEnd (mode : LogicalBlockMode) (result : Reg)
  deriving Repr

namespace Instruction

/--
Compatibility spelling for the former `AssertCondition` opcode.  Rust now
encodes it as `Guard { mode: Condition }`.
-/
def AssertCondition (condition : Reg) : Instruction :=
  .Guard condition .Condition

/--
Compatibility spelling for the former `AssertNotUndefined` opcode.  Rust now
encodes it as `Guard { mode: NotUndefined }`.
-/
def AssertNotUndefined (register : Reg) : Instruction :=
  .Guard register .NotUndefined

end Instruction

structure ObjectCreateParams where
  dest : Reg
  templateLiteralIdx : LiteralIdx
  literalKeyFields : List (LiteralIdx × Reg)
  fields : List (Reg × Reg)
  deriving Repr, DecidableEq

structure ArrayCreateParams where
  dest : Reg
  elements : List Reg
  deriving Repr, DecidableEq

structure SetCreateParams where
  dest : Reg
  elements : List Reg
  deriving Repr, DecidableEq

/--
The phase-one portion of Rust's `InstructionData`.  Tables for loops, calls,
virtual lookup, chained indexing, and comprehensions are deferred with those
instructions.
-/
structure InstructionData where
  objectCreateParams : List ObjectCreateParams := []
  arrayCreateParams : List ArrayCreateParams := []
  setCreateParams : List SetCreateParams := []
  deriving Repr, DecidableEq

end Regorus.RVM

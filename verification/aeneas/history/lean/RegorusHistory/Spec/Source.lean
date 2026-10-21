/- Copyright (c) Microsoft Corporation. All rights reserved.
   Licensed under the MIT License. -/
module

public import RegorusHistory.Spec.Data

public section

namespace RegorusHistory.Spec

/-- Request patterns inspect only the nodes they visit; literals are opaque. -/
inductive Head where
  | literal (value : Data)
  | variable (name : String)
  | any
  | array (children : List Head)
  | object (fields : List (Data × Head))

inductive Term where
  | constant (value : Data)
  | variable (name : String)

/-- Internal tests form a Boolean algebra. Source disequality also requires presence. -/
inductive Test where
  | truth (value : Bool)
  | hasValue (path : List Data)
  | eqCore (path : List Data) (term : Term)
  | negate (child : Test)
  | conj (children : List Test)
  | disj (children : List Test)

inductive Regex where
  | empty
  | universal
  | epsilon
  | test (guard : Test)
  | union (children : List Regex)
  | concat (children : List Regex)
  | star (child : Regex)
  | intersect (children : List Regex)
  | complement (child : Regex)

inductive Transition where
  | constant (regex : Regex)
  | conditional (guard : Test) (yes no : Transition)
  | union (children : List Transition)
  | intersect (children : List Transition)
  | complement (child : Transition)
  | append (front : Transition) (suffix : List Regex)

abbrev Subst := String → Option Data

/-- A variable occurs only in a variable pattern, never inside an opaque literal or key. -/
inductive HeadFV : Head → String → Prop where
  | variable (name : String) : HeadFV (.variable name) name
  | array {children : List Head} {child : Head} {name : String} :
      child ∈ children → HeadFV child name → HeadFV (.array children) name
  | object {fields : List (Data × Head)} {key : Data} {child : Head} {name : String} :
      (key, child) ∈ fields → HeadFV child name → HeadFV (.object fields) name

mutual
  /-- Structural satisfaction with one shared valuation for repeated variables. -/
  inductive HeadSatisfies : Head → Data → Subst → Prop where
    | literal {value : Data} {θ : Subst} :
        value ≠ .undefined → HeadSatisfies (.literal value) value θ
    | variable {name : String} {value : Data} {θ : Subst} :
        value ≠ .undefined → θ name = some value →
        HeadSatisfies (.variable name) value θ
    | any {value : Data} {θ : Subst} :
        value ≠ .undefined → HeadSatisfies .any value θ
    | array {children : List Head} {values : List Data} {θ : Subst} :
        HeadListSatisfies children values θ →
        HeadSatisfies (.array children) (.array values) θ
    | object {fields : List (Data × Head)} {values : List (Data × Data)} {θ : Subst} :
        HeadFieldsSatisfy fields values θ →
        HeadSatisfies (.object fields) (.object values) θ

  /-- Lists match pointwise, including exact arity. -/
  inductive HeadListSatisfies : List Head → List Data → Subst → Prop where
    | nil {θ : Subst} : HeadListSatisfies [] [] θ
    | cons {head : Head} {heads : List Head} {value : Data} {values : List Data}
        {θ : Subst} :
        HeadSatisfies head value θ → HeadListSatisfies heads values θ →
        HeadListSatisfies (head :: heads) (value :: values) θ

  /-- Each requested object field must exist; unmentioned fields are unrestricted. -/
  inductive HeadFieldsSatisfy : List (Data × Head) → List (Data × Data) → Subst → Prop where
    | nil {values : List (Data × Data)} {θ : Subst} : HeadFieldsSatisfy [] values θ
    | cons {key value : Data} {head : Head} {fields : List (Data × Head)}
        {values : List (Data × Data)} {θ : Subst} :
        selectData (.object values) [key] = some value →
        HeadSatisfies head value θ → HeadFieldsSatisfy fields values θ →
        HeadFieldsSatisfy ((key, head) :: fields) values θ
end

/-- No bindings outside the head, and every head variable has a binding. -/
def HeadDenotes (head : Head) (request : Data) (θ : Subst) : Prop :=
  HeadSatisfies head request θ ∧
    ∀ name, (∃ value, θ name = some value) ↔ HeadFV head name

/-- Constants are opaque complete Values, including Undefined. -/
def termValue (θ : Subst) : Term → Option Data
  | .constant value => some value
  | .variable name => θ name

/-- Missing selection makes EqCore false, but its internal complement true. -/
def TestHolds (θ : Subst) (test : Test) (event : Data) : Prop :=
  match test with
  | .truth value => value = true
  | .hasValue path => ∃ value, selectData event path = some value
  | .eqCore path term =>
      ∃ value, selectData event path = some value ∧ termValue θ term = some value
  | .negate child => ¬ TestHolds θ child event
  | .conj children => ∀ child : {t // t ∈ children}, TestHolds θ child.val event
  | .disj children => ∃ child : {t // t ∈ children}, TestHolds θ child.val event
termination_by sizeOf test
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := List.sizeOf_lt_of_mem child.property
      omega

/-- Source path keys themselves must be defined; opaque nested values are allowed. -/
inductive DecodedPath : Data → List Data → Prop where
  | array {keys : List Data} :
      (∀ key ∈ keys, key ≠ .undefined) → DecodedPath (.array keys) keys

mutual
  /-- This is the source grammar, not the normalized or compiled representation. -/
  inductive DecodedHead : Data → Head → Prop where
    | literal (value : Data) :
        DecodedHead (.object [(.string "value", value)]) (.literal value)
    | variable {name : String} :
        name ≠ "" →
        DecodedHead (.object [(.string "var", .string name)]) (.variable name)
    | any : DecodedHead (.object [(.string "any", .bool true)]) .any
    | array {sources : List Data} {heads : List Head} :
        DecodedHeads sources heads →
        DecodedHead (.object [(.string "array", .array sources)]) (.array heads)
    | object {sources : List (Data × Data)} {heads : List (Data × Head)} :
        DecodedHeadFields sources heads →
        DecodedHead (.object [(.string "object", .object sources)]) (.object heads)

  inductive DecodedHeads : List Data → List Head → Prop where
    | nil : DecodedHeads [] []
    | cons {source : Data} {head : Head} {sources : List Data} {heads : List Head} :
        DecodedHead source head → DecodedHeads sources heads →
        DecodedHeads (source :: sources) (head :: heads)

  /-- Object keys are arbitrary Values, not just strings. -/
  inductive DecodedHeadFields : List (Data × Data) → List (Data × Head) → Prop where
    | nil : DecodedHeadFields [] []
    | cons {key source : Data} {head : Head} {sources : List (Data × Data)}
        {heads : List (Data × Head)} :
        DecodedHead source head → DecodedHeadFields sources heads →
        DecodedHeadFields ((key, source) :: sources) ((key, head) :: heads)
end

inductive DecodedTerm (declared : String → Prop) : Data → Term → Prop where
  | constant (value : Data) :
      DecodedTerm declared (.object [(.string "value", value)]) (.constant value)
  | variable {name : String} :
      name ≠ "" → declared name →
      DecodedTerm declared (.object [(.string "var", .string name)]) (.variable name)

/-- The two members may occur in either order; extra or non-string members cannot fit. -/
inductive DecodedComparison (declared : String → Prop) : Data → List Data → Term → Prop where
  | object {fields : List (Data × Data)} {pathSource termSource : Data}
      {path : List Data} {term : Term} :
      fields.length = 2 →
      (.string "path", pathSource) ∈ fields →
      (.string "term", termSource) ∈ fields →
      DecodedPath pathSource path → DecodedTerm declared termSource term →
      DecodedComparison declared (.object fields) path term

mutual
  /-- There is deliberately no source not-test tag. Every Boolean child is decoded. -/
  inductive DecodedTest (declared : String → Prop) : Data → Test → Prop where
    | truth (value : Bool) : DecodedTest declared (.bool value) (.truth value)
    | conj {sources : List Data} {tests : List Test} :
        DecodedTests declared sources tests →
        DecodedTest declared (.object [(.string "and", .array sources)]) (.conj tests)
    | disj {sources : List Data} {tests : List Test} :
        DecodedTests declared sources tests →
        DecodedTest declared (.object [(.string "or", .array sources)]) (.disj tests)
    | equal {payload : Data} {path : List Data} {term : Term} :
        DecodedComparison declared payload path term →
        DecodedTest declared (.object [(.string "eq", payload)])
          (.conj [.hasValue path, .eqCore path term])
    | notEqual {payload : Data} {path : List Data} {term : Term} :
        DecodedComparison declared payload path term →
        DecodedTest declared (.object [(.string "neq", payload)])
          (.conj [.hasValue path, .negate (.eqCore path term)])

  inductive DecodedTests (declared : String → Prop) : List Data → List Test → Prop where
    | nil : DecodedTests declared [] []
    | cons {source : Data} {test : Test} {sources : List Data} {tests : List Test} :
        DecodedTest declared source test → DecodedTests declared sources tests →
        DecodedTests declared (source :: sources) (test :: tests)
end

mutual
  /-- All operands are validated, even in unions/intersections that could later absorb them. -/
  inductive DecodedRegex (declared : String → Prop) : Data → Regex → Prop where
    | empty : DecodedRegex declared (.object [(.string "empty", .bool true)]) .empty
    | universal : DecodedRegex declared (.object [(.string "all", .bool true)]) .universal
    | epsilon : DecodedRegex declared (.object [(.string "epsilon", .bool true)]) .epsilon
    | test {source : Data} {test : Test} :
        DecodedTest declared source test →
        DecodedRegex declared (.object [(.string "test", source)]) (.test test)
    | star {source : Data} {regex : Regex} :
        DecodedRegex declared source regex →
        DecodedRegex declared (.object [(.string "star", source)]) (.star regex)
    | complement {source : Data} {regex : Regex} :
        DecodedRegex declared source regex →
        DecodedRegex declared (.object [(.string "not", source)]) (.complement regex)
    | union {sources : List Data} {regexes : List Regex} :
        DecodedRegexes declared sources regexes →
        DecodedRegex declared (.object [(.string "union", .array sources)]) (.union regexes)
    | concat {sources : List Data} {regexes : List Regex} :
        DecodedRegexes declared sources regexes →
        DecodedRegex declared (.object [(.string "concat", .array sources)]) (.concat regexes)
    | intersect {sources : List Data} {regexes : List Regex} :
        DecodedRegexes declared sources regexes →
        DecodedRegex declared (.object [(.string "intersect", .array sources)]) (.intersect regexes)

  inductive DecodedRegexes (declared : String → Prop) : List Data → List Regex → Prop where
    | nil : DecodedRegexes declared [] []
    | cons {source : Data} {regex : Regex} {sources : List Data} {regexes : List Regex} :
        DecodedRegex declared source regex → DecodedRegexes declared sources regexes →
        DecodedRegexes declared (source :: sources) (regex :: regexes)
end

/-- Independent policy decoding; physical/canonical DataWF is a separate domain invariant. -/
inductive DecodedPolicy : Data → Head → Regex → Prop where
  | object {fields : List (Data × Data)} {request history : Data} {head : Head}
      {tail : Regex} :
      fields.length = 2 →
      (.string "request", request) ∈ fields →
      (.string "history", history) ∈ fields →
      DecodedHead request head → DecodedRegex (HeadFV head) history tail →
      DecodedPolicy (.object fields) head tail

@[simp] theorem testHolds_negate (θ : Subst) (test : Test) (event : Data) :
    TestHolds θ (.negate test) event ↔ ¬ TestHolds θ test event := by
  rw [TestHolds]

/-- Source equality and disequality both reject missing or selected Undefined values. -/
theorem source_eq_absent (θ : Subst) (path : List Data) (term : Term) (event : Data)
    (absent : selectData event path = none) :
    ¬ TestHolds θ (.conj [.hasValue path, .eqCore path term]) event := by
  simp [TestHolds, absent]

theorem source_neq_absent (θ : Subst) (path : List Data) (term : Term) (event : Data)
    (absent : selectData event path = none) :
    ¬ TestHolds θ (.conj [.hasValue path, .negate (.eqCore path term)]) event := by
  simp [TestHolds, absent]

end RegorusHistory.Spec

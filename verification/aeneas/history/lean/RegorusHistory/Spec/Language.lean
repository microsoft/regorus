-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT License.
module
public import RegorusHistory.Spec.Source
public import Mathlib.Data.List.Basic
@[expose] public section

namespace RegorusHistory.Spec

open Classical

/-- Languages contain committed histories, oldest event first. -/
abbrev Language := List Data → Prop

def sequence (left right : Language) : Language :=
  fun word => ∃ front suffix, word = front ++ suffix ∧ left front ∧ right suffix

def sequences : List Language → Language
  | [] => fun word => word = []
  | first :: rest => sequence first (sequences rest)

/-- Finite concatenations, including zero factors; empty factors are permitted. -/
inductive Kleene (language : Language) : List Data → Prop
  | nil : Kleene language []
  | append {front suffix} : language front → Kleene language suffix →
      Kleene language (front ++ suffix)

def TailLang (θ : Subst) : Regex → Language
  | .empty => fun _ => False
  | .universal => fun _ => True
  | .epsilon => fun word => word = []
  | .test test => fun word => ∃ event, word = [event] ∧ TestHolds θ test event
  | .union children => fun word => ∃ child : {r // r ∈ children}, TailLang θ child.val word
  | .concat children => sequences (children.map (TailLang θ))
  | .star child => Kleene (TailLang θ child)
  | .intersect children => fun word => ∀ child : {r // r ∈ children}, TailLang θ child.val word
  | .complement child => fun word => ¬ TailLang θ child word
termination_by regex => sizeOf regex
decreasing_by
  all_goals simp_wf
  all_goals try have membership := child.property
  all_goals decreasing_tactic

def PairLang (head : Head) (tail : Regex) : List Data → Prop
  | [] => False
  | request :: history => ∃ θ, HeadDenotes head request θ ∧ TailLang θ tail history

def PolicyLang (policy request : Data) (history : List Data) : Prop :=
  ∃ head tail, DecodedPolicy policy head tail ∧ PairLang head tail (request :: history)

def nullable : Regex → Bool
  | .empty | .test _ => false
  | .universal | .epsilon | .star _ => true
  | .union children => children.attach.any (fun child => nullable child.val)
  | .concat children | .intersect children => children.attach.all (fun child => nullable child.val)
  | .complement child => !nullable child
termination_by regex => sizeOf regex
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := List.sizeOf_lt_of_mem child.property
      omega

noncomputable def derivative (θ : Subst) (event : Data) : Regex → Regex
  | .empty | .epsilon => .empty
  | .universal => .universal
  | .test test => if TestHolds θ test event then .epsilon else .empty
  | .union children => .union (children.map (derivative θ event))
  | .intersect children => .intersect (children.map (derivative θ event))
  | .complement child => .complement (derivative θ event child)
  | .star child => .concat [derivative θ event child, .star child]
  | .concat [] => .empty
  | .concat (first :: rest) =>
      if nullable first then
        .union [.concat (derivative θ event first :: rest),
          derivative θ event (.concat rest)]
      else .concat (derivative θ event first :: rest)
termination_by regex => sizeOf regex

noncomputable def deriveWord (θ : Subst) : List Data → Regex → Regex
  | [], regex => regex
  | event :: rest, regex => deriveWord θ rest (derivative θ event regex)

/-- Guards use one fixed event and substitution; append is right concatenation. -/
def TransitionLang (θ : Subst) (event : Data) : Transition → Language
  | .constant regex => TailLang θ regex
  | .conditional test yes no => fun word =>
      (TestHolds θ test event ∧ TransitionLang θ event yes word) ∨
      (¬TestHolds θ test event ∧ TransitionLang θ event no word)
  | .union children => fun word =>
      ∃ child : {t // t ∈ children}, TransitionLang θ event child.val word
  | .intersect children => fun word =>
      ∀ child : {t // t ∈ children}, TransitionLang θ event child.val word
  | .complement child => fun word => ¬TransitionLang θ event child word
  | .append child suffix => sequence (TransitionLang θ event child) (TailLang θ (.concat suffix))
termination_by transition => sizeOf transition
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := List.sizeOf_lt_of_mem child.property
      omega

@[simp] theorem sequence_nil (left right : Language) :
    sequence left right [] ↔ left [] ∧ right [] := by
  simp [sequence]

@[simp] theorem sequences_nil (languages : List Language) :
    sequences languages [] ↔ ∀ language ∈ languages, language [] := by
  induction languages with
  | nil => simp [sequences]
  | cons first rest ih => simp [sequences, ih]

@[simp] theorem nullable_iff_nil (θ : Subst) (regex : Regex) :
    nullable regex = true ↔ TailLang θ regex [] := by
  cases regex with
  | empty => simp [nullable, TailLang]
  | universal => simp [nullable, TailLang]
  | epsilon => simp [nullable, TailLang]
  | test test => simp [nullable, TailLang]
  | union children =>
      simp only [nullable, List.any_eq_true, List.mem_attach, true_and, TailLang]
      exact exists_congr fun child => nullable_iff_nil θ child.val
  | concat children =>
      simp only [nullable, List.all_eq_true, List.mem_attach, forall_const,
        TailLang, sequences_nil, List.mem_map]
      constructor
      · intro h language ⟨child, hc, he⟩
        subst language
        exact (nullable_iff_nil θ child).mp (h ⟨child, hc⟩)
      · intro h child
        exact (nullable_iff_nil θ child.val).mpr (h _ ⟨child.val, child.property, rfl⟩)
  | star child => simp [nullable, TailLang, Kleene.nil]
  | intersect children =>
      simp only [nullable, List.all_eq_true, List.mem_attach, forall_const, TailLang]
      exact forall_congr' fun child => nullable_iff_nil θ child.val
  | complement child =>
      simp only [nullable, TailLang]
      rw [← nullable_iff_nil θ child]
      cases nullable child <;> decide
termination_by sizeOf regex
decreasing_by
  all_goals simp_wf
  all_goals try have membership := child.property
  all_goals decreasing_tactic

@[simp] theorem sequence_epsilon (language : Language) (word : List Data) :
    sequence language (fun rest => rest = []) word ↔ language word := by
  simp [sequence]

theorem tail_concat_cons (θ : Subst) (first : Regex) (rest : List Regex) (word : List Data) :
    TailLang θ (.concat (first :: rest)) word ↔
      sequence (TailLang θ first) (TailLang θ (.concat rest)) word := by
  simp only [TailLang, List.map_cons, sequences]

@[simp] theorem tail_concat_singleton (θ : Subst) (regex : Regex) (word : List Data) :
    TailLang θ (.concat [regex]) word ↔ TailLang θ regex word := by
  simp only [TailLang, List.map_cons, List.map_nil, sequences, sequence_epsilon]

theorem tail_union_two (θ : Subst) (left right : Regex) (word : List Data) :
    TailLang θ (.union [left, right]) word ↔
      TailLang θ left word ∨ TailLang θ right word := by
  simp [TailLang]

/-- Splitting a nonempty word either consumes its first event on the left or
    uses an empty left factor. -/
theorem sequence_cons (left right : Language) (event : Data) (suffix : List Data) :
    sequence left right (event :: suffix) ↔
      (∃ front rest, suffix = front ++ rest ∧ left (event :: front) ∧ right rest) ∨
      (left [] ∧ right (event :: suffix)) := by
  constructor
  · rintro ⟨front, rest, eq, hp, hr⟩
    cases front with
    | nil => exact Or.inr ⟨hp, by simpa using eq ▸ hr⟩
    | cons first front =>
        cases eq
        exact Or.inl ⟨front, rest, rfl, hp, hr⟩
  · rintro (⟨front, rest, eq, hp, hr⟩ | ⟨hp, hr⟩)
    · exact ⟨event :: front, rest, by simp [eq], hp, hr⟩
    · exact ⟨[], event :: suffix, rfl, hp, hr⟩

theorem kleene_cons (language : Language) (event : Data) (suffix : List Data) :
    Kleene language (event :: suffix) ↔
      ∃ front rest, suffix = front ++ rest ∧ language (event :: front) ∧
        Kleene language rest := by
  constructor
  · intro h
    generalize eq : event :: suffix = word at h
    induction h with
    | nil => simp at eq
    | @append front rest hp hr ih =>
        cases front with
        | nil => exact ih eq
        | cons first front =>
            simp only [List.cons_append, List.cons.injEq] at eq
            exact ⟨front, rest, eq.2, eq.1 ▸ hp, hr⟩
  · rintro ⟨front, rest, eq, hp, hr⟩
    simpa [eq] using Kleene.append hp hr

/-- Concrete one-event left quotient; no normalizer or generated operation. -/
theorem derivative_correct (θ : Subst) (event : Data) (regex : Regex) (suffix : List Data) :
    TailLang θ (derivative θ event regex) suffix ↔ TailLang θ regex (event :: suffix) := by
  classical
  cases regex with
  | empty => simp [derivative, TailLang]
  | universal => simp [derivative, TailLang]
  | epsilon => simp [derivative, TailLang]
  | test test =>
      by_cases h : TestHolds θ test event
      · simp [derivative, h, TailLang]
      · simp [derivative, h, TailLang]
  | union children =>
      simp only [derivative, TailLang, Subtype.exists, List.mem_map]
      constructor
      · rintro ⟨_, ⟨child, hc, rfl⟩, h⟩
        exact ⟨child, hc, (derivative_correct θ event child suffix).mp h⟩
      · rintro ⟨child, hc, h⟩
        exact ⟨_, ⟨child, hc, rfl⟩, (derivative_correct θ event child suffix).mpr h⟩
  | intersect children =>
      simp only [derivative, TailLang, Subtype.forall, List.mem_map]
      constructor
      · intro h child hc
        exact (derivative_correct θ event child suffix).mp (h _ ⟨child, hc, rfl⟩)
      · rintro h _ ⟨child, hc, rfl⟩
        exact (derivative_correct θ event child suffix).mpr (h child hc)
  | complement child =>
      simpa only [derivative, TailLang] using not_congr (derivative_correct θ event child suffix)
  | star child =>
      rw [derivative, tail_concat_cons]
      have singleton : TailLang θ (.concat [.star child]) = TailLang θ (.star child) := by
        funext word
        exact propext (tail_concat_singleton θ (.star child) word)
      rw [singleton]
      simp only [TailLang]
      unfold sequence
      rw [kleene_cons]
      exact exists_congr fun front => exists_congr fun rest =>
        and_congr_right fun _ => and_congr (derivative_correct θ event child front) Iff.rfl
  | concat children =>
      cases children with
      | nil => simp [derivative, TailLang, sequences]
      | cons first rest =>
          rw [tail_concat_cons, sequence_cons]
          by_cases hn : nullable first = true
          · have empty := (nullable_iff_nil θ first).mp hn
            rw [derivative, ite_eq_left hn, tail_union_two, tail_concat_cons,
              derivative_correct θ event (.concat rest) suffix]
            simp only [empty, true_and]
            exact or_congr (exists_congr fun front => exists_congr fun tail =>
              and_congr_right fun _ => and_congr (derivative_correct θ event first front) Iff.rfl) Iff.rfl
          · have empty : ¬TailLang θ first [] := by
              intro h
              exact hn ((nullable_iff_nil θ first).mpr h)
            rw [derivative, ite_eq_right hn, tail_concat_cons]
            simp only [empty, false_and, or_false]
            exact exists_congr fun front => exists_congr fun tail =>
              and_congr_right fun _ => and_congr (derivative_correct θ event first front) Iff.rfl
termination_by sizeOf regex

/-- The fold consumes committed history left-to-right, never request-first replay. -/
theorem deriveWord_correct (θ : Subst) (history : List Data) (regex : Regex)
    (suffix : List Data) :
    TailLang θ (deriveWord θ history regex) suffix ↔ TailLang θ regex (history ++ suffix) := by
  induction history generalizing regex with
  | nil => rfl
  | cons event history ih =>
      simpa only [deriveWord, List.cons_append] using
        (ih (derivative θ event regex)).trans (derivative_correct θ event regex (history ++ suffix))

theorem deriveWord_nullable (θ : Subst) (history : List Data) (regex : Regex) :
    nullable (deriveWord θ history regex) = true ↔ TailLang θ regex history := by
  rw [nullable_iff_nil, deriveWord_correct, List.append_nil]

end RegorusHistory.Spec

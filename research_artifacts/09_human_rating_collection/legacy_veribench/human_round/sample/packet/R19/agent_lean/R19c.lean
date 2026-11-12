import Mathlib

/-!
# Levenshtein edit distance

This file formalizes unit-cost Levenshtein distance for lists.  Strings are represented by
their lists of characters through `editDistanceString`.  Lean's type system enforces the
Python precondition that both arguments are sequences with comparable elements.

The functional implementation uses Mathlib's purely functional rolling-row computation.
The imperative implementation exposes the same algorithm as an `Id.run do` program with a
mutable current row.
-/

namespace edit_distance

/-! ## Functional implementation -/

/-- Unit-cost Levenshtein distance between two lists. -/
def editDistance {α : Type} [DecidableEq α] (s₁ s₂ : List α) : Nat :=
  levenshtein Levenshtein.defaultCost s₁ s₂

/-- String adapter for `editDistance`. -/
def editDistanceString (s₁ s₂ : String) : Nat :=
  editDistance s₁.data s₂.data

/-! ## Functional unit tests -/

example : editDistanceString "hello" "hello" = 0 := by native_decide
example : editDistanceString "cat" "bat" = 1 := by native_decide
example : editDistanceString "cat" "cats" = 1 := by native_decide
example : editDistanceString "cats" "cat" = 1 := by native_decide
example : editDistanceString "cat" "dog" = 3 := by native_decide
example : editDistanceString "kitten" "sitting" = 3 := by native_decide

example :
    editDistanceString "" "" = 0 ∧
    editDistanceString "" "abc" = 3 ∧
    editDistanceString "ab" "" = 2 ∧
    editDistanceString "a" "b" = 1 := by native_decide

example :
    editDistance [1, 2, 3] [1, 2, 3] = 0 ∧
    editDistance [1, 2, 3] [1, 4, 3] = 1 ∧
    editDistance [1, 2, 3, 4] [1, 3, 4] = 1 ∧
    editDistance [1, 2, 3] [4, 5, 6] = 3 ∧
    editDistance [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide

example :
    editDistance ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 ∧
    editDistance ['c', 'a', 't'] ['b', 'a', 't'] = 1 ∧
    editDistance ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 ∧
    editDistance ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide

example :
    editDistanceString "intention" "execution" = 5 ∧
    editDistanceString "saturday" "sunday" = 3 ∧
    editDistanceString "abc" "def" = 3 ∧
    editDistanceString "xyz" "abc" = 3 := by native_decide

example :
    editDistanceString "aaa" "aa" = 1 ∧
    editDistanceString "aa" "aaa" = 1 ∧
    editDistanceString "aaaa" "bbbb" = 4 := by native_decide

#eval editDistanceString "kitten" "sitting"
#eval editDistance [1, 2, 3, 4, 5] [6, 7, 8]

/-! ## Preconditions and functional properties -/

/--
For list inputs the Python dynamic type check is discharged by Lean's static types.
`DecidableEq α` supplies the executable equality test used by substitution.
-/
def Pre {α : Type} [DecidableEq α] (_s₁ _s₂ : List α) : Prop :=
  True

/-- The distance from the empty list is the number of required insertions. -/
def empty_left_prop {α : Type} [DecidableEq α] (s : List α) : Prop :=
  editDistance [] s = s.length

theorem empty_left_thm {α : Type} [DecidableEq α] (s : List α) :
    empty_left_prop s := by
  induction s with
  | nil => simp [empty_left_prop, editDistance, levenshtein_nil_nil]
  | cons x xs ih =>
      simp only [empty_left_prop, editDistance, levenshtein_nil_cons,
        Levenshtein.defaultCost_insert, List.length_cons]
      rw [show levenshtein Levenshtein.defaultCost [] xs = xs.length from ih]
      omega

/-- The distance to the empty list is the number of required deletions. -/
def empty_right_prop {α : Type} [DecidableEq α] (s : List α) : Prop :=
  editDistance s [] = s.length

theorem empty_right_thm {α : Type} [DecidableEq α] (s : List α) :
    empty_right_prop s := by
  induction s with
  | nil => simp [empty_right_prop, editDistance, levenshtein_nil_nil]
  | cons x xs ih =>
      simp only [empty_right_prop, editDistance, levenshtein_cons_nil,
        Levenshtein.defaultCost_delete, List.length_cons]
      rw [show levenshtein Levenshtein.defaultCost xs [] = xs.length from ih]
      omega

/-- A list has edit distance zero from itself. -/
def identity_prop {α : Type} [DecidableEq α] (s : List α) : Prop :=
  editDistance s s = 0

theorem identity_thm {α : Type} [DecidableEq α] (s : List α) :
    identity_prop s := by
  induction s with
  | nil => simp [identity_prop, editDistance, levenshtein_nil_nil]
  | cons x xs ih =>
      simp only [identity_prop, editDistance, levenshtein_cons_cons,
        Levenshtein.defaultCost_delete, Levenshtein.defaultCost_insert,
        Levenshtein.defaultCost_substitute, if_pos]
      rw [show levenshtein Levenshtein.defaultCost xs xs = 0 from ih]
      simp

/--
The dynamic-programming recurrence: deletion, insertion, and substitution have unit cost,
while replacing an element by itself has cost zero.
-/
def recurrence_prop {α : Type} [DecidableEq α]
    (x : α) (xs : List α) (y : α) (ys : List α) : Prop :=
  editDistance (x :: xs) (y :: ys) =
    min (1 + editDistance xs (y :: ys))
      (min (1 + editDistance (x :: xs) ys)
        ((if x = y then 0 else 1) + editDistance xs ys))

theorem recurrence_thm {α : Type} [DecidableEq α]
    (x : α) (xs : List α) (y : α) (ys : List α) :
    recurrence_prop x xs y ys := by
  simp [recurrence_prop, editDistance, levenshtein_cons_cons,
    Levenshtein.defaultCost]

/-- Deleting all of the first list and inserting all of the second is always an upper bound. -/
def upper_bound_prop {α : Type} [DecidableEq α] (s₁ s₂ : List α) : Prop :=
  editDistance s₁ s₂ ≤ s₁.length + s₂.length

theorem upper_bound_thm {α : Type} [DecidableEq α] (s₁ s₂ : List α) :
    upper_bound_prop s₁ s₂ := by
  induction s₁ generalizing s₂ with
  | nil =>
      rw [upper_bound_prop, show editDistance [] s₂ = s₂.length from empty_left_thm s₂]
      simp
  | cons x xs ih =>
      cases s₂ with
      | nil =>
          rw [upper_bound_prop,
            show editDistance (x :: xs) [] = (x :: xs).length from empty_right_thm _]
          simp
      | cons y ys =>
          rw [upper_bound_prop, editDistance, levenshtein_cons_cons]
          apply le_trans (Nat.min_le_left ..)
          simpa [editDistance, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            Nat.add_le_add_left (ih (y :: ys)) 1

/-! ## Postcondition and total correctness -/

/--
The result obeys a constructive upper bound, both empty-sequence cases, and reflexivity.
The implications specialize these facts to the supplied input pair.
-/
def Post_prop {α : Type} [DecidableEq α] (s₁ s₂ : List α) : Prop :=
  upper_bound_prop s₁ s₂ ∧
  (s₁ = [] → editDistance s₁ s₂ = s₂.length) ∧
  (s₂ = [] → editDistance s₁ s₂ = s₁.length) ∧
  (s₁ = s₂ → editDistance s₁ s₂ = 0)

theorem correctness_thm {α : Type} [DecidableEq α] (s₁ s₂ : List α) :
    Pre s₁ s₂ → Post_prop s₁ s₂ := by
  intro _
  refine ⟨upper_bound_thm s₁ s₂, ?_, ?_, ?_⟩
  · intro h
    subst s₁
    exact empty_left_thm s₂
  · intro h
    subst s₂
    exact empty_right_thm s₁
  · intro h
    subst s₂
    exact identity_thm s₁

/-! ## Imperative rolling-row implementation -/

/--
An imperative presentation of the rolling-row algorithm.  The initial row contains the
costs of deleting suffixes of `s₁`.  Each iteration mutates that row for one element of
`s₂`; the reverse traversal matches the suffix-oriented recurrence.
-/
def editDistanceImperative {α : Type} [DecidableEq α] (s₁ s₂ : List α) : Nat :=
  Id.run do
    let mut row := suffixLevenshtein Levenshtein.defaultCost s₁ []
    for y in s₂.reverse do
      row := Levenshtein.impl Levenshtein.defaultCost s₁ y row
    return row.1[0]

/-- String adapter for the imperative implementation. -/
def editDistanceStringImperative (s₁ s₂ : String) : Nat :=
  editDistanceImperative s₁.data s₂.data

/-! ## Imperative unit tests -/

example : editDistanceStringImperative "hello" "hello" = 0 := by native_decide
example : editDistanceStringImperative "cat" "bat" = 1 := by native_decide
example : editDistanceStringImperative "kitten" "sitting" = 3 := by native_decide
example : editDistanceStringImperative "intention" "execution" = 5 := by native_decide
example : editDistanceImperative [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : editDistanceImperative [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide

#eval editDistanceStringImperative "saturday" "sunday"
#eval editDistanceImperative ['c', 'a', 't'] ['c', 'a', 't', 's']

/-- The functional and mutable rolling-row presentations compute exactly the same result. -/
theorem functional_eq_imperative_thm {α : Type} [DecidableEq α]
    (s₁ s₂ : List α) :
    editDistance s₁ s₂ = editDistanceImperative s₁ s₂ := by
  simp [editDistance, editDistanceImperative, levenshtein, suffixLevenshtein]

end edit_distance

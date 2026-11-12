import Mathlib

/-!
# HumanEval 29: Filter by Prefix

This file formalizes the Python function that retains, in their original order,
exactly the strings beginning with a supplied prefix.
-/

namespace humaneval_29_filter_by_prefix

/-- Keep exactly the strings whose initial characters equal the given prefix. -/
def filterByPrefix (strings : List String) (pre : String) : List String :=
  strings.filter (fun string => string.startsWith pre)

example : filterByPrefix [] "a" = [] := by native_decide

example :
    filterByPrefix ["abc", "bcd", "cde", "array"] "a" =
      ["abc", "array"] := by native_decide

example :
    filterByPrefix ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" =
      ["xxx", "xxxAAA", "xxx"] := by native_decide

#eval filterByPrefix [] "john"
#eval filterByPrefix ["abc", "bcd", "cde", "array"] "a"

/-- The Python function is total, so it has no input restrictions. -/
def Pre (_strings : List String) (_pre : String) : Prop := True

/-- Membership in the result is precisely membership in the input together
with the prefix test. -/
def selected_members_prop
    (strings : List String) (pre : String) (result : List String) : Prop :=
  ∀ string, string ∈ result ↔ string ∈ strings ∧ string.startsWith pre = true

theorem selected_members_thm (strings : List String) (pre : String) :
    selected_members_prop strings pre (filterByPrefix strings pre) := by
  intro string
  simp [filterByPrefix]

/-- The exact-list property captures order and multiplicity, in addition to
which strings are retained. -/
def exact_filter_prop
    (strings : List String) (pre : String) (result : List String) : Prop :=
  result = strings.filter (fun string => string.startsWith pre)

theorem exact_filter_thm (strings : List String) (pre : String) :
    exact_filter_prop strings pre (filterByPrefix strings pre) := by
  rfl

/-- The complete postcondition for a candidate output. -/
def Post_prop
    (strings : List String) (pre : String) (result : List String) : Prop :=
  selected_members_prop strings pre result ∧
    exact_filter_prop strings pre result

theorem filterByPrefix_correct (strings : List String) (pre : String) :
    Pre strings pre → Post_prop strings pre (filterByPrefix strings pre) := by
  intro _
  exact ⟨selected_members_thm strings pre, exact_filter_thm strings pre⟩

/-- An imperative presentation: accumulate matching strings while traversing
the input from left to right. -/
def filterByPrefixImperative (strings : List String) (pre : String) : List String :=
  Id.run do
    let mut result : List String := []
    for string in strings do
      if string.startsWith pre then
        result := result ++ [string]
    return result

example : filterByPrefixImperative [] "john" = [] := by native_decide

example :
    filterByPrefixImperative
        ["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" =
      ["xxx", "xxxAAA", "xxx"] := by native_decide

#eval filterByPrefixImperative ["abc", "bcd", "cde", "array"] "a"

/-- Loop invariant: starting with `acc` produces the old accumulator followed
by the functional result for the still-unvisited input. -/
theorem filterByPrefixImperative_loop
    (strings acc : List String) (pre : String) :
    (Id.run do
      let mut result := acc
      for string in strings do
        if string.startsWith pre then
          result := result ++ [string]
      return result) =
      acc ++ filterByPrefix strings pre := by
  induction strings generalizing acc with
  | nil => simp [filterByPrefix]
  | cons string strings ih =>
      by_cases h : string.startsWith pre = true
      · simp only [Id.run, List.forIn_cons, h, if_true]
        change
          (Id.run do
            let mut result := acc ++ [string]
            for remaining in strings do
              if remaining.startsWith pre then
                result := result ++ [remaining]
            return result) =
            acc ++ filterByPrefix (string :: strings) pre
        rw [ih (acc ++ [string])]
        simp [filterByPrefix, h, List.append_assoc]
      · simp only [Id.run, List.forIn_cons, h]
        change
          (Id.run do
            let mut result := acc
            for remaining in strings do
              if remaining.startsWith pre then
                result := result ++ [remaining]
            return result) =
            acc ++ filterByPrefix (string :: strings) pre
        rw [ih acc]
        simp [filterByPrefix, h]

theorem filterByPrefix_equiv (strings : List String) (pre : String) :
    filterByPrefix strings pre = filterByPrefixImperative strings pre := by
  rw [filterByPrefixImperative]
  simpa using (filterByPrefixImperative_loop strings [] pre).symm

end humaneval_29_filter_by_prefix

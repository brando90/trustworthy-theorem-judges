import Mathlib

/-!
# All prefixes of a string

This file formalizes HumanEval problem 14.  The function returns every nonempty
prefix of its input, ordered from shortest to longest.  String lengths and
slices are measured in Unicode characters, as they are in the Python program.
-/

namespace humaneval_14_all_prefixes

/-- The first `n` Unicode characters of a string. -/
def takePrefix (string : String) (n : Nat) : String :=
  String.mk (string.data.take n)

/-- Return all nonempty prefixes of `string`, shortest first. -/
def allPrefixes (string : String) : List String :=
  (List.range string.length).map fun i => takePrefix string (i + 1)

example : allPrefixes "" = [] := by native_decide
example : allPrefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide
example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by native_decide
example : allPrefixes "L∃" = ["L", "L∃"] := by native_decide

#eval allPrefixes "abc"

/-- The Python function accepts every string. -/
def Pre (_string : String) : Prop := True

/-- The result has one entry for each character of the input. -/
def length_prop (string : String) (result : List String) : Prop :=
  result.length = string.length

/-- Entry `i` is precisely the prefix containing the first `i + 1` characters. -/
def entries_prop (string : String) (result : List String) : Prop :=
  ∀ (i : Nat) (h : i < result.length), result[i] = takePrefix string (i + 1)

/-- A nonempty input occurs itself as the last (longest) prefix. -/
def final_prop (string : String) (result : List String) : Prop :=
  0 < string.length → result.getLast? = some string

theorem length_thm (string : String) :
    length_prop string (allPrefixes string) := by
  simp [length_prop, allPrefixes]

theorem entries_thm (string : String) :
    entries_prop string (allPrefixes string) := by
  intro i h
  simp only [allPrefixes, List.length_map, List.length_range] at h ⊢
  simp [List.getElem_map]

theorem final_thm (string : String) :
    final_prop string (allPrefixes string) := by
  intro hlen
  simp only [allPrefixes, List.getLast?_map]
  rw [List.getLast?_range]
  have hindex : string.length - 1 + 1 = string.length :=
    Nat.sub_add_cancel hlen
  simp only [Nat.ne_of_gt hlen, ↓reduceIte, Option.map_some, hindex]
  congr 1
  apply String.ext
  simp [takePrefix]

/-- Complete post-condition for `allPrefixes`. -/
def Post_prop (string : String) (result : List String) : Prop :=
  length_prop string result ∧ entries_prop string result ∧ final_prop string result

/-- The functional implementation meets its full specification. -/
theorem allPrefixes_correct (string : String) :
    Pre string → Post_prop string (allPrefixes string) := by
  intro _
  exact ⟨length_thm string, entries_thm string, final_thm string⟩

/-- An imperative-style translation of the Python loop. -/
def allPrefixesImperative (string : String) : List String := Id.run do
  let mut result : List String := []
  for i in [0:string.length] do
    result := result ++ [takePrefix string (i + 1)]
  return result

example : allPrefixesImperative "" = [] := by native_decide
example : allPrefixesImperative "asdfgh" =
    ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixesImperative "WWW" = ["W", "WW", "WWW"] := by native_decide

#eval allPrefixesImperative "abc"

/-- The functional and imperative translations compute identical results. -/
theorem allPrefixes_equiv (string : String) :
    allPrefixes string = allPrefixesImperative string := by
  simp [allPrefixes, allPrefixesImperative]
  have range_zero (n : Nat) : List.range' 0 n = List.range n := by
    rw [List.range'_eq_map_range]
    simp
  rw [range_zero]
  have singleton_flatten (xs : List Nat) :
      (xs.map fun i => [takePrefix string (i + 1)]).flatten =
        xs.map fun i => takePrefix string (i + 1) := by
    induction xs with
    | nil => rfl
    | cons i xs ih => simp [ih]
  exact (singleton_flatten (List.range string.length)).symm

end humaneval_14_all_prefixes

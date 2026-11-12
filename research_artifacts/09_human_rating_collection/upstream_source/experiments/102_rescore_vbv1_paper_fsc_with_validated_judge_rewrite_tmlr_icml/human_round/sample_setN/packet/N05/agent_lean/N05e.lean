import Mathlib
import Plausible

/-!
# Duplicate characters (task 41)

Python source under formalisation:

```python
def pre(s: str) -> bool:
    return isinstance(s, str)

def duplicate_chars(s: str) -> str:
    if not pre(s):
        raise ValueError("Input must be a string")
    return ''.join(c * 2 for c in s)
```

`duplicate_chars` returns a new string in which every character of the input
string is duplicated, e.g. `"abc" ↦ "aabbcc"`. The Python precondition
`isinstance(s, str)` is trivially satisfied for statically typed Lean
`String` inputs, so the `ValueError` branch is unreachable here and `Pre`
holds on the whole domain.
-/

namespace DuplicateChars41

/-! ## Functional implementation -/

/-- Duplicate each character of the input string (functional version). -/
def duplicateChars (s : String) : String :=
  String.mk (s.toList.flatMap fun c => [c, c])

-- Unit tests -----------------------------------------------------------------

example : duplicateChars "abc" = "aabbcc" := by native_decide

example : duplicateChars "" = "" := by native_decide

example : duplicateChars "!a " = "!!aa  " := by native_decide

#eval duplicateChars "abc"    -- "aabbcc"
#eval duplicateChars ""       -- ""
#eval duplicateChars "!a "    -- "!!aa  "

-- The Python negative test `candidate(None)` raises `ValueError`; in Lean the
-- input type `String` rules out non-string inputs at compile time, so there is
-- no corresponding failing call to test.

/-! ## Precondition -/

/-- Precondition: the Python `pre` is `isinstance(s, str)`, which holds for
every Lean `String`. -/
def Pre (_s : String) : Prop := True

/-! ## Properties -/

/-- Specification properties of `duplicateChars s`:
1. at the level of character lists it is exactly `flatMap (fun c => [c, c])`;
2. its length is twice the length of the input. -/
def duplicateChars_prop (s : String) : Prop :=
  (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c]) ∧
  (duplicateChars s).length = 2 * s.length

theorem length_flatMap_pair (xs : List Char) :
    (xs.flatMap fun c => [c, c]).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons c cs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      omega

theorem duplicateChars_thm (s : String) : duplicateChars_prop s := by
  refine ⟨rfl, ?_⟩
  cases s with
  | mk data => exact length_flatMap_pair data

/-! ## Postcondition -/

/-- Postcondition: the conjunction of the specification properties. -/
def Post_prop (s : String) : Prop := duplicateChars_prop s

/-! ## Property-based tests -/

/-- Executable Boolean form of `duplicateChars_prop`. -/
def checkDuplicateCharsProp (s : String) : Bool :=
  ((duplicateChars s).toList == s.toList.flatMap (fun c => [c, c])) &&
  ((duplicateChars s).length == 2 * s.length)

/-- Small set of test strings used for the bounded property-based tests. -/
def pbtStrings : List String :=
  ["", "a", "b", "ab", "abc", "!a ", "hello", "  ", "xy z",
   "é2", "αβγ", "The quick brown fox", "00", "aáâ"]

-- Bounded PBT for `duplicateChars_prop` (executable Boolean form).
example : pbtStrings.all checkDuplicateCharsProp = true := by native_decide

-- Bounded PBT for the postcondition (`Post_prop` unfolds to the same check).
example : pbtStrings.all (fun s => checkDuplicateCharsProp s) = true := by
  native_decide

-- Randomized PBT (Plausible) for the executable form of the properties.
#eval Plausible.Testable.check (∀ s : String, checkDuplicateCharsProp s = true)

/-! ## Correctness theorem -/

theorem duplicateChars_correct (s : String) (_h : Pre s) : Post_prop s :=
  duplicateChars_thm s

/-! ## Imperative implementation -/

/-- Imperative implementation using `Id.run` with mutable state. -/
def duplicateCharsImp (s : String) : String := Id.run do
  let mut out : List Char := []
  out := s.toList.foldl (fun acc c => acc ++ [c, c]) out
  return String.mk out

-- Imperative tests -----------------------------------------------------------

example : duplicateCharsImp "abc" = "aabbcc" := by native_decide

example : duplicateCharsImp "" = "" := by native_decide

example : duplicateCharsImp "!a " = "!!aa  " := by native_decide

#eval duplicateCharsImp "abc"   -- "aabbcc"

/-! ## Equivalence of the two implementations -/

theorem foldl_pair (xs : List Char) (acc : List Char) :
    xs.foldl (fun acc c => acc ++ [c, c]) acc = acc ++ xs.flatMap (fun c => [c, c]) := by
  induction xs generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih, ← List.append_assoc]

theorem duplicateChars_imp_eq (s : String) :
    duplicateCharsImp s = duplicateChars s := by
  show String.mk (s.toList.foldl (fun acc c => acc ++ [c, c]) []) =
    String.mk (s.toList.flatMap fun c => [c, c])
  rw [foldl_pair]
  exact congrArg String.mk (List.nil_append _)

end DuplicateChars41

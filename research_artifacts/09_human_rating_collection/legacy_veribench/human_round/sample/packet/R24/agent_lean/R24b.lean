import Mathlib

/-!
# Duplicate each character in a string

Lean 4 formalization of the Python program `duplicate_chars`, which returns a new
string where every character of the input is repeated twice
(`"abc" ↦ "aabbcc"`, `"" ↦ ""`, `"!a " ↦ "!!aa  "`).

In Python the function first checks `isinstance(s, str)` and raises `ValueError`
otherwise; in Lean the argument is already typed as `String`, so the
pre-condition `Pre` is vacuously satisfied for every well-typed input.

The file contains:
* a functional implementation (`duplicateChars`),
* unit tests mirroring the Python doctests / `check`,
* the pre-condition, individual properties with proofs, and the post-condition,
* the correctness theorem `Pre → Post`,
* an imperative implementation using `Id.run do` with mutable state, and
* the equivalence theorem between the two implementations.
-/

namespace «41_duplicate_chars»

/-! ## Functional implementation -/

/-- Duplicate every character of `s`: `''.join(c * 2 for c in s)`. -/
def duplicateChars (s : String) : String :=
  ⟨s.data.flatMap (fun c => [c, c])⟩

/-! ## Unit tests (functional) -/

example : duplicateChars "abc" = "aabbcc" := by native_decide
example : duplicateChars "" = "" := by native_decide
example : duplicateChars "!a " = "!!aa  " := by native_decide

#eval duplicateChars "abc"   -- "aabbcc"
#eval duplicateChars ""      -- ""
#eval duplicateChars "!a "   -- "!!aa  "

/-! ## Pre-condition -/

/-- Python's `pre(s)` is `isinstance(s, str)`. Every value of Lean's `String`
type is a string, so the pre-condition holds unconditionally. -/
def Pre (_s : String) : Prop := True

theorem Pre_holds (s : String) : Pre s := trivial

/-! ## Properties -/

/-- The character list of the result is obtained by doubling every character. -/
def data_prop (s : String) : Prop :=
  (duplicateChars s).data = s.data.flatMap (fun c => [c, c])

theorem data_thm (s : String) : data_prop s := rfl

/-- The result has exactly twice as many characters as the input. -/
def length_prop (s : String) : Prop :=
  (duplicateChars s).length = 2 * s.length

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop
  rw [← String.length_data, ← String.length_data, data_thm s]
  simp [List.length_flatMap]
  ring

/-- The empty string is mapped to the empty string. -/
def empty_prop : Prop :=
  duplicateChars "" = ""

theorem empty_thm : empty_prop := rfl

/-- Positions `2*i` and `2*i+1` of the result both hold the `i`-th input
character (and are out of range exactly when `i` is). -/
def index_prop (s : String) : Prop :=
  ∀ i : Nat,
    (duplicateChars s).data[2 * i]? = s.data[i]? ∧
    (duplicateChars s).data[2 * i + 1]? = s.data[i]?

private theorem list_index_aux (l : List Char) (i : Nat) :
    (l.flatMap (fun c => [c, c]))[2 * i]? = l[i]? ∧
    (l.flatMap (fun c => [c, c]))[2 * i + 1]? = l[i]? := by
  induction l generalizing i with
  | nil => simp
  | cons c t ih =>
    cases i with
    | zero => simp
    | succ j =>
      have h1 : 2 * (j + 1) = (2 * j) + 1 + 1 := by ring
      have h2 : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
      simpa [h1, h2] using ih j

theorem index_thm (s : String) : index_prop s := by
  intro i
  rw [data_thm s]
  exact list_index_aux s.data i

/-- Duplication distributes over concatenation. -/
def append_prop (s t : String) : Prop :=
  duplicateChars (s ++ t) = duplicateChars s ++ duplicateChars t

theorem append_thm (s t : String) : append_prop s t := by
  unfold append_prop duplicateChars
  simp [String.ext_iff, String.data_append, List.flatMap_append]

/-- Every character occurs exactly twice as often in the result. -/
def count_prop (s : String) (c : Char) : Prop :=
  (duplicateChars s).data.count c = 2 * s.data.count c

theorem count_thm (s : String) (c : Char) : count_prop s c := by
  unfold count_prop
  rw [data_thm s]
  induction s.data with
  | nil => simp
  | cons a t ih =>
    by_cases h : a = c <;> simp [h, ih] <;> ring

/-- The result is empty iff the input is empty. -/
def isEmpty_prop (s : String) : Prop :=
  duplicateChars s = "" ↔ s = ""

theorem isEmpty_thm (s : String) : isEmpty_prop s := by
  unfold isEmpty_prop duplicateChars
  constructor
  · intro h
    have h' : s.data.flatMap (fun c => [c, c]) = [] := congrArg String.data h
    cases s with
    | mk data => cases data with
      | nil => rfl
      | cons a t => simp at h'
  · intro h
    subst h
    rfl

/-! ## Post-condition -/

/-- Full post-condition: the conjunction of all the properties above. -/
def Post_prop (s : String) : Prop :=
  data_prop s ∧
  length_prop s ∧
  index_prop s ∧
  isEmpty_prop s ∧
  (∀ c : Char, count_prop s c) ∧
  (∀ t : String, append_prop s t)

theorem Post_thm (s : String) : Post_prop s :=
  ⟨data_thm s, length_thm s, index_thm s, isEmpty_thm s,
   fun c => count_thm s c, fun t => append_thm s t⟩

/-! ## Correctness -/

/-- Correctness: whenever the pre-condition holds, so does the post-condition. -/
theorem duplicateChars_correct (s : String) (_h : Pre s) : Post_prop s :=
  Post_thm s

/-! ## Imperative implementation -/

/-- Imperative version: walk over the characters, pushing each one twice onto a
mutable accumulator string. -/
def duplicateCharsImp (s : String) : String := Id.run do
  let mut out : String := ""
  for c in s.data do
    out := out.push c
    out := out.push c
  return out

/-! ## Unit tests (imperative) -/

example : duplicateCharsImp "abc" = "aabbcc" := by native_decide
example : duplicateCharsImp "" = "" := by native_decide
example : duplicateCharsImp "!a " = "!!aa  " := by native_decide

#eval duplicateCharsImp "abc"   -- "aabbcc"
#eval duplicateCharsImp ""      -- ""
#eval duplicateCharsImp "!a "   -- "!!aa  "

/-! ## Equivalence of the two implementations -/

private theorem foldl_push_aux (l : List Char) (acc : String) :
    List.foldl (fun b a => (b.push a).push a) acc l
      = ⟨acc.data ++ l.flatMap (fun c => [c, c])⟩ := by
  induction l generalizing acc with
  | nil => simp
  | cons c t ih => simp [ih]

/-- The functional and the imperative implementation agree on every input. -/
theorem duplicateChars_eq_imp (s : String) :
    duplicateChars s = duplicateCharsImp s := by
  simp [duplicateChars, duplicateCharsImp, Id.run, foldl_push_aux]
  rfl

/-- The imperative implementation also satisfies the post-condition. -/
theorem duplicateCharsImp_correct (s : String) (_h : Pre s) :
    Post_prop s := Post_thm s

end «41_duplicate_chars»

import Mathlib

/-!
# Levenshtein edit distance

Lean 4 formalization of the Python program `edit_distance.py`:

```python
def edit_distance(s1, s2) -> int:
    # Levenshtein distance between two sequences (str or list), computed with a
    # (m+1) x (n+1) dynamic-programming table:
    #   dp[i][0] = i, dp[0][j] = j,
    #   dp[i][j] = dp[i-1][j-1]                                   if s1[i-1] == s2[j-1]
    #            = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])  otherwise
    # Inputs that are neither `str` nor `list` raise ValueError.
```

* A Python `str` is modelled as `List Char`, a Python `list` as `List α` with decidable
  equality on the elements (Python's `==`).  The `isinstance` pre-condition of the Python
  code is enforced by the Lean type system, so `Pre` is trivially true; the `ValueError`
  branch is modelled separately by `PyInput` / `editDistanceChecked` at the end of the file.
* `editDistance` is the functional (recursive) definition; `editDistanceImp` mirrors the
  Python DP table imperatively (mutable 2-D array, nested `for` loops) and is proved equal.
* The docstring's defining property -- "minimum number of single-element edits
  (insertions, deletions, substitutions) required to change one sequence into another" --
  is formalised by the inductive `Edits` and the theorem `editDistance_is_min_edits_thm`.
-/

namespace edit_distance

variable {α : Type} [DecidableEq α]

/-! ## Functional implementation -/

/-- Levenshtein edit distance of two sequences (recursive formulation of the DP recurrence). -/
def editDistance : List α → List α → Nat
  | [], ys => ys.length
  | xs, [] => xs.length
  | x :: xs, y :: ys =>
    if x = y then editDistance xs ys
    else 1 + min (editDistance xs (y :: ys)) (min (editDistance (x :: xs) ys) (editDistance xs ys))

/-- Edit distance of two Python `str` values (strings are sequences of characters). -/
def editDistanceStr (s1 s2 : String) : Nat :=
  editDistance s1.toList s2.toList

/-! ### Equation lemmas -/

@[simp] theorem editDistance_nil_left (ys : List α) : editDistance [] ys = ys.length := by
  rw [editDistance]

@[simp] theorem editDistance_nil_right (xs : List α) : editDistance xs [] = xs.length := by
  cases xs <;> rw [editDistance]

theorem editDistance_cons_cons (x y : α) (xs ys : List α) :
    editDistance (x :: xs) (y :: ys) =
      if x = y then editDistance xs ys
      else 1 + min (editDistance xs (y :: ys))
                   (min (editDistance (x :: xs) ys) (editDistance xs ys)) := by
  rw [editDistance]

theorem editDistance_cons_cons_same (x : α) (xs ys : List α) :
    editDistance (x :: xs) (x :: ys) = editDistance xs ys := by
  rw [editDistance_cons_cons, if_pos rfl]

theorem editDistance_cons_cons_ne {x y : α} (h : x ≠ y) (xs ys : List α) :
    editDistance (x :: xs) (y :: ys) =
      1 + min (editDistance xs (y :: ys))
              (min (editDistance (x :: xs) ys) (editDistance xs ys)) := by
  rw [editDistance_cons_cons, if_neg h]

/-! ## Unit tests (the assertions of the Python `check` function) -/

-- strings
example : editDistanceStr "hello" "hello" = 0 := by native_decide
example : editDistanceStr "cat" "bat" = 1 := by native_decide
example : editDistanceStr "cat" "cats" = 1 := by native_decide
example : editDistanceStr "cats" "cat" = 1 := by native_decide
example : editDistanceStr "cat" "dog" = 3 := by native_decide
example : editDistanceStr "kitten" "sitting" = 3 := by native_decide
-- edge cases
example : editDistanceStr "" "" = 0 := by native_decide
example : editDistanceStr "" "abc" = 3 := by native_decide
example : editDistanceStr "ab" "" = 2 := by native_decide
example : editDistanceStr "a" "b" = 1 := by native_decide
-- lists of integers
example : editDistance [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : editDistance [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : editDistance [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : editDistance [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : editDistance [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide
-- lists of characters
example : editDistance ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide
example : editDistance ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : editDistance ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : editDistance ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide
-- longer sequences
example : editDistanceStr "intention" "execution" = 5 := by native_decide
example : editDistanceStr "saturday" "sunday" = 3 := by native_decide
-- same length, all different
example : editDistanceStr "abc" "def" = 3 := by native_decide
example : editDistanceStr "xyz" "abc" = 3 := by native_decide
-- one character strings
example : editDistanceStr "a" "a" = 0 := by native_decide
example : editDistanceStr "a" "b" = 1 := by native_decide
example : editDistanceStr "a" "" = 1 := by native_decide
example : editDistanceStr "" "a" = 1 := by native_decide
-- repeated characters
example : editDistanceStr "aaa" "aa" = 1 := by native_decide
example : editDistanceStr "aa" "aaa" = 1 := by native_decide
example : editDistanceStr "aaaa" "bbbb" = 4 := by native_decide

#eval editDistanceStr "kitten" "sitting"          -- 3
#eval editDistanceStr "intention" "execution"     -- 5
#eval editDistance [1, 2, 3, 4, 5] [6, 7, 8]      -- 5
#eval editDistance ([] : List Nat) []             -- 0

/-! ## Pre-condition

The Python pre-condition `isinstance(s1, (str, list)) and isinstance(s2, (str, list))`
is enforced statically by the Lean types (`List α`, with `String` entering via `toList`),
so every well-typed input is admissible. -/

/-- Pre-condition: all typed inputs are admissible sequences. -/
def Pre (_s1 _s2 : List α) : Prop := True

/-! ## Properties -/

/-- Basic structural facts used by the later proofs. -/
theorem editDistance_comm : ∀ (xs ys : List α), editDistance xs ys = editDistance ys xs
  | [], ys => by simp
  | x :: xs, [] => by simp
  | x :: xs, y :: ys => by
    have h1 := editDistance_comm xs ys
    have h2 := editDistance_comm xs (y :: ys)
    have h3 := editDistance_comm (x :: xs) ys
    rw [editDistance_cons_cons, editDistance_cons_cons]
    by_cases hxy : x = y
    · subst hxy; simp [h1]
    · have hyx : y ≠ x := fun h => hxy h.symm
      rw [if_neg hxy, if_neg hyx, h1, h2, h3]
      omega
termination_by xs ys => xs.length + ys.length

/-- Prepending (or removing) one element on the left changes the distance by at most one. -/
theorem editDistance_cons_bound : ∀ (xs ys : List α) (x : α),
    editDistance (x :: xs) ys ≤ editDistance xs ys + 1 ∧
    editDistance xs ys ≤ editDistance (x :: xs) ys + 1
  | xs, [], x => by simp
  | xs, y :: ys, x => by
    have ih1 := editDistance_cons_bound ys xs y
    have ih2 := editDistance_cons_bound xs ys x
    rw [editDistance_comm (y :: ys) xs, editDistance_comm ys xs] at ih1
    rw [editDistance_cons_cons]
    by_cases hxy : x = y
    · subst hxy; rw [if_pos rfl]; omega
    · rw [if_neg hxy]; omega
termination_by xs ys x => xs.length + ys.length

/-- Appending one element on the right of both arguments: the Python DP recurrence
(which looks at the *last* elements of the prefixes `s1[:i]`, `s2[:j]`). -/
theorem editDistance_snoc_snoc (a b : α) : ∀ (xs ys : List α),
    editDistance (xs ++ [a]) (ys ++ [b]) =
      if a = b then editDistance xs ys
      else 1 + min (editDistance xs (ys ++ [b]))
                   (min (editDistance (xs ++ [a]) ys) (editDistance xs ys))
  | [], [] => by
    simp only [List.nil_append, editDistance_cons_cons, editDistance_nil_left,
      editDistance_nil_right, List.length_nil, List.length_singleton]
  | [], y :: ys => by
    have ih := editDistance_snoc_snoc a b [] ys
    simp only [List.nil_append, List.cons_append] at *
    rw [editDistance_cons_cons a y [] (ys ++ [b]), editDistance_cons_cons a y [] ys]
    simp only [editDistance_nil_left, editDistance_nil_right, List.length_cons,
      List.length_append, List.length_singleton, List.length_nil] at *
    split_ifs at * <;> omega
  | x :: xs, [] => by
    have ih := editDistance_snoc_snoc a b xs []
    simp only [List.nil_append, List.cons_append] at *
    rw [editDistance_cons_cons x b (xs ++ [a]) [], editDistance_cons_cons x b xs []]
    simp only [editDistance_nil_left, editDistance_nil_right, List.length_cons,
      List.length_append, List.length_singleton, List.length_nil] at *
    split_ifs at * <;> omega
  | x :: xs, y :: ys => by
    have ih1 := editDistance_snoc_snoc a b xs ys
    have ih2 := editDistance_snoc_snoc a b xs (y :: ys)
    have ih3 := editDistance_snoc_snoc a b (x :: xs) ys
    simp only [List.cons_append] at *
    rw [editDistance_cons_cons x y (xs ++ [a]) (ys ++ [b]),
      editDistance_cons_cons x y xs (ys ++ [b]), editDistance_cons_cons x y (xs ++ [a]) ys,
      editDistance_cons_cons x y xs ys]
    split_ifs at * <;> omega
termination_by xs ys => xs.length + ys.length

/-- Property: the distance of a sequence to itself is zero. -/
def editDistance_self_prop (s : List α) : Prop := editDistance s s = 0

theorem editDistance_self_thm (s : List α) : editDistance_self_prop s := by
  unfold editDistance_self_prop
  induction s with
  | nil => simp
  | cons x s ih => rw [editDistance_cons_cons_same, ih]

/-- Property: the distance from the empty sequence is the length (pure insertions). -/
def editDistance_nil_left_prop (s : List α) : Prop := editDistance [] s = s.length

theorem editDistance_nil_left_thm (s : List α) : editDistance_nil_left_prop s := by
  unfold editDistance_nil_left_prop; simp

/-- Property: the distance to the empty sequence is the length (pure deletions). -/
def editDistance_nil_right_prop (s : List α) : Prop := editDistance s [] = s.length

theorem editDistance_nil_right_thm (s : List α) : editDistance_nil_right_prop s := by
  unfold editDistance_nil_right_prop; simp

/-- Property: symmetry. -/
def editDistance_comm_prop (s1 s2 : List α) : Prop := editDistance s1 s2 = editDistance s2 s1

theorem editDistance_comm_thm (s1 s2 : List α) : editDistance_comm_prop s1 s2 :=
  editDistance_comm s1 s2

/-- Property: the distance is zero exactly for equal sequences. -/
def editDistance_eq_zero_iff_prop (s1 s2 : List α) : Prop := editDistance s1 s2 = 0 ↔ s1 = s2

theorem editDistance_eq_zero_iff_thm : ∀ (s1 s2 : List α), editDistance_eq_zero_iff_prop s1 s2
  | [], ys => by
    unfold editDistance_eq_zero_iff_prop
    simp [eq_comm]
  | x :: xs, [] => by
    unfold editDistance_eq_zero_iff_prop
    simp
  | x :: xs, y :: ys => by
    unfold editDistance_eq_zero_iff_prop
    have ih := editDistance_eq_zero_iff_thm xs ys
    unfold editDistance_eq_zero_iff_prop at ih
    rw [editDistance_cons_cons]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, ih]
      simp
    · rw [if_neg hxy]
      constructor
      · intro h; omega
      · intro h; exact absurd (List.cons.inj h).1 hxy
termination_by s1 s2 => s1.length + s2.length

/-- Property: upper bound by the longer length (substitute, then insert/delete the rest). -/
def editDistance_le_max_prop (s1 s2 : List α) : Prop :=
  editDistance s1 s2 ≤ max s1.length s2.length

theorem editDistance_le_max_thm : ∀ (s1 s2 : List α), editDistance_le_max_prop s1 s2
  | [], ys => by unfold editDistance_le_max_prop; simp
  | x :: xs, [] => by unfold editDistance_le_max_prop; simp
  | x :: xs, y :: ys => by
    have ih := editDistance_le_max_thm xs ys
    unfold editDistance_le_max_prop at *
    rw [editDistance_cons_cons]
    simp only [List.length_cons]
    split_ifs <;> omega
termination_by s1 s2 => s1.length + s2.length

/-- Property: lower bound by the length difference (each insertion/deletion changes the
length by one). -/
def length_diff_le_editDistance_prop (s1 s2 : List α) : Prop :=
  s1.length - s2.length ≤ editDistance s1 s2 ∧ s2.length - s1.length ≤ editDistance s1 s2

theorem length_diff_le_editDistance_thm : ∀ (s1 s2 : List α), length_diff_le_editDistance_prop s1 s2
  | [], ys => by unfold length_diff_le_editDistance_prop; simp
  | x :: xs, [] => by unfold length_diff_le_editDistance_prop; simp
  | x :: xs, y :: ys => by
    have ih1 := length_diff_le_editDistance_thm xs ys
    have ih2 := length_diff_le_editDistance_thm xs (y :: ys)
    have ih3 := length_diff_le_editDistance_thm (x :: xs) ys
    unfold length_diff_le_editDistance_prop at *
    rw [editDistance_cons_cons]
    simp only [List.length_cons] at *
    split_ifs <;> omega
termination_by s1 s2 => s1.length + s2.length

/-- Property: a single element on the left changes the distance by at most one
(in either direction). -/
def editDistance_cons_bound_prop (x : α) (s1 s2 : List α) : Prop :=
  editDistance (x :: s1) s2 ≤ editDistance s1 s2 + 1 ∧
  editDistance s1 s2 ≤ editDistance (x :: s1) s2 + 1

theorem editDistance_cons_bound_thm (x : α) (s1 s2 : List α) : editDistance_cons_bound_prop x s1 s2 :=
  editDistance_cons_bound s1 s2 x

/-- Property: the recurrence on first elements (match / substitute / delete / insert). -/
def editDistance_cons_cons_prop (x y : α) (s1 s2 : List α) : Prop :=
  editDistance (x :: s1) (y :: s2) =
    if x = y then editDistance s1 s2
    else 1 + min (editDistance s1 (y :: s2)) (min (editDistance (x :: s1) s2) (editDistance s1 s2))

theorem editDistance_cons_cons_thm (x y : α) (s1 s2 : List α) : editDistance_cons_cons_prop x y s1 s2 :=
  editDistance_cons_cons x y s1 s2

/-- Property: the Python DP recurrence on last elements. -/
def editDistance_snoc_snoc_prop (a b : α) (s1 s2 : List α) : Prop :=
  editDistance (s1 ++ [a]) (s2 ++ [b]) =
    if a = b then editDistance s1 s2
    else 1 + min (editDistance s1 (s2 ++ [b])) (min (editDistance (s1 ++ [a]) s2) (editDistance s1 s2))

theorem editDistance_snoc_snoc_thm (a b : α) (s1 s2 : List α) : editDistance_snoc_snoc_prop a b s1 s2 :=
  editDistance_snoc_snoc a b s1 s2

/-- Property: reversing both sequences preserves the distance. -/
def editDistance_reverse_prop (s1 s2 : List α) : Prop :=
  editDistance s1.reverse s2.reverse = editDistance s1 s2

theorem editDistance_reverse_thm : ∀ (s1 s2 : List α), editDistance_reverse_prop s1 s2
  | [], ys => by unfold editDistance_reverse_prop; simp
  | x :: xs, [] => by unfold editDistance_reverse_prop; simp
  | x :: xs, y :: ys => by
    have ih1 := editDistance_reverse_thm xs ys
    have ih2 := editDistance_reverse_thm xs (y :: ys)
    have ih3 := editDistance_reverse_thm (x :: xs) ys
    unfold editDistance_reverse_prop at *
    rw [List.reverse_cons] at ih2 ih3
    rw [List.reverse_cons, List.reverse_cons, editDistance_snoc_snoc, editDistance_cons_cons,
      ih1, ih2, ih3]
termination_by s1 s2 => s1.length + s2.length

/-- Property: a common prefix does not change the distance. -/
def editDistance_append_left_prop (p s1 s2 : List α) : Prop :=
  editDistance (p ++ s1) (p ++ s2) = editDistance s1 s2

theorem editDistance_append_left_thm (p s1 s2 : List α) : editDistance_append_left_prop p s1 s2 := by
  unfold editDistance_append_left_prop
  induction p with
  | nil => simp
  | cons a p ih => simp only [List.cons_append]; rw [editDistance_cons_cons_same, ih]

/-- Property: a common suffix does not change the distance. -/
def editDistance_append_right_prop (s1 s2 p : List α) : Prop :=
  editDistance (s1 ++ p) (s2 ++ p) = editDistance s1 s2

theorem editDistance_append_right_thm (s1 s2 p : List α) : editDistance_append_right_prop s1 s2 p := by
  unfold editDistance_append_right_prop
  have h := editDistance_reverse_thm (s1 ++ p) (s2 ++ p)
  unfold editDistance_reverse_prop at h
  rw [← h, List.reverse_append, List.reverse_append]
  have h2 := editDistance_append_left_thm p.reverse s1.reverse s2.reverse
  unfold editDistance_append_left_prop at h2
  rw [h2]
  exact editDistance_reverse_thm s1 s2

/-- Property: triangle inequality (together with symmetry and `eq_zero_iff`, the edit
distance is a metric on sequences). -/
def editDistance_triangle_prop (s1 s2 s3 : List α) : Prop :=
  editDistance s1 s3 ≤ editDistance s1 s2 + editDistance s2 s3

theorem editDistance_triangle_thm : ∀ (s1 s2 s3 : List α), editDistance_triangle_prop s1 s2 s3
  | xs, [], zs => by
    unfold editDistance_triangle_prop
    have h := editDistance_le_max_thm xs zs
    unfold editDistance_le_max_prop at h
    simp only [editDistance_nil_left, editDistance_nil_right]
    omega
  | [], y :: ys, zs => by
    unfold editDistance_triangle_prop
    have h := length_diff_le_editDistance_thm (y :: ys) zs
    unfold length_diff_le_editDistance_prop at h
    simp only [editDistance_nil_left]
    omega
  | x :: xs, y :: ys, [] => by
    unfold editDistance_triangle_prop
    have h := length_diff_le_editDistance_thm (x :: xs) (y :: ys)
    unfold length_diff_le_editDistance_prop at h
    simp only [editDistance_nil_right]
    omega
  | x :: xs, y :: ys, z :: zs => by
    have i1 := editDistance_triangle_thm xs ys zs
    have i2 := editDistance_triangle_thm xs (y :: ys) zs
    have i3 := editDistance_triangle_thm xs ys (z :: zs)
    have i4 := editDistance_triangle_thm (x :: xs) ys zs
    have i5 := editDistance_triangle_thm xs (y :: ys) (z :: zs)
    have i6 := editDistance_triangle_thm (x :: xs) (y :: ys) zs
    have i7 := editDistance_triangle_thm (x :: xs) ys (z :: zs)
    unfold editDistance_triangle_prop at *
    have b1 := editDistance_cons_bound xs ys x
    have b2 := editDistance_cons_bound xs (y :: ys) x
    have b3 := editDistance_cons_bound ys zs y
    have b4 := editDistance_cons_bound ys (z :: zs) y
    have b5 := editDistance_cons_bound xs zs x
    have b6 := editDistance_cons_bound xs (z :: zs) x
    have c1 := editDistance_cons_bound ys xs y
    have c2 := editDistance_cons_bound ys (x :: xs) y
    have c3 := editDistance_cons_bound zs ys z
    have c4 := editDistance_cons_bound zs (y :: ys) z
    have c5 := editDistance_cons_bound zs xs z
    have c6 := editDistance_cons_bound zs (x :: xs) z
    rw [editDistance_comm (y :: ys) xs, editDistance_comm ys xs] at c1
    rw [editDistance_comm (y :: ys) (x :: xs), editDistance_comm ys (x :: xs)] at c2
    rw [editDistance_comm (z :: zs) ys, editDistance_comm zs ys] at c3
    rw [editDistance_comm (z :: zs) (y :: ys), editDistance_comm zs (y :: ys)] at c4
    rw [editDistance_comm (z :: zs) xs, editDistance_comm zs xs] at c5
    rw [editDistance_comm (z :: zs) (x :: xs), editDistance_comm zs (x :: xs)] at c6
    by_cases hxy : x = y <;> by_cases hyz : y = z <;> by_cases hxz : x = z
    all_goals
      simp only [editDistance_cons_cons x y, editDistance_cons_cons y z,
        editDistance_cons_cons x z, hxy, hyz, hxz, ↓reduceIte] at *
    all_goals omega
termination_by s1 s2 s3 => s1.length + s2.length + s3.length

/-! ### Edit scripts: the docstring's defining property

`Edits xs ys k` holds when `xs` can be transformed into `ys` by an alignment using exactly
`k` single-element edits (substitutions, deletions and insertions; matching elements are
kept for free).  The edit distance is the least such `k`. -/

/-- `Edits xs ys k`: `xs` can be turned into `ys` with exactly `k` single-element edits. -/
inductive Edits : List α → List α → Nat → Prop
  | nil : Edits [] [] 0
  | keep (a : α) {xs ys : List α} {k : Nat} : Edits xs ys k → Edits (a :: xs) (a :: ys) k
  | sub (a b : α) {xs ys : List α} {k : Nat} : Edits xs ys k → Edits (a :: xs) (b :: ys) (k + 1)
  | del (a : α) {xs ys : List α} {k : Nat} : Edits xs ys k → Edits (a :: xs) ys (k + 1)
  | ins (b : α) {xs ys : List α} {k : Nat} : Edits xs ys k → Edits xs (b :: ys) (k + 1)

theorem edits_nil_left (ys : List α) : Edits [] ys ys.length := by
  induction ys with
  | nil => exact Edits.nil
  | cons y ys ih => exact Edits.ins y ih

theorem edits_nil_right (xs : List α) : Edits xs [] xs.length := by
  induction xs with
  | nil => exact Edits.nil
  | cons x xs ih => exact Edits.del x ih

/-- The edit distance is achieved by some edit script. -/
theorem edits_editDistance : ∀ (xs ys : List α), Edits xs ys (editDistance xs ys)
  | [], ys => by rw [editDistance_nil_left]; exact edits_nil_left ys
  | x :: xs, [] => by rw [editDistance_nil_right]; exact edits_nil_right (x :: xs)
  | x :: xs, y :: ys => by
    rw [editDistance_cons_cons]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      exact Edits.keep x (edits_editDistance xs ys)
    · rw [if_neg hxy]
      have h1 := edits_editDistance xs (y :: ys)
      have h2 := edits_editDistance (x :: xs) ys
      have h3 := edits_editDistance xs ys
      rcases (show
          1 + min (editDistance xs (y :: ys)) (min (editDistance (x :: xs) ys) (editDistance xs ys))
            = editDistance xs (y :: ys) + 1 ∨
          1 + min (editDistance xs (y :: ys)) (min (editDistance (x :: xs) ys) (editDistance xs ys))
            = editDistance (x :: xs) ys + 1 ∨
          1 + min (editDistance xs (y :: ys)) (min (editDistance (x :: xs) ys) (editDistance xs ys))
            = editDistance xs ys + 1 by omega) with h | h | h
      · rw [h]; exact Edits.del x h1
      · rw [h]; exact Edits.ins y h2
      · rw [h]; exact Edits.sub x y h3
termination_by xs ys => xs.length + ys.length

/-- No edit script is cheaper than the edit distance. -/
theorem editDistance_le_of_edits {xs ys : List α} {k : Nat} (h : Edits xs ys k) :
    editDistance xs ys ≤ k := by
  induction h with
  | nil => simp
  | keep a _ ih => rw [editDistance_cons_cons_same]; exact ih
  | sub a b _ ih => rw [editDistance_cons_cons]; split_ifs <;> omega
  | @del a xs ys k _ ih =>
    have hb := (editDistance_cons_bound xs ys a).1
    omega
  | @ins b xs ys k _ ih =>
    have hb := (editDistance_cons_bound ys xs b).1
    rw [editDistance_comm (b :: ys) xs, editDistance_comm ys xs] at hb
    omega

/-- Property: the edit distance is the minimum number of single-element edits turning
`s1` into `s2`. -/
def editDistance_is_min_edits_prop (s1 s2 : List α) : Prop :=
  Edits s1 s2 (editDistance s1 s2) ∧ ∀ k, Edits s1 s2 k → editDistance s1 s2 ≤ k

theorem editDistance_is_min_edits_thm (s1 s2 : List α) : editDistance_is_min_edits_prop s1 s2 :=
  ⟨edits_editDistance s1 s2, fun _ h => editDistance_le_of_edits h⟩

/-- Executable counterpart of `Edits` (exhaustive search), used for property-based testing. -/
def editsB : List α → List α → Nat → Bool
  | [], [], k => k == 0
  | [], _ :: ys, k => k != 0 && editsB [] ys (k - 1)
  | _ :: xs, [], k => k != 0 && editsB xs [] (k - 1)
  | x :: xs, y :: ys, k =>
    (decide (x = y) && editsB xs ys k) ||
    (k != 0 && (editsB xs ys (k - 1) || editsB xs (y :: ys) (k - 1) || editsB (x :: xs) ys (k - 1)))
termination_by xs ys _ => xs.length + ys.length

/-! ## Post-condition -/

/-- Post-condition on the result `r` of `edit_distance s1 s2`. -/
def Post_prop (s1 s2 : List α) (r : Nat) : Prop :=
  -- r is the minimum number of single-element edits turning s1 into s2
  Edits s1 s2 r ∧ (∀ k, Edits s1 s2 k → r ≤ k) ∧
  -- metric-style facts
  (r = 0 ↔ s1 = s2) ∧
  r = editDistance s2 s1 ∧
  r ≤ max s1.length s2.length ∧
  s1.length - s2.length ≤ r ∧ s2.length - s1.length ≤ r ∧
  -- base cases of the DP table
  (s1 = [] → r = s2.length) ∧ (s2 = [] → r = s1.length)

/-- Executable Boolean form of `Post_prop` (with `Edits` replaced by its executable
counterpart `editsB`), used for property-based testing. -/
def postCheck (s1 s2 : List α) : Bool :=
  let r := editDistance s1 s2
  editsB s1 s2 r && (List.range r).all (fun k => !editsB s1 s2 k) &&
  (decide (r = 0) == decide (s1 = s2)) &&
  (r == editDistance s2 s1) &&
  (r ≤ max s1.length s2.length) &&
  (s1.length - s2.length ≤ r) && (s2.length - s1.length ≤ r) &&
  (!s1.isEmpty || r == s2.length) && (!s2.isEmpty || r == s1.length)

/-! ## Property-based tests -/

/-- All sequences over the alphabet `{0, …, a-1}` of length at most `n`. -/
def allSeqs (a : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [] :: ((allSeqs a n).flatMap fun s => (List.range a).map fun c => c :: s)

#eval (allSeqs 3 3).length  -- 1 + 3 + 9 + 27 = 40

-- exhaustive bounded checks over all pairs of sequences of length ≤ 4 over {0,1,2}
example : (allSeqs 3 4).all (fun s => editDistance s s == 0) = true := by native_decide
example : (allSeqs 3 4).all (fun s => editDistance [] s == s.length) = true := by native_decide
example : (allSeqs 3 4).all (fun s => editDistance s [] == s.length) = true := by native_decide
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 =>
    editDistance s1 s2 == editDistance s2 s1) = true := by native_decide
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 =>
    decide (editDistance s1 s2 = 0) == decide (s1 = s2)) = true := by native_decide
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 =>
    editDistance s1 s2 ≤ max s1.length s2.length) = true := by native_decide
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 =>
    s1.length - s2.length ≤ editDistance s1 s2 && s2.length - s1.length ≤ editDistance s1 s2) = true := by
  native_decide
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 => (List.range 3).all fun x =>
    editDistance (x :: s1) s2 ≤ editDistance s1 s2 + 1 &&
    editDistance s1 s2 ≤ editDistance (x :: s1) s2 + 1) = true := by native_decide
example : (allSeqs 3 3).all (fun s1 => (allSeqs 3 3).all fun s2 => (List.range 3).all fun x =>
    (List.range 3).all fun y =>
    editDistance (x :: s1) (y :: s2) ==
      if x = y then editDistance s1 s2
      else 1 + min (editDistance s1 (y :: s2)) (min (editDistance (x :: s1) s2) (editDistance s1 s2)))
    = true := by native_decide
example : (allSeqs 3 3).all (fun s1 => (allSeqs 3 3).all fun s2 => (List.range 3).all fun a =>
    (List.range 3).all fun b =>
    editDistance (s1 ++ [a]) (s2 ++ [b]) ==
      if a = b then editDistance s1 s2
      else 1 + min (editDistance s1 (s2 ++ [b])) (min (editDistance (s1 ++ [a]) s2) (editDistance s1 s2)))
    = true := by native_decide
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 =>
    editDistance s1.reverse s2.reverse == editDistance s1 s2) = true := by native_decide
example : (allSeqs 2 3).all (fun p => (allSeqs 3 3).all fun s1 => (allSeqs 3 3).all fun s2 =>
    editDistance (p ++ s1) (p ++ s2) == editDistance s1 s2) = true := by native_decide
example : (allSeqs 2 3).all (fun p => (allSeqs 3 3).all fun s1 => (allSeqs 3 3).all fun s2 =>
    editDistance (s1 ++ p) (s2 ++ p) == editDistance s1 s2) = true := by native_decide
example : (allSeqs 2 4).all (fun s1 => (allSeqs 2 4).all fun s2 => (allSeqs 2 4).all fun s3 =>
    editDistance s1 s3 ≤ editDistance s1 s2 + editDistance s2 s3) = true := by native_decide
-- minimality over edit scripts (executable form via `editsB`)
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 =>
    editsB s1 s2 (editDistance s1 s2) &&
    (List.range (editDistance s1 s2)).all fun k => !editsB s1 s2 k) = true := by native_decide
-- post-condition
example : (allSeqs 3 4).all (fun s1 => (allSeqs 3 4).all fun s2 => postCheck s1 s2) = true := by
  native_decide

-- randomized checks (inputs truncated to length ≤ 6 to keep the naive recursion cheap)
#eval Plausible.Testable.check (∀ s : List Nat, editDistance (s.take 6) (s.take 6) = 0)
#eval Plausible.Testable.check (∀ s : List Nat, editDistance [] (s.take 6) = (s.take 6).length)
#eval Plausible.Testable.check (∀ s : List Nat, editDistance (s.take 6) [] = (s.take 6).length)
#eval Plausible.Testable.check (∀ s1 s2 : List Bool,
  editDistance (s1.take 6) (s2.take 6) = editDistance (s2.take 6) (s1.take 6))
#eval Plausible.Testable.check (∀ s1 s2 : List Bool,
  (editDistance (s1.take 6) (s2.take 6) = 0 ↔ s1.take 6 = s2.take 6))
#eval Plausible.Testable.check (∀ s1 s2 : List Nat,
  editDistance (s1.take 6) (s2.take 6) ≤ max (s1.take 6).length (s2.take 6).length)
#eval Plausible.Testable.check (∀ s1 s2 : List Nat,
  (s1.take 6).length - (s2.take 6).length ≤ editDistance (s1.take 6) (s2.take 6) ∧
  (s2.take 6).length - (s1.take 6).length ≤ editDistance (s1.take 6) (s2.take 6))
#eval Plausible.Testable.check (∀ (x : Bool) (s1 s2 : List Bool),
  editDistance (x :: s1.take 6) (s2.take 6) ≤ editDistance (s1.take 6) (s2.take 6) + 1 ∧
  editDistance (s1.take 6) (s2.take 6) ≤ editDistance (x :: s1.take 6) (s2.take 6) + 1)
#eval Plausible.Testable.check (∀ (x y : Bool) (s1 s2 : List Bool),
  editDistance (x :: s1.take 5) (y :: s2.take 5) =
    if x = y then editDistance (s1.take 5) (s2.take 5)
    else 1 + min (editDistance (s1.take 5) (y :: s2.take 5))
      (min (editDistance (x :: s1.take 5) (s2.take 5)) (editDistance (s1.take 5) (s2.take 5))))
#eval Plausible.Testable.check (∀ (a b : Bool) (s1 s2 : List Bool),
  editDistance (s1.take 5 ++ [a]) (s2.take 5 ++ [b]) =
    if a = b then editDistance (s1.take 5) (s2.take 5)
    else 1 + min (editDistance (s1.take 5) (s2.take 5 ++ [b]))
      (min (editDistance (s1.take 5 ++ [a]) (s2.take 5)) (editDistance (s1.take 5) (s2.take 5))))
#eval Plausible.Testable.check (∀ s1 s2 : List Bool,
  editDistance (s1.take 6).reverse (s2.take 6).reverse = editDistance (s1.take 6) (s2.take 6))
#eval Plausible.Testable.check (∀ p s1 s2 : List Bool,
  editDistance (p.take 4 ++ s1.take 4) (p.take 4 ++ s2.take 4) = editDistance (s1.take 4) (s2.take 4))
#eval Plausible.Testable.check (∀ p s1 s2 : List Bool,
  editDistance (s1.take 4 ++ p.take 4) (s2.take 4 ++ p.take 4) = editDistance (s1.take 4) (s2.take 4))
#eval Plausible.Testable.check (∀ s1 s2 s3 : List Bool,
  editDistance (s1.take 5) (s3.take 5) ≤
    editDistance (s1.take 5) (s2.take 5) + editDistance (s2.take 5) (s3.take 5))
#eval Plausible.Testable.check (∀ s1 s2 : List Bool,
  editsB (s1.take 5) (s2.take 5) (editDistance (s1.take 5) (s2.take 5)) = true ∧
  (List.range (editDistance (s1.take 5) (s2.take 5))).all (fun k => !editsB (s1.take 5) (s2.take 5) k) = true)
#eval Plausible.Testable.check (∀ s1 s2 : List Bool, postCheck (s1.take 5) (s2.take 5) = true)
#eval Plausible.Testable.check (∀ s1 s2 : String,
  editDistanceStr (s1.take 5) (s2.take 5) = editDistanceStr (s2.take 5) (s1.take 5))

/-! ## Correctness: `Pre → Post` -/

theorem editDistance_correct (s1 s2 : List α) (_h : Pre s1 s2) : Post_prop s1 s2 (editDistance s1 s2) := by
  unfold Post_prop
  refine ⟨edits_editDistance s1 s2, fun _ h => editDistance_le_of_edits h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact editDistance_eq_zero_iff_thm s1 s2
  · exact editDistance_comm s1 s2
  · exact editDistance_le_max_thm s1 s2
  · exact (length_diff_le_editDistance_thm s1 s2).1
  · exact (length_diff_le_editDistance_thm s1 s2).2
  · rintro rfl; simp
  · rintro rfl; simp

/-- Strings: the result is the edit distance of the character sequences. -/
theorem editDistanceStr_correct (s1 s2 : String) :
    Post_prop s1.toList s2.toList (editDistanceStr s1 s2) :=
  editDistance_correct s1.toList s2.toList trivial

end edit_distance

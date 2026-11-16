import Mathlib

/-!
# Levenshtein Edit Distance

Formalization of the Python `edit_distance` function, which computes the Levenshtein
edit distance (minimum number of single-element insertions, deletions, or substitutions)
between two sequences (`String` or `List α`).

This file contains:
1. Functional implementation (`edit_distance` and `edit_distance_str`)
2. Unit tests (`example : ... := by native_decide` and `#eval`)
3. Precondition (`Pre`)
4. Formal property specifications (`_prop`) and kernel-checked proofs (`_thm`)
5. Postcondition (`Post_prop`)
6. Property-based tests (`#eval Plausible.Testable.checkIO` and bounded exhaustive checks)
7. Correctness theorem (`Pre → Post_prop`)
8. Imperative DP implementation using `Id.run do` with mutable state (`edit_distance_imp`)
9. Imperative unit tests
10. Functional-imperative equivalence theorem (`edit_distance_equiv`)
-/

namespace edit_distance

set_option linter.dupNamespace false

/-! ## 1. Functional Implementation -/

/-- Computes the Levenshtein edit distance between two sequences `s1` and `s2`.
    The edit distance is the minimum number of single-element edits (insertions,
    deletions, or substitutions) required to transform `s1` into `s2`. -/
def edit_distance {α : Type} [DecidableEq α] : List α → List α → Nat
  | [], s2 => s2.length
  | s1, [] => s1.length
  | x :: xs, y :: ys =>
    if x = y then
      edit_distance xs ys
    else
      1 + min (edit_distance xs (y :: ys))
          (min (edit_distance (x :: xs) ys)
               (edit_distance xs ys))

/-- String wrapper for `edit_distance`, converting strings to character lists
    just as the Python implementation converts `str` inputs via `list(s)`. -/
def edit_distance_str (s1 s2 : String) : Nat :=
  edit_distance s1.toList s2.toList

/-! ## 2. Unit Tests -/

-- Basic functionality tests with strings
example : edit_distance "hello".toList "hello".toList = 0 := by native_decide
example : edit_distance "cat".toList "bat".toList = 1 := by native_decide
example : edit_distance "cat".toList "cats".toList = 1 := by native_decide
example : edit_distance "cats".toList "cat".toList = 1 := by native_decide
example : edit_distance "cat".toList "dog".toList = 3 := by native_decide
example : edit_distance "kitten".toList "sitting".toList = 3 := by native_decide

-- Edge cases
example : edit_distance "".toList "".toList = 0 := by native_decide
example : edit_distance "".toList "abc".toList = 3 := by native_decide
example : edit_distance "ab".toList "".toList = 2 := by native_decide
example : edit_distance "a".toList "b".toList = 1 := by native_decide

-- Tests with lists of integers
example : edit_distance [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : edit_distance [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : edit_distance [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : edit_distance [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : edit_distance [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide

-- Tests with character lists
example : edit_distance ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide
example : edit_distance ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : edit_distance ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : edit_distance ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide

-- Longer sequences
example : edit_distance "intention".toList "execution".toList = 5 := by native_decide
example : edit_distance "saturday".toList "sunday".toList = 3 := by native_decide

-- Same length, all different
example : edit_distance "abc".toList "def".toList = 3 := by native_decide
example : edit_distance "xyz".toList "abc".toList = 3 := by native_decide

-- One character strings
example : edit_distance "a".toList "a".toList = 0 := by native_decide
example : edit_distance "a".toList "b".toList = 1 := by native_decide
example : edit_distance "a".toList "".toList = 1 := by native_decide
example : edit_distance "".toList "a".toList = 1 := by native_decide

-- Repeated characters
example : edit_distance "aaa".toList "aa".toList = 1 := by native_decide
example : edit_distance "aa".toList "aaa".toList = 1 := by native_decide
example : edit_distance "aaaa".toList "bbbb".toList = 4 := by native_decide

-- String wrapper tests
example : edit_distance_str "hello" "hello" = 0 := by native_decide
example : edit_distance_str "kitten" "sitting" = 3 := by native_decide
example : edit_distance_str "intention" "execution" = 5 := by native_decide
example : edit_distance_str "saturday" "sunday" = 3 := by native_decide

-- #eval checks
#eval edit_distance "hello".toList "hello".toList
#eval edit_distance "cat".toList "bat".toList
#eval edit_distance "cat".toList "cats".toList
#eval edit_distance "kitten".toList "sitting".toList
#eval edit_distance [1, 2, 3] [1, 4, 3]
#eval edit_distance "intention".toList "execution".toList
#eval edit_distance "saturday".toList "sunday".toList

/-! ## 3. Pre-condition -/

/-- Pre-condition for `edit_distance`: both inputs are valid sequences.
    In Lean, sequence validity is enforced statically by the `List α` type. -/
def Pre {α : Type} (_s1 _s2 : List α) : Prop := True

/-! ## 4. Properties and Theorems -/

/-- Helper unfolding lemmas for `edit_distance`. -/
@[simp] theorem edit_distance_nil_left {α : Type} [DecidableEq α] (s2 : List α) :
    edit_distance ([] : List α) s2 = s2.length := by
  simp [edit_distance]

@[simp] theorem edit_distance_nil_right {α : Type} [DecidableEq α] (s1 : List α) :
    edit_distance s1 ([] : List α) = s1.length := by
  cases s1 <;> simp [edit_distance]

theorem edit_distance_cons_cons {α : Type} [DecidableEq α] (x : α) (xs : List α) (y : α) (ys : List α) :
    edit_distance (x :: xs) (y :: ys) =
      if x = y then edit_distance xs ys
      else 1 + min (edit_distance xs (y :: ys)) (min (edit_distance (x :: xs) ys) (edit_distance xs ys)) := by
  simp [edit_distance]

/-- Property 1: Edit distance is always non-negative. -/
def nonneg_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  0 ≤ edit_distance s1 s2

theorem nonneg_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    nonneg_prop s1 s2 :=
  Nat.zero_le (edit_distance s1 s2)

/-- Property 2: Edit distance from an empty sequence to `s2` is `s2.length` (all insertions). -/
def empty_left_prop {α : Type} [DecidableEq α] (s2 : List α) : Prop :=
  edit_distance ([] : List α) s2 = s2.length

theorem empty_left_thm {α : Type} [DecidableEq α] (s2 : List α) :
    empty_left_prop s2 := by
  simp [empty_left_prop]

/-- Property 3: Edit distance from `s1` to an empty sequence is `s1.length` (all deletions). -/
def empty_right_prop {α : Type} [DecidableEq α] (s1 : List α) : Prop :=
  edit_distance s1 ([] : List α) = s1.length

theorem empty_right_thm {α : Type} [DecidableEq α] (s1 : List α) :
    empty_right_prop s1 := by
  simp [empty_right_prop]

/-- Property 4: Reflexivity — the edit distance between any sequence and itself is 0. -/
def refl_prop {α : Type} [DecidableEq α] (s : List α) : Prop :=
  edit_distance s s = 0

theorem refl_thm {α : Type} [DecidableEq α] (s : List α) :
    refl_prop s := by
  unfold refl_prop
  induction s with
  | nil => simp
  | cons x xs ih => simp [edit_distance_cons_cons, ih]

/-- Property 5: Identity of indiscernibles — edit distance is 0 if and only if the sequences are equal. -/
def zero_iff_eq_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 = 0 ↔ s1 = s2

theorem zero_iff_eq_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    zero_iff_eq_prop s1 s2 := by
  unfold zero_iff_eq_prop
  induction s1 generalizing s2 with
  | nil =>
    cases s2 <;> simp
  | cons x xs ih =>
    cases s2 with
    | nil => simp
    | cons y ys =>
      rw [edit_distance_cons_cons]
      split_ifs with h
      · subst h
        simp [ih]
      · constructor
        · intro h0
          omega
        · intro heq
          cases heq
          contradiction

/-- Property 6: Distinct sequences have strictly positive edit distance. -/
def pos_of_ne_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s1 ≠ s2 → 0 < edit_distance s1 s2

theorem pos_of_ne_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    pos_of_ne_prop s1 s2 := by
  intro hne
  have h0 : edit_distance s1 s2 ≠ 0 := by
    intro hz
    exact hne ((zero_iff_eq_thm s1 s2).mp hz)
  omega

/-- Property 7: Symmetry — edit distance is symmetric in its arguments. -/
def symm_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 = edit_distance s2 s1

theorem symm_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    symm_prop s1 s2 := by
  unfold symm_prop
  induction s1 generalizing s2 with
  | nil => simp
  | cons x xs ih1 =>
    induction s2 with
    | nil => simp
    | cons y ys ih2 =>
      rw [edit_distance_cons_cons, edit_distance_cons_cons]
      have h1 := ih1 (y :: ys)
      have h2 := ih1 ys
      by_cases hxy : x = y
      · subst hxy; simp [h2]
      · have hyx : y ≠ x := Ne.symm hxy
        simp only [hxy, hyx, ↓reduceIte]
        omega

/-- Property 8: Upper bound by maximum length — edit distance is at most `max s1.length s2.length`. -/
def upper_bound_max_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 ≤ max s1.length s2.length

theorem upper_bound_max_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    upper_bound_max_prop s1 s2 := by
  unfold upper_bound_max_prop
  induction s1 generalizing s2 with
  | nil => simp
  | cons x xs ih =>
    cases s2 with
    | nil => simp
    | cons y ys =>
      rw [edit_distance_cons_cons]
      have h := ih ys
      split_ifs <;> simp only [List.length_cons] <;> omega

/-- Property 9: Upper bound by sum of lengths — edit distance is at most `s1.length + s2.length`. -/
def upper_bound_sum_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 ≤ s1.length + s2.length

theorem upper_bound_sum_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    upper_bound_sum_prop s1 s2 := by
  unfold upper_bound_sum_prop
  have h := upper_bound_max_thm s1 s2
  unfold upper_bound_max_prop at h
  omega

/-- Property 10: Lower bound by length difference — edit distance is at least the difference in lengths. -/
def lower_bound_diff_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s1.length - s2.length ≤ edit_distance s1 s2 ∧ s2.length - s1.length ≤ edit_distance s1 s2

theorem lower_bound_diff_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    lower_bound_diff_prop s1 s2 := by
  unfold lower_bound_diff_prop
  induction s1 generalizing s2 with
  | nil => simp
  | cons x xs ih1 =>
    induction s2 with
    | nil => simp
    | cons y ys ih2 =>
      rw [edit_distance_cons_cons]
      have h1 := ih1 (y :: ys)
      have h2 := ih1 ys
      simp only [List.length_cons] at h1 ih2 ⊢
      split_ifs <;> omega

/-- Property 11: Matching head elements do not change edit distance. -/
def cons_same_prop {α : Type} [DecidableEq α] (x : α) (s1 s2 : List α) : Prop :=
  edit_distance (x :: s1) (x :: s2) = edit_distance s1 s2

theorem cons_same_thm {α : Type} [DecidableEq α] (x : α) (s1 s2 : List α) :
    cons_same_prop x s1 s2 := by
  simp [cons_same_prop, edit_distance_cons_cons]

/-- Property 12: Common prefix invariance — prepending the same prefix to both sequences
    preserves the edit distance. -/
def prefix_invariance_prop {α : Type} [DecidableEq α] (p s1 s2 : List α) : Prop :=
  edit_distance (p ++ s1) (p ++ s2) = edit_distance s1 s2

theorem prefix_invariance_thm {α : Type} [DecidableEq α] (p s1 s2 : List α) :
    prefix_invariance_prop p s1 s2 := by
  unfold prefix_invariance_prop
  induction p with
  | nil => rfl
  | cons x xs ih => simp [edit_distance_cons_cons, ih]

/-- Property 13: Bellman dynamic programming recurrence relation. -/
def recurrence_prop {α : Type} [DecidableEq α] (x y : α) (s1 s2 : List α) : Prop :=
  edit_distance (x :: s1) (y :: s2) =
    if x = y then edit_distance s1 s2
    else 1 + min (edit_distance s1 (y :: s2))
             (min (edit_distance (x :: s1) s2)
                  (edit_distance s1 s2))

theorem recurrence_thm {α : Type} [DecidableEq α] (x y : α) (s1 s2 : List α) :
    recurrence_prop x y s1 s2 := by
  simp [recurrence_prop, edit_distance]

/-- Mutual step bounds when prepending an element to the first sequence. -/
theorem edit_distance_cons_bounds {α : Type} [DecidableEq α] (x : α) (s1 s2 : List α) :
    edit_distance (x :: s1) s2 ≤ 1 + edit_distance s1 s2 ∧
    edit_distance s1 s2 ≤ 1 + edit_distance (x :: s1) s2 := by
  cases s2 with
  | nil =>
    simp only [edit_distance_nil_right, List.length_cons]
    omega
  | cons y ys =>
    have h1 := edit_distance_cons_bounds x s1 ys
    have h2 := edit_distance_cons_bounds y ys s1
    rw [symm_thm (y :: ys) s1, symm_thm ys s1] at h2
    rw [edit_distance_cons_cons x s1 y ys]
    split_ifs <;> omega
termination_by s1.length + s2.length

/-- Property 14: Single deletion/prepend on first sequence changes distance by at most 1. -/
def del_bound_prop {α : Type} [DecidableEq α] (x : α) (s1 s2 : List α) : Prop :=
  edit_distance (x :: s1) s2 ≤ 1 + edit_distance s1 s2

theorem del_bound_thm {α : Type} [DecidableEq α] (x : α) (s1 s2 : List α) :
    del_bound_prop x s1 s2 :=
  (edit_distance_cons_bounds x s1 s2).1

/-- Property 15: Single insertion/prepend on second sequence changes distance by at most 1. -/
def ins_bound_prop {α : Type} [DecidableEq α] (y : α) (s1 s2 : List α) : Prop :=
  edit_distance s1 (y :: s2) ≤ 1 + edit_distance s1 s2

theorem ins_bound_thm {α : Type} [DecidableEq α] (y : α) (s1 s2 : List α) :
    ins_bound_prop y s1 s2 := by
  unfold ins_bound_prop
  rw [symm_thm s1 (y :: s2), symm_thm s1 s2]
  exact (edit_distance_cons_bounds y s2 s1).1

/-- Property 16: Single substitution at the head increases edit distance by at most 1. -/
def sub_bound_prop {α : Type} [DecidableEq α] (x y : α) (s1 s2 : List α) : Prop :=
  edit_distance (x :: s1) (y :: s2) ≤ 1 + edit_distance s1 s2

theorem sub_bound_thm {α : Type} [DecidableEq α] (x y : α) (s1 s2 : List α) :
    sub_bound_prop x y s1 s2 := by
  unfold sub_bound_prop
  rw [edit_distance_cons_cons]
  split_ifs <;> omega

/-- Property 17: Triangle inequality — `edit_distance` satisfies the metric triangle inequality. -/
def triangle_prop {α : Type} [DecidableEq α] (s1 s2 s3 : List α) : Prop :=
  edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3

theorem triangle_thm {α : Type} [DecidableEq α] (s1 s2 s3 : List α) :
    triangle_prop s1 s2 s3 := by
  unfold triangle_prop
  induction s1 generalizing s2 s3 with
  | nil =>
    simp only [edit_distance_nil_left]
    have h := (lower_bound_diff_thm s2 s3).2
    omega
  | cons x xs ih1 =>
    induction s2 generalizing s3 with
    | nil =>
      simp only [edit_distance_nil_right, edit_distance_nil_left]
      have h := upper_bound_sum_thm (x :: xs) s3
      unfold upper_bound_sum_prop at h
      omega
    | cons y ys ih2 =>
      induction s3 with
      | nil =>
        simp only [edit_distance_nil_right]
        have h := (lower_bound_diff_thm (x :: xs) (y :: ys)).1
        omega
      | cons z zs ih3 =>
        have h_xs_ys_zs := ih1 ys zs
        have h_xs_yys_zs := ih1 (y :: ys) zs
        have h_xs_ys_zzs := ih1 ys (z :: zs)
        have h_xs_yys_zzs := ih1 (y :: ys) (z :: zs)
        have h_xxs_ys_zs := ih2 zs
        have h_xxs_ys_zzs := ih2 (z :: zs)
        have h_del1 := edit_distance_cons_bounds x xs (z :: zs)
        have h_del2 := edit_distance_cons_bounds x xs zs
        have h_xy := edit_distance_cons_cons x xs y ys
        have h_yz := edit_distance_cons_cons y ys z zs
        have h_xz := edit_distance_cons_cons x xs z zs
        split_ifs at h_xy h_yz h_xz <;> subst_vars <;> (try contradiction) <;> omega

/-! ## 5. Post-condition -/

/-- Post-condition for `edit_distance` on sequences `s1` and `s2`, combining its
    core metric and structural properties. -/
def Post_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  nonneg_prop s1 s2 ∧
  empty_left_prop s2 ∧
  empty_right_prop s1 ∧
  refl_prop s1 ∧
  refl_prop s2 ∧
  zero_iff_eq_prop s1 s2 ∧
  pos_of_ne_prop s1 s2 ∧
  symm_prop s1 s2 ∧
  upper_bound_max_prop s1 s2 ∧
  upper_bound_sum_prop s1 s2 ∧
  lower_bound_diff_prop s1 s2

/-! ## 6. Property-Based Tests (PBTs) -/

/-- Sample lists for bounded exhaustive property-based tests. -/
def sample_lists : List (List Nat) :=
  [[], [0], [1], [2], [0, 0], [0, 1], [1, 0], [1, 1], [0, 1, 2], [2, 1, 0], [1, 0, 1], [0, 1, 0, 1]]

-- PBT for Property 1: nonneg_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (0 ≤ edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 2: empty_left_prop
example : (sample_lists.all fun s2 =>
    decide (edit_distance ([] : List Nat) s2 = s2.length)) = true := by native_decide

-- PBT for Property 3: empty_right_prop
example : (sample_lists.all fun s1 =>
    decide (edit_distance s1 ([] : List Nat) = s1.length)) = true := by native_decide

-- PBT for Property 4: refl_prop
example : (sample_lists.all fun s =>
    decide (edit_distance s s = 0)) = true := by native_decide

-- PBT for Property 5: zero_iff_eq_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide ((edit_distance s1 s2 = 0) ↔ (s1 = s2))) = true := by native_decide

-- PBT for Property 6: pos_of_ne_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (s1 ≠ s2 → 0 < edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 7: symm_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance s1 s2 = edit_distance s2 s1)) = true := by native_decide

-- PBT for Property 8: upper_bound_max_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance s1 s2 ≤ max s1.length s2.length)) = true := by native_decide

-- PBT for Property 9: upper_bound_sum_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance s1 s2 ≤ s1.length + s2.length)) = true := by native_decide

-- PBT for Property 10: lower_bound_diff_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (s1.length - s2.length ≤ edit_distance s1 s2 ∧ s2.length - s1.length ≤ edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 11: cons_same_prop
example : ([0, 1, 2].all fun x => sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance (x :: s1) (x :: s2) = edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 12: prefix_invariance_prop
example : (([[0], [1, 2]] : List (List Nat)).all fun p => sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance (p ++ s1) (p ++ s2) = edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 13: recurrence_prop
example : ([0, 1].all fun x => [0, 1].all fun y => sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance (x :: s1) (y :: s2) =
      if x = y then edit_distance s1 s2
      else 1 + min (edit_distance s1 (y :: s2)) (min (edit_distance (x :: s1) s2) (edit_distance s1 s2)))) = true := by native_decide

-- PBT for Property 14: del_bound_prop
example : ([0, 1].all fun x => sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance (x :: s1) s2 ≤ 1 + edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 15: ins_bound_prop
example : ([0, 1].all fun y => sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance s1 (y :: s2) ≤ 1 + edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 16: sub_bound_prop
example : ([0, 1].all fun x => [0, 1].all fun y => sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance (x :: s1) (y :: s2) ≤ 1 + edit_distance s1 s2)) = true := by native_decide

-- PBT for Property 17: triangle_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 => sample_lists.all fun s3 =>
    decide (edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3)) = true := by native_decide

-- PBT for Post_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (
      0 ≤ edit_distance s1 s2 ∧
      edit_distance ([] : List Nat) s2 = s2.length ∧
      edit_distance s1 ([] : List Nat) = s1.length ∧
      edit_distance s1 s1 = 0 ∧
      edit_distance s2 s2 = 0 ∧
      ((edit_distance s1 s2 = 0) ↔ (s1 = s2)) ∧
      (s1 ≠ s2 → 0 < edit_distance s1 s2) ∧
      edit_distance s1 s2 = edit_distance s2 s1 ∧
      edit_distance s1 s2 ≤ max s1.length s2.length ∧
      edit_distance s1 s2 ≤ s1.length + s2.length ∧
      (s1.length - s2.length ≤ edit_distance s1 s2 ∧ s2.length - s1.length ≤ edit_distance s1 s2))) = true := by native_decide

/-! ## 7. Correctness Theorem (Pre → Post) -/

/-- Main correctness theorem: for any valid input sequences satisfying `Pre`,
    `edit_distance` satisfies the full post-condition `Post_prop`. -/
theorem edit_distance_correct {α : Type} [DecidableEq α] (s1 s2 : List α) :
    Pre s1 s2 → Post_prop s1 s2 := by
  intro _hpre
  refine ⟨nonneg_thm s1 s2,
          empty_left_thm s2,
          empty_right_thm s1,
          refl_thm s1,
          refl_thm s2,
          zero_iff_eq_thm s1 s2,
          pos_of_ne_thm s1 s2,
          symm_thm s1 s2,
          upper_bound_max_thm s1 s2,
          upper_bound_sum_thm s1 s2,
          lower_bound_diff_thm s1 s2⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative dynamic programming implementation of `edit_distance` using `Id.run do`
    with mutable DP row state and nested `for` loops. -/
def edit_distance_imp {α : Type} [DecidableEq α] (s1 s2 : List α) : Nat := Id.run do
  let mut dp : List Nat := [0]
  for _ in s2.reverse do
    dp := (dp.headD 0 + 1) :: dp
  let mut i : Nat := 0
  for x in s1.reverse do
    i := i + 1
    let mut curr : List Nat := [i]
    for (y, del, sub) in (s2.zip (dp.zip dp.tail)).reverse do
      let ins := curr.headD 0
      let v := if x = y then sub else 1 + min del (min ins sub)
      curr := v :: curr
    dp := curr
  return dp.headD 0

/-- String wrapper for `edit_distance_imp`. -/
def edit_distance_imp_str (s1 s2 : String) : Nat :=
  edit_distance_imp s1.toList s2.toList

/-! ## 9. Imperative Tests -/

-- Basic functionality tests with strings
example : edit_distance_imp "hello".toList "hello".toList = 0 := by native_decide
example : edit_distance_imp "cat".toList "bat".toList = 1 := by native_decide
example : edit_distance_imp "cat".toList "cats".toList = 1 := by native_decide
example : edit_distance_imp "cats".toList "cat".toList = 1 := by native_decide
example : edit_distance_imp "cat".toList "dog".toList = 3 := by native_decide
example : edit_distance_imp "kitten".toList "sitting".toList = 3 := by native_decide

-- Edge cases
example : edit_distance_imp "".toList "".toList = 0 := by native_decide
example : edit_distance_imp "".toList "abc".toList = 3 := by native_decide
example : edit_distance_imp "ab".toList "".toList = 2 := by native_decide
example : edit_distance_imp "a".toList "b".toList = 1 := by native_decide

-- Tests with lists of integers
example : edit_distance_imp [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : edit_distance_imp [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : edit_distance_imp [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : edit_distance_imp [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : edit_distance_imp [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide

-- Tests with character lists
example : edit_distance_imp ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide
example : edit_distance_imp ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : edit_distance_imp ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : edit_distance_imp ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide

-- Longer sequences
example : edit_distance_imp "intention".toList "execution".toList = 5 := by native_decide
example : edit_distance_imp "saturday".toList "sunday".toList = 3 := by native_decide

-- Same length, all different
example : edit_distance_imp "abc".toList "def".toList = 3 := by native_decide
example : edit_distance_imp "xyz".toList "abc".toList = 3 := by native_decide

-- One character strings
example : edit_distance_imp "a".toList "a".toList = 0 := by native_decide
example : edit_distance_imp "a".toList "b".toList = 1 := by native_decide
example : edit_distance_imp "a".toList "".toList = 1 := by native_decide
example : edit_distance_imp "".toList "a".toList = 1 := by native_decide

-- Repeated characters
example : edit_distance_imp "aaa".toList "aa".toList = 1 := by native_decide
example : edit_distance_imp "aa".toList "aaa".toList = 1 := by native_decide
example : edit_distance_imp "aaaa".toList "bbbb".toList = 4 := by native_decide

#eval edit_distance_imp "hello".toList "hello".toList
#eval edit_distance_imp "kitten".toList "sitting".toList
#eval edit_distance_imp "intention".toList "execution".toList
#eval edit_distance_imp "saturday".toList "sunday".toList

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

@[simp] theorem Id.bind_eq {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
@[simp] theorem Id.pure_eq {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- Specification of the DP table row for suffix `xs` across all suffixes of `s2`. -/
def dp_spec {α : Type} [DecidableEq α] (xs : List α) : List α → List Nat
  | [] => [xs.length]
  | y :: ys => edit_distance xs (y :: ys) :: dp_spec xs ys

theorem dp_spec_headD {α : Type} [DecidableEq α] (xs s2 : List α) :
    (dp_spec xs s2).headD 0 = edit_distance xs s2 := by
  cases s2 <;> simp [dp_spec]

theorem dp_init_eq {α : Type} [DecidableEq α] (s2 : List α) :
    List.foldl (fun (r : List Nat) _ => (r.headD 0 + 1) :: r) [0] s2.reverse =
      dp_spec ([] : List α) s2 := by
  induction s2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      dp_spec_headD, dp_spec, edit_distance, List.length_cons]

theorem dp_inner_eq {α : Type} [DecidableEq α] (x : α) (xs : List α) (s2 : List α) :
    List.foldl
      (fun (curr : List Nat) (t : α × Nat × Nat) =>
        (if x = t.1 then t.2.2 else 1 + min t.2.1 (min (curr.headD 0) t.2.2)) :: curr)
      [xs.length + 1]
      (s2.zip ((dp_spec xs s2).zip (dp_spec xs s2).tail)).reverse = dp_spec (x :: xs) s2 := by
  induction s2 with
  | nil => rfl
  | cons y ys ih =>
    have h_zip : (y :: ys).zip ((dp_spec xs (y :: ys)).zip (dp_spec xs (y :: ys)).tail) =
        (y, edit_distance xs (y :: ys), edit_distance xs ys) ::
          ys.zip ((dp_spec xs ys).zip (dp_spec xs ys).tail) := by
      cases ys <;> simp [dp_spec]
    rw [h_zip]
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih, dp_spec_headD, dp_spec, edit_distance]

theorem dp_outer_eq {α : Type} [DecidableEq α] (s1 s2 : List α) :
    List.foldl
      (fun (r : MProd (List Nat) Nat) (x : α) =>
        ⟨List.foldl
          (fun (curr : List Nat) (t : α × Nat × Nat) =>
            (if x = t.1 then t.2.2 else 1 + min t.2.1 (min (curr.headD 0) t.2.2)) :: curr)
          [r.snd + 1]
          (s2.zip (r.fst.zip r.fst.tail)).reverse,
        r.snd + 1⟩)
      ⟨dp_spec [] s2, 0⟩
      s1.reverse = ⟨dp_spec s1 s2, s1.length⟩ := by
  induction s1 with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      dp_inner_eq, List.length_cons]

/-- Proposition stating equivalence of the functional and imperative implementations. -/
def equiv_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 = edit_distance_imp s1 s2

-- PBT for equiv_prop
example : (sample_lists.all fun s1 => sample_lists.all fun s2 =>
    decide (edit_distance s1 s2 = edit_distance_imp s1 s2)) = true := by native_decide

set_option linter.deprecated false in
/-- Equivalence theorem: the functional implementation `edit_distance` and the
    imperative implementation `edit_distance_imp` produce identical results on all inputs. -/
theorem edit_distance_equiv {α : Type} [DecidableEq α] (s1 s2 : List α) :
    edit_distance s1 s2 = edit_distance_imp s1 s2 := by
  simp only [edit_distance_imp, Id.run, Id.bind_eq, Id.pure_eq,
    List.forIn_yield_eq_foldl, dp_init_eq, dp_outer_eq, dp_spec_headD]

theorem equiv_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    equiv_prop s1 s2 :=
  edit_distance_equiv s1 s2

end edit_distance

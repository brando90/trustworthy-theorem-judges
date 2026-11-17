import Mathlib

/-!
# Levenshtein Edit Distance

This module formalizes the Levenshtein edit distance between two sequences in Lean 4,
corresponding to the Python `edit_distance` implementation.

The edit distance is the minimum number of single-element edits (insertions,
deletions, or substitutions) required to transform one sequence into another.

It includes:
- Functional recursive specification (`edit_distance`) and functional DP implementation (`edit_distance_dp`)
- Unit tests covering strings, integer lists, character lists, and edge cases
- Pre-condition (`Pre`) and 14 formal properties (`_prop` and proven `_thm`) establishing
  that edit distance forms a metric space with tight length bounds and structural invariances
- Post-condition (`Post_prop`) and property-based tests (PBTs) using `Plausible` and bounded checks
- Correctness theorem (`edit_distance_correct : Pre s1 s2 → Post_prop s1 s2`)
- Imperative dynamic programming implementation (`edit_distance_imp`) using `Id.run do` and mutable state
- Equivalence theorem (`edit_distance_eq_imp`) proving functional and imperative implementations agree on all inputs
-/

set_option linter.dupNamespace false

namespace edit_distance

/-! ## 1. Functional Implementation -/

/-- Functional recursive definition of the Levenshtein edit distance between two sequences. -/
def edit_distance {α : Type} [DecidableEq α] : List α → List α → Nat
  | [], s2 => s2.length
  | s1, [] => s1.length
  | a :: s1, b :: s2 =>
    if a = b then
      edit_distance s1 s2
    else
      1 + min (edit_distance s1 (b :: s2))
            (min (edit_distance (a :: s1) s2)
                 (edit_distance s1 s2))

/-- Convenience wrapper computing Levenshtein edit distance between two strings. -/
def edit_distance_str (s1 s2 : String) : Nat :=
  edit_distance s1.toList s2.toList

/-- Inner loop step for row-by-row dynamic programming computation of edit distance. -/
def innerStep {α : Type} [DecidableEq α] (a : α) :
    MProd Nat (MProd Nat (List Nat)) → (α × Nat) → MProd Nat (MProd Nat (List Nat)) :=
  fun r x =>
    let curr := if a = x.1 then r.fst else 1 + min x.2 (min r.snd.fst r.fst)
    ⟨x.2, curr, curr :: r.snd.snd⟩

/-- Outer loop step for row-by-row dynamic programming computation of edit distance. -/
def outerStep {α : Type} [DecidableEq α] (ys : List α) :
    MProd Nat (MProd (List Nat) Nat) → α → MProd Nat (MProd (List Nat) Nat) :=
  fun r a =>
    let res := (ys.zip r.snd.fst).foldl (innerStep a) ⟨r.fst, r.fst + 1, []⟩
    ⟨r.fst + 1, res.snd.snd.reverse, res.snd.fst⟩

/-- Functional dynamic programming implementation of Levenshtein edit distance ($O(mn)$ time). -/
def edit_distance_dp {α : Type} [DecidableEq α] (s1 s2 : List α) : Nat :=
  (s1.reverse.foldl (outerStep s2.reverse) ⟨0, List.range' 1 s2.length, s2.length⟩).snd.snd

/-- Specification of the DP row tail for a given first sequence `s1`,
    accumulated prefix `acc2` of the second sequence, and remaining elements `ys`. -/
def specTail {α : Type} [DecidableEq α] (s1 : List α) : List α → List α → List Nat
  | _, [] => []
  | acc2, b :: ys => edit_distance s1 (b :: acc2) :: specTail s1 (b :: acc2) ys

theorem edit_distance_nil_left {α : Type} [DecidableEq α] (s2 : List α) :
    edit_distance [] s2 = s2.length := by
  simp [edit_distance]

theorem edit_distance_nil_right {α : Type} [DecidableEq α] (s1 : List α) :
    edit_distance s1 [] = s1.length := by
  cases s1 <;> simp [edit_distance]

theorem specTail_nil {α : Type} [DecidableEq α] (acc2 ys : List α) :
    specTail [] acc2 ys = List.range' (acc2.length + 1) ys.length := by
  induction ys generalizing acc2 with
  | nil => rfl
  | cons b ys ih =>
    simp only [specTail, edit_distance_nil_left, List.length_cons, List.range'_succ]
    rw [ih (b :: acc2)]
    simp [Nat.add_assoc]

theorem inner_foldl_spec {α : Type} [DecidableEq α] (a : α) (s1 acc2 ys : List α) (rev_tail : List Nat) :
    (ys.zip (specTail s1 acc2 ys)).foldl (innerStep a)
      ⟨edit_distance s1 acc2, edit_distance (a :: s1) acc2, rev_tail⟩ =
    ⟨edit_distance s1 (ys.reverse ++ acc2),
     edit_distance (a :: s1) (ys.reverse ++ acc2),
     (specTail (a :: s1) acc2 ys).reverse ++ rev_tail⟩ := by
  induction ys generalizing acc2 rev_tail with
  | nil =>
    simp [specTail]
  | cons b ys ih =>
    simp only [specTail, List.zip_cons_cons, List.foldl_cons, innerStep]
    have h_ed : (if a = b then edit_distance s1 acc2
                 else 1 + min (edit_distance s1 (b :: acc2))
                           (min (edit_distance (a :: s1) acc2) (edit_distance s1 acc2))) =
                edit_distance (a :: s1) (b :: acc2) := by
      rw [edit_distance]
    rw [h_ed, ih (b :: acc2) (edit_distance (a :: s1) (b :: acc2) :: rev_tail)]
    simp [List.reverse_cons, List.append_assoc]

theorem outer_foldl_spec {α : Type} [DecidableEq α] (xs acc1 ys : List α) :
    xs.foldl (outerStep ys)
      ⟨edit_distance acc1 [], specTail acc1 [] ys, edit_distance acc1 ys.reverse⟩ =
    ⟨edit_distance (xs.reverse ++ acc1) [],
     specTail (xs.reverse ++ acc1) [] ys,
     edit_distance (xs.reverse ++ acc1) ys.reverse⟩ := by
  induction xs generalizing acc1 with
  | nil =>
    simp
  | cons a xs ih =>
    simp only [List.foldl_cons, outerStep]
    have h_head : edit_distance acc1 [] + 1 = edit_distance (a :: acc1) [] := by
      simp [edit_distance_nil_right]
    rw [h_head, inner_foldl_spec a acc1 [] ys []]
    simp only [List.append_nil, List.reverse_reverse]
    rw [ih (a :: acc1)]
    simp [List.reverse_cons, List.append_assoc]

theorem edit_distance_eq_dp {α : Type} [DecidableEq α] (s1 s2 : List α) :
    edit_distance s1 s2 = edit_distance_dp s1 s2 := by
  unfold edit_distance_dp
  have h1 : List.range' 1 s2.length = specTail ([] : List α) [] s2.reverse := by
    rw [specTail_nil]
    simp
  have h_out := congrArg (fun p => p.snd.snd) (outer_foldl_spec s1.reverse ([] : List α) s2.reverse)
  simp only [List.append_nil, List.reverse_reverse, edit_distance_nil_left, List.length_nil] at h_out
  rw [← h1] at h_out
  exact h_out.symm

@[csimp]
theorem edit_distance_csimp : @edit_distance = @edit_distance_dp := by
  funext α inst s1 s2
  exact edit_distance_eq_dp s1 s2

/-! ## 2. Unit Tests -/

-- Basic functionality tests with strings (as character lists and via `edit_distance_str`)
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

-- Test with lists of integers
example : edit_distance [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : edit_distance [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : edit_distance [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : edit_distance [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : edit_distance [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide

-- Test with character lists
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

-- String wrapper unit tests
example : edit_distance_str "hello" "hello" = 0 := by native_decide
example : edit_distance_str "kitten" "sitting" = 3 := by native_decide
example : edit_distance_str "intention" "execution" = 5 := by native_decide
example : edit_distance_str "saturday" "sunday" = 3 := by native_decide

#eval edit_distance "hello".toList "hello".toList
#eval edit_distance "kitten".toList "sitting".toList
#eval edit_distance [1, 2, 3, 4, 5] [6, 7, 8]
#eval edit_distance_str "intention" "execution"

/-! ## 3. Pre-condition -/

/-- Pre-condition for `edit_distance`: any two finite sequences (`List α`) are valid inputs. -/
def Pre {α : Type} (_s1 _s2 : List α) : Prop := True

/-! ## 4. Properties and Theorems -/

/-- Property 1: Edit distance from an empty sequence to `s2` is `s2.length` (all insertions). -/
def empty_left_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s1 = [] → edit_distance s1 s2 = s2.length

theorem empty_left_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    empty_left_prop s1 s2 := by
  intro h
  subst h
  exact edit_distance_nil_left s2

/-- Property 2: Edit distance from `s1` to an empty sequence is `s1.length` (all deletions). -/
def empty_right_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s2 = [] → edit_distance s1 s2 = s1.length

theorem empty_right_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    empty_right_prop s1 s2 := by
  intro h
  subst h
  exact edit_distance_nil_right s1

theorem edit_distance_same_head {α : Type} [DecidableEq α] (a : α) (s1 s2 : List α) :
    edit_distance (a :: s1) (a :: s2) = edit_distance s1 s2 := by
  rw [edit_distance]
  simp

theorem edit_distance_self {α : Type} [DecidableEq α] (s : List α) :
    edit_distance s s = 0 := by
  induction s with
  | nil => simp [edit_distance_nil_left]
  | cons a s ih => rw [edit_distance_same_head, ih]

/-- Property 3: Identical sequences have zero edit distance (reflexivity). -/
def self_zero_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s1 = s2 → edit_distance s1 s2 = 0

theorem self_zero_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    self_zero_prop s1 s2 := by
  intro h
  subst h
  exact edit_distance_self s1

/-- Property 4: Edit distance is zero if and only if the two sequences are equal
    (identity of indiscernibles). -/
def zero_iff_eq_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 = 0 ↔ s1 = s2

theorem zero_iff_eq_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    zero_iff_eq_prop s1 s2 := by
  unfold zero_iff_eq_prop
  induction s1 generalizing s2 with
  | nil =>
    rw [edit_distance_nil_left, List.length_eq_zero_iff]
    exact eq_comm
  | cons a s1 ih =>
    cases s2 with
    | nil =>
      rw [edit_distance_nil_right]
      simp
    | cons b s2 =>
      rw [edit_distance]
      by_cases h : a = b
      · subst h
        simp [ih s2]
      · simp only [h, ↓reduceIte, List.cons.injEq, false_and, iff_false]
        omega

/-- Property 5: Distinct sequences have strictly positive edit distance. -/
def pos_of_ne_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s1 ≠ s2 → 0 < edit_distance s1 s2

theorem pos_of_ne_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    pos_of_ne_prop s1 s2 := by
  intro hne
  have h0 : edit_distance s1 s2 ≠ 0 := by
    intro h
    exact hne ((zero_iff_eq_thm s1 s2).mp h)
  omega

/-- Property 6: Edit distance is symmetric (`edit_distance s1 s2 = edit_distance s2 s1`). -/
def symmetry_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 = edit_distance s2 s1

theorem symmetry_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    symmetry_prop s1 s2 := by
  unfold symmetry_prop
  induction s1 generalizing s2 with
  | nil =>
    rw [edit_distance_nil_left, edit_distance_nil_right]
  | cons a s1 ih1 =>
    induction s2 with
    | nil =>
      rw [edit_distance_nil_right, edit_distance_nil_left]
    | cons b s2 ih2 =>
      rw [edit_distance, edit_distance]
      by_cases h : a = b
      · subst h
        simp [ih1 s2]
      · have h' : b ≠ a := Ne.symm h
        simp only [h, h', ↓reduceIte]
        have h_a : edit_distance s1 (b :: s2) = edit_distance (b :: s2) s1 := ih1 (b :: s2)
        have h_b : edit_distance (a :: s1) s2 = edit_distance s2 (a :: s1) := ih2
        have h_c : edit_distance s1 s2 = edit_distance s2 s1 := ih1 s2
        omega

/-- Property 7: Edit distance is bounded above by the maximum of the two sequence lengths. -/
def upper_bound_max_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 ≤ max s1.length s2.length

theorem upper_bound_max_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    upper_bound_max_prop s1 s2 := by
  unfold upper_bound_max_prop
  induction s1 generalizing s2 with
  | nil =>
    rw [edit_distance_nil_left]
    omega
  | cons a s1 ih =>
    cases s2 with
    | nil =>
      rw [edit_distance_nil_right]
      omega
    | cons b s2 =>
      rw [edit_distance]
      have h := ih s2
      split_ifs <;> simp only [List.length_cons] <;> omega

/-- Property 8: Edit distance is bounded above by the sum of the two sequence lengths. -/
def upper_bound_sum_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  edit_distance s1 s2 ≤ s1.length + s2.length

theorem upper_bound_sum_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    upper_bound_sum_prop s1 s2 := by
  unfold upper_bound_sum_prop
  have h := upper_bound_max_thm s1 s2
  unfold upper_bound_max_prop at h
  omega

/-- Property 9: Edit distance is bounded below by the absolute difference of the sequence lengths. -/
def lower_bound_diff_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  s1.length - s2.length ≤ edit_distance s1 s2 ∧
  s2.length - s1.length ≤ edit_distance s1 s2

theorem lower_bound_diff_thm {α : Type} [DecidableEq α] (s1 s2 : List α) :
    lower_bound_diff_prop s1 s2 := by
  unfold lower_bound_diff_prop
  induction s1 generalizing s2 with
  | nil =>
    rw [edit_distance_nil_left]
    simp
  | cons a s1 ih1 =>
    induction s2 with
    | nil =>
      rw [edit_distance_nil_right]
      simp
    | cons b s2 ih2 =>
      rw [edit_distance]
      have h1 := ih1 (b :: s2)
      have h2 := ih1 s2
      simp only [List.length_cons] at h1 ih2 ⊢
      split_ifs <;> omega

theorem edit_distance_cons_bounds_aux {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (s1 s2 : List α), s1.length + s2.length ≤ n →
      ∀ (a : α),
        edit_distance (a :: s1) s2 ≤ 1 + edit_distance s1 s2 ∧
        edit_distance s1 s2 ≤ 1 + edit_distance (a :: s1) s2
  | _, s1, [], _, _ => by
    simp [edit_distance_nil_right]
    omega
  | 0, _, _ :: _, h, _ => by
    simp at h
  | n + 1, s1, b :: s2, h, a => by
    have h_len : s2.length + s1.length ≤ n := by
      simp only [List.length_cons] at h
      omega
    have h_len' : s1.length + s2.length ≤ n := by
      simp only [List.length_cons] at h
      omega
    have ⟨ih_b1, ih_b2⟩ := edit_distance_cons_bounds_aux n s2 s1 h_len b
    have ⟨ih_a1, ih_a2⟩ := edit_distance_cons_bounds_aux n s1 s2 h_len' a
    rw [symmetry_thm (b :: s2) s1, symmetry_thm s2 s1] at ih_b1 ih_b2
    rw [edit_distance]
    split_ifs <;> omega

theorem edit_distance_cons_left_le {α : Type} [DecidableEq α] (a : α) (s1 s2 : List α) :
    edit_distance (a :: s1) s2 ≤ 1 + edit_distance s1 s2 :=
  (edit_distance_cons_bounds_aux (s1.length + s2.length) s1 s2 le_rfl a).1

theorem edit_distance_le_cons_left {α : Type} [DecidableEq α] (a : α) (s1 s2 : List α) :
    edit_distance s1 s2 ≤ 1 + edit_distance (a :: s1) s2 :=
  (edit_distance_cons_bounds_aux (s1.length + s2.length) s1 s2 le_rfl a).2

theorem edit_distance_cons_right_le {α : Type} [DecidableEq α] (b : α) (s1 s2 : List α) :
    edit_distance s1 (b :: s2) ≤ 1 + edit_distance s1 s2 := by
  rw [symmetry_thm s1 (b :: s2), symmetry_thm s1 s2]
  exact edit_distance_cons_left_le b s2 s1

theorem edit_distance_le_cons_right {α : Type} [DecidableEq α] (b : α) (s1 s2 : List α) :
    edit_distance s1 s2 ≤ 1 + edit_distance s1 (b :: s2) := by
  rw [symmetry_thm s1 (b :: s2), symmetry_thm s1 s2]
  exact edit_distance_le_cons_left b s2 s1

theorem edit_distance_cons_cons_le {α : Type} [DecidableEq α] (a b : α) (s1 s2 : List α) :
    edit_distance (a :: s1) (b :: s2) ≤ (if a = b then 0 else 1) + edit_distance s1 s2 := by
  rw [edit_distance]
  split_ifs <;> omega

/-- Property 10: Prepending a single element to either sequence changes the edit distance by at most 1. -/
def step_bound_prop {α : Type} [DecidableEq α] (a : α) (s1 s2 : List α) : Prop :=
  edit_distance (a :: s1) s2 ≤ 1 + edit_distance s1 s2 ∧
  edit_distance s1 (a :: s2) ≤ 1 + edit_distance s1 s2 ∧
  edit_distance s1 s2 ≤ 1 + edit_distance (a :: s1) s2 ∧
  edit_distance s1 s2 ≤ 1 + edit_distance s1 (a :: s2)

theorem step_bound_thm {α : Type} [DecidableEq α] (a : α) (s1 s2 : List α) :
    step_bound_prop a s1 s2 :=
  ⟨edit_distance_cons_left_le a s1 s2,
   edit_distance_cons_right_le a s1 s2,
   edit_distance_le_cons_left a s1 s2,
   edit_distance_le_cons_right a s1 s2⟩

/-- Property 11: Bellman dynamic programming recurrence for non-empty sequences. -/
def recurrence_prop {α : Type} [DecidableEq α] (a b : α) (s1 s2 : List α) : Prop :=
  edit_distance (a :: s1) (b :: s2) =
    if a = b then
      edit_distance s1 s2
    else
      1 + min (edit_distance s1 (b :: s2))
            (min (edit_distance (a :: s1) s2)
                 (edit_distance s1 s2))

theorem recurrence_thm {α : Type} [DecidableEq α] (a b : α) (s1 s2 : List α) :
    recurrence_prop a b s1 s2 := by
  unfold recurrence_prop
  rw [edit_distance]

/-- Property 12: Common prefixes do not change the edit distance (`edit_distance (p ++ s1) (p ++ s2) = edit_distance s1 s2`). -/
def common_prefix_prop {α : Type} [DecidableEq α] (p s1 s2 : List α) : Prop :=
  edit_distance (p ++ s1) (p ++ s2) = edit_distance s1 s2

theorem common_prefix_thm {α : Type} [DecidableEq α] (p s1 s2 : List α) :
    common_prefix_prop p s1 s2 := by
  unfold common_prefix_prop
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.cons_append, edit_distance_same_head, ih]

theorem edit_distance_triangle_aux {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (s1 s2 s3 : List α), s1.length + s2.length + s3.length ≤ n →
      edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3
  | _, [], s2, s3, _ => by
    rw [edit_distance_nil_left, edit_distance_nil_left]
    have h := (lower_bound_diff_thm s2 s3).2
    omega
  | _, s1, s2, [], _ => by
    rw [edit_distance_nil_right, edit_distance_nil_right]
    have h := (lower_bound_diff_thm s1 s2).1
    omega
  | _, a :: s1, [], c :: s3, _ => by
    rw [edit_distance_nil_right, edit_distance_nil_left]
    exact upper_bound_sum_thm (a :: s1) (c :: s3)
  | 0, _ :: _, _ :: _, _ :: _, h => by
    simp at h
  | n + 1, a :: s1, b :: s2, c :: s3, h => by
    have h1 : s1.length + (b :: s2).length + (c :: s3).length ≤ n := by
      simp only [List.length_cons] at h ⊢; omega
    have h2 : (a :: s1).length + s2.length + (c :: s3).length ≤ n := by
      simp only [List.length_cons] at h ⊢; omega
    have h3 : s1.length + s2.length + (c :: s3).length ≤ n := by
      simp only [List.length_cons] at h ⊢; omega
    have h4 : (a :: s1).length + (b :: s2).length + s3.length ≤ n := by
      simp only [List.length_cons] at h ⊢; omega
    have h5 : (a :: s1).length + s2.length + s3.length ≤ n := by
      simp only [List.length_cons] at h ⊢; omega
    have h6 : s1.length + s2.length + s3.length ≤ n := by
      simp only [List.length_cons] at h ⊢; omega
    have ih1 := edit_distance_triangle_aux n s1 (b :: s2) (c :: s3) h1
    have ih2 := edit_distance_triangle_aux n (a :: s1) s2 (c :: s3) h2
    have ih3 := edit_distance_triangle_aux n s1 s2 (c :: s3) h3
    have ih4 := edit_distance_triangle_aux n (a :: s1) (b :: s2) s3 h4
    have ih5 := edit_distance_triangle_aux n (a :: s1) s2 s3 h5
    have ih6 := edit_distance_triangle_aux n s1 s2 s3 h6
    have hb1 := edit_distance_cons_left_le a s1 (c :: s3)
    have hb2 := edit_distance_cons_right_le c (a :: s1) s3
    have hb3 := edit_distance_cons_cons_le a c s1 s3
    have hd1 : edit_distance (a :: s1) (b :: s2) =
      if a = b then edit_distance s1 s2
      else 1 + min (edit_distance s1 (b :: s2))
                (min (edit_distance (a :: s1) s2) (edit_distance s1 s2)) := by
      rw [edit_distance]
    have hd2 : edit_distance (b :: s2) (c :: s3) =
      if b = c then edit_distance s2 s3
      else 1 + min (edit_distance s2 (c :: s3))
                (min (edit_distance (b :: s2) s3) (edit_distance s2 s3)) := by
      rw [edit_distance]
    by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c
    · rw [if_pos hab] at hd1; rw [if_pos hbc] at hd2; rw [if_pos hac] at hb3; omega
    · exfalso; exact hac (hab.trans hbc)
    · rw [if_pos hab] at hd1; rw [if_neg hbc] at hd2; rw [if_pos hac] at hb3; omega
    · rw [if_pos hab] at hd1; rw [if_neg hbc] at hd2; rw [if_neg hac] at hb3; omega
    · exfalso; exact hab (hac.trans hbc.symm)
    · rw [if_neg hab] at hd1; rw [if_pos hbc] at hd2; rw [if_neg hac] at hb3; omega
    · rw [if_neg hab] at hd1; rw [if_neg hbc] at hd2; rw [if_pos hac] at hb3; omega
    · rw [if_neg hab] at hd1; rw [if_neg hbc] at hd2; rw [if_neg hac] at hb3; omega

/-- Property 13: Triangle inequality (`edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3`). -/
def triangle_ineq_prop {α : Type} [DecidableEq α] (s1 s2 s3 : List α) : Prop :=
  edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3

theorem triangle_ineq_thm {α : Type} [DecidableEq α] (s1 s2 s3 : List α) :
    triangle_ineq_prop s1 s2 s3 :=
  edit_distance_triangle_aux (s1.length + s2.length + s3.length) s1 s2 s3 le_rfl

/-- Property 14: Subadditivity under sequence concatenation. -/
def append_subadd_prop {α : Type} [DecidableEq α] (s1 t1 s2 t2 : List α) : Prop :=
  edit_distance (s1 ++ t1) (s2 ++ t2) ≤ edit_distance s1 s2 + edit_distance t1 t2

theorem append_subadd_thm {α : Type} [DecidableEq α] (s1 t1 s2 t2 : List α) :
    append_subadd_prop s1 t1 s2 t2 := by
  unfold append_subadd_prop
  induction s1 generalizing s2 with
  | nil =>
    rw [List.nil_append, edit_distance_nil_left]
    induction s2 with
    | nil =>
      simp
    | cons b s2 ih =>
      simp only [List.cons_append, List.length_cons]
      have h := edit_distance_cons_right_le b t1 (s2 ++ t2)
      omega
  | cons a s1 ih1 =>
    induction s2 with
    | nil =>
      simp only [List.cons_append, List.nil_append, edit_distance_nil_right, List.length_cons]
      have h := edit_distance_cons_left_le a (s1 ++ t1) t2
      have ih := ih1 []
      simp only [List.nil_append, edit_distance_nil_right] at ih
      omega
    | cons b s2 ih2 =>
      simp only [List.cons_append]
      have hd : edit_distance (a :: s1) (b :: s2) =
        if a = b then edit_distance s1 s2
        else 1 + min (edit_distance s1 (b :: s2))
                  (min (edit_distance (a :: s1) s2) (edit_distance s1 s2)) := by
        rw [edit_distance]
      have h1 := edit_distance_cons_left_le a (s1 ++ t1) (b :: (s2 ++ t2))
      have h2 := edit_distance_cons_right_le b (a :: (s1 ++ t1)) (s2 ++ t2)
      have h3 := edit_distance_cons_cons_le a b (s1 ++ t1) (s2 ++ t2)
      have ih_a := ih1 (b :: s2)
      have ih_b := ih2
      have ih_c := ih1 s2
      simp only [List.cons_append] at ih_a ih_b
      by_cases hab : a = b
      · rw [if_pos hab] at hd h3
        omega
      · rw [if_neg hab] at hd h3
        omega

/-! ## 5. Post-condition -/

/-- Post-condition combining all formal properties of `edit_distance` on `s1` and `s2`. -/
def Post_prop {α : Type} [DecidableEq α] (s1 s2 : List α) : Prop :=
  empty_left_prop s1 s2 ∧
  empty_right_prop s1 s2 ∧
  self_zero_prop s1 s2 ∧
  zero_iff_eq_prop s1 s2 ∧
  pos_of_ne_prop s1 s2 ∧
  symmetry_prop s1 s2 ∧
  upper_bound_max_prop s1 s2 ∧
  upper_bound_sum_prop s1 s2 ∧
  lower_bound_diff_prop s1 s2 ∧
  (∀ a : α, step_bound_prop a s1 s2) ∧
  (∀ a b : α, recurrence_prop a b s1 s2) ∧
  (∀ p : List α, common_prefix_prop p s1 s2) ∧
  (∀ s3 : List α, triangle_ineq_prop s1 s2 s3) ∧
  (∀ t1 t2 : List α, append_subadd_prop s1 t1 s2 t2)

/-! ## 6. Property-Based Tests (PBTs) -/

-- PBT for `empty_left_prop`
#eval Plausible.Testable.check (∀ s2 : List Nat, edit_distance [] s2 = s2.length)
example : (List.range 15).all (fun n => edit_distance ([] : List Nat) (List.range n) == n) = true := by native_decide

-- PBT for `empty_right_prop`
#eval Plausible.Testable.check (∀ s1 : List Nat, edit_distance s1 [] = s1.length)
example : (List.range 15).all (fun n => edit_distance (List.range n) ([] : List Nat) == n) = true := by native_decide

-- PBT for `self_zero_prop`
#eval Plausible.Testable.check (∀ s : List Nat, edit_distance s s = 0)
example : (List.range 15).all (fun n => edit_distance (List.range n) (List.range n) == 0) = true := by native_decide

-- PBT for `zero_iff_eq_prop`
#eval Plausible.Testable.check (∀ s1 s2 : List Bool, (edit_distance s1 s2 == 0) = (s1 == s2))
#eval Plausible.Testable.check (∀ s1 s2 : List Nat, (edit_distance s1 s2 == 0) = (s1 == s2))

-- PBT for `pos_of_ne_prop`
#eval Plausible.Testable.check (∀ s1 s2 : List Nat, s1 = s2 ∨ 0 < edit_distance s1 s2)
example : (List.range 10).all (fun m =>
  (List.range 10).all (fun n =>
    if m == n then true else decide (0 < edit_distance (List.range m) (List.range n)))) = true := by native_decide

-- PBT for `symmetry_prop`
#eval Plausible.Testable.check (∀ s1 s2 : List Nat, edit_distance s1 s2 = edit_distance s2 s1)

-- PBT for `upper_bound_max_prop`
#eval Plausible.Testable.check (∀ s1 s2 : List Nat, edit_distance s1 s2 ≤ max s1.length s2.length)

-- PBT for `upper_bound_sum_prop`
#eval Plausible.Testable.check (∀ s1 s2 : List Nat, edit_distance s1 s2 ≤ s1.length + s2.length)

-- PBT for `lower_bound_diff_prop`
#eval Plausible.Testable.check (∀ s1 s2 : List Nat,
  s1.length - s2.length ≤ edit_distance s1 s2 ∧ s2.length - s1.length ≤ edit_distance s1 s2)

-- PBT for `step_bound_prop`
#eval Plausible.Testable.check (∀ (a : Nat) (s1 s2 : List Nat),
  edit_distance (a :: s1) s2 ≤ 1 + edit_distance s1 s2 ∧
  edit_distance s1 (a :: s2) ≤ 1 + edit_distance s1 s2 ∧
  edit_distance s1 s2 ≤ 1 + edit_distance (a :: s1) s2 ∧
  edit_distance s1 s2 ≤ 1 + edit_distance s1 (a :: s2))

-- PBT for `recurrence_prop`
#eval Plausible.Testable.check (∀ (a b : Nat) (s1 s2 : List Nat),
  edit_distance (a :: s1) (b :: s2) =
    if a = b then edit_distance s1 s2
    else 1 + min (edit_distance s1 (b :: s2))
              (min (edit_distance (a :: s1) s2) (edit_distance s1 s2)))

-- PBT for `common_prefix_prop`
#eval Plausible.Testable.check (∀ p s1 s2 : List Nat,
  edit_distance (p ++ s1) (p ++ s2) = edit_distance s1 s2)

-- PBT for `triangle_ineq_prop`
#eval Plausible.Testable.check (∀ s1 s2 s3 : List Nat,
  edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3)

-- PBT for `append_subadd_prop`
#eval Plausible.Testable.check (∀ s1 t1 s2 t2 : List Nat,
  edit_distance (s1 ++ t1) (s2 ++ t2) ≤ edit_distance s1 s2 + edit_distance t1 t2)

-- Combined PBT for `Post_prop`
#eval Plausible.Testable.check (∀ (a b : Nat) (p s1 s2 s3 t1 t2 : List Nat),
  edit_distance [] s2 = s2.length ∧
  edit_distance s1 [] = s1.length ∧
  edit_distance s1 s1 = 0 ∧
  ((edit_distance s1 s2 == 0) = (s1 == s2)) ∧
  (s1 = s2 ∨ 0 < edit_distance s1 s2) ∧
  edit_distance s1 s2 = edit_distance s2 s1 ∧
  edit_distance s1 s2 ≤ max s1.length s2.length ∧
  edit_distance s1 s2 ≤ s1.length + s2.length ∧
  s1.length - s2.length ≤ edit_distance s1 s2 ∧
  s2.length - s1.length ≤ edit_distance s1 s2 ∧
  edit_distance (a :: s1) s2 ≤ 1 + edit_distance s1 s2 ∧
  edit_distance s1 (a :: s2) ≤ 1 + edit_distance s1 s2 ∧
  edit_distance (a :: s1) (b :: s2) =
    (if a = b then edit_distance s1 s2
     else 1 + min (edit_distance s1 (b :: s2))
               (min (edit_distance (a :: s1) s2) (edit_distance s1 s2))) ∧
  edit_distance (p ++ s1) (p ++ s2) = edit_distance s1 s2 ∧
  edit_distance s1 s3 ≤ edit_distance s1 s2 + edit_distance s2 s3 ∧
  edit_distance (s1 ++ t1) (s2 ++ t2) ≤ edit_distance s1 s2 + edit_distance t1 t2)

/-! ## 7. Correctness Theorem (`Pre → Post`) -/

/-- Main correctness theorem: for any valid sequences `s1` and `s2`, `Post_prop s1 s2` holds. -/
theorem edit_distance_correct {α : Type} [DecidableEq α] (s1 s2 : List α)
    (_hPre : Pre s1 s2) : Post_prop s1 s2 :=
  ⟨empty_left_thm s1 s2,
   empty_right_thm s1 s2,
   self_zero_thm s1 s2,
   zero_iff_eq_thm s1 s2,
   pos_of_ne_thm s1 s2,
   symmetry_thm s1 s2,
   upper_bound_max_thm s1 s2,
   upper_bound_sum_thm s1 s2,
   lower_bound_diff_thm s1 s2,
   fun a => step_bound_thm a s1 s2,
   fun a b => recurrence_thm a b s1 s2,
   fun p => common_prefix_thm p s1 s2,
   fun s3 => triangle_ineq_thm s1 s2 s3,
   fun t1 t2 => append_subadd_thm s1 t1 s2 t2⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of Levenshtein edit distance using `Id.run do` and mutable state. -/
def edit_distance_imp {α : Type} [DecidableEq α] (s1 s2 : List α) : Nat := Id.run do
  let mut dp_head : Nat := 0
  let mut dp_tail : List Nat := List.range' 1 s2.length
  let mut result : Nat := s2.length
  for a in s1.reverse do
    let mut diag : Nat := dp_head
    let mut left : Nat := dp_head + 1
    let mut rev_tail : List Nat := []
    for (b, up) in s2.reverse.zip dp_tail do
      let curr := if a = b then diag else 1 + min up (min left diag)
      rev_tail := curr :: rev_tail
      diag := up
      left := curr
    dp_head := dp_head + 1
    dp_tail := rev_tail.reverse
    result := left
  return result

/-- Convenience wrapper for imperative edit distance on strings. -/
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

-- Lists of integers
example : edit_distance_imp [1, 2, 3] [1, 2, 3] = 0 := by native_decide
example : edit_distance_imp [1, 2, 3] [1, 4, 3] = 1 := by native_decide
example : edit_distance_imp [1, 2, 3, 4] [1, 3, 4] = 1 := by native_decide
example : edit_distance_imp [1, 2, 3] [4, 5, 6] = 3 := by native_decide
example : edit_distance_imp [1, 2, 3, 4, 5] [6, 7, 8] = 5 := by native_decide

-- Character lists
example : edit_distance_imp ['h', 'e', 'l', 'l', 'o'] ['h', 'e', 'l', 'l', 'o'] = 0 := by native_decide
example : edit_distance_imp ['c', 'a', 't'] ['b', 'a', 't'] = 1 := by native_decide
example : edit_distance_imp ['c', 'a', 't'] ['c', 'a', 't', 's'] = 1 := by native_decide
example : edit_distance_imp ['c', 'a', 't', 's'] ['c', 'a', 't'] = 1 := by native_decide

-- Longer sequences, all different, one-char, repeated
example : edit_distance_imp "intention".toList "execution".toList = 5 := by native_decide
example : edit_distance_imp "saturday".toList "sunday".toList = 3 := by native_decide
example : edit_distance_imp "abc".toList "def".toList = 3 := by native_decide
example : edit_distance_imp "xyz".toList "abc".toList = 3 := by native_decide
example : edit_distance_imp "a".toList "a".toList = 0 := by native_decide
example : edit_distance_imp "a".toList "".toList = 1 := by native_decide
example : edit_distance_imp "".toList "a".toList = 1 := by native_decide
example : edit_distance_imp "aaa".toList "aa".toList = 1 := by native_decide
example : edit_distance_imp "aa".toList "aaa".toList = 1 := by native_decide
example : edit_distance_imp "aaaa".toList "bbbb".toList = 4 := by native_decide
example : edit_distance_imp_str "intention" "execution" = 5 := by native_decide

#eval edit_distance_imp "kitten".toList "sitting".toList
#eval edit_distance_imp_str "saturday" "sunday"
#eval Plausible.Testable.check (∀ s1 s2 : List Nat, edit_distance s1 s2 = edit_distance_imp s1 s2)

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

theorem forIn_id_yield {α β : Type} (xs : List α) (init : β) (f : α → β → β) :
    forIn (m := Id) xs init (fun a r => ForInStep.yield (f a r)) =
    xs.foldl (fun r a => f a r) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [forIn, List.forIn'_cons, Bind.bind, List.foldl_cons]
    exact ih (f x init)

/-- Equivalence theorem: the functional implementation `edit_distance` and the imperative
    implementation `edit_distance_imp` return identical results on all inputs. -/
theorem edit_distance_eq_imp {α : Type} [DecidableEq α] (s1 s2 : List α) :
    edit_distance s1 s2 = edit_distance_imp s1 s2 := by
  rw [edit_distance_eq_dp]
  unfold edit_distance_dp edit_distance_imp
  simp only [Id.run, Bind.bind, Pure.pure, forIn_id_yield]
  rfl

/-- Equivalence theorem for the string wrappers. -/
theorem edit_distance_str_eq_imp_str (s1 s2 : String) :
    edit_distance_str s1 s2 = edit_distance_imp_str s1 s2 :=
  edit_distance_eq_imp s1.toList s2.toList

end edit_distance

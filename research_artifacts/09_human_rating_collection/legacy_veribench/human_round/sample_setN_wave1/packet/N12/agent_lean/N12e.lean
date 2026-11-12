import Mathlib

/-!
# Counting sort: a Lean 4 formalization of the Python program `counting_sort`

The Python program sorts a list of integers with counting sort:

* `pre(arr)` rejects inputs that are not a `list` of `int` (raising `ValueError`),
* the empty list is returned unchanged,
* otherwise `min_val`/`max_val` are computed, a counting array of size
  `max_val - min_val + 1` is allocated (this *shift* is what makes negative numbers work),
  the occurrences of every value are counted, and finally the values are emitted in
  increasing order, each repeated as many times as it occurs.

## Structure of this file

1. functional implementation `countingSort`
2. unit tests (`native_decide` / `#eval`) mirroring the assertions of the Python `check`
3. pre-condition `Pre`
4. executable properties (`*_prop`) together with their theorems (`*_thm`)
5. post-condition `Post_prop`
6. property-based tests (randomised with `Plausible`, plus bounded `native_decide` tests)
7. correctness theorem `Pre arr -> Post_prop arr`
8. imperative implementation `countingSortImp` (`Id.run do` with mutable state),
   its tests, and the equivalence theorem `countingSortImp arr = countingSort arr`
9. a model of the Python `isinstance` pre-condition check, including the `ValueError` branch

Every theorem below is proved by the Lean kernel: no placeholder proofs, and no `native_decide` inside a theorem proof
(`native_decide` is used only in `example` unit tests) and no new axioms.
-/

namespace counting_sort

open List

/-!
## 1. Functional implementation
-/

/-- `occ v l` is the number of occurrences of `v` in `l`; it is the content of the Python
counting-array entry `count[v - min_val]`. -/
def occ (v : Int) : List Int → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + occ v xs

@[simp] theorem occ_nil (v : Int) : occ v [] = 0 := rfl

@[simp] theorem occ_cons (v x : Int) (xs : List Int) :
    occ v (x :: xs) = (if x = v then 1 else 0) + occ v xs := rfl

/-- `lo arr` is Python's `min_val = min(arr)` (`0` for the empty list). -/
def lo (arr : List Int) : Int := arr.foldl min (arr.headD 0)

/-- `hi arr` is Python's `max_val = max(arr)` (`0` for the empty list). -/
def hi (arr : List Int) : Int := arr.foldl max (arr.headD 0)

/-- `rangeSize arr` is Python's `range_size = max_val - min_val + 1`. -/
def rangeSize (arr : List Int) : Nat := Int.toNat (hi arr - lo arr) + 1

/-- `bucket arr i` is the value `i + min_val` handled by counting-array slot `i`. -/
def bucket (arr : List Int) (i : Nat) : Int := (i : Int) + lo arr

/-- `spread n l0 arr` is Python's output loop
`for i in range(range_size): result.extend([i + min_val] * count[i])`. -/
def spread (n : Nat) (l0 : Int) (arr : List Int) : List Int :=
  List.flatMap (fun (i : Nat) => List.replicate (occ ((i : Int) + l0) arr) ((i : Int) + l0))
    (List.range n)

/-- Counting sort without the empty-list shortcut. -/
def countingSortCore (arr : List Int) : List Int := spread (rangeSize arr) (lo arr) arr

/-- Counting sort, the Lean counterpart of the Python function `counting_sort`.
The `if arr = [] then [] else ...` branch mirrors Python's `if not arr: return []`. -/
def countingSort (arr : List Int) : List Int :=
  if arr = [] then [] else countingSortCore arr

/-- The implementation really is the counting-array scheme: bucket `i` holds the value
`bucket arr i = i + lo arr` and is emitted `occ (bucket arr i) arr` times. -/
theorem countingSortCore_eq_bucket (arr : List Int) :
    countingSortCore arr =
      List.flatMap
        (fun (i : Nat) => List.replicate (occ (bucket arr i) arr) (bucket arr i))
        (List.range (rangeSize arr)) := rfl

example : bucket [3, 1, 2] 0 = 1 := by native_decide
example : bucket [3, 1, 2] 2 = 3 := by native_decide
example : rangeSize [3, 1, 2] = 3 := by native_decide
example : rangeSize [-5, 3] = 9 := by native_decide
example : lo [3, 1, 2] = 1 := by native_decide
example : hi [3, 1, 2] = 3 := by native_decide
example : occ 1 [3, 1, 4, 1, 2, 3] = 2 := by native_decide

/-!
## 2. Unit tests (they mirror the assertions of the Python `check` function)
-/

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort ([] : List Int) = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
-- negative entries exercise the `min_val` shift of the Python program
example : countingSort [-3, 1, -4, 1, -2, 3] = [-4, -3, -2, 1, 1, 3] := by native_decide
example : countingSort [-1, -2, -3] = [-3, -2, -1] := by native_decide
example : countingSort [-5, 0, 5] = [-5, 0, 5] := by native_decide

#eval countingSort [3, 1, 2]
#eval countingSort ([] : List Int)
#eval countingSort [1]
#eval countingSort [3, 1, 4, 1, 2, 3]
#eval countingSort [-5, 3, -1, 0, 2, -1]
#eval countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

/-!
## 3. Pre-condition

Python's `pre(arr)` checks `isinstance(arr, list) and all(isinstance(x, int) for x in arr)`.
In Lean both checks are discharged by the static type `List Int` of the argument, so every
well-typed input satisfies the pre-condition.  Section 9 additionally models the heterogeneous
input for which Python raises `ValueError`.
-/

/-- Pre-condition of `countingSort`: the input is a list of integers (guaranteed by the type). -/
def Pre (_arr : List Int) : Prop := True

example : Pre [3, 1, 2] := trivial
example : Pre [] := trivial
example : Pre [-1, -2] := trivial

/-!
## 4. Auxiliary lemmas
-/

theorem occ_append (v : Int) : ∀ (l₁ l₂ : List Int), occ v (l₁ ++ l₂) = occ v l₁ + occ v l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons x xs ih =>
      intro l₂
      rw [List.cons_append, occ_cons, ih, occ_cons]
      omega

@[simp] theorem occ_replicate (v x : Int) : ∀ (n : Nat),
    occ v (List.replicate n x) = if x = v then n else 0 := by
  intro n
  induction n with
  | zero =>
      by_cases h : x = v
      · simp [h]
      · simp [h]
  | succ n ih =>
      rw [List.replicate_succ, occ_cons, ih]
      by_cases h : x = v
      · rw [if_pos h, if_pos h, if_pos h]
        omega
      · rw [if_neg h, if_neg h, if_neg h]

theorem occ_eq_zero_or_mem (v : Int) : ∀ (l : List Int), occ v l = 0 ∨ v ∈ l := by
  intro l
  induction l with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      rcases ih with h | h
      · by_cases h' : x = v
        · subst h'
          exact Or.inr (by simp)
        · rw [occ_cons, if_neg h', h]
          exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- `occ` agrees with the `List.count` of the library. -/
theorem occ_eq_count (v : Int) : ∀ (l : List Int), occ v l = l.count v := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hb : ((x == v) = true) ↔ (x = v) := beq_iff_eq
      rw [occ_cons, List.count_cons, ih]
      by_cases h : x = v
      · rw [if_pos h, if_pos (hb.mpr h)]
        omega
      · rw [if_neg h, if_neg (mt hb.mp h)]
        omega

theorem count_flatMap : ∀ (l : List Nat) (f : Nat → List Int) (a : Int),
    occ a (List.flatMap f l) = (List.map (fun b => occ a (f b)) l).sum := by
  intro l
  induction l with
  | nil => intro f a; simp
  | cons x xs ih =>
      intro f a
      rw [List.flatMap_cons, occ_append, List.map_cons, List.sum_cons, ih f a]

/-- Summing the guarded counts over `List.range n`: at most one index can hit `a`. -/
theorem sum_range_ite (l0 : Int) (arr : List Int) (a : Int) :
    ∀ (n : Nat),
      (List.map (fun (i : Nat) => if (i : Int) + l0 = a then occ ((i : Int) + l0) arr else 0)
          (List.range n)).sum =
        if ∃ i ∈ List.range n, (i : Int) + l0 = a then occ a arr else 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hsum : (List.map
            (fun (i : Nat) => if (i : Int) + l0 = a then occ ((i : Int) + l0) arr else 0)
            (List.range (n + 1))).sum =
          (if ∃ i ∈ List.range n, (i : Int) + l0 = a then occ a arr else 0) +
            (if (n : Int) + l0 = a then occ ((n : Int) + l0) arr else 0) := by
        have hclean : (List.map
              (fun (i : Nat) => if (i : Int) + l0 = a then occ ((i : Int) + l0) arr else 0)
              [n]).sum =
            (if (n : Int) + l0 = a then occ ((n : Int) + l0) arr else 0) := by simp
        rw [List.range_succ, List.map_append, List.sum_append, hclean, ih]
      rw [hsum]
      by_cases h1 : ∃ i ∈ List.range n, (i : Int) + l0 = a
      · obtain ⟨i, hi, hie⟩ := h1
        have h1' : ∃ j ∈ List.range n, (j : Int) + l0 = a := ⟨i, hi, hie⟩
        have hilt : i < n := List.mem_range.mp hi
        have h2 : ¬((n : Int) + l0 = a) := by
          intro h2
          have hin : i = n := by
            have hc : (i : Int) + l0 = (n : Int) + l0 := by rw [hie, h2]
            omega
          omega
        rw [if_pos h1', if_neg h2,
          if_pos ⟨i, List.mem_range.mpr (by omega : i < n + 1), hie⟩]
        omega
      · rw [if_neg h1]
        by_cases h2 : (n : Int) + l0 = a
        · rw [if_pos h2, if_pos ⟨n, List.mem_range.mpr (by omega : n < n + 1), h2⟩, h2]
          omega
        · rw [if_neg h2, if_neg (by
            intro h3
            obtain ⟨i, hi, hie⟩ := h3
            have hilt : i < n + 1 := List.mem_range.mp hi
            by_cases hin : i = n
            · subst hin
              exact absurd hie h2
            · have hlt : i < n := by omega
              exact absurd ⟨i, List.mem_range.mpr hlt, hie⟩ h1)]

/-- Every element of `d :: l` is an upper bound of the left fold of `min`. -/
theorem foldl_min_le : ∀ (l : List Int) (d y : Int), y ∈ d :: l → l.foldl min d ≤ y := by
  intro l
  induction l with
  | nil =>
      intro d y hy
      simp only [List.mem_singleton] at hy
      subst hy
      simp
  | cons x xs ih =>
      intro d y hy
      have hself : min d x ∈ (min d x) :: xs := by simp
      have hmin : xs.foldl min (min d x) ≤ min d x := ih (min d x) (min d x) hself
      rw [List.foldl_cons]
      simp only [List.mem_cons] at hy
      rcases hy with h | hy
      · rw [h]
        exact le_trans hmin (min_le_left d x)
      · rcases hy with h | hy
        · rw [h]
          exact le_trans hmin (min_le_right d x)
        · exact ih (min d x) y (List.mem_cons.mpr (Or.inr hy))

/-- Every element of `d :: l` is a lower bound of the left fold of `max`. -/
theorem foldl_max_le : ∀ (l : List Int) (d y : Int), y ∈ d :: l → y ≤ l.foldl max d := by
  intro l
  induction l with
  | nil =>
      intro d y hy
      simp only [List.mem_singleton] at hy
      subst hy
      simp
  | cons x xs ih =>
      intro d y hy
      have hself : max d x ∈ (max d x) :: xs := by simp
      have hmax : max d x ≤ xs.foldl max (max d x) := ih (max d x) (max d x) hself
      rw [List.foldl_cons]
      simp only [List.mem_cons] at hy
      rcases hy with h | hy
      · rw [h]
        exact le_trans (le_max_left d x) hmax
      · rcases hy with h | hy
        · rw [h]
          exact le_trans (le_max_right d x) hmax
        · exact ih (max d x) y (List.mem_cons.mpr (Or.inr hy))

theorem lo_le (arr : List Int) : ∀ (x : Int), x ∈ arr → lo arr ≤ x := by
  cases arr with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons a l =>
      intro x hx
      have hl : lo (a :: l) = l.foldl min a := by simp [lo]
      rw [hl]
      exact foldl_min_le l a x hx

theorem le_hi (arr : List Int) : ∀ (x : Int), x ∈ arr → x ≤ hi arr := by
  cases arr with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons a l =>
      intro x hx
      have hl : hi (a :: l) = l.foldl max a := by simp [hi]
      rw [hl]
      exact foldl_max_le l a x hx

theorem lo_le_hi (arr : List Int) : lo arr ≤ hi arr := by
  cases arr with
  | nil => simp [lo, hi]
  | cons a l =>
      have ha : a ∈ (a :: l) := by simp
      exact le_trans (lo_le (a :: l) a ha) (le_hi (a :: l) a ha)

/-- Every element of `arr` lies in the shifted counting range of the Python program, i.e.
`num - min_val` is a valid index into the counting array. -/
theorem bounds (arr : List Int) : ∀ (x : Int), x ∈ arr →
    lo arr ≤ x ∧ x ≤ (rangeSize arr : Int) - 1 + lo arr := by
  intro x hx
  have h1 := lo_le arr x hx
  have h2 := le_hi arr x hx
  have h3 := lo_le_hi arr
  have h4 : (rangeSize arr : Int) - 1 + lo arr = hi arr := by
    simp only [rangeSize, Nat.cast_add, Nat.cast_one]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi arr - lo arr)]
    omega
  rw [h4]
  exact ⟨h1, h2⟩

theorem core_nil : countingSortCore [] = [] := rfl

/-- Python's shortcut `if not arr: return []` agrees with the general path. -/
theorem countingSort_eq_core (arr : List Int) : countingSort arr = countingSortCore arr := by
  by_cases h : arr = []
  · subst h
    exact core_nil
  · simp [countingSort, h]
/-!
## 5. The three key facts about `spread`
-/

/-- Counting sort preserves multiplicities: the emitted blocks contain every value exactly
as often as it occurs in the input. -/
theorem occ_spread (n : Nat) (l0 : Int) (arr : List Int) (a : Int)
    (hb : ∀ x ∈ arr, l0 ≤ x ∧ x ≤ (n : Int) - 1 + l0) :
    occ a (spread n l0 arr) = occ a arr := by
  simp only [spread, count_flatMap, occ_replicate, sum_range_ite]
  by_cases h : ∃ i ∈ List.range n, (i : Int) + l0 = a
  · rw [if_pos h]
  · rw [if_neg h]
    rcases occ_eq_zero_or_mem a arr with hz | hm
    · exact hz.symm
    · exfalso
      obtain ⟨hle, hge⟩ := hb a hm
      have hnn : 0 ≤ a - l0 := by omega
      have hcast : (Int.toNat (a - l0) : Int) = a - l0 := Int.toNat_of_nonneg hnn
      have hlt : Int.toNat (a - l0) < n := by
        have hc : (Int.toNat (a - l0) : Int) < (n : Int) := by omega
        exact Nat.cast_lt.mp hc
      exact absurd ⟨Int.toNat (a - l0), List.mem_range.mpr hlt, by omega⟩ h

/-- The output of counting sort is a permutation of the input. -/
theorem perm_spread (n : Nat) (l0 : Int) (arr : List Int)
    (hb : ∀ x ∈ arr, l0 ≤ x ∧ x ≤ (n : Int) - 1 + l0) :
    spread n l0 arr ~ arr := by
  rw [← Multiset.coe_eq_coe]
  apply Multiset.count_injective
  funext a
  simp only [Multiset.coe_count]
  rw [← occ_eq_count, ← occ_eq_count]
  exact occ_spread n l0 arr a hb

/-- The output of counting sort is sorted in non-decreasing order: the blocks are emitted
in increasing index order. -/
theorem sorted_spread (n : Nat) (l0 : Int) (arr : List Int) :
    (spread n l0 arr).Sorted (· ≤ ·) := by
  induction n with
  | zero =>
      show (spread 0 l0 arr).Sorted (· ≤ ·)
      simp [spread]
  | succ n ih =>
      have hsplit : spread (n + 1) l0 arr =
          spread n l0 arr ++ List.replicate (occ ((n : Int) + l0) arr) ((n : Int) + l0) := by
        simp only [spread, List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rw [hsplit]
      show List.Pairwise (· ≤ ·)
        (spread n l0 arr ++ List.replicate (occ ((n : Int) + l0) arr) ((n : Int) + l0))
      rw [List.pairwise_append]
      refine ⟨ih, List.sorted_le_replicate _ _, ?_⟩
      intro x hx y hy
      have hx2 : x ∈ List.flatMap
          (fun (i : Nat) => List.replicate (occ ((i : Int) + l0) arr) ((i : Int) + l0))
          (List.range n) := hx
      obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hx2
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hxi
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hy
      have hilt : i < n := List.mem_range.mp hi
      have hcast : (i : Int) ≤ (n : Int) := Int.ofNat_le.mpr (Nat.le_of_lt hilt)
      omega

/-!
## 6. Executable properties of `countingSort` and their proofs
-/

/-- The output has the same length as the input. -/
def length_prop (arr : List Int) : Prop := (countingSort arr).length = arr.length

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop := (countingSort arr).Sorted (· ≤ ·)

/-- The output is a permutation of the input. -/
def perm_prop (arr : List Int) : Prop := countingSort arr ~ arr

/-- Every value occurs equally often in the output and in the input. -/
def count_prop (arr : List Int) : Prop := ∀ a : Int, (countingSort arr).count a = arr.count a

/-- The output contains exactly the elements of the input. -/
def mem_prop (arr : List Int) : Prop := ∀ x : Int, x ∈ countingSort arr ↔ x ∈ arr

/-- Sorting an already sorted list does not change it. -/
def idempotent_prop (arr : List Int) : Prop := countingSort (countingSort arr) = countingSort arr

/-- The empty list is mapped to the empty list (Python's `if not arr: return []`). -/
def empty_prop : Prop := countingSort [] = []

/-- A singleton list is a fixed point (Python's `counting_sort([1]) == [1]`). -/
def singleton_prop (a : Int) : Prop := countingSort [a] = [a]

theorem count_thm (arr : List Int) : count_prop arr := by
  intro a
  have h : occ a (countingSort arr) = occ a arr := by
    rw [countingSort_eq_core, countingSortCore]
    exact occ_spread (rangeSize arr) (lo arr) arr a (bounds arr)
  rw [← occ_eq_count a (countingSort arr), ← occ_eq_count a arr]
  exact h

theorem perm_thm (arr : List Int) : perm_prop arr := by
  show countingSort arr ~ arr
  rw [countingSort_eq_core, countingSortCore]
  exact perm_spread (rangeSize arr) (lo arr) arr (bounds arr)

theorem length_thm (arr : List Int) : length_prop arr := by
  show (countingSort arr).length = arr.length
  exact List.Perm.length_eq (perm_thm arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  show (countingSort arr).Sorted (· ≤ ·)
  rw [countingSort_eq_core, countingSortCore]
  exact sorted_spread (rangeSize arr) (lo arr) arr

theorem mem_thm (arr : List Int) : mem_prop arr := by
  intro x
  have h1 : (countingSort arr).count x = 0 ↔ x ∉ countingSort arr := List.count_eq_zero
  have h2 : arr.count x = 0 ↔ x ∉ arr := List.count_eq_zero
  have h3 : (countingSort arr).count x = arr.count x := count_thm arr x
  have h4 : (x ∉ countingSort arr) ↔ (x ∉ arr) := by
    rw [← h1, h3, ← h2]
  exact not_iff_not.mp h4

theorem idempotent_thm (arr : List Int) : idempotent_prop arr := by
  show countingSort (countingSort arr) = countingSort arr
  exact List.eq_of_perm_of_sorted (perm_thm (countingSort arr)) (sorted_thm (countingSort arr))
    (sorted_thm arr)

theorem empty_thm : empty_prop := by
  show countingSort [] = []
  rw [countingSort_eq_core]
  exact core_nil

theorem singleton_thm (a : Int) : singleton_prop a := by
  show countingSort [a] = [a]
  exact List.eq_of_perm_of_sorted (perm_thm [a]) (sorted_thm [a]) (List.sorted_singleton a)


/-- The left fold of `min` always produces an element of `d :: l`. -/
theorem foldl_min_mem : ∀ (l : List Int) (d : Int), l.foldl min d ∈ d :: l := by
  intro l
  induction l with
  | nil => intro d; simp
  | cons x xs ih =>
      intro d
      rw [List.foldl_cons]
      have h1 : xs.foldl min (min d x) ∈ (min d x) :: xs := ih (min d x)
      rw [List.mem_cons] at h1
      rcases h1 with h1 | h1
      · rw [h1]
        have h2 : min d x = d ∨ min d x = x := by
          by_cases h : d ≤ x
          · exact Or.inl (min_eq_left h)
          · exact Or.inr (min_eq_right (le_of_not_ge h))
        rcases h2 with h2 | h2
        · rw [h2]
          simp
        · rw [h2]
          simp
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h1)))

/-- The left fold of `max` always produces an element of `d :: l`. -/
theorem foldl_max_mem : ∀ (l : List Int) (d : Int), l.foldl max d ∈ d :: l := by
  intro l
  induction l with
  | nil => intro d; simp
  | cons x xs ih =>
      intro d
      rw [List.foldl_cons]
      have h1 : xs.foldl max (max d x) ∈ (max d x) :: xs := ih (max d x)
      rw [List.mem_cons] at h1
      rcases h1 with h1 | h1
      · rw [h1]
        have h2 : max d x = d ∨ max d x = x := by
          by_cases h : d ≤ x
          · exact Or.inr (max_eq_right h)
          · exact Or.inl (max_eq_left (le_of_not_ge h))
        rcases h2 with h2 | h2
        · rw [h2]
          simp
        · rw [h2]
          simp
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h1)))

/-- `lo arr` and `hi arr` are Python's `min_val` and `max_val`: they bound every element of
`arr` and, for a non-empty input, they are attained (so the counting array is exactly as
large as the Python one). -/
def minmax_prop (arr : List Int) : Prop :=
  (∀ x ∈ arr, lo arr ≤ x ∧ x ≤ hi arr) ∧ (arr ≠ [] → lo arr ∈ arr ∧ hi arr ∈ arr)

theorem minmax_thm (arr : List Int) : minmax_prop arr := by
  constructor
  · intro x hx
    exact ⟨lo_le arr x hx, le_hi arr x hx⟩
  · intro hne
    cases arr with
    | nil => exact absurd rfl hne
    | cons a l =>
        have h1 : lo (a :: l) = l.foldl min a := by simp [lo]
        have h2 : hi (a :: l) = l.foldl max a := by simp [hi]
        rw [h1, h2]
        exact ⟨foldl_min_mem l a, foldl_max_mem l a⟩

/-!
## 7. Post-condition
-/

/-- Post-condition of counting sort: the result is a sorted permutation of the input with
the same length and the same multiplicities. -/
def Post_prop (arr : List Int) : Prop :=
  length_prop arr ∧ sorted_prop arr ∧ perm_prop arr ∧ count_prop arr

/-- The result is empty exactly when the input is empty. -/
def empty_iff_prop (arr : List Int) : Prop := countingSort arr = [] ↔ arr = []

theorem empty_iff_thm (arr : List Int) : empty_iff_prop arr := by
  constructor
  · intro h
    have hl : (countingSort arr).length = arr.length := length_thm arr
    rw [h] at hl
    exact List.length_eq_zero_iff.mp hl.symm
  · intro h
    subst h
    exact empty_thm

/-!
## 8. Property-based tests

`sortedB` / `postB` are the executable Boolean counterparts of `sorted_prop` / `Post_prop`;
they are used by the bounded (`native_decide`) tests, while the randomised tests below use
`Plausible.Testable.check`, which makes the file fail to compile if a counterexample exists.
-/

/-- Executable counterpart of `List.Sorted (· ≤ ·)`. -/
def sortedB : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: l => (if x ≤ y then true else false) && sortedB (y :: l)

/-- Executable counterpart of `Post_prop`. -/
def postB (arr : List Int) : Bool :=
  let s := countingSort arr
  (s.length == arr.length) && sortedB s && arr.all (fun a => s.count a == arr.count a)

/-- Deterministic families of inputs for the bounded property-based tests. -/
def testList (n : Nat) : List Int :=
  List.map (fun (i : Nat) => (↑((i * i + 3 * i) % 13) : Int) - 6) (List.range n)

def testList2 (n : Nat) : List Int :=
  List.map (fun (i : Nat) => if i % 3 = 0 then -(↑i : Int) else (↑i : Int) - 4) (List.range n)

def testList3 (n : Nat) : List Int :=
  List.map (fun (i : Nat) => (↑(n - i) : Int) * (if i % 2 = 0 then 1 else -1)) (List.range n)

example : sortedB [1, 2, 2, 5] = true := by native_decide
example : sortedB [3, 1] = false := by native_decide
example : postB [3, 1, 2] = true := by native_decide
example : postB ([] : List Int) = true := by native_decide
example : postB [-5, 3, -1, 0, 2, -1] = true := by native_decide
example : postB [7, 7, 7, -2, 0] = true := by native_decide

-- bounded property-based tests: the post-condition holds on 30 inputs of each family
example : (List.range 30).all (fun n => postB (testList n)) = true := by native_decide
example : (List.range 30).all (fun n => postB (testList2 n)) = true := by native_decide
example : (List.range 30).all (fun n => postB (testList3 n)) = true := by native_decide
example : (List.range 30).all (fun n => sortedB (countingSort (testList2 n))) = true :=
  by native_decide
example : (List.range 30).all (fun n => (countingSort (testList3 n)).length == (testList3 n).length)
    = true := by native_decide
example : (List.range 30).all (fun n => countingSort (countingSort (testList n)) ==
    countingSort (testList n)) = true := by native_decide

-- randomised property-based tests (Plausible)
#eval Plausible.Testable.check (∀ xs : List Int, (countingSort xs).length = xs.length)
#eval Plausible.Testable.check (∀ xs : List Int, countingSort xs ~ xs)
#eval Plausible.Testable.check (∀ xs : List Int, (countingSort xs).Sorted (· ≤ ·))
#eval Plausible.Testable.check
  (∀ xs : List Int, ∀ a : Int, (countingSort xs).count a = xs.count a)
#eval Plausible.Testable.check
  (∀ xs : List Int, xs.all (fun a => (countingSort xs).count a == xs.count a) = true)
#eval Plausible.Testable.check (∀ xs : List Int, ∀ x : Int, x ∈ countingSort xs ↔ x ∈ xs)
#eval Plausible.Testable.check (∀ xs : List Int, countingSort (countingSort xs) = countingSort xs)
#eval Plausible.Testable.check (∀ xs : List Int, countingSort xs = [] ↔ xs = [])
#eval Plausible.Testable.check (∀ xs : List Int, postB xs = true)


-- property-based tests for the remaining properties
#eval Plausible.Testable.check (∀ xs : List Int, countingSort xs = [] ↔ xs = [])
#eval Plausible.Testable.check (∀ a : Int, countingSort [a] = [a])
#eval Plausible.Testable.check
  (∀ xs : List Int, ∀ x : Int, x ∉ xs ∨ (lo xs ≤ x ∧ x ≤ hi xs))
#eval Plausible.Testable.check (∀ xs : List Int, xs = [] ∨ (lo xs ∈ xs ∧ hi xs ∈ xs))
example : (List.range 30).all (fun n =>
    decide (countingSort (testList n) = []) == decide (testList n = [])) = true :=
  by native_decide
example : (List.range 30).all (fun n =>
    decide (lo (testList2 n) ∈ testList2 n ∨ testList2 n = [])) = true := by native_decide
example : (List.range 30).all (fun n =>
    decide (hi (testList3 n) ∈ testList3 n ∨ testList3 n = [])) = true := by native_decide

/-!
## 9. Correctness theorem
-/

/-- Correctness of counting sort: under the (type-guaranteed) pre-condition the result
satisfies the full post-condition. -/
theorem countingSort_correct (arr : List Int) (_h : Pre arr) : Post_prop arr :=
  ⟨length_thm arr, sorted_thm arr, perm_thm arr, count_thm arr⟩

/-!
## 10. Imperative implementation (`Id.run do` with mutable state)
-/

/-- An `Id` `for`-loop that always `yield`s is a left fold. -/
@[simp] theorem id_run_forIn_yield {α β : Type} (g : α → β → β) (l : List α) (b : β) :
    Id.run (forIn l b (fun x s => (ForInStep.yield (g x s) : Id (ForInStep β)))) =
      l.foldl (fun s x => g x s) b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp only [List.forIn_cons, Id.run]
      exact ih (g a b)

/-- The imperative counting loop computes the number of occurrences. -/
theorem foldl_occ (v : Int) (l : List Int) :
    l.foldl (fun c x => c + (if x = v then 1 else 0)) 0 = occ v l := by
  have h : ∀ (l : List Int) (c : Nat),
      l.foldl (fun c x => c + (if x = v then 1 else 0)) c = c + occ v l := by
    intro l
    induction l with
    | nil => intro c; simp [occ]
    | cons x xs ih =>
        intro c
        rw [List.foldl_cons, ih, occ_cons]
        by_cases h' : x = v
        · rw [if_pos h']
          omega
        · rw [if_neg h']
          omega
  have h0 := h l 0
  simpa using h0

/-- Reading out a fold that appends replicated blocks gives the flattened list of blocks. -/
theorem toList_foldl_replicate :
    ∀ (l : List Nat) (a : Array Int) (f : Nat → Nat) (g : Nat → Int),
      (l.foldl (fun acc i => acc ++ Array.replicate (f i) (g i)) a).toList =
        a.toList ++ List.flatMap (fun i => List.replicate (f i) (g i)) l := by
  intro l
  induction l with
  | nil => intro a f g; simp
  | cons i l ih =>
      intro a f g
      rw [List.foldl_cons, ih (a ++ Array.replicate (f i) (g i)) f g,
        Array.toList_append, Array.toList_replicate, List.flatMap_cons, List.append_assoc]

/-- Imperative counting sort.  Mutable state: the running minimum `lo`, the running maximum
`hi`, the per-bucket counter `c` and the output array `out`.  This mirrors the Python body:
two scans for `min`/`max`, then, for every bucket `i`, counting the occurrences of
`i + min_val` and extending the result with that many copies. -/
def countingSortImp (arr : List Int) : List Int := Id.run do
  let mut lo : Int := arr.headD 0
  for x in arr do
    lo := min lo x
  let mut hi : Int := arr.headD 0
  for x in arr do
    hi := max hi x
  let n := Int.toNat (hi - lo) + 1
  let mut out : Array Int := #[]
  for i in List.range n do
    let mut c : Nat := 0
    for x in arr do
      c := c + (if x = (i : Int) + lo then 1 else 0)
    for _ in List.range c do
      out := out.push ((i : Int) + lo)
  return out.toList

theorem countingSortImp_eq_core (arr : List Int) :
    countingSortImp arr = countingSortCore arr := by
  have h1 : countingSortImp arr =
      (List.foldl (fun (out : Array Int) (i : Nat) =>
          out ++ Array.replicate (occ ((i : Int) + lo arr) arr) ((i : Int) + lo arr))
        #[] (List.range (rangeSize arr))).toList := by
    simp [countingSortImp, lo, hi, rangeSize, foldl_occ]
  rw [h1, toList_foldl_replicate]
  show List.flatMap
      (fun (i : Nat) => List.replicate (occ ((i : Int) + lo arr) arr) ((i : Int) + lo arr))
      (List.range (rangeSize arr)) = countingSortCore arr
  rfl

/-!
## 11. Imperative tests
-/

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp ([] : List Int) = [] := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [-5, 3, -1, 0, 2, -1] = [-5, -1, -1, 0, 2, 3] := by native_decide
example : countingSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] :=
  by native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval countingSortImp [3, 1, 2]
#eval countingSortImp ([] : List Int)
#eval countingSortImp [-5, 3, -1, 0, 2, -1]
#eval countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

/-- Executable counterpart of `Post_prop` for the imperative implementation. -/
def postBImp (arr : List Int) : Bool :=
  let s := countingSortImp arr
  (s.length == arr.length) && sortedB s && arr.all (fun a => s.count a == arr.count a)

example : postBImp [3, 1, 2] = true := by native_decide
example : postBImp [-5, 3, -1, 0, 2, -1] = true := by native_decide

-- bounded property-based tests for the imperative implementation
example : (List.range 25).all (fun n => postBImp (testList n)) = true := by native_decide
example : (List.range 25).all (fun n => postBImp (testList2 n)) = true := by native_decide
example : (List.range 25).all (fun n => countingSortImp (testList3 n) ==
    countingSort (testList3 n)) = true := by native_decide

-- randomised property-based tests for the imperative implementation
#eval Plausible.Testable.check (∀ xs : List Int, countingSortImp xs = countingSort xs)
#eval Plausible.Testable.check (∀ xs : List Int, postBImp xs = true)

/-!
## 12. Equivalence of the functional and the imperative implementation
-/

/-- The imperative implementation computes the same result as the functional one. -/
theorem imp_eq_thm (arr : List Int) : countingSortImp arr = countingSort arr := by
  rw [countingSort_eq_core]
  exact countingSortImp_eq_core arr

/-- Post-condition, phrased directly about the imperative implementation. -/
def Post_propImp (arr : List Int) : Prop :=
  (countingSortImp arr).length = arr.length ∧ (countingSortImp arr).Sorted (· ≤ ·) ∧
    countingSortImp arr ~ arr ∧ ∀ a : Int, (countingSortImp arr).count a = arr.count a

/-- The imperative implementation also satisfies the full post-condition. -/
theorem countingSortImp_correct (arr : List Int) (_h : Pre arr) : Post_propImp arr := by
  have h : countingSortImp arr = countingSort arr := imp_eq_thm arr
  simp only [Post_propImp, h]
  exact ⟨length_thm arr, sorted_thm arr, perm_thm arr, count_thm arr⟩

/-!
## 13. The Python `pre` check and the `ValueError` branch

Python's `pre(arr)` inspects a *heterogeneous* list and `counting_sort` raises
`ValueError("Input must be List[int]")` when some element is not an `int`
(the Python test suite exercises this with `candidate([1, 2.5])`).
A Lean `List Int` cannot express such an input, so Python values are modelled explicitly
below; `none` plays the role of the raised exception.
-/

/-- A Python value: either an `int`, or (modelled by a rational) a non-integer such as `2.5`. -/
inductive PyVal where
  | int : Int → PyVal
  | float : Rat → PyVal

/-- The `isinstance(x, int)` test. -/
def PyVal.toInt? : PyVal → Option Int
  | PyVal.int n => some n
  | PyVal.float _ => none

@[simp] theorem PyVal.toInt?_int (n : Int) : (PyVal.int n).toInt? = some n := rfl
@[simp] theorem PyVal.toInt?_float (q : Rat) : (PyVal.float q).toInt? = none := rfl

/-- Python's `pre`: every element of the list must be an `int`. -/
def PrePy (vs : List PyVal) : Prop := ∀ v ∈ vs, ∃ n : Int, v = PyVal.int n

/-- Convert a heterogeneous list of Python values, failing (Python: raising `ValueError`)
as soon as a non-integer is found. -/
def toIntList? : List PyVal → Option (List Int)
  | [] => some []
  | v :: vs =>
      match v.toInt? with
      | none => none
      | some n => Option.map (List.cons n) (toIntList? vs)

@[simp] theorem toIntList?_nil : toIntList? [] = some [] := rfl

theorem toIntList?_int (n : Int) (vs : List PyVal) :
    toIntList? (PyVal.int n :: vs) = Option.map (List.cons n) (toIntList? vs) := rfl

theorem toIntList?_float (q : Rat) (vs : List PyVal) :
    toIntList? (PyVal.float q :: vs) = none := rfl

/-- `countingSortChecked` is the complete Python function `counting_sort`, including the
`if not pre(arr): raise ValueError` guard: `none` models the exception. -/
def countingSortChecked (vs : List PyVal) : Option (List Int) :=
  Option.map countingSort (toIntList? vs)

theorem option_map_countingSort_eq_none (o : Option (List Int)) :
    (Option.map countingSort o = none) ↔ o = none := by
  cases o with
  | none => simp [Option.map]
  | some arr => simp [Option.map]

theorem toIntList?_eq_none : ∀ (vs : List PyVal),
    toIntList? vs = none ↔ ∃ v ∈ vs, PyVal.toInt? v = none := by
  intro vs
  induction vs with
  | nil => simp
  | cons v vs ih =>
      cases v with
      | int n =>
          rw [toIntList?_int]
          have hmap : ∀ (o : Option (List Int)),
              (Option.map (List.cons n) o = none) ↔ o = none := by
            intro o
            cases o with
            | none => simp [Option.map]
            | some xs => simp [Option.map]
          rw [hmap, ih]
          constructor
          · intro h
            obtain ⟨w, hw, hw'⟩ := h
            exact ⟨w, List.mem_cons.mpr (Or.inr hw), hw'⟩
          · intro h
            obtain ⟨w, hw, hw'⟩ := h
            rw [List.mem_cons] at hw
            rcases hw with hw | hw
            · subst hw
              simp [PyVal.toInt?] at hw'
            · exact ⟨w, hw, hw'⟩
      | float q =>
          constructor
          · intro _
            exact ⟨PyVal.float q, List.mem_cons.mpr (Or.inl rfl), rfl⟩
          · intro _
            rfl

theorem PrePy_iff (vs : List PyVal) :
    PrePy vs ↔ ∀ v ∈ vs, PyVal.toInt? v ≠ none := by
  constructor
  · intro h v hv
    obtain ⟨n, hn⟩ := h v hv
    subst hn
    simp
  · intro h v hv
    have hne := h v hv
    cases val : PyVal.toInt? v with
    | none => exact absurd val hne
    | some n =>
        cases v with
        | int m => exact ⟨m, rfl⟩
        | float q => simp at val

/-- On a valid input no exception is raised and the sorted result satisfies the
post-condition. -/
theorem countingSortChecked_some (vs : List PyVal) (h : PrePy vs) :
    ∃ arr : List Int, countingSortChecked vs = some (countingSort arr) ∧ Post_prop arr := by
  have h1 : toIntList? vs ≠ none := by
    intro h2
    rw [toIntList?_eq_none] at h2
    obtain ⟨v, hv, hv'⟩ := h2
    obtain ⟨n, hn⟩ := h v hv
    subst hn
    simp [PyVal.toInt?] at hv'
  cases hvs : toIntList? vs with
  | none => exact absurd hvs h1
  | some arr =>
      refine ⟨arr, ?_, countingSort_correct arr trivial⟩
      simp [countingSortChecked, hvs]

/-- On an invalid input the Python `ValueError` is raised (modelled by `none`).
This is the Lean counterpart of the negative Python test `candidate([1, 2.5])`. -/
theorem countingSortChecked_none (vs : List PyVal) :
    countingSortChecked vs = none ↔ ¬ PrePy vs := by
  constructor
  · intro h
    rw [countingSortChecked, option_map_countingSort_eq_none, toIntList?_eq_none] at h
    intro hpre
    obtain ⟨v, hv, hv'⟩ := h
    obtain ⟨n, hn⟩ := hpre v hv
    subst hn
    simp [PyVal.toInt?] at hv'
  · intro h
    rw [countingSortChecked, option_map_countingSort_eq_none, toIntList?_eq_none]
    by_contra h'
    apply h
    intro v hv
    cases v with
    | int n => exact ⟨n, rfl⟩
    | float q => exact absurd ⟨PyVal.float q, hv, rfl⟩ h'

-- unit tests for the `ValueError` branch (Python: `candidate([1, 2.5])` must raise)
example : countingSortChecked [PyVal.int 1, PyVal.float (5 / 2)] = none := by native_decide
example : countingSortChecked [PyVal.float (1 / 2)] = none := by native_decide
example : countingSortChecked [PyVal.int 3, PyVal.int 1, PyVal.int 2] = some [1, 2, 3] :=
  by native_decide
example : countingSortChecked [] = some ([] : List Int) := by native_decide
example : countingSortChecked [PyVal.int (-1), PyVal.int (-3)] = some [-3, -1] :=
  by native_decide

example : ¬ PrePy [PyVal.int 1, PyVal.float (5 / 2)] := by
  intro h
  obtain ⟨n, hn⟩ := h (PyVal.float (5 / 2)) (by simp)
  cases hn

example : PrePy [PyVal.int 1, PyVal.int 2] := by
  intro v hv
  simp only [List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact ⟨1, rfl⟩
  · rcases hv with rfl | hv
    · exact ⟨2, rfl⟩
    · simp at hv

example : PrePy [] := by
  intro v hv
  exact absurd hv (by simp)

#eval countingSortChecked [PyVal.int 3, PyVal.int 1, PyVal.int 2]
#eval countingSortChecked [PyVal.int 1, PyVal.float (5 / 2)]
#eval countingSortChecked []


/-- A deterministic family of heterogeneous Python lists: index `i ≡ 4 [MOD 5]` is a float,
so the list is invalid exactly when `n ≥ 5`. -/
def pyTestList (n : Nat) : List PyVal :=
  List.map
    (fun (i : Nat) =>
      if i % 5 = 4 then PyVal.float ((i : Rat) / 2) else PyVal.int ((i : Int) - 3))
    (List.range n)

-- bounded property-based test for the `ValueError` model
example : (List.range 20).all (fun n =>
    decide (countingSortChecked (pyTestList n) = none) == decide (5 ≤ n)) = true :=
  by native_decide
example : (List.range 20).all (fun n =>
    decide (countingSortChecked (pyTestList n) ≠ none) == decide (n < 5)) = true :=
  by native_decide

end counting_sort

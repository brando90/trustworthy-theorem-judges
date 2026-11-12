import Mathlib

/-!
# Counting sort (Python → Lean 4)

Formalisation of the Python program `counting_sort`, which sorts a `List[int]` by
counting how many times each value of the range `[min arr, max arr]` occurs and then
emitting every value as often as it occurs (negative numbers are supported by shifting
the range with `min arr`).

Contents of this file (in order):

1. the functional implementation `countingSort` (plus the helper `rangeBlocks`, which is
   the mathematical "emit each value `lo + i` exactly `arr.count (lo + i)` times" loop),
2. unit tests: the doctests of the Python source and every assertion of its `check`,
3. the pre-condition `Pre` (Python's `pre`),
4. auxiliary lemmas,
5. executable properties `*_prop` together with their theorems `*_thm`,
6. the post-condition `Post_prop`,
7. property-based tests (randomised with `Plausible` and bounded with `native_decide`),
8. the correctness theorem `Pre arr → Post_prop arr (countingSort arr)`,
9. the imperative implementation `countingSortImp` (`Id.run do` + mutable state),
10. imperative tests,
11. the equivalence theorem `countingSortImp arr = countingSort arr`.

About Python's `pre` / `ValueError`: `pre(arr)` checks `isinstance(arr, list)` and that
every element is an `int`.  In Lean this check *is* the type `List Int`: an input of that
type is a list of integers by construction, so the `ValueError` branch is unreachable and
the negative test `candidate([1, 2.5])` has no well-typed counterpart (a `Float` cannot be
an element of a `List Int`).  Hence `Pre` holds for every admissible input.
-/

namespace counting_sort

/-! ## 1. Functional implementation -/

/-- One step of the counting phase: Python's `count[num - min_val] += 1`.
The count table is a function `Nat → Nat` indexed by the shifted value `num - lo`;
it plays the role of Python's `count` list (of size `max - min + 1`). -/
def countStep (lo : Int) (c : Nat → Nat) (x : Int) : Nat → Nat :=
  Function.update c ((x - lo).toNat) (c ((x - lo).toNat) + 1)

/-- `rangeBlocks lo k arr` is the output construction phase of counting sort: for every
shifted index `i` with `i < k` the value `lo + i` is emitted exactly `arr.count (lo + i)`
times, in increasing order of `i`.  This is Python's

    for i in range(range_size):
        result.extend([i + min_val] * count[i])

stated mathematically (it is the specification used for the proofs). -/
def rangeBlocks : Int → Nat → List Int → List Int
  | _, 0, _ => []
  | lo, k + 1, arr =>
      rangeBlocks lo k arr ++ List.replicate (arr.count (lo + (k : Int))) (lo + (k : Int))

/-- Counting sort.  The empty list is sorted to the empty list (Python's
`if not arr: return []`); otherwise `lo = min arr`, `hi = max arr`,
`k = hi - lo + 1` (`range_size`), the count table is built by one pass over the input
and the result is the concatenation of the `k` blocks. -/
def countingSort : List Int → List Int
  | [] => []
  | a :: as =>
      let lo := as.foldl (fun m x => min m x) a
      let hi := as.foldl (fun m x => max m x) a
      let k := (hi - lo).toNat + 1
      let c := (a :: as).foldl (fun c x => countStep lo c x) (fun _ => 0)
      ((List.range k).map (fun i => List.replicate (c i) (lo + (i : Int)))).flatten

/-! ## 2. Unit tests (Python doctests and the assertions of `check`) -/

#eval countingSort [3, 1, 2]
#eval countingSort ([] : List Int)
#eval countingSort [1]
#eval countingSort [-3, 5, -1, 0, 5, -3]

-- Python doctests
example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [] = ([] : List Int) := by native_decide
example : countingSort [1] = [1] := by native_decide

-- `check`: basic functionality
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide

-- `check`: larger arrays
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide

-- `check`: two elements
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide

-- `check`: duplicates
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide

-- `check`: already sorted / reverse sorted / random order
example : countingSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

-- `check`: with zeros
example : countingSort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide

-- `check`: larger test case
example : countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

-- negative numbers (Python supports them through the `min_val` shift)
example : countingSort [-3, 5, -1, 0, 5, -3] = [-3, -3, -1, 0, 5, 5] := by native_decide
example : countingSort [-1, -2, -3] = [-3, -2, -1] := by native_decide

/-! ## 3. Pre-condition -/

/-- Python's pre-condition

    def pre(arr): return isinstance(arr, list) and all(isinstance(x, int) for x in arr)

In Lean the input type `List Int` already guarantees both conjuncts, so `Pre` holds for
every admissible input and the `ValueError` branch of the Python program is unreachable.
-/
def Pre (_arr : List Int) : Prop := True

theorem Pre_holds (_arr : List Int) : Pre _arr := trivial

/-! ## 4. Auxiliary lemmas -/

/-- `as.foldl (fun m x => min m x) acc` is the minimum of `acc :: as`: it is `≤ acc`,
`≤` every element of `as`, and it is one of the elements of `acc :: as`. -/
theorem foldl_min_spec : ∀ (acc : Int) (as : List Int),
    as.foldl (fun m x => min m x) acc ≤ acc ∧
    (∀ y ∈ as, as.foldl (fun m x => min m x) acc ≤ y) ∧
    (as.foldl (fun m x => min m x) acc = acc ∨ as.foldl (fun m x => min m x) acc ∈ as) := by
  intro acc as
  induction as generalizing acc with
  | nil => simp
  | cons b bs ih =>
      have h := ih (min acc b)
      simp only [List.foldl_cons] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨le_trans h1 (min_le_left acc b), ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with hyb | hy
        · rw [hyb]; exact le_trans h1 (min_le_right acc b)
        · exact h2 y hy
      · rcases h3 with h3 | h3
        · rcases le_total acc b with hab | hab
          · exact Or.inl (h3.trans (min_eq_left hab))
          · exact Or.inr (by rw [h3, min_eq_right hab]; simp)
        · exact Or.inr (List.mem_cons_of_mem b h3)

/-- `as.foldl (fun m x => max m x) acc` is the maximum of `acc :: as`. -/
theorem foldl_max_spec : ∀ (acc : Int) (as : List Int),
    acc ≤ as.foldl (fun m x => max m x) acc ∧
    (∀ y ∈ as, y ≤ as.foldl (fun m x => max m x) acc) ∧
    (as.foldl (fun m x => max m x) acc = acc ∨ as.foldl (fun m x => max m x) acc ∈ as) := by
  intro acc as
  induction as generalizing acc with
  | nil => simp
  | cons b bs ih =>
      have h := ih (max acc b)
      simp only [List.foldl_cons] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨le_trans (le_max_left acc b) h1, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with hyb | hy
        · rw [hyb]; exact le_trans (le_max_right acc b) h1
        · exact h2 y hy
      · rcases h3 with h3 | h3
        · rcases le_total acc b with hab | hab
          · exact Or.inr (by rw [h3, max_eq_right hab]; simp)
          · exact Or.inl (h3.trans (max_eq_left hab))
        · exact Or.inr (List.mem_cons_of_mem b h3)

theorem foldl_min_le_all (a : Int) (as : List Int) :
    ∀ y ∈ (a :: as), as.foldl (fun m x => min m x) a ≤ y := by
  intro y hy
  rcases List.mem_cons.mp hy with hyb | hy
  · rw [hyb]; exact (foldl_min_spec a as).1
  · exact (foldl_min_spec a as).2.1 y hy

theorem foldl_max_ge_all (a : Int) (as : List Int) :
    ∀ y ∈ (a :: as), y ≤ as.foldl (fun m x => max m x) a := by
  intro y hy
  rcases List.mem_cons.mp hy with hyb | hy
  · rw [hyb]; exact (foldl_max_spec a as).1
  · exact (foldl_max_spec a as).2.1 y hy

theorem rangeBlocks_zero (lo : Int) (arr : List Int) : rangeBlocks lo 0 arr = [] := rfl

theorem rangeBlocks_succ (lo : Int) (k : Nat) (arr : List Int) :
    rangeBlocks lo (k + 1) arr =
      rangeBlocks lo k arr ++ List.replicate (arr.count (lo + (k : Int))) (lo + (k : Int)) :=
  rfl

/-- Every element produced by `rangeBlocks lo k arr` is one of the values `lo + i`, `i < k`.
In particular it is `≥ lo`. -/
theorem mem_rangeBlocks (lo : Int) (arr : List Int) (x : Int) : ∀ k : Nat,
    x ∈ rangeBlocks lo k arr → ∃ i, i < k ∧ x = lo + (i : Int) := by
  intro k
  induction k with
  | zero =>
      intro h
      rw [rangeBlocks_zero] at h
      exact absurd h (by simp)
  | succ k ih =>
      intro h
      rw [rangeBlocks_succ, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, hi, hx⟩ := ih h
        exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
      · rw [List.mem_replicate] at h
        exact ⟨k, Nat.lt_succ_self k, h.2⟩

/-- If `arr` really contains the value `lo + i` and `i < k`, then `lo + i` occurs in the
output of the block construction. -/
theorem mem_rangeBlocks_of_count (lo : Int) (arr : List Int) :
    ∀ k i : Nat, i < k → arr.count (lo + (i : Int)) ≠ 0 →
      lo + (i : Int) ∈ rangeBlocks lo k arr := by
  intro k
  induction k with
  | zero => intro i hi _; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
      intro i hi hcount
      rw [rangeBlocks_succ, List.mem_append]
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with h | h
      · subst h
        right
        rw [List.mem_replicate]
        exact ⟨hcount, rfl⟩
      · left
        exact ih i h hcount

theorem sorted_replicate_le (n : Nat) (a : Int) :
    (List.replicate n a).Pairwise (fun x y : Int => x ≤ y) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
      rw [List.replicate_succ]
      exact List.Pairwise.cons
        (fun b hb => le_of_eq ((List.mem_replicate.mp hb).2.symm)) ih

/-- The blocks are emitted in increasing order, hence the result is sorted. -/
theorem sorted_rangeBlocks (lo : Int) (arr : List Int) :
    ∀ k : Nat, (rangeBlocks lo k arr).Sorted (· ≤ ·) := by
  intro k
  induction k with
  | zero => exact List.sorted_nil
  | succ k ih =>
      have h : (rangeBlocks lo k.succ arr).Pairwise (fun x y : Int => x ≤ y) := by
        rw [rangeBlocks_succ, List.pairwise_append]
        refine ⟨ih, sorted_replicate_le _ _, ?_⟩
        intro a ha b hb
        obtain ⟨i, hi, ha'⟩ := mem_rangeBlocks lo arr a k ha
        obtain ⟨_, hb'⟩ := List.mem_replicate.mp hb
        rw [ha', hb']
        exact add_le_add_left (Int.ofNat_le.mpr (Nat.le_of_lt hi)) lo
      exact h

/-- The number of occurrences of `x` in `rangeBlocks lo k arr` is `arr.count x` as soon as
the block `lo + i` with `i = x - lo` lies inside the range, i.e. as soon as
`(x - lo).toNat < k`. -/
theorem count_rangeBlocks (lo : Int) (arr : List Int) (x : Int) (hx : lo ≤ x) :
    ∀ k : Nat, (rangeBlocks lo k arr).count x =
      if (x - lo).toNat < k then arr.count x else 0 := by
  intro k
  induction k with
  | zero => simp [rangeBlocks_zero]
  | succ k ih =>
      have hcast : ((x - lo).toNat : Int) = x - lo := Int.toNat_of_nonneg (by omega)
      rw [rangeBlocks_succ, List.count_append, List.count_replicate]
      simp only [beq_iff_eq]
      rw [ih]
      by_cases hlt : (x - lo).toNat < k
      · have hne : lo + (k : Int) ≠ x := by
          intro hc
          have h2 : x - lo = (k : Int) := by omega
          have h1 : ((x - lo).toNat : Int) = (k : Int) := hcast.trans h2
          exact absurd (Nat.cast_inj.mp h1) (Nat.ne_of_lt hlt)
        rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt), if_neg hne]
        simp
      · by_cases heq : (x - lo).toNat = k
        · have hcast' : lo + (k : Int) = x := by
            rw [heq] at hcast
            omega
          rw [if_neg hlt, if_pos hcast', if_pos (by rw [heq]; exact Nat.lt_succ_self k)]
          rw [← hcast']
          simp
        · have hgt : k < (x - lo).toNat := by omega
          have hne : lo + (k : Int) ≠ x := by
            intro hc
            have h2 : x - lo = (k : Int) := by omega
            have h1 : ((x - lo).toNat : Int) = (k : Int) := hcast.trans h2
            exact absurd (Nat.cast_inj.mp h1) heq
          rw [if_neg hlt, if_neg hne, if_neg (by omega)]

/-- Values below the minimum of the range never occur in the output. -/
theorem count_rangeBlocks_of_lt (lo : Int) (arr : List Int) (x : Int) (k : Nat)
    (hx : x < lo) : (rangeBlocks lo k arr).count x = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro h
  obtain ⟨i, _, hi⟩ := mem_rangeBlocks lo arr x k h
  rw [hi] at hx
  omega

/-- The counting phase: folding `countStep lo` over `xs` starting from a table `acc` that
agrees with `d` yields a table that records `d j + xs.count (lo + j)` at every index `j`.
-/
theorem countTable_aux (lo : Int) : ∀ (xs : List Int) (acc d : Nat → Nat),
    (∀ j, acc j = d j) → (∀ y ∈ xs, lo ≤ y) →
    ∀ j : Nat,
      (xs.foldl (fun c x => countStep lo c x) acc) j = d j + xs.count (lo + (j : Int)) := by
  intro xs
  induction xs with
  | nil => intro acc d hacc _ j; simp only [List.foldl_nil, List.count_nil, add_zero, hacc]
  | cons x xs' ih =>
      intro acc d hacc hlo j
      have hlex : lo ≤ x := hlo x (by simp)
      have hlo' : ∀ y ∈ xs', lo ≤ y := fun y hy => hlo y (List.mem_cons_of_mem x hy)
      have hcast : lo + ((x - lo).toNat : Int) = x := by
        rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ x - lo)]
        omega
      have hacc' : ∀ i, (countStep lo acc x) i =
          (if i = (x - lo).toNat then d ((x - lo).toNat) + 1 else d i) := by
        intro i
        simp [countStep, Function.update_apply, hacc]
      have h1 := ih (countStep lo acc x)
        (fun i => if i = (x - lo).toNat then d ((x - lo).toNat) + 1 else d i) hacc' hlo' j
      simp only [List.foldl_cons]
      rw [h1, List.count_cons]
      simp only [beq_iff_eq]
      by_cases hxj : x = lo + (j : Int)
      · have hj : j = (x - lo).toNat :=
          (Nat.cast_inj.mp (add_left_cancel (hcast.trans hxj))).symm
        rw [if_pos hj, if_pos hxj, ← hj]
        omega
      · have hj : j ≠ (x - lo).toNat := by
          intro hcontra
          have hc : lo + (j : Int) = x := by rw [← hcontra] at hcast; exact hcast
          exact absurd hc.symm hxj
        rw [if_neg hj, if_neg hxj]
        omega

/-- After the counting phase the table entry at index `j` is exactly the number of
occurrences of `lo + j` in the input (Python: `count[num - min_val] += 1`). -/
theorem countTable_cons_spec (lo a : Int) (as : List Int)
    (hlo : ∀ y ∈ (a :: as), lo ≤ y) (j : Nat) :
    (as.foldl (fun c x => countStep lo c x) (countStep lo (fun _ => 0) a)) j =
      (a :: as).count (lo + (j : Int)) := by
  have hacc : ∀ i, (countStep lo (fun _ => 0) a) i =
      (if i = (a - lo).toNat then 1 else 0) := by
    intro i
    simp [countStep, Function.update_apply]
  have hlo' : ∀ y ∈ as, lo ≤ y := fun y hy => hlo y (List.mem_cons_of_mem a hy)
  have h2 := countTable_aux lo as (countStep lo (fun _ => 0) a)
    (fun i => if i = (a - lo).toNat then 1 else 0) hacc hlo' j
  have hlea : lo ≤ a := hlo a (by simp)
  have hcast : lo + ((a - lo).toNat : Int) = a := by
    rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ a - lo)]
    omega
  rw [List.count_cons]
  simp only [beq_iff_eq]
  rw [h2]
  by_cases hj : j = (a - lo).toNat
  · have h3 : lo + (j : Int) = a := by rw [← hj] at hcast; exact hcast
    rw [if_pos hj, if_pos h3.symm]
    omega
  · have h3 : lo + (j : Int) ≠ a := by
      intro hc
      have h4 : ((a - lo).toNat : Int) = (j : Int) := add_left_cancel (hcast.trans hc.symm)
      exact hj (Nat.cast_inj.mp h4).symm
    rw [if_neg hj, if_neg h3.symm]
    omega

/-- The block construction of the implementation coincides with the mathematical
specification `rangeBlocks`, provided the count table is correct. -/
theorem flatten_map_replicate_eq_rangeBlocks (lo : Int) (arr : List Int) (c : Nat → Nat) :
    ∀ k : Nat, (∀ i, i < k → c i = arr.count (lo + (i : Int))) →
      ((List.range k).map (fun i => List.replicate (c i) (lo + (i : Int)))).flatten =
        rangeBlocks lo k arr := by
  intro k
  induction k with
  | zero => intro _; simp [rangeBlocks_zero]
  | succ k ih =>
      intro hc
      rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
        List.flatten_singleton,
        rangeBlocks_succ]
      rw [ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))]
      rw [hc k (Nat.lt_succ_self k)]

theorem rangeBlocks_congr (lo : Int) (arr₁ arr₂ : List Int)
    (h : ∀ x : Int, arr₁.count x = arr₂.count x) :
    ∀ k : Nat, rangeBlocks lo k arr₁ = rangeBlocks lo k arr₂ := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [rangeBlocks_succ, rangeBlocks_succ, ih, h]

/-- Unfolding `countingSort` on a non-empty input: the range is `[min, max]` and the output
is the block construction for that range. -/
theorem countingSort_cons (a : Int) (as : List Int) :
    countingSort (a :: as) =
      rangeBlocks (as.foldl (fun m x => min m x) a)
        (((as.foldl (fun m x => max m x) a) - (as.foldl (fun m x => min m x) a)).toNat + 1)
        (a :: as) := by
  simp only [countingSort]
  refine flatten_map_replicate_eq_rangeBlocks _ _ _ _ ?_
  intro i _
  exact countTable_cons_spec _ _ _ (foldl_min_le_all a as) i

/-- `countingSort` preserves the multiplicity of every value. -/
theorem countingSort_count (arr : List Int) :
    ∀ x : Int, (countingSort arr).count x = arr.count x := by
  cases arr with
  | nil => intro x; simp [countingSort]
  | cons a as =>
      intro x
      rw [countingSort_cons]
      by_cases hx : as.foldl (fun m x => min m x) a ≤ x
      · rw [count_rangeBlocks _ _ _ hx]
        by_cases hmem : x ∈ (a :: as)
        · have h1 : x ≤ as.foldl (fun m x => max m x) a := foldl_max_ge_all a as x hmem
          have h3 : (x - as.foldl (fun m x => min m x) a).toNat <
              ((as.foldl (fun m x => max m x) a - as.foldl (fun m x => min m x) a).toNat + 1) :=
            Nat.lt_succ_of_le (Int.toNat_le_toNat (by omega))
          rw [if_pos h3]
        · have h0 : (a :: as).count x = 0 := List.count_eq_zero_of_not_mem hmem
          split <;> simp [h0]
      · have hnotin : x ∉ (a :: as) :=
          fun hcontra => absurd (foldl_min_le_all a as x hcontra) hx
        rw [count_rangeBlocks_of_lt _ _ _ _ (Int.not_le.mp hx),
          List.count_eq_zero_of_not_mem hnotin]

/-- `countingSort` returns a sorted list. -/
theorem countingSort_sorted (arr : List Int) : (countingSort arr).Sorted (· ≤ ·) := by
  cases arr with
  | nil => simp [countingSort]
  | cons a as =>
      rw [countingSort_cons]
      exact sorted_rangeBlocks _ _ _

/-- `countingSort` returns a permutation of its input. -/
theorem countingSort_perm (arr : List Int) : (countingSort arr).Perm arr :=
  List.perm_iff_count.mpr (countingSort_count arr)

/-- `countingSort` preserves the length. -/
theorem countingSort_length (arr : List Int) : (countingSort arr).length = arr.length :=
  (countingSort_perm arr).length_eq

/-- `countingSort` preserves the set of occurring values. -/
theorem countingSort_mem (arr : List Int) (x : Int) : x ∈ countingSort arr ↔ x ∈ arr := by
  constructor
  · intro h
    have h1 := List.count_pos_iff.mpr h
    rw [countingSort_count arr x] at h1
    exact List.count_pos_iff.mp h1
  · intro h
    have h1 := List.count_pos_iff.mpr h
    rw [← countingSort_count arr x] at h1
    exact List.count_pos_iff.mp h1

/-- If `lo`, `hi` are respectively a lower and an upper bound of the non-empty list `l`
which are themselves elements of `l`, then `countingSort l` is the block construction over
the range `[lo, hi]`. -/
theorem countingSort_of_min_max (l : List Int) (lo hi : Int) (k : Nat)
    (hne : l ≠ []) (hlo : lo ∈ l) (hhi : hi ∈ l)
    (hle : ∀ y ∈ l, lo ≤ y) (hge : ∀ y ∈ l, y ≤ hi) (hk : k = (hi - lo).toNat + 1) :
    countingSort l = rangeBlocks lo k l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a as =>
      have hspec := foldl_min_spec a as
      have hspec' := foldl_max_spec a as
      have h1 : as.foldl (fun m x => min m x) a = lo := by
        apply le_antisymm
        · rcases List.mem_cons.mp hlo with hyb | hlo'
          · rw [hyb]; exact hspec.1
          · exact hspec.2.1 lo hlo'
        · rcases hspec.2.2 with h | h
          · rw [h]; exact hle a (by simp)
          · exact hle _ (List.mem_cons_of_mem a h)
      have h2 : as.foldl (fun m x => max m x) a = hi := by
        apply le_antisymm
        · rcases hspec'.2.2 with h | h
          · rw [h]; exact hge a (by simp)
          · exact hge _ (List.mem_cons_of_mem a h)
        · rcases List.mem_cons.mp hhi with hyb | hhi'
          · rw [hyb]; exact hspec'.1
          · exact hspec'.2.1 hi hhi'
      rw [countingSort_cons, h1, h2, ← hk]

/-- Counting sort is idempotent: sorting an already sorted list changes nothing. -/
theorem countingSort_idempotent (arr : List Int) :
    countingSort (countingSort arr) = countingSort arr := by
  cases arr with
  | nil => simp [countingSort]
  | cons a as =>
      let lo := as.foldl (fun m x => min m x) a
      let hi := as.foldl (fun m x => max m x) a
      let k := (hi - lo).toNat + 1
      have hcs : countingSort (a :: as) = rangeBlocks lo k (a :: as) := by
        rw [countingSort_cons]
      have hle := foldl_min_le_all a as
      have hge := foldl_max_ge_all a as
      have hlo_mem : as.foldl (fun m x => min m x) a ∈ (a :: as) := by
        rcases (foldl_min_spec a as).2.2 with h | h
        · rw [h]; simp
        · exact List.mem_cons_of_mem a h
      have hhi_mem : as.foldl (fun m x => max m x) a ∈ (a :: as) := by
        rcases (foldl_max_spec a as).2.2 with h | h
        · rw [h]; simp
        · exact List.mem_cons_of_mem a h
      have hk0 : 0 < k := Nat.succ_pos _
      have hres_lo : lo ∈ rangeBlocks lo k (a :: as) := by
        have hcnt : 0 < (a :: as).count (lo + (0 : Int)) :=
          List.count_pos_iff.mpr (by simpa using hlo_mem)
        have h := mem_rangeBlocks_of_count lo (a :: as) k 0 hk0
          (Nat.pos_iff_ne_zero.mp hcnt)
        simpa using h
      have hcast : lo + ((hi - lo).toNat : Int) = hi := by
        have hlohi : lo ≤ hi := hle hi hhi_mem
        rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ hi - lo)]
        omega
      have hres_hi : hi ∈ rangeBlocks lo k (a :: as) := by
        have hcnt : 0 < (a :: as).count (lo + ((hi - lo).toNat : Int)) :=
          List.count_pos_iff.mpr (by rw [hcast]; exact hhi_mem)
        have h := mem_rangeBlocks_of_count lo (a :: as) k ((hi - lo).toNat)
          (Nat.lt_succ_self _) (Nat.pos_iff_ne_zero.mp hcnt)
        rwa [hcast] at h
      have hres_bound : ∀ y ∈ rangeBlocks lo k (a :: as), lo ≤ y ∧ y ≤ hi := by
        intro y hy
        obtain ⟨i, hi_lt, hy'⟩ := mem_rangeBlocks lo (a :: as) y k hy
        have hi_le : (i : Int) ≤ ((hi - lo).toNat : Int) :=
          Int.ofNat_le.mpr (Nat.lt_succ_iff.mp hi_lt)
        constructor
        · rw [hy']; omega
        · rw [hy', ← hcast]; exact add_le_add_left hi_le lo
      have hne : rangeBlocks lo k (a :: as) ≠ [] := by
        intro h
        rw [h] at hres_lo
        exact absurd hres_lo (by simp)
      rw [hcs]
      rw [countingSort_of_min_max (rangeBlocks lo k (a :: as)) lo hi k hne hres_lo hres_hi
        (fun y hy => (hres_bound y hy).1) (fun y hy => (hres_bound y hy).2) rfl]
      exact rangeBlocks_congr lo (rangeBlocks lo k (a :: as)) (a :: as)
        (fun x => by rw [← hcs]; exact countingSort_count (a :: as) x) k

/-! ## 5. Properties of the functional implementation -/

/-- The result is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop := (countingSort arr).Sorted (· ≤ ·)

theorem sorted_thm (arr : List Int) : sorted_prop arr := countingSort_sorted arr

/-- The result is a permutation of the input: nothing is lost and nothing is invented. -/
def perm_prop (arr : List Int) : Prop := (countingSort arr).Perm arr

theorem perm_thm (arr : List Int) : perm_prop arr := countingSort_perm arr

/-- The result has the same length as the input. -/
def length_prop (arr : List Int) : Prop := (countingSort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr := countingSort_length arr

/-- Every value occurs in the result exactly as often as in the input; this is precisely
what the counting phase (`count[num - min_val] += 1`) guarantees. -/
def count_prop (arr : List Int) : Prop :=
  ∀ x : Int, (countingSort arr).count x = arr.count x

theorem count_thm (arr : List Int) : count_prop arr := countingSort_count arr

/-- The result contains exactly the values of the input. -/
def mem_prop (arr : List Int) : Prop := ∀ x : Int, x ∈ countingSort arr ↔ x ∈ arr

theorem mem_thm (arr : List Int) : mem_prop arr := fun x => countingSort_mem arr x

/-- Sorting an already sorted list changes nothing. -/
def idempotent_prop (arr : List Int) : Prop :=
  countingSort (countingSort arr) = countingSort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr := countingSort_idempotent arr

/-- The empty list is sorted to the empty list (Python: `if not arr: return []`). -/
def empty_prop : Prop := countingSort [] = []

theorem empty_thm : empty_prop := by
  show countingSort [] = []
  simp [countingSort]

/-- A singleton list is already sorted (Python doctest `counting_sort([1]) == [1]`). -/
def singleton_prop (a : Int) : Prop := countingSort [a] = [a]

theorem singleton_thm (a : Int) : singleton_prop a := by
  show countingSort [a] = [a]
  have h : countingSort [a] = rangeBlocks a 1 [a] := by
    rw [countingSort_cons]
    simp
  rw [h, rangeBlocks_succ, rangeBlocks_zero, List.nil_append]
  simp

/-! ## 6. Post-condition -/

/-- Post-condition of `counting_sort`: the returned list is sorted and it is a permutation
of the input, hence has the same length and the same multiplicities for every value. -/
def Post_prop (arr result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ result.Perm arr ∧ result.length = arr.length ∧
    ∀ x : Int, result.count x = arr.count x

/-! ## 7. Property-based tests -/

/-- Executable counterpart of the order relation `(· ≤ ·)`. -/
def leB (x y : Int) : Bool := if x ≤ y then true else false

/-- Executable counterpart of `sorted_prop` (`List.Sorted (· ≤ ·)`). -/
def sortedB : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: l => leB x y && sortedB (y :: l)

/-- Executable counterpart of `perm_prop` / `count_prop`: both lists contain every value
equally often. -/
def sameCountsB (l₁ l₂ : List Int) : Bool :=
  (l₁ ++ l₂).all (fun x => l₁.count x == l₂.count x)

/-- Executable counterpart of `mem_prop`: both lists contain the same values. -/
def memB (arr res : List Int) : Bool :=
  (arr.all (fun x => res.any (fun y => x == y))) &&
    (res.all (fun x => arr.any (fun y => x == y)))

/-- Executable counterpart of `Post_prop`. -/
def postB (arr result : List Int) : Bool :=
  sortedB result && sameCountsB result arr && (result.length == arr.length)

/-- Executable counterpart of `idempotent_prop`. -/
def idemB (arr : List Int) : Bool :=
  let r := countingSort arr
  countingSort r == r

-- Randomised property-based tests: `Plausible` searches for a counterexample and the file
-- fails to compile if it finds one.
#eval Plausible.Testable.check (∀ xs : List Int, sortedB (countingSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, sameCountsB (countingSort xs) xs)
#eval Plausible.Testable.check (∀ xs : List Int, (countingSort xs).length == xs.length)
#eval Plausible.Testable.check (∀ xs : List Int, memB xs (countingSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, postB xs (countingSort xs))
#eval Plausible.Testable.check (∀ xs : List Int, idemB xs)

-- Bounded property-based tests (exhaustive over a fixed family of inputs).
def testLists : List (List Int) :=
  [[], [1], [3, 1, 2], [-5, 3, -1, 0, 2, 2, -5], [7], [2, 1], [0, 0, 0], [-1, -2, -3],
   [100, -100, 0], [5, 2, 4, 6, 1, 3], [9, 8, 7, 6, 5, 4, 3, 2, 1], [3, 1, 4, 1, 2, 3],
   [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]]

example : testLists.all (fun xs => postB xs (countingSort xs)) = true := by native_decide
example : testLists.all (fun xs => memB xs (countingSort xs)) = true := by native_decide
example : testLists.all (fun xs => idemB xs) = true := by native_decide

example : (List.range 25).all (fun n =>
    let xs := (List.range n).map (fun i => ((i * 7) % 11 : Int) - 5)
    postB xs (countingSort xs)) = true := by native_decide

example : (List.range 20).all (fun n =>
    let xs := List.replicate n (-3 : Int)
    postB xs (countingSort xs)) = true := by native_decide

example : (List.range 15).all (fun n =>
    let xs := (List.range n).map (fun i => (12 : Int) - 2 * (i : Int))
    sortedB (countingSort xs) && (countingSort xs).length == xs.length) = true :=
  by native_decide

/-! ## 8. Correctness theorem -/

/-- `counting_sort` is correct: under the (always satisfiable) pre-condition it returns a
sorted permutation of its input. -/
theorem correctness (arr : List Int) : Pre arr → Post_prop arr (countingSort arr) := by
  intro _
  exact ⟨countingSort_sorted arr, countingSort_perm arr, countingSort_length arr,
    countingSort_count arr⟩

/-! ## 9. Imperative implementation -/

/-- Imperative counting sort, written with `Id.run do` and mutable state, following the
Python program line by line. -/
def countingSortImp (arr : List Int) : List Int := Id.run do
  -- `if not arr: return []`
  if arr.isEmpty then
    return []
  -- `min_val = min(arr)`
  let mut lo := arr.head!
  for x in arr do
    lo := min lo x
  -- `max_val = max(arr)`
  let mut hi := arr.head!
  for x in arr do
    hi := max hi x
  -- `range_size = max_val - min_val + 1`
  let k := (hi - lo).toNat + 1
  -- `count = [0] * range_size` followed by `for num in arr: count[num - min_val] += 1`
  let mut c : Nat → Nat := fun _ => 0
  for x in arr do
    c := countStep lo c x
  -- `result = []` followed by
  -- `for i in range(range_size): result.extend([i + min_val] * count[i])`
  let mut out : List Int := []
  for i in List.range k do
    out := out ++ List.replicate (c i) (lo + (i : Int))
  return out

/-! ## 10. Imperative tests -/

#eval countingSortImp [3, 1, 2]
#eval countingSortImp ([] : List Int)
#eval countingSortImp [1]
#eval countingSortImp [-3, 5, -1, 0, 5, -3]

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp [] = ([] : List Int) := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSortImp [-3, 5, -1, 0, 5, -3] = [-3, -3, -1, 0, 5, 5] := by native_decide

-- property-based tests for the imperative implementation
#eval Plausible.Testable.check (∀ xs : List Int, sortedB (countingSortImp xs))
#eval Plausible.Testable.check (∀ xs : List Int, postB xs (countingSortImp xs))
example : testLists.all (fun xs => postB xs (countingSortImp xs)) = true := by native_decide
example : testLists.all (fun xs => countingSortImp xs == countingSort xs) = true :=
  by native_decide

/-! ## 11. Equivalence of the imperative and the functional implementation -/

/-- The imperative implementation computes exactly the same list as the functional one. -/
theorem imp_eq_functional (arr : List Int) : countingSortImp arr = countingSort arr := by
  cases arr with
  | nil => simp [countingSortImp, countingSort]
  | cons a as => simp [countingSortImp, countingSort]

end counting_sort

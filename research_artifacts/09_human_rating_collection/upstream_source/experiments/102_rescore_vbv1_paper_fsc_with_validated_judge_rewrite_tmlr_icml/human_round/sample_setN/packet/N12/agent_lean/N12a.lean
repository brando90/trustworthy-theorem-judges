import Mathlib

/-!
# Counting Sort for a List of Integers

This module formalizes the Python `counting_sort` program in Lean 4.
The algorithm sorts a list of integers (supporting negative numbers via shifting by the
minimum element) by:
1. Returning `[]` on an empty list.
2. Computing the maximum (`max_val`) and minimum (`min_val`) elements of the list.
3. Computing `range_size = max_val - min_val + 1`.
4. Building a count list of length `range_size` where entry `i` counts occurrences of
   `i + min_val` in the input list.
5. Reconstructing the sorted list by repeating each value `i + min_val` according to its count.
-/

set_option linter.dupNamespace false

namespace counting_sort

/-! ## 1. Functional Implementation -/

/-- Single step of counting occurrences: increment the bucket at index `(num - min_val).toNat`. -/
def countStep (min_val : Int) (c : List Nat) (num : Int) : List Nat :=
  let idx := (num - min_val).toNat
  c.set idx (c.getD idx 0 + 1)

/-- Build the count list of length `range_size` by folding `countStep` over `arr`. -/
def buildCounts (arr : List Int) (min_val : Int) (range_size : Nat) : List Nat :=
  arr.foldl (countStep min_val) (List.replicate range_size 0)

/-- Direct characterization of the output expansion using `List.count`. -/
def expandCounts (arr : List Int) (min_val : Int) (range_size : Nat) : List Int :=
  (List.range range_size).flatMap (fun (i : Nat) =>
    List.replicate (arr.count ((i : Int) + min_val)) ((i : Int) + min_val))

/--
Functional implementation of counting sort for a list of integers.
Supports negative integers via shifting by `min_val`.
-/
def counting_sort (arr : List Int) : List Int :=
  match arr with
  | [] => []
  | x :: xs =>
    let max_val := xs.foldl max x
    let min_val := xs.foldl min x
    let range_size := (max_val - min_val).toNat + 1
    let count := buildCounts (x :: xs) min_val range_size
    (List.range range_size).flatMap (fun (i : Nat) =>
      List.replicate (count.getD i 0) ((i : Int) + min_val))

/-! ## 2. Unit Tests -/

-- Basic functionality tests
example : counting_sort [3, 1, 2] = [1, 2, 3] := by native_decide
example : counting_sort [1, 2, 3] = [1, 2, 3] := by native_decide
example : counting_sort [2, 1, 3] = [1, 2, 3] := by native_decide

-- Edge cases
example : counting_sort [] = [] := by native_decide
example : counting_sort [1] = [1] := by native_decide

-- Larger arrays
example : counting_sort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : counting_sort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : counting_sort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide

-- Two elements
example : counting_sort [2, 1] = [1, 2] := by native_decide
example : counting_sort [1, 2] = [1, 2] := by native_decide

-- Duplicates
example : counting_sort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : counting_sort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : counting_sort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : counting_sort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide

-- Already sorted
example : counting_sort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide

-- Reverse sorted
example : counting_sort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide

-- Random order
example : counting_sort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide

-- With zeros
example : counting_sort [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide

-- Larger test case
example : counting_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

-- Negative numbers (testing range shift)
example : counting_sort [-3, -1, -2, 0, 2, -3] = [-3, -3, -2, -1, 0, 2] := by native_decide
example : counting_sort [-5, -10, 0, -3, 8, 5, -1, 10] =
    [-10, -5, -3, -1, 0, 5, 8, 10] := by native_decide

#eval counting_sort [3, 1, 2]
#eval counting_sort ([] : List Int)
#eval counting_sort [1]
#eval counting_sort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval counting_sort [-3, -1, -2, 0, 2, -3]

/-! ## 3. Pre-condition -/

/--
Pre-condition for `counting_sort`.
In Python, `pre(arr)` checks that `arr` is a `List[int]`, which is guaranteed by
the static type `List Int` in Lean 4.
-/
def Pre (_arr : List Int) : Prop := True

/-! ## 4. Helper Lemmas -/

theorem getD_set_of_lt (c : List Nat) (idx val i d : Nat) (hi : i < c.length) :
    (c.set idx val).getD i d = if idx = i then val else c.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2
  · rfl
  · omega
  · rfl

theorem length_countStep (min_val : Int) (c : List Nat) (num : Int) :
    (countStep min_val c num).length = c.length := by
  simp [countStep]

theorem foldl_countStep_getD (min_val : Int) (a : List Int) (c : List Nat) (i : Nat)
    (hi : i < c.length) (hmin : ∀ num ∈ a, min_val ≤ num) :
    (a.foldl (countStep min_val) c).getD i 0 = c.getD i 0 + a.count ((i : Int) + min_val) := by
  induction a generalizing c with
  | nil => simp
  | cons x xs ih =>
    have hx : min_val ≤ x := hmin x (by simp)
    have hxs : ∀ num ∈ xs, min_val ≤ num := fun num h => hmin num (by simp [h])
    have hlen : i < (countStep min_val c x).length := by
      rw [length_countStep]; exact hi
    simp only [List.foldl_cons, ih (countStep min_val c x) hlen hxs]
    simp only [countStep, getD_set_of_lt c _ _ i 0 hi, List.count_cons, beq_iff_eq]
    by_cases h1 : (x - min_val).toNat = i
    · rw [if_pos h1, h1, if_pos (by omega)]
      omega
    · rw [if_neg h1, if_neg (by omega)]
      omega

theorem buildCounts_getD (arr : List Int) (min_val : Int) (range_size i : Nat)
    (hi : i < range_size) (hmin : ∀ num ∈ arr, min_val ≤ num) :
    (buildCounts arr min_val range_size).getD i 0 = arr.count ((i : Int) + min_val) := by
  unfold buildCounts
  have hlen : i < (List.replicate range_size 0).length := by simp [hi]
  rw [foldl_countStep_getD min_val arr _ i hlen hmin]
  simp [List.getD_eq_getElem?_getD, hi]

theorem foldl_min_le (x : Int) (xs : List Int) :
    xs.foldl min x ≤ x ∧ ∀ y ∈ xs, xs.foldl min x ≤ y := by
  induction xs generalizing x with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    have ⟨h1, h2⟩ := ih (min x a)
    refine ⟨by omega, ⟨by omega, h2⟩⟩

theorem le_foldl_max (x : Int) (xs : List Int) :
    x ≤ xs.foldl max x ∧ ∀ y ∈ xs, y ≤ xs.foldl max x := by
  induction xs generalizing x with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    have ⟨h1, h2⟩ := ih (max x a)
    refine ⟨by omega, ⟨by omega, h2⟩⟩

theorem min_le_of_mem (x : Int) (xs : List Int) (y : Int) (hy : y ∈ x :: xs) :
    xs.foldl min x ≤ y := by
  have ⟨h1, h2⟩ := foldl_min_le x xs
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h1
  · exact h2 y hy

theorem le_max_of_mem (x : Int) (xs : List Int) (y : Int) (hy : y ∈ x :: xs) :
    y ≤ xs.foldl max x := by
  have ⟨h1, h2⟩ := le_foldl_max x xs
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h1
  · exact h2 y hy

theorem counting_sort_eq_expandCounts (x : Int) (xs : List Int) :
    counting_sort (x :: xs) =
      expandCounts (x :: xs) (xs.foldl min x) ((xs.foldl max x - xs.foldl min x).toNat + 1) := by
  simp only [counting_sort, expandCounts]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [buildCounts_getD (x :: xs) (xs.foldl min x) _ i hi (min_le_of_mem x xs)]

theorem count_expandCounts (arr : List Int) (lo : Int) (n : Nat) (v : Int) :
    (expandCounts arr lo n).count v =
      if lo ≤ v ∧ v < lo + (n : Int) then arr.count v else 0 := by
  induction n with
  | zero =>
    simp only [expandCounts, List.range_zero, List.flatMap_nil, List.count_nil]
    split_ifs with h <;> omega
  | succ n ih =>
    simp only [expandCounts, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.count_append, List.count_replicate] at *
    rw [ih]
    simp only [beq_iff_eq]
    by_cases h1 : lo ≤ v ∧ v < lo + (n : Int)
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]
      omega
    · rw [if_neg h1]
      by_cases h2 : (n : Int) + lo = v
      · rw [if_pos h2, if_pos (by omega), h2]; omega
      · rw [if_neg h2, if_neg (by omega)]

theorem mem_expandCounts_le (arr : List Int) (lo : Int) (n : Nat) (x : Int)
    (hx : x ∈ expandCounts arr lo n) : lo ≤ x ∧ x < lo + (n : Int) := by
  simp only [expandCounts, List.mem_flatMap, List.mem_replicate] at hx
  rcases hx with ⟨i, hi, _, rfl⟩
  rw [List.mem_range] at hi
  omega

theorem pairwise_replicate_le (k : Nat) (a : Int) :
    List.Pairwise (· ≤ ·) (List.replicate k a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.pairwise_cons, List.mem_replicate]
    refine ⟨fun b ⟨_, hb⟩ => by omega, ih⟩

theorem pairwise_expandCounts (arr : List Int) (lo : Int) (n : Nat) :
    List.Pairwise (· ≤ ·) (expandCounts arr lo n) := by
  induction n with
  | zero => simp [expandCounts]
  | succ n ih =>
    simp only [expandCounts, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.pairwise_append]
    refine ⟨ih, pairwise_replicate_le _ _, ?_⟩
    intro a ha b hb
    have ha' := mem_expandCounts_le arr lo n a ha
    simp only [List.mem_replicate] at hb
    rcases hb with ⟨_, rfl⟩
    omega

theorem pairwise_mergeSort_int (arr : List Int) :
    List.Pairwise (· ≤ ·) (arr.mergeSort (· ≤ ·)) := by
  have h := List.sorted_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total a b)
    arr
  simpa only [decide_eq_true_eq] using h

/-! ## 5. Properties and Theorems -/

/-- Property 1: Counting sort preserves the count of every integer element. -/
def count_prop (arr : List Int) (v : Int) : Prop :=
  (counting_sort arr).count v = arr.count v

theorem count_thm (arr : List Int) (v : Int) : count_prop arr v := by
  unfold count_prop
  cases arr with
  | nil => rfl
  | cons x xs =>
    rw [counting_sort_eq_expandCounts, count_expandCounts]
    have hlo_hi : xs.foldl min x ≤ xs.foldl max x := by
      have := min_le_of_mem x xs x (by simp)
      have := le_max_of_mem x xs x (by simp)
      omega
    split_ifs with h
    · rfl
    · symm
      rw [List.count_eq_zero]
      intro hv
      have hmin := min_le_of_mem x xs v hv
      have hmax := le_max_of_mem x xs v hv
      omega

/-- Property 2: The output of `counting_sort` is a permutation of the input list. -/
def perm_prop (arr : List Int) : Prop :=
  (counting_sort arr).Perm arr

theorem perm_thm (arr : List Int) : perm_prop arr := by
  unfold perm_prop
  rw [List.perm_iff_count]
  exact count_thm arr

/-- Property 3: The output of `counting_sort` is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop :=
  List.Pairwise (· ≤ ·) (counting_sort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  unfold sorted_prop
  cases arr with
  | nil => simp [counting_sort]
  | cons x xs =>
    rw [counting_sort_eq_expandCounts]
    exact pairwise_expandCounts _ _ _

/-- Property 4: `counting_sort` preserves the length of the input list. -/
def length_prop (arr : List Int) : Prop :=
  (counting_sort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr := by
  unfold length_prop
  exact (perm_thm arr).length_eq

/-- Property 5: `counting_sort` preserves element membership. -/
def mem_prop (arr : List Int) (v : Int) : Prop :=
  v ∈ counting_sort arr ↔ v ∈ arr

theorem mem_thm (arr : List Int) (v : Int) : mem_prop arr v := by
  unfold mem_prop
  exact (perm_thm arr).mem_iff

/-- Property 6: `counting_sort` on the empty list returns the empty list. -/
def empty_prop : Prop :=
  counting_sort [] = []

theorem empty_thm : empty_prop := rfl

/-- Property 7: `counting_sort arr` is empty if and only if `arr` is empty. -/
def nil_iff_prop (arr : List Int) : Prop :=
  counting_sort arr = [] ↔ arr = []

theorem nil_iff_thm (arr : List Int) : nil_iff_prop arr := by
  unfold nil_iff_prop
  constructor
  · intro h
    have hlen := length_thm arr
    unfold length_prop at hlen
    rw [h, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  · intro h
    subst h
    rfl

/-- Property 8: `counting_sort` on a singleton list returns the same singleton list. -/
def singleton_prop (x : Int) : Prop :=
  counting_sort [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x := by
  unfold singleton_prop
  exact List.perm_singleton.mp (perm_thm [x])

/-- Property 9: Permutation invariance — two lists that are permutations sort to the same list. -/
def perm_invariant_prop (l₁ l₂ : List Int) : Prop :=
  l₁.Perm l₂ → counting_sort l₁ = counting_sort l₂

theorem perm_invariant_thm (l₁ l₂ : List Int) : perm_invariant_prop l₁ l₂ := by
  intro h
  apply List.Perm.eq_of_sorted (fun a b _ _ hab hba => le_antisymm hab hba)
  · exact sorted_thm l₁
  · exact sorted_thm l₂
  · exact (perm_thm l₁).trans (h.trans (perm_thm l₂).symm)

/-- Property 10: Fixed point on already sorted lists. -/
def sorted_fixed_prop (arr : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr → counting_sort arr = arr

theorem sorted_fixed_thm (arr : List Int) : sorted_fixed_prop arr := by
  intro h
  apply List.Perm.eq_of_sorted (fun a b _ _ hab hba => le_antisymm hab hba)
  · exact sorted_thm arr
  · exact h
  · exact perm_thm arr

/-- Property 11: Idempotence — applying `counting_sort` twice equals applying it once. -/
def idempotent_prop (arr : List Int) : Prop :=
  counting_sort (counting_sort arr) = counting_sort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr := by
  unfold idempotent_prop
  exact sorted_fixed_thm (counting_sort arr) (sorted_thm arr)

/-- Property 12: Reversing the input list does not change the sorted result. -/
def reverse_invariant_prop (arr : List Int) : Prop :=
  counting_sort arr.reverse = counting_sort arr

theorem reverse_invariant_thm (arr : List Int) : reverse_invariant_prop arr := by
  unfold reverse_invariant_prop
  exact perm_invariant_thm arr.reverse arr (List.reverse_perm arr)

/-- Property 13: Every element in the sorted non-empty list is bounded by `min_val` and `max_val`. -/
def bounds_prop (x : Int) (xs : List Int) : Prop :=
  ∀ y ∈ counting_sort (x :: xs), xs.foldl min x ≤ y ∧ y ≤ xs.foldl max x

theorem bounds_thm (x : Int) (xs : List Int) : bounds_prop x xs := by
  intro y hy
  have hmem : y ∈ counting_sort (x :: xs) ↔ y ∈ x :: xs := mem_thm (x :: xs) y
  rw [hmem] at hy
  exact ⟨min_le_of_mem x xs y hy, le_max_of_mem x xs y hy⟩

/-- Property 14: `counting_sort` agrees with `List.mergeSort (· ≤ ·)` on all inputs. -/
def eq_mergeSort_prop (arr : List Int) : Prop :=
  counting_sort arr = arr.mergeSort (· ≤ ·)

theorem eq_mergeSort_thm (arr : List Int) : eq_mergeSort_prop arr := by
  unfold eq_mergeSort_prop
  apply List.Perm.eq_of_sorted (fun a b _ _ hab hba => le_antisymm hab hba)
  · exact sorted_thm arr
  · exact pairwise_mergeSort_int arr
  · exact (perm_thm arr).trans (List.mergeSort_perm arr (· ≤ ·)).symm

/-! ## 6. Post-condition -/

/--
Full post-condition for `counting_sort`: conjunction of sortedness, permutation,
count preservation, length preservation, membership preservation, empty-list characterization,
idempotence, fixed-point on sorted lists, reverse invariance, and equivalence to `mergeSort`.
-/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧
  perm_prop arr ∧
  (∀ v : Int, count_prop arr v) ∧
  length_prop arr ∧
  (∀ v : Int, mem_prop arr v) ∧
  nil_iff_prop arr ∧
  idempotent_prop arr ∧
  sorted_fixed_prop arr ∧
  reverse_invariant_prop arr ∧
  eq_mergeSort_prop arr

abbrev Post (arr : List Int) : Prop := Post_prop arr

/-! ## 7. Property-Based Tests (PBTs) -/

/-- Decidable Boolean check for whether a `List Int` is sorted non-decreasingly. -/
def isSortedBool (l : List Int) : Bool :=
  l.zipWith (fun a b => decide (a ≤ b)) l.tail |>.all id

-- PBT for `count_prop`
#eval Plausible.Testable.check (∀ (arr : List Int) (v : Int),
  (counting_sort arr).count v = arr.count v)

-- PBT for `perm_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  (counting_sort arr).isPerm arr = true)

-- PBT for `sorted_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  isSortedBool (counting_sort arr) = true)

-- PBT for `length_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  (counting_sort arr).length = arr.length)

-- PBT for `mem_prop`
#eval Plausible.Testable.check (∀ (arr : List Int) (v : Int),
  (decide (v ∈ counting_sort arr)) = (decide (v ∈ arr)))

-- PBT for `empty_prop`
example : counting_sort [] = [] := by native_decide

-- PBT for `nil_iff_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  (counting_sort arr == []) = (arr == []))

-- PBT for `singleton_prop`
#eval Plausible.Testable.check (∀ x : Int,
  counting_sort [x] = [x])

-- PBT for `perm_invariant_prop`
#eval Plausible.Testable.check (∀ l₁ l₂ : List Int,
  counting_sort (l₁ ++ l₂) = counting_sort (l₂ ++ l₁))

example : ([([1, -1, 2] : List Int), [-1, 2, 1], [2, 1, -1], [0, 0, -2], [-2, 0, 0]].all
    (fun l => counting_sort l == counting_sort l.reverse)) = true := by native_decide

-- PBT for `sorted_fixed_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  let s := arr.mergeSort (· ≤ ·)
  counting_sort s = s)

example : ([([] : List Int), [-5], [-3, -1, 0, 2, 4], [1, 1, 2, 3, 3]].all
    (fun s => counting_sort s == s)) = true := by native_decide

-- PBT for `idempotent_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  counting_sort (counting_sort arr) = counting_sort arr)

-- PBT for `reverse_invariant_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  counting_sort arr.reverse = counting_sort arr)

-- PBT for `bounds_prop`
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let lo := xs.foldl min x
  let hi := xs.foldl max x
  (counting_sort (x :: xs)).all (fun y => decide (lo ≤ y ∧ y ≤ hi)) = true)

-- PBT for `eq_mergeSort_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  counting_sort arr = arr.mergeSort (· ≤ ·))

-- PBT for `Post_prop`
#eval Plausible.Testable.check (∀ arr : List Int,
  isSortedBool (counting_sort arr) &&
  (counting_sort arr).isPerm arr &&
  ((counting_sort arr).length == arr.length) &&
  ((counting_sort arr == []) == (arr == [])) &&
  (counting_sort (counting_sort arr) == counting_sort arr) &&
  (counting_sort arr.reverse == counting_sort arr) &&
  (counting_sort arr == arr.mergeSort (· ≤ ·)))

/-! ## 8. Correctness Theorem -/

/--
Main correctness theorem: for any integer list `arr` satisfying `Pre arr`,
`counting_sort arr` satisfies `Post_prop arr`.
-/
theorem counting_sort_correct (arr : List Int) (_hpre : Pre arr) : Post_prop arr :=
  ⟨sorted_thm arr,
   perm_thm arr,
   count_thm arr,
   length_thm arr,
   mem_thm arr,
   nil_iff_thm arr,
   idempotent_thm arr,
   sorted_fixed_thm arr,
   reverse_invariant_thm arr,
   eq_mergeSort_thm arr⟩

/-! ## 9. Imperative Implementation -/

/--
Imperative implementation of `counting_sort` using `Id.run do` and mutable variables
(`max_val`, `min_val`, `count`, and `result`), directly mirroring the Python loops.
-/
def counting_sort_imp (arr : List Int) : List Int := Id.run do
  match arr with
  | [] => return []
  | x :: xs =>
    let mut max_val : Int := x
    for num in xs do
      max_val := max max_val num
    let mut min_val : Int := x
    for num in xs do
      min_val := min min_val num
    let range_size : Nat := (max_val - min_val).toNat + 1
    let mut count : List Nat := List.replicate range_size 0
    for num in x :: xs do
      let idx := (num - min_val).toNat
      count := count.set idx (count.getD idx 0 + 1)
    let mut result : List Int := []
    for i in List.range range_size do
      result := result ++ List.replicate (count.getD i 0) ((i : Int) + min_val)
    return result

/-! ## 10. Imperative Tests -/

example : counting_sort_imp [3, 1, 2] = [1, 2, 3] := by native_decide
example : counting_sort_imp [1, 2, 3] = [1, 2, 3] := by native_decide
example : counting_sort_imp [2, 1, 3] = [1, 2, 3] := by native_decide
example : counting_sort_imp [] = [] := by native_decide
example : counting_sort_imp [1] = [1] := by native_decide
example : counting_sort_imp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : counting_sort_imp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : counting_sort_imp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : counting_sort_imp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : counting_sort_imp [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : counting_sort_imp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
    [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : counting_sort_imp [-3, -1, -2, 0, 2, -3] = [-3, -3, -2, -1, 0, 2] := by native_decide

#eval counting_sort_imp [3, 1, 2]
#eval counting_sort_imp ([] : List Int)
#eval counting_sort_imp [-3, -1, -2, 0, 2, -3]

-- PBT checking functional-imperative equivalence on random lists
#eval Plausible.Testable.check (∀ arr : List Int,
  counting_sort arr = counting_sort_imp arr)

/-! ## 11. Equivalence Theorem -/

theorem forIn_id_yield_eq_foldl {α β : Type*} (l : List α) (init : β) (f : α → β → β) :
    (forIn (m := Id) l init (fun a b => ForInStep.yield (f a b))) =
      l.foldl (fun b a => f a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, List.foldl_cons, bind]
    exact ih (f x init)

theorem foldl_append_eq_flatMap {α β : Type*} (l : List α) (f : α → List β) (init : List β) :
    l.foldl (fun acc x => acc ++ f x) init = init ++ l.flatMap f := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]

/--
Functional-imperative equivalence theorem:
`counting_sort` and `counting_sort_imp` produce identical results for every input list `arr`.
-/
theorem counting_sort_equiv (arr : List Int) :
    counting_sort arr = counting_sort_imp arr := by
  cases arr with
  | nil => rfl
  | cons x xs =>
    simp only [counting_sort, counting_sort_imp, buildCounts,
      Id.run, forIn_id_yield_eq_foldl, pure, bind]
    rw [foldl_append_eq_flatMap, List.nil_append]
    rfl

/-- Corollary: `counting_sort_imp` is sorted and a permutation of its input. -/
theorem counting_sort_imp_correct (arr : List Int) (_hpre : Pre arr) :
    List.Pairwise (· ≤ ·) (counting_sort_imp arr) ∧ (counting_sort_imp arr).Perm arr := by
  rw [← counting_sort_equiv arr]
  exact ⟨sorted_thm arr, perm_thm arr⟩

end counting_sort

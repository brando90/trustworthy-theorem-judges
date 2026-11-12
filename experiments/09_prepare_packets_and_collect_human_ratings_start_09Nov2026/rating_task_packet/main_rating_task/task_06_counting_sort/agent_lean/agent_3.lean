import Mathlib

/-!
# Counting sort

Lean 4 formalization of the Python program `counting_sort.py`.

The Python function `counting_sort(arr)` sorts a list of integers:
* the empty list is returned unchanged;
* otherwise it computes `min_val`/`max_val`, builds a count table of size
  `max_val - min_val + 1`, counts the occurrences of every element
  (`count[num - min_val] += 1`) and then emits, for every `i` in
  `range(range_size)`, the value `i + min_val` exactly `count[i]` times
  (`result.extend([i + min_val] * count[i])`).

The precondition `pre(arr)` (the argument is a list whose elements are all
`int`) is enforced by the type `List Int`; the Python `ValueError` branch for
non-integer elements is therefore unrepresentable (vacuous) in this model.

Contents:
* functional implementation `countingSort` and unit tests,
* pre-condition `Pre`, properties (`*_prop` / `*_thm`), post-condition
  `Post_prop` and the correctness theorem `correctness_thm`,
* property-based tests,
* imperative implementation `countingSortImp` (`Id.run do`, mutable state,
  count array) and the equivalence theorem `equiv_thm`.
-/

namespace counting_sort

/-! ## Functional implementation -/

/-- The output phase of counting sort: for every `i < rangeSize` emit the value
`i + minVal` as many times as it occurs in `arr` (this number is `count[i]` in
the Python program). -/
def build (minVal : Int) (arr : List Int) (rangeSize : Nat) : List Int :=
  (List.range rangeSize).flatMap
    (fun (i : Nat) => List.replicate (arr.count ((i : Int) + minVal)) ((i : Int) + minVal))

/-- Counting sort (functional version of the Python `counting_sort`). -/
def countingSort (arr : List Int) : List Int :=
  match arr with
  | [] => []
  | x :: xs =>
    let maxVal := xs.foldl max x
    let minVal := xs.foldl min x
    let rangeSize := (maxVal - minVal + 1).toNat
    build minVal (x :: xs) rangeSize

/-! ## Unit tests (mirroring the Python `check`) -/

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSort [] = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [2, 1] = [1, 2] := by native_decide
example : countingSort [1, 2] = [1, 2] := by native_decide
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
-- negative numbers are supported via the shift by `min_val`
example : countingSort [-3, 5, -10, 0, 5] = [-10, -3, 0, 5, 5] := by native_decide

#eval countingSort [3, 1, 2]
#eval countingSort []
#eval countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval countingSort [-3, 5, -10, 0, 5]

-- The Python negative test `candidate([1, 2.5])` raises `ValueError`; a list
-- containing a non-integer cannot be expressed as a `List Int`, so this
-- branch is unrepresentable in the Lean model.

/-! ## Pre-condition -/

/-- Python `pre`: the input is a list of integers.  This is guaranteed by the
type `List Int`, so the predicate is trivially true. -/
def Pre (_arr : List Int) : Prop := True

/-! ## Helper lemmas about `foldl max` / `foldl min` -/

theorem foldl_max_init_le (x : Int) (xs : List Int) : x ≤ xs.foldl max x := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left x y) (ih (max x y))

theorem foldl_max_mem_le (x : Int) (xs : List Int) : ∀ y ∈ xs, y ≤ xs.foldl max x := by
  induction xs generalizing x with
  | nil => simp
  | cons z zs ih =>
    intro y hy
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans (le_max_right x y) (foldl_max_init_le _ _)
    · exact ih _ y hy

/-- `xs.foldl max x` is an upper bound of every element of `x :: xs` (Python `max(arr)`). -/
theorem foldl_max_ge_all (x : Int) (xs : List Int) : ∀ y ∈ x :: xs, y ≤ xs.foldl max x := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact foldl_max_init_le _ _
  · exact foldl_max_mem_le _ _ y hy

theorem foldl_min_le_init (x : Int) (xs : List Int) : xs.foldl min x ≤ x := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (min x y)) (min_le_left x y)

theorem foldl_min_le_mem (x : Int) (xs : List Int) : ∀ y ∈ xs, xs.foldl min x ≤ y := by
  induction xs generalizing x with
  | nil => simp
  | cons z zs ih =>
    intro y hy
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans (foldl_min_le_init _ _) (min_le_right x y)
    · exact ih _ y hy

/-- `xs.foldl min x` is a lower bound of every element of `x :: xs` (Python `min(arr)`). -/
theorem foldl_min_le_all (x : Int) (xs : List Int) : ∀ y ∈ x :: xs, xs.foldl min x ≤ y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact foldl_min_le_init _ _
  · exact foldl_min_le_mem _ _ y hy

/-! ## Helper lemmas about `build` -/

theorem build_zero (minVal : Int) (arr : List Int) : build minVal arr 0 = [] := by
  simp [build]

theorem build_succ (minVal : Int) (arr : List Int) (n : Nat) :
    build minVal arr (n + 1)
      = build minVal arr n ++ List.replicate (arr.count ((n : Int) + minVal)) ((n : Int) + minVal) := by
  simp [build, List.range_succ, List.flatMap_append]

theorem mem_build_lt (minVal : Int) (arr : List Int) (n : Nat) :
    ∀ y ∈ build minVal arr n, y < (n : Int) + minVal := by
  induction n with
  | zero => simp [build_zero]
  | succ n ih =>
    intro y hy
    rw [build_succ, List.mem_append] at hy
    rcases hy with hy | hy
    · have := ih y hy
      push_cast
      omega
    · rw [List.mem_replicate] at hy
      rw [hy.2]
      push_cast
      omega

theorem mem_build_ge (minVal : Int) (arr : List Int) (n : Nat) :
    ∀ y ∈ build minVal arr n, minVal ≤ y := by
  induction n with
  | zero => simp [build_zero]
  | succ n ih =>
    intro y hy
    rw [build_succ, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ih y hy
    · rw [List.mem_replicate] at hy
      rw [hy.2]
      omega

theorem build_sorted (minVal : Int) (arr : List Int) (n : Nat) :
    List.Sorted (· ≤ ·) (build minVal arr n) := by
  induction n with
  | zero => simp [build_zero]
  | succ n ih =>
    rw [build_succ]
    unfold List.Sorted at *
    rw [List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · rw [List.pairwise_replicate]
      right
      exact le_refl _
    · intro a ha b hb
      have h1 := mem_build_lt minVal arr n a ha
      rw [List.mem_replicate] at hb
      rw [hb.2]
      omega

theorem count_build (minVal : Int) (arr : List Int) (n : Nat) (v : Int) :
    (build minVal arr n).count v
      = if minVal ≤ v ∧ v < (n : Int) + minVal then arr.count v else 0 := by
  induction n with
  | zero =>
    simp [build_zero]
  | succ n ih =>
    rw [build_succ, List.count_append, ih, List.count_replicate]
    push_cast
    by_cases hv : (n : Int) + minVal = v
    · subst hv
      simp
    · have hne : ((n : Int) + minVal == v) = false := by
        simp [hv]
      rw [hne]
      simp only [Bool.false_eq_true, if_false, add_zero]
      by_cases h1 : minVal ≤ v ∧ v < (n : Int) + minVal
      · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
      · rw [if_neg h1, if_neg]
        omega

theorem countingSort_nil : countingSort [] = [] := rfl

theorem countingSort_cons (x : Int) (xs : List Int) :
    countingSort (x :: xs)
      = build (xs.foldl min x) (x :: xs) ((xs.foldl max x - xs.foldl min x + 1).toNat) := rfl

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) (countingSort arr)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  unfold sorted_prop
  cases arr with
  | nil => simp [countingSort_nil]
  | cons x xs =>
    rw [countingSort_cons]
    exact build_sorted _ _ _

/-- The output is a permutation of the input. -/
def perm_prop (arr : List Int) : Prop :=
  List.Perm (countingSort arr) arr

theorem perm_thm (arr : List Int) : perm_prop arr := by
  unfold perm_prop
  cases arr with
  | nil => simp [countingSort_nil]
  | cons x xs =>
    rw [countingSort_cons]
    set mn := xs.foldl min x with hmn
    set mx := xs.foldl max x with hmx
    have hmn_le : ∀ y ∈ x :: xs, mn ≤ y := foldl_min_le_all x xs
    have hmx_ge : ∀ y ∈ x :: xs, y ≤ mx := foldl_max_ge_all x xs
    have hle : mn ≤ mx :=
      le_trans (hmn_le x (List.mem_cons_self ..)) (hmx_ge x (List.mem_cons_self ..))
    have hcast : (((mx - mn + 1).toNat : Nat) : Int) = mx - mn + 1 := by
      rw [Int.toNat_of_nonneg]
      omega
    rw [List.perm_iff_count]
    intro v
    rw [count_build, hcast]
    by_cases hv : mn ≤ v ∧ v < mx - mn + 1 + mn
    · rw [if_pos hv]
    · rw [if_neg hv]
      symm
      rw [List.count_eq_zero]
      intro hmem
      have h1 := hmn_le v hmem
      have h2 := hmx_ge v hmem
      omega

/-- The output has the same length as the input. -/
def length_prop (arr : List Int) : Prop :=
  (countingSort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr :=
  (perm_thm arr).length_eq

/-- The output contains exactly the elements of the input. -/
def mem_prop (arr : List Int) : Prop :=
  ∀ v : Int, v ∈ countingSort arr ↔ v ∈ arr

theorem mem_thm (arr : List Int) : mem_prop arr :=
  fun _ => (perm_thm arr).mem_iff

/-- Every value occurs in the output exactly as often as in the input
(this is exactly what the count table records). -/
def count_prop (arr : List Int) : Prop :=
  ∀ v : Int, (countingSort arr).count v = arr.count v

theorem count_thm (arr : List Int) : count_prop arr :=
  fun v => (perm_thm arr).count_eq v

/-- The empty list is returned unchanged (`if not arr: return []`). -/
def empty_prop : Prop := countingSort [] = []

theorem empty_thm : empty_prop := rfl

/-- A singleton list is returned unchanged. -/
def singleton_prop (x : Int) : Prop := countingSort [x] = [x]

theorem singleton_thm (x : Int) : singleton_prop x := by
  unfold singleton_prop
  rw [countingSort_cons]
  simp [build]

/-- Sorting an already sorted list returns it unchanged. -/
def sorted_fixed_prop (arr : List Int) : Prop :=
  List.Sorted (· ≤ ·) arr → countingSort arr = arr

theorem sorted_fixed_thm (arr : List Int) : sorted_fixed_prop arr := by
  intro h
  exact List.eq_of_perm_of_sorted (perm_thm arr) (sorted_thm arr) h

/-- Counting sort is idempotent. -/
def idempotent_prop (arr : List Int) : Prop :=
  countingSort (countingSort arr) = countingSort arr

theorem idempotent_thm (arr : List Int) : idempotent_prop arr :=
  sorted_fixed_thm (countingSort arr) (sorted_thm arr)

/-- Counting sort agrees with Mathlib's reference insertion sort, i.e. it is
*the* sorted rearrangement of the input. -/
def insertionSort_prop (arr : List Int) : Prop :=
  countingSort arr = List.insertionSort (· ≤ ·) arr

theorem insertionSort_thm (arr : List Int) : insertionSort_prop arr := by
  unfold insertionSort_prop
  exact List.eq_of_perm_of_sorted
    ((perm_thm arr).trans (List.perm_insertionSort (· ≤ ·) arr).symm)
    (sorted_thm arr) (List.sorted_insertionSort (· ≤ ·) arr)

/-! ## Post-condition -/

/-- Post-condition of `counting_sort`: the result is a sorted permutation of
the input (hence also of the same length with the same element counts). -/
def Post_prop (arr : List Int) (result : List Int) : Prop :=
  List.Sorted (· ≤ ·) result ∧ List.Perm result arr ∧ result.length = arr.length

/-! ## Property-based tests -/

-- `sorted_prop`
#eval Plausible.Testable.check (∀ arr : List Int, List.Sorted (· ≤ ·) (countingSort arr))
-- `perm_prop`
#eval Plausible.Testable.check (∀ arr : List Int, List.Perm (countingSort arr) arr)
-- `length_prop`
#eval Plausible.Testable.check (∀ arr : List Int, (countingSort arr).length = arr.length)
-- `mem_prop`
#eval Plausible.Testable.check
  (∀ arr : List Int, ∀ v : Int, v ∈ countingSort arr ↔ v ∈ arr)
-- `count_prop`
#eval Plausible.Testable.check
  (∀ arr : List Int, ∀ v : Int, (countingSort arr).count v = arr.count v)
-- `singleton_prop`
#eval Plausible.Testable.check (∀ x : Int, countingSort [x] = [x])
-- `sorted_fixed_prop`
#eval Plausible.Testable.check
  (∀ arr : List Int, List.Sorted (· ≤ ·) arr → countingSort arr = arr)
-- `idempotent_prop`
#eval Plausible.Testable.check
  (∀ arr : List Int, countingSort (countingSort arr) = countingSort arr)
-- `insertionSort_prop`
#eval Plausible.Testable.check
  (∀ arr : List Int, countingSort arr = List.insertionSort (· ≤ ·) arr)
-- `Post_prop`
#eval Plausible.Testable.check
  (∀ arr : List Int, List.Sorted (· ≤ ·) (countingSort arr) ∧ List.Perm (countingSort arr) arr
    ∧ (countingSort arr).length = arr.length)

/-- All lists of length `n` over the alphabet `[-2, -1, 0, 1, 2, 3]` (used for
exhaustive bounded property-based tests). -/
def allLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (allLists n).flatMap (fun l => [-2, -1, 0, 1, 2, 3].map (fun v => v :: l))

/-- All lists of length at most `4` over the alphabet (1555 lists). -/
def smallLists : List (List Int) := (List.range 5).flatMap allLists

-- bounded exhaustive PBT for `sorted_prop`, `perm_prop`, `length_prop`, `Post_prop`
example : smallLists.all (fun l =>
    decide (List.Sorted (· ≤ ·) (countingSort l)) && decide (List.Perm (countingSort l) l)
      && ((countingSort l).length == l.length)) = true := by native_decide
-- bounded exhaustive PBT for `mem_prop` and `count_prop`
example : smallLists.all (fun l =>
    [-3, -2, -1, 0, 1, 2, 3, 4].all (fun v =>
      (decide (v ∈ countingSort l) == decide (v ∈ l))
        && ((countingSort l).count v == l.count v))) = true := by native_decide
-- bounded exhaustive PBT for `sorted_fixed_prop` (on all sorted small lists)
example : smallLists.all (fun l =>
    !decide (List.Sorted (· ≤ ·) l) || (countingSort l == l)) = true := by native_decide
-- bounded PBT for `sorted_fixed_prop` on longer sorted lists (with duplicates)
example : (List.range 40).all (fun n =>
    let l := (List.range n).map (fun k => ((k / 2 : Nat) : Int) - 7)
    countingSort l == l) = true := by native_decide
-- bounded exhaustive PBT for `idempotent_prop` and `insertionSort_prop`
example : smallLists.all (fun l =>
    (countingSort (countingSort l) == countingSort l)
      && (countingSort l == List.insertionSort (· ≤ ·) l)) = true := by native_decide
-- `empty_prop` (closed statement, checked directly)
example : countingSort [] = [] := by native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (arr : List Int) (_hpre : Pre arr) : Post_prop arr (countingSort arr) :=
  ⟨sorted_thm arr, perm_thm arr, length_thm arr⟩

/-! ## Imperative implementation -/

/-- Imperative counting sort, following the Python program line by line:
early return on the empty list, `max`/`min` computed by loops, a mutable
count array indexed by `num - min_val`, and the result assembled by extending
with `[i + min_val] * count[i]` for `i in range(range_size)`. -/
def countingSortImp (arr : List Int) : List Int := Id.run do
  if arr.isEmpty then
    return []
  let first := arr.headD 0
  -- max_val = max(arr)
  let mut maxVal := first
  for num in arr do
    if num > maxVal then maxVal := num
  -- min_val = min(arr)
  let mut minVal := first
  for num in arr do
    if num < minVal then minVal := num
  -- range_size = max_val - min_val + 1 ; count = [0] * range_size
  let rangeSize := (maxVal - minVal + 1).toNat
  let mut count : Array Nat := Array.replicate rangeSize 0
  -- for num in arr: count[num - min_val] += 1
  for num in arr do
    count := count.modify (num - minVal).toNat (· + 1)
  -- result = [] ; for i in range(range_size): result.extend([i + min_val] * count[i])
  let mut result : Array Int := #[]
  for i in List.range rangeSize do
    result := result ++ Array.replicate (count.getD i 0) ((i : Int) + minVal)
  return result.toList

/-! ## Imperative tests -/

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSortImp [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSortImp [] = [] := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSortImp [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSortImp [2, 1] = [1, 2] := by native_decide
example : countingSortImp [1, 2] = [1, 2] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSortImp [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by native_decide
example : countingSortImp [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSortImp [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : countingSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSortImp [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : countingSortImp [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSortImp [-3, 5, -10, 0, 5] = [-10, -3, 0, 5, 5] := by native_decide

#eval countingSortImp [3, 1, 2]
#eval countingSortImp []
#eval countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval countingSortImp [-3, 5, -10, 0, 5]

-- PBTs for the functional/imperative equivalence
#eval Plausible.Testable.check (∀ arr : List Int, countingSortImp arr = countingSort arr)
example : smallLists.all (fun l => countingSortImp l == countingSort l) = true := by native_decide

/-! ## Equivalence: functional = imperative -/

/-- A `for` loop over a list in the `Id` monad whose body always `yield`s is a left fold. -/
theorem forIn_id_eq_foldl {α β : Type} (xs : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : α → β → β) (hf : ∀ a b, f a b = pure (ForInStep.yield (g a b))) :
    (forIn (m := Id) xs init f).run = xs.foldl (fun b a => g a b) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons y ys ih =>
    rw [List.forIn_cons, hf]
    simp only [List.foldl_cons]
    exact ih (g y init)

theorem maxLoop_eq (xs : List Int) (m : Int) :
    (forIn (m := Id) xs m fun num r =>
        if num > r then pure (ForInStep.yield num) else pure (ForInStep.yield r)).run
      = xs.foldl (fun b a => if a > b then a else b) m := by
  rw [forIn_id_eq_foldl _ _ _ (fun a b => if a > b then a else b)]
  intro a b
  by_cases h : a > b <;> simp [h]

theorem minLoop_eq (xs : List Int) (m : Int) :
    (forIn (m := Id) xs m fun num r =>
        if num < r then pure (ForInStep.yield num) else pure (ForInStep.yield r)).run
      = xs.foldl (fun b a => if a < b then a else b) m := by
  rw [forIn_id_eq_foldl _ _ _ (fun a b => if a < b then a else b)]
  intro a b
  by_cases h : a < b <;> simp [h]

theorem countLoop_eq (xs : List Int) (mn : Int) (cnt : Array Nat) :
    (forIn (m := Id) xs cnt fun num r =>
        pure (ForInStep.yield (r.modify (num - mn).toNat fun x => x + 1))).run
      = xs.foldl (fun r num => r.modify (num - mn).toNat (· + 1)) cnt := by
  rw [forIn_id_eq_foldl _ _ _ (fun num r => r.modify (num - mn).toNat (· + 1))]
  intro a b
  rfl

theorem buildLoop_eq (n : Nat) (mn : Int) (cnt : Array Nat) (init : Array Int) :
    (forIn (m := Id) (List.range n) init fun i r =>
        pure (ForInStep.yield (r ++ Array.replicate (cnt.getD i 0) ((i : Int) + mn)))).run
      = (List.range n).foldl (fun r i => r ++ Array.replicate (cnt.getD i 0) ((i : Int) + mn)) init := by
  rw [forIn_id_eq_foldl _ _ _ (fun i r => r ++ Array.replicate (cnt.getD i 0) ((i : Int) + mn))]
  intro a b
  rfl

theorem foldl_ite_gt_eq_max (xs : List Int) (m : Int) :
    xs.foldl (fun b a => if a > b then a else b) m = xs.foldl max m := by
  induction xs generalizing m with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have h : (if y > m then y else m) = max m y := by
      rw [max_def]; split <;> split <;> omega
    rw [h, ih]

theorem foldl_ite_lt_eq_min (xs : List Int) (m : Int) :
    xs.foldl (fun b a => if a < b then a else b) m = xs.foldl min m := by
  induction xs generalizing m with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have h : (if y < m then y else m) = min m y := by
      rw [min_def]; split <;> split <;> omega
    rw [h, ih]

/-- Loop invariant of the counting phase: after processing `xs`, slot `i` of the
count array has been incremented once per occurrence of `i + mn` in `xs`. -/
theorem countLoop_getElem_opt (mn : Int) (xs : List Int) (cnt : Array Nat)
    (hxs : ∀ y ∈ xs, mn ≤ y) (i : Nat) :
    (xs.foldl (fun r num => r.modify (num - mn).toNat (· + 1)) cnt)[i]?
      = cnt[i]?.map (· + xs.count ((i : Int) + mn)) := by
  induction xs generalizing cnt with
  | nil =>
    simp only [List.foldl_nil, List.count_nil, add_zero]
    cases h : cnt[i]? <;> simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun z hz => hxs z (List.mem_cons_of_mem _ hz))]
    rw [Array.getElem?_modify, List.count_cons]
    have hy := hxs y (List.mem_cons_self ..)
    by_cases h : (y - mn).toNat = i
    · rw [if_pos h]
      have hyi : y = (i : Int) + mn := by omega
      subst hyi
      simp only [beq_self_eq_true, if_true]
      cases cnt[i]? with
      | none => simp
      | some v => simp; omega
    · rw [if_neg h]
      have hyi : y ≠ (i : Int) + mn := by omega
      have hb : (y == (i : Int) + mn) = false := by simpa using hyi
      rw [hb]
      simp

/-- The output phase (`result.extend([i + min_val] * count[i])` for all `i`)
appends exactly the blocks of `build`. -/
theorem buildLoop_toList (mn : Int) (g : Nat → Nat) (n : Nat) (init : Array Int) :
    ((List.range n).foldl (fun r i => r ++ Array.replicate (g i) ((i : Int) + mn)) init).toList
      = init.toList ++ (List.range n).flatMap (fun i => List.replicate (g i) ((i : Int) + mn)) := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.flatMap_append]
    simp only [List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [Array.toList_append, Array.toList_replicate, ih, List.append_assoc]

theorem countingSortImp_nil : countingSortImp [] = [] := by
  rfl

theorem countingSortImp_cons (x : Int) (xs : List Int) :
    countingSortImp (x :: xs) = countingSort (x :: xs) := by
  unfold countingSortImp
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.headD_cons, pure_bind,
    Id.run_bind, Id.run_pure]
  rw [maxLoop_eq, minLoop_eq, countLoop_eq, buildLoop_eq, foldl_ite_gt_eq_max, foldl_ite_lt_eq_min]
  rw [buildLoop_toList, Array.toList_empty, List.nil_append, countingSort_cons]
  have hmax : List.foldl max x (x :: xs) = xs.foldl max x := by simp
  have hmin : List.foldl min x (x :: xs) = xs.foldl min x := by simp
  rw [hmax, hmin]
  unfold build
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_range] at hi
  congr 1
  rw [Array.getD_eq_getD_getElem?, countLoop_getElem_opt _ _ _ (foldl_min_le_all x xs) i,
    Array.getElem?_replicate, if_pos hi]
  simp

/-- The imperative implementation computes exactly the functional one. -/
theorem equiv_thm (arr : List Int) : countingSortImp arr = countingSort arr := by
  cases arr with
  | nil => exact countingSortImp_nil
  | cons x xs => exact countingSortImp_cons x xs

/-- Consequently the imperative implementation also satisfies the post-condition. -/
theorem imp_correctness_thm (arr : List Int) (_hpre : Pre arr) :
    Post_prop arr (countingSortImp arr) := by
  rw [equiv_thm]
  exact correctness_thm arr trivial

end counting_sort

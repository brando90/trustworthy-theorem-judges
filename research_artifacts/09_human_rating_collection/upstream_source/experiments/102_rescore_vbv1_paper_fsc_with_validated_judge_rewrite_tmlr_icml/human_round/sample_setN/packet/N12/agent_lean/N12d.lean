import Mathlib

/-!
# Counting sort

Lean 4 formalization of the Python program `counting_sort`.

The Python function sorts a list of integers (negative numbers are supported by
shifting with the minimum): it computes `min(arr)` and `max(arr)`, builds a count
array of size `max - min + 1`, counts the occurrences of every element and finally
emits every value `i + min` exactly `count[i]` times, for `i = 0, ..., range_size - 1`.
The empty list is mapped to the empty list.

The Python precondition `pre` (the input must be a `List[int]`) is enforced by the
Lean type `List Int`, so `Pre` is trivially satisfied; the `ValueError` branch is not
reachable in Lean.

Contents:
* `countingSort`    : functional implementation
* unit tests, `Pre`, properties (`*_prop`) with proofs (`*_thm`), `Post_prop`
* property-based tests
* `countingSort_correct` : `Pre → Post_prop`
* `countingSortImp` : imperative implementation (`Id.run do`, mutable count array)
* `countingSort_eq_imp` : functional = imperative
-/

namespace counting_sort

/-! ## Functional implementation -/

/-- Minimum of the non-empty list `x :: xs` (Python `min(arr)`). -/
def listMin (x : Int) (xs : List Int) : Int := xs.foldl min x

/-- Maximum of the non-empty list `x :: xs` (Python `max(arr)`). -/
def listMax (x : Int) (xs : List Int) : Int := xs.foldl max x

/-- Counting sort.  For a non-empty list the value `i + min` is emitted
`count[i]` times where `count[i]` is the number of occurrences of `i + min` in the
input, for `i = 0, …, max - min`. -/
def countingSort : List Int → List Int
  | [] => []
  | x :: xs =>
    let maxVal := listMax x xs
    let minVal := listMin x xs
    -- Handle negative numbers by shifting the range
    let rangeSize := (maxVal - minVal + 1).toNat
    -- count[i] = number of occurrences of the value `i + minVal`
    let count : Nat → Nat := fun i => (x :: xs).count ((i : Int) + minVal)
    -- Build the sorted list
    (List.range rangeSize).flatMap (fun (i : Nat) => List.replicate (count i) ((i : Int) + minVal))

/-! ## Unit tests (from the Python `check`) -/

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
-- negative numbers (handled through the shift by the minimum)
example : countingSort [-3, 5, -10, 0, 2, -3] = [-10, -3, -3, 0, 2, 5] := by native_decide

#eval countingSort [3, 1, 2]
#eval countingSort []
#eval countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
#eval countingSort [-3, 5, -10, 0, 2, -3]

-- The Python negative test `candidate([1, 2.5])` (a `ValueError`) is not expressible:
-- the Lean type `List Int` rules out non-integer elements statically.

/-! ## Pre-condition -/

/-- Python `pre`: the input is a `List[int]`.  The Lean type `List Int` guarantees
this, hence the precondition is always satisfied. -/
def Pre (_arr : List Int) : Prop := True

/-! ## Auxiliary lemmas about `listMin` / `listMax` -/

theorem listMin_le_head (x : Int) (xs : List Int) : listMin x xs ≤ x := by
  induction xs generalizing x with
  | nil => simp [listMin]
  | cons y ys ih =>
    simp only [listMin, List.foldl_cons]
    exact le_trans (ih (min x y)) (min_le_left x y)

theorem listMin_le_of_mem (x : Int) (xs : List Int) : ∀ y ∈ xs, listMin x xs ≤ y := by
  induction xs generalizing x with
  | nil => simp
  | cons z zs ih =>
    intro y hy
    simp only [listMin, List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact le_trans (listMin_le_head (min x y) zs) (min_le_right x y)
    · exact ih (min x z) y hy'

/-- `min(arr)` is a lower bound of every element of `arr`. -/
theorem listMin_le (x : Int) (xs : List Int) : ∀ y ∈ x :: xs, listMin x xs ≤ y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact listMin_le_head _ _
  · exact listMin_le_of_mem _ _ _ hy'

theorem head_le_listMax (x : Int) (xs : List Int) : x ≤ listMax x xs := by
  induction xs generalizing x with
  | nil => simp [listMax]
  | cons y ys ih =>
    simp only [listMax, List.foldl_cons]
    exact le_trans (le_max_left x y) (ih (max x y))

theorem le_listMax_of_mem (x : Int) (xs : List Int) : ∀ y ∈ xs, y ≤ listMax x xs := by
  induction xs generalizing x with
  | nil => simp
  | cons z zs ih =>
    intro y hy
    simp only [listMax, List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact le_trans (le_max_right x y) (head_le_listMax (max x y) zs)
    · exact ih (max x z) y hy'

/-- `max(arr)` is an upper bound of every element of `arr`. -/
theorem le_listMax (x : Int) (xs : List Int) : ∀ y ∈ x :: xs, y ≤ listMax x xs := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact head_le_listMax _ _
  · exact le_listMax_of_mem _ _ _ hy'

theorem listMin_le_listMax (x : Int) (xs : List Int) : listMin x xs ≤ listMax x xs :=
  le_trans (listMin_le_head x xs) (head_le_listMax x xs)

/-- `min(arr)` is an element of `arr`. -/
theorem listMin_mem (x : Int) (xs : List Int) : listMin x xs ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [listMin]
  | cons y ys ih =>
    have hdef : listMin x (y :: ys) = listMin (min x y) ys := rfl
    rw [hdef]
    rcases List.mem_cons.mp (ih (min x y)) with h' | h'
    · rw [h']
      rcases min_choice x y with hm | hm <;> rw [hm] <;> simp
    · simp [h']

/-- `max(arr)` is an element of `arr`. -/
theorem listMax_mem (x : Int) (xs : List Int) : listMax x xs ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [listMax]
  | cons y ys ih =>
    have hdef : listMax x (y :: ys) = listMax (max x y) ys := rfl
    rw [hdef]
    rcases List.mem_cons.mp (ih (max x y)) with h' | h'
    · rw [h']
      rcases max_choice x y with hm | hm <;> rw [hm] <;> simp
    · simp [h']

/-- The head of a sorted list containing a lower bound `m` of all its elements is `m`. -/
theorem head?_eq_of_sorted (s : List Int) (m : Int) (hs : List.Sorted (· ≤ ·) s) (hm : m ∈ s)
    (hle : ∀ b ∈ s, m ≤ b) : s.head? = some m := by
  cases s with
  | nil => simp at hm
  | cons h t =>
    simp only [List.head?_cons, Option.some.injEq]
    rw [List.sorted_cons] at hs
    have h1 : h ≤ m := by
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact le_refl _
      · exact hs.1 m hm'
    have h2 : m ≤ h := hle h (by simp)
    exact le_antisymm h1 h2

/-- The last element of a sorted list containing an upper bound `M` of all its elements
is `M`. -/
theorem getLast?_eq_of_sorted (s : List Int) (M : Int) (hs : List.Sorted (· ≤ ·) s)
    (hM : M ∈ s) (hge : ∀ b ∈ s, b ≤ M) : s.getLast? = some M := by
  rw [← List.head?_reverse]
  have hs' : List.Pairwise (fun a b => b ≤ a) s.reverse := by
    rw [List.pairwise_reverse]; exact hs
  have hM' : M ∈ s.reverse := List.mem_reverse.mpr hM
  have hge' : ∀ b ∈ s.reverse, b ≤ M := fun b hb => hge b (List.mem_reverse.mp hb)
  revert hs' hM' hge'
  generalize s.reverse = r
  intro hs' hM' hge'
  cases r with
  | nil => simp at hM'
  | cons h t =>
    simp only [List.head?_cons, Option.some.injEq]
    rw [List.pairwise_cons] at hs'
    have h1 : M ≤ h := by
      rcases List.mem_cons.mp hM' with rfl | hm'
      · exact le_refl _
      · exact hs'.1 M hm'
    have h2 : h ≤ M := hge' h (by simp)
    exact le_antisymm h2 h1

/-- Unfolding lemma for the non-empty case. -/
theorem countingSort_cons (x : Int) (xs : List Int) :
    countingSort (x :: xs) =
      (List.range ((listMax x xs - listMin x xs + 1).toNat)).flatMap
        (fun (i : Nat) => List.replicate ((x :: xs).count ((i : Int) + listMin x xs))
          ((i : Int) + listMin x xs)) := rfl

/-! ## Auxiliary lemmas about the output construction -/

/-- The construction `value i + mn, repeated c i times, for i = 0..n-1` is sorted. -/
theorem sorted_build (c : Nat → Nat) (mn : Int) (n : Nat) :
    List.Sorted (· ≤ ·)
      ((List.range n).flatMap (fun (i : Nat) => List.replicate (c i) ((i : Int) + mn))) := by
  unfold List.Sorted
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_replicate]
    exact Or.inr (le_refl _)
  · refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := n))
    intro a b hab x hx y hy
    rw [List.mem_replicate] at hx hy
    rw [hx.2, hy.2]
    omega

/-- Counting the occurrences of `v` in the constructed list. -/
theorem count_build (arr : List Int) (mn : Int) (n : Nat) (v : Int) :
    ((List.range n).flatMap
        (fun (i : Nat) => List.replicate (arr.count ((i : Int) + mn)) ((i : Int) + mn))).count v
      = if mn ≤ v ∧ v < mn + n then arr.count v else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_replicate,
      beq_iff_eq]
    push_cast
    by_cases hv : (n : Int) + mn = v
    · subst hv
      rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
      simp
    · rw [if_neg hv, add_zero]
      by_cases h : mn ≤ v ∧ v < mn + n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

/-! ## Properties -/

/-- The output is sorted in non-decreasing order. -/
def sorted_prop (arr : List Int) : Prop := List.Sorted (· ≤ ·) (countingSort arr)

/-- The output is a permutation of the input. -/
def perm_prop (arr : List Int) : Prop := List.Perm (countingSort arr) arr

/-- Every value occurs in the output exactly as often as in the input. -/
def count_prop (arr : List Int) : Prop := ∀ v : Int, (countingSort arr).count v = arr.count v

/-- The output has the same length as the input. -/
def length_prop (arr : List Int) : Prop := (countingSort arr).length = arr.length

/-- The output contains exactly the elements of the input. -/
def mem_prop (arr : List Int) : Prop := ∀ v : Int, v ∈ countingSort arr ↔ v ∈ arr

/-- The empty list is mapped to the empty list. -/
def empty_prop : Prop := countingSort [] = []

/-- A singleton list is returned unchanged. -/
def singleton_prop (x : Int) : Prop := countingSort [x] = [x]

/-- The output is *the* sorted rearrangement of the input: it coincides with
insertion sort (the reference specification of sorting). -/
def eq_insertionSort_prop (arr : List Int) : Prop :=
  countingSort arr = arr.insertionSort (· ≤ ·)

/-- Sorting is idempotent. -/
def idempotent_prop (arr : List Int) : Prop :=
  countingSort (countingSort arr) = countingSort arr

/-- For a non-empty input the first element of the output is `min(arr)` and the last
one is `max(arr)`. -/
def head_last_prop (arr : List Int) : Prop :=
  ∀ x xs, arr = x :: xs →
    (countingSort arr).head? = some (listMin x xs) ∧
    (countingSort arr).getLast? = some (listMax x xs)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  unfold sorted_prop
  cases arr with
  | nil => simp [countingSort]
  | cons x xs =>
    rw [countingSort_cons]
    exact sorted_build _ _ _

theorem perm_thm (arr : List Int) : perm_prop arr := by
  unfold perm_prop
  cases arr with
  | nil => simp [countingSort]
  | cons x xs =>
    rw [List.perm_iff_count]
    intro v
    rw [countingSort_cons, count_build]
    split_ifs with h
    · rfl
    · symm
      rw [List.count_eq_zero]
      intro hv
      have h1 := listMin_le x xs v hv
      have h2 := le_listMax x xs v hv
      have h3 := listMin_le_listMax x xs
      omega

theorem count_thm (arr : List Int) : count_prop arr := fun v => (perm_thm arr).count_eq v

theorem length_thm (arr : List Int) : length_prop arr := (perm_thm arr).length_eq

theorem mem_thm (arr : List Int) : mem_prop arr := fun _ => (perm_thm arr).mem_iff

theorem empty_thm : empty_prop := rfl

theorem eq_insertionSort_thm (arr : List Int) : eq_insertionSort_prop arr := by
  unfold eq_insertionSort_prop
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (perm_thm arr).trans (List.perm_insertionSort _ _).symm
  · exact sorted_thm arr
  · exact List.sorted_insertionSort _ _

theorem idempotent_thm (arr : List Int) : idempotent_prop arr := by
  unfold idempotent_prop
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact perm_thm _
  · exact sorted_thm _
  · exact sorted_thm _

theorem singleton_thm (x : Int) : singleton_prop x := by
  unfold singleton_prop
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact perm_thm _
  · exact sorted_thm _
  · simp

theorem head_last_thm (arr : List Int) : head_last_prop arr := by
  intro x xs harr
  subst harr
  have hs := sorted_thm (x :: xs)
  have hp := perm_thm (x :: xs)
  unfold sorted_prop at hs
  unfold perm_prop at hp
  constructor
  · apply head?_eq_of_sorted _ _ hs
    · exact hp.mem_iff.mpr (listMin_mem x xs)
    · intro b hb
      exact listMin_le x xs b (hp.mem_iff.mp hb)
  · apply getLast?_eq_of_sorted _ _ hs
    · exact hp.mem_iff.mpr (listMax_mem x xs)
    · intro b hb
      exact le_listMax x xs b (hp.mem_iff.mp hb)

/-! ## Post-condition -/

/-- Post-condition of `counting_sort`: the result is a sorted permutation of the input
(with all the derived properties). -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ perm_prop arr ∧ count_prop arr ∧ length_prop arr ∧ mem_prop arr ∧
  eq_insertionSort_prop arr ∧ idempotent_prop arr ∧ head_last_prop arr

/-! ## Property-based tests -/

/-- Executable sortedness check. -/
def isSortedB : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (x ≤ y) && isSortedB (y :: rest)

/-- Executable form of `Post_prop` (`count`/`mem` are probed on the input values and a
few extra values). -/
def postB (arr : List Int) : Bool :=
  let out := countingSort arr
  isSortedB out && out.isPerm arr && (out.length == arr.length) &&
  (arr ++ [0, 1, -1, 7]).all
    (fun v => (out.count v == arr.count v) && (out.contains v == arr.contains v)) &&
  (out == arr.insertionSort (· ≤ ·)) && (countingSort out == out)

-- randomized PBTs (Plausible)
#eval Plausible.Testable.check (∀ arr : List Int, isSortedB (countingSort arr) = true)
#eval Plausible.Testable.check (∀ arr : List Int, (countingSort arr).isPerm arr = true)
#eval Plausible.Testable.check
  (∀ arr : List Int, ∀ v : Int, (countingSort arr).count v = arr.count v)
#eval Plausible.Testable.check (∀ arr : List Int, (countingSort arr).length = arr.length)
#eval Plausible.Testable.check (∀ arr : List Int, ∀ v : Int, (v ∈ countingSort arr ↔ v ∈ arr))
#eval Plausible.Testable.check (∀ x : Int, countingSort [x] = [x])
#eval Plausible.Testable.check (∀ arr : List Int, countingSort arr = arr.insertionSort (· ≤ ·))
#eval Plausible.Testable.check
  (∀ arr : List Int, countingSort (countingSort arr) = countingSort arr)
#eval Plausible.Testable.check (∀ x : Int, ∀ xs : List Int,
  (countingSort (x :: xs)).head? = some (listMin x xs) ∧
  (countingSort (x :: xs)).getLast? = some (listMax x xs))
#eval Plausible.Testable.check (∀ arr : List Int, postB arr = true)

/-- All lists of length `n` over the alphabet `vals`. -/
def allLists (vals : List Int) : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (allLists vals n).flatMap (fun l => vals.map (fun v => v :: l))

/-- Exhaustive small inputs: all lists of length `< 5` over `{-2, -1, 0, 1, 3}`. -/
def smallInputs : List (List Int) := (List.range 5).flatMap (allLists [-2, -1, 0, 1, 3])

-- bounded (exhaustive) PBTs
example : smallInputs.all (fun arr => isSortedB (countingSort arr)) = true := by native_decide
example : smallInputs.all (fun arr => (countingSort arr).isPerm arr) = true := by native_decide
example : smallInputs.all (fun arr =>
    ([-3, -2, -1, 0, 1, 2, 3, 4] : List Int).all
      (fun v => (countingSort arr).count v == arr.count v)) = true := by native_decide
example : smallInputs.all (fun arr => (countingSort arr).length == arr.length) = true := by
  native_decide
example : smallInputs.all (fun arr =>
    ([-3, -2, -1, 0, 1, 2, 3, 4] : List Int).all
      (fun v => (countingSort arr).contains v == arr.contains v)) = true := by native_decide
example : countingSort [] = [] := by native_decide
example : ([-5, 0, 7] : List Int).all (fun x => countingSort [x] == [x]) = true := by
  native_decide
example : smallInputs.all (fun arr => countingSort arr == arr.insertionSort (· ≤ ·)) = true := by
  native_decide
example : smallInputs.all
    (fun arr => countingSort (countingSort arr) == countingSort arr) = true := by
  native_decide
example : smallInputs.all (fun arr => match arr with
    | [] => true
    | x :: xs => ((countingSort (x :: xs)).head? == some (listMin x xs)) &&
        ((countingSort (x :: xs)).getLast? == some (listMax x xs))) = true := by native_decide
example : smallInputs.all postB = true := by native_decide

/-! ## Correctness -/

/-- Correctness: the precondition implies the post-condition. -/
theorem countingSort_correct (arr : List Int) : Pre arr → Post_prop arr := fun _ =>
  ⟨sorted_thm arr, perm_thm arr, count_thm arr, length_thm arr, mem_thm arr,
    eq_insertionSort_thm arr, idempotent_thm arr, head_last_thm arr⟩

/-! ## Imperative implementation -/

/-- Imperative counting sort, mirroring the Python code: compute `max`/`min`, fill a
mutable count array, then build the result. -/
def countingSortImp (arr : List Int) : List Int := Id.run do
  match arr with
  | [] => return []
  | x :: xs =>
    -- max_val = max(arr); min_val = min(arr)
    let mut maxVal := x
    for y in xs do
      if y > maxVal then maxVal := y
    let mut minVal := x
    for y in xs do
      if y < minVal then minVal := y
    -- Handle negative numbers by shifting the range
    let rangeSize := (maxVal - minVal + 1).toNat
    -- Create count array and count occurrences of each element
    let mut count : Array Nat := Array.replicate rangeSize 0
    for num in arr do
      let idx := (num - minVal).toNat
      count := count.set! idx (count[idx]! + 1)
    -- Build the sorted array
    let mut result : Array Int := #[]
    for i in [0:rangeSize] do
      result := result ++ (List.replicate count[i]! ((i : Int) + minVal)).toArray
    return result.toList

/-! ## Imperative tests -/

example : countingSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : countingSortImp [2, 1, 3] = [1, 2, 3] := by native_decide
example : countingSortImp [] = [] := by native_decide
example : countingSortImp [1] = [1] := by native_decide
example : countingSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSortImp [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSortImp [2, 1] = [1, 2] := by native_decide
example : countingSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSortImp [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSortImp [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : countingSortImp [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : countingSortImp [0, 3, 1, 0, 2] = [0, 0, 1, 2, 3] := by native_decide
example : countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : countingSortImp [-3, 5, -10, 0, 2, -3] = [-10, -3, -3, 0, 2, 5] := by native_decide

#eval countingSortImp [3, 1, 2]
#eval countingSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

#eval Plausible.Testable.check (∀ arr : List Int, countingSort arr = countingSortImp arr)
example : smallInputs.all (fun arr => countingSort arr == countingSortImp arr) = true := by
  native_decide

/-! ## Loop lemmas for the imperative implementation -/

/-- The `max` loop of the imperative implementation computes `listMax`. -/
theorem forIn_max_loop (xs : List Int) (x : Int) :
    (forIn (m := Id) xs x fun y r =>
        if y > r then pure (ForInStep.yield y) else pure (ForInStep.yield r)).run
      = listMax x xs := by
  induction xs generalizing x with
  | nil => simp [listMax]
  | cons y ys ih =>
    rw [List.forIn_cons]
    by_cases h : y > x
    · rw [if_pos h]
      simp only [pure_bind]
      rw [ih]
      simp only [listMax, List.foldl_cons]
      rw [max_eq_right (le_of_lt h)]
    · rw [if_neg h]
      simp only [pure_bind]
      rw [ih]
      simp only [listMax, List.foldl_cons]
      rw [max_eq_left (not_lt.mp h)]

/-- The `min` loop of the imperative implementation computes `listMin`. -/
theorem forIn_min_loop (xs : List Int) (x : Int) :
    (forIn (m := Id) xs x fun y r =>
        if y < r then pure (ForInStep.yield y) else pure (ForInStep.yield r)).run
      = listMin x xs := by
  induction xs generalizing x with
  | nil => simp [listMin]
  | cons y ys ih =>
    rw [List.forIn_cons]
    by_cases h : y < x
    · rw [if_pos h]
      simp only [pure_bind]
      rw [ih]
      simp only [listMin, List.foldl_cons]
      rw [min_eq_right (le_of_lt h)]
    · rw [if_neg h]
      simp only [pure_bind]
      rw [ih]
      simp only [listMin, List.foldl_cons]
      rw [min_eq_left (not_lt.mp h)]

/-- A `for` loop over a list that only updates its state is a left fold. -/
theorem forIn_update_loop {α β : Type} (l : List α) (init : β) (g : α → β → β) :
    (forIn (m := Id) l init fun a r => pure (ForInStep.yield (g a r))).run
      = l.foldl (fun r a => g a r) init := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    rw [List.forIn_cons]
    simp only [pure_bind]
    rw [ih, List.foldl_cons]

/-- A `for i in [0:n]` loop that only updates its state is a left fold over
`List.range n`. -/
theorem forIn_range_update_loop {β : Type} (n : Nat) (init : β) (g : Nat → β → β) :
    (forIn (m := Id) [0:n] init fun i r => pure (ForInStep.yield (g i r))).run
      = (List.range n).foldl (fun r i => g i r) init := by
  rw [Std.Range.forIn_eq_forIn_range', List.range_eq_range']
  have hsize : ([0:n] : Std.Range).size = n := by simp [Std.Range.size]
  simp only [hsize]
  exact forIn_update_loop _ _ _

/-- One step of the counting loop: `count[num - min_val] += 1`. -/
def countStep (mn : Int) (cnt : Array Nat) (y : Int) : Array Nat :=
  cnt.set! (y - mn).toNat (cnt[(y - mn).toNat]! + 1)

/-- The counting loop is a left fold of `countStep`. -/
theorem forIn_count_loop (arr : List Int) (mn : Int) (init : Array Nat) :
    (forIn (m := Id) arr init fun num r =>
        pure (ForInStep.yield (r.set! (num - mn).toNat (r[(num - mn).toNat]! + 1)))).run
      = arr.foldl (countStep mn) init :=
  forIn_update_loop arr init (fun num r => countStep mn r num)

/-- The building loop is a left fold over `List.range n`. -/
theorem forIn_build_loop (n : Nat) (cnt : Array Nat) (mn : Int) (init : Array Int) :
    (forIn (m := Id) [0:n] init fun (i : Nat) (r : Array Int) =>
        pure (ForInStep.yield (r ++ (List.replicate cnt[i]! ((i : Int) + mn)).toArray))).run
      = (List.range n).foldl
          (fun (r : Array Int) (i : Nat) => r ++ (List.replicate cnt[i]! ((i : Int) + mn)).toArray)
          init :=
  forIn_range_update_loop n init _

theorem countStep_size (mn : Int) (cnt : Array Nat) (y : Int) :
    (countStep mn cnt y).size = cnt.size := by
  simp [countStep]

theorem countStep_get! (mn : Int) (cnt : Array Nat) (y : Int) (hy : mn ≤ y)
    (hlt : (y - mn).toNat < cnt.size) (i : Nat) (hi : i < cnt.size) :
    (countStep mn cnt y)[i]! = cnt[i]! + if y = (i : Int) + mn then 1 else 0 := by
  have hi' : i < (countStep mn cnt y).size := by rw [countStep_size]; exact hi
  rw [getElem!_pos (countStep mn cnt y) i hi', getElem!_pos cnt i hi]
  simp only [countStep, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi]
  rw [getElem!_pos cnt _ hlt]
  by_cases h1 : (y - mn).toNat = i
  · subst h1
    rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega), add_zero]

/-- Invariant of the counting loop: afterwards `count[i]` has been increased by the
number of occurrences of `i + min_val`. -/
theorem countFold_spec (mn : Int) (n : Nat) (arr : List Int)
    (hb : ∀ y ∈ arr, mn ≤ y ∧ (y - mn).toNat < n) (cnt : Array Nat) (hc : cnt.size = n) :
    (arr.foldl (countStep mn) cnt).size = n ∧
    ∀ i, i < n → (arr.foldl (countStep mn) cnt)[i]! = cnt[i]! + arr.count ((i : Int) + mn) := by
  induction arr generalizing cnt with
  | nil => exact ⟨hc, fun i _ => by simp⟩
  | cons y ys ih =>
    have hy := hb y (by simp)
    have hb' : ∀ z ∈ ys, mn ≤ z ∧ (z - mn).toNat < n := fun z hz => hb z (by simp [hz])
    have hsize : (countStep mn cnt y).size = n := by rw [countStep_size, hc]
    obtain ⟨h1, h2⟩ := ih hb' (countStep mn cnt y) hsize
    refine ⟨by simpa [List.foldl_cons] using h1, fun i hi => ?_⟩
    rw [List.foldl_cons, h2 i hi,
      countStep_get! mn cnt y hy.1 (by rw [hc]; exact hy.2) i (by rw [hc]; exact hi)]
    simp only [List.count_cons, beq_iff_eq]
    split_ifs <;> omega

/-- The building loop produces the concatenation of the replicated values. -/
theorem buildFold_toList (cnt : Array Nat) (mn : Int) (l : List Nat) (acc : Array Int) :
    (l.foldl (fun (r : Array Int) (i : Nat) => r ++ (List.replicate cnt[i]! ((i : Int) + mn)).toArray)
        acc).toList
      = acc.toList ++ l.flatMap (fun (i : Nat) => List.replicate cnt[i]! ((i : Int) + mn)) := by
  induction l generalizing acc with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons, ih, Array.toList_append, List.toList_toArray, List.flatMap_cons,
      List.append_assoc]

/-! ## Equivalence -/

/-- The functional and the imperative implementations agree on every input. -/
theorem countingSort_eq_imp (arr : List Int) : countingSort arr = countingSortImp arr := by
  cases arr with
  | nil => rfl
  | cons x xs =>
    rw [countingSort_cons]
    unfold countingSortImp
    simp only [Id.run_bind, bind_pure_comp, map_pure, Id.run_map]
    rw [forIn_max_loop, forIn_min_loop, forIn_count_loop, forIn_build_loop, buildFold_toList,
      Array.toList_empty, List.nil_append]
    have hb : ∀ y ∈ x :: xs, listMin x xs ≤ y ∧
        (y - listMin x xs).toNat < (listMax x xs - listMin x xs + 1).toNat := by
      intro y hy
      have h1 := listMin_le x xs y hy
      have h2 := le_listMax x xs y hy
      exact ⟨h1, by omega⟩
    obtain ⟨_, hget⟩ := countFold_spec (listMin x xs) ((listMax x xs - listMin x xs + 1).toNat)
      (x :: xs) hb (Array.replicate ((listMax x xs - listMin x xs + 1).toNat) 0)
      Array.size_replicate
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [hget i hi,
      getElem!_pos (Array.replicate ((listMax x xs - listMin x xs + 1).toNat) 0) i
        (by simpa using hi),
      Array.getElem_replicate, zero_add]

/-- Consequently the imperative implementation also satisfies the post-condition. -/
theorem countingSortImp_correct (arr : List Int) :
    Pre arr → List.Sorted (· ≤ ·) (countingSortImp arr) ∧ (countingSortImp arr).Perm arr := by
  intro _
  rw [← countingSort_eq_imp]
  exact ⟨sorted_thm arr, perm_thm arr⟩

end counting_sort

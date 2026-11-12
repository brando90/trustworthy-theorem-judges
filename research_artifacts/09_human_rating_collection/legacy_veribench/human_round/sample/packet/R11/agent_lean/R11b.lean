import Mathlib

/-!
# Heap sort for a list of integers

This file is a Lean 4 formalization of the Python program `heap_sort`.

The Python program builds a max heap in place inside a copy of the input array
(`build_max_heap`, using the recursive `heapify` sift-down helper), and then
repeatedly swaps the root (the current maximum) with the last position of the
still-unsorted prefix and restores the heap property on the shrunken heap.
Lists of length `≤ 1` are returned as a copy, and the Python precondition
`pre` (input must be a `list` of `int`s, otherwise `ValueError` is raised) is
carried by Lean's type `List Int`, so it is vacuously true here.

Contents:
* `swapAt` / `heapify` / `buildMaxHeap` / `extractLoop` : the array primitives,
  mirroring the Python helpers one-for-one.
* `heapSort` : the functional implementation (`List Int → List Int`).
* `heapSortImp` : the imperative implementation using `Id.run do` with a mutable
  array and two `for` loops, mirroring the Python control flow.
* Properties: the output is sorted, is a permutation of the input and has the
  same length; plus the documented edge cases.
* `heapSort_eq_heapSortImp` : the two implementations agree.
-/

namespace heap_sort

/-! ## Implementation (functional) -/

/-- `swapAt a i j` exchanges the entries at indices `i` and `j`
(the Python statement `arr[i], arr[largest] = arr[largest], arr[i]`).
Out-of-bounds indices leave the array unchanged. -/
def swapAt (a : Array Int) (i j : Nat) : Array Int :=
  if h : i < a.size ∧ j < a.size then a.swap i j h.1 h.2 else a

/-- The index of the largest of `a[i]`, `a[2i+1]`, `a[2i+2]` among those that lie
inside the heap of size `n` — the `largest` variable of the Python `heapify`. -/
def largestIdx (a : Array Int) (n i : Nat) : Nat :=
  let l := 2 * i + 1
  let r := 2 * i + 2
  let m := if l < n ∧ a[l]! > a[i]! then l else i
  if r < n ∧ a[r]! > a[m]! then r else m

/-- Sift-down step, the Lean counterpart of the recursive Python `heapify`.
`fuel` bounds the recursion depth (the Python recursion always terminates
because the index strictly increases; `a.size` is always enough fuel). -/
def heapifyAux (fuel : Nat) (a : Array Int) (n i : Nat) : Array Int :=
  match fuel with
  | 0 => a
  | fuel + 1 =>
    let largest := largestIdx a n i
    if largest = i then a else heapifyAux fuel (swapAt a i largest) n largest

/-- `heapify a n i` restores the max-heap property at index `i` of the heap
occupying the first `n` entries of `a`. -/
def heapify (a : Array Int) (n i : Nat) : Array Int :=
  heapifyAux a.size a n i

/-- `build_max_heap`: heapify every internal node, from `n / 2 - 1` down to `0`. -/
def buildMaxHeap (a : Array Int) (n : Nat) : Array Int :=
  (List.range (n / 2)).reverse.foldl (fun acc i => heapify acc n i) a

/-- The extraction loop: for `i = n - 1, …, 1`, swap the root to position `i`
and re-heapify the first `i` entries. -/
def extractLoop (a : Array Int) (n : Nat) : Array Int :=
  ((List.range n).drop 1).reverse.foldl
    (fun acc i => heapify (swapAt acc 0 i) i 0) a

/-- Heap sort on arrays. -/
def heapSortArr (a : Array Int) : Array Int :=
  if a.size ≤ 1 then a else extractLoop (buildMaxHeap a a.size) a.size

/-- Heap sort on lists: the functional translation of Python's `heap_sort`. -/
def heapSort (l : List Int) : List Int :=
  (heapSortArr l.toArray).toList

/-! ## Unit tests (mirroring the Python `check` function) -/

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [] = [] := by native_decide
example : heapSort [1] = [1] := by native_decide
example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example : heapSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [2, 1] = [1, 2] := by native_decide
example : heapSort [1, 2] = [1, 2] := by native_decide
example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide
example :
    heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
      = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

-- The output really is a sorted permutation of the input on concrete data.
example : (heapSort [3, 7, 1, 9, 2, 8, 4, 6, 5]).Sorted (· ≤ ·) := by decide
example : (heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]).Sorted (· ≤ ·) := by decide
example : (heapSort [3, 1, 4, 1, 2, 3]).Perm [3, 1, 4, 1, 2, 3] := by decide

#eval heapSort [3, 1, 2]
#eval heapSort ([] : List Int)
#eval heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

/-! ## Pre-condition

The Python `pre` requires the input to be a `list` of `int`s; a violation raises
`ValueError`. In Lean the type `List Int` already enforces this, so the
pre-condition holds for every well-typed input. -/

def Pre (_l : List Int) : Prop := True

/-- The `ValueError` branch of the Python program is unreachable for well-typed
Lean inputs: the pre-condition holds for every `l : List Int`. -/
theorem Pre_holds (l : List Int) : Pre l := trivial

/-! ## Properties -/

/-- The result is sorted in non-decreasing order. -/
def sorted_prop (l : List Int) : Prop := (heapSort l).Sorted (· ≤ ·)

/-- The result is a permutation of the input (same elements with multiplicity). -/
def perm_prop (l : List Int) : Prop := (heapSort l).Perm l

/-- The result has the same length as the input. -/
def length_prop (l : List Int) : Prop := (heapSort l).length = l.length

/-- Inputs of length at most one are returned unchanged (`arr.copy()`). -/
def small_prop (l : List Int) : Prop := l.length ≤ 1 → heapSort l = l

/-! ### Auxiliary lemmas -/

theorem swapAt_size (a : Array Int) (i j : Nat) : (swapAt a i j).size = a.size := by
  unfold swapAt
  split
  · simp
  · rfl

theorem swapAt_perm (a : Array Int) (i j : Nat) :
    (swapAt a i j).toList.Perm a.toList := by
  unfold swapAt
  split
  · rename_i h
    exact Array.perm_iff_toList_perm.mp (Array.swap_perm h.1 h.2)
  · exact List.Perm.refl _

theorem heapifyAux_size (fuel : Nat) (a : Array Int) (n i : Nat) :
    (heapifyAux fuel a n i).size = a.size := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
    rw [heapifyAux]
    split
    · rfl
    · rw [ih, swapAt_size]

theorem heapifyAux_perm (fuel : Nat) (a : Array Int) (n i : Nat) :
    (heapifyAux fuel a n i).toList.Perm a.toList := by
  induction fuel generalizing a i with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    rw [heapifyAux]
    split
    · exact List.Perm.refl _
    · exact (ih _ _).trans (swapAt_perm _ _ _)

theorem heapify_size (a : Array Int) (n i : Nat) : (heapify a n i).size = a.size :=
  heapifyAux_size _ _ _ _

theorem heapify_perm (a : Array Int) (n i : Nat) :
    (heapify a n i).toList.Perm a.toList :=
  heapifyAux_perm _ _ _ _

/-- A fold of size-preserving array operations preserves the size. -/
theorem foldl_size (f : Array Int → Nat → Array Int)
    (hf : ∀ a i, (f a i).size = a.size) (is : List Nat) (a : Array Int) :
    (is.foldl f a).size = a.size := by
  induction is generalizing a with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

/-- A fold of permutation-preserving array operations permutes the array. -/
theorem foldl_perm (f : Array Int → Nat → Array Int)
    (hf : ∀ a i, (f a i).toList.Perm a.toList) (is : List Nat) (a : Array Int) :
    (is.foldl f a).toList.Perm a.toList := by
  induction is generalizing a with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (ih (f a x)).trans (hf a x)

theorem buildMaxHeap_size (a : Array Int) (n : Nat) : (buildMaxHeap a n).size = a.size :=
  foldl_size _ (fun b i => heapify_size b n i) _ _

theorem buildMaxHeap_perm (a : Array Int) (n : Nat) :
    (buildMaxHeap a n).toList.Perm a.toList :=
  foldl_perm _ (fun b i => heapify_perm b n i) _ _

theorem extractLoop_size (a : Array Int) (n : Nat) : (extractLoop a n).size = a.size :=
  foldl_size _ (fun _ _ => by rw [heapify_size, swapAt_size]) _ _

theorem extractLoop_perm (a : Array Int) (n : Nat) :
    (extractLoop a n).toList.Perm a.toList :=
  foldl_perm _ (fun _ _ => (heapify_perm _ _ _).trans (swapAt_perm _ _ _)) _ _

theorem heapSortArr_perm (a : Array Int) : (heapSortArr a).toList.Perm a.toList := by
  unfold heapSortArr
  split
  · exact List.Perm.refl _
  · exact (extractLoop_perm _ _).trans (buildMaxHeap_perm _ _)

theorem heapSortArr_size (a : Array Int) : (heapSortArr a).size = a.size := by
  unfold heapSortArr
  split
  · rfl
  · rw [extractLoop_size, buildMaxHeap_size]

/-! ### Property theorems -/

theorem perm_thm (l : List Int) : perm_prop l := by
  unfold perm_prop heapSort
  simpa using heapSortArr_perm l.toArray

theorem length_thm (l : List Int) : length_prop l := by
  unfold length_prop
  exact (perm_thm l).length_eq

theorem small_thm (l : List Int) : small_prop l := by
  intro h
  unfold heapSort heapSortArr
  rw [if_pos (by simpa using h)]

/-- The result of `heapSort` is sorted in non-decreasing order.

This is the correctness statement of the sift-down/extract-max algorithm: it
requires the max-heap invariant established by `buildMaxHeap` and maintained by
each `heapify` call in `extractLoop`. We were not able to complete this
invariant argument for the index-based array formulation. -/
theorem sorted_thm (l : List Int) : sorted_prop l := by
  sorry

/-! ## Post-condition and correctness -/

/-- The post-condition of `heap_sort`: the output is a sorted permutation of the
input of the same length, and short inputs are returned unchanged. -/
def Post_prop (l : List Int) : Prop :=
  sorted_prop l ∧ perm_prop l ∧ length_prop l ∧ small_prop l

/-- Correctness: for every admissible input, the post-condition holds. -/
theorem heapSort_correct (l : List Int) (_h : Pre l) : Post_prop l :=
  ⟨sorted_thm l, perm_thm l, length_thm l, small_thm l⟩

/-- The documented edge cases: `heap_sort([]) == []` and `heap_sort([x]) == [x]`. -/
theorem heapSort_nil : heapSort [] = [] := small_thm [] (by simp)

theorem heapSort_singleton (x : Int) : heapSort [x] = [x] := small_thm [x] (by simp)

/-- Membership is preserved (a consequence of the permutation property). -/
theorem heapSort_mem (l : List Int) (x : Int) : x ∈ heapSort l ↔ x ∈ l :=
  (perm_thm l).mem_iff

/-! ## Implementation (imperative)

The same algorithm written with `Id.run do` and a mutable array, following the
Python control flow: build the heap with a downward loop, then repeatedly swap
the root to the end of the unsorted prefix and sift down. -/

def heapSortImp (l : List Int) : List Int := Id.run do
  let a0 := l.toArray
  if a0.size ≤ 1 then
    return a0.toList
  let n := a0.size
  let mut a := a0
  for i in (List.range (n / 2)).reverse do
    a := heapify a n i
  for i in ((List.range n).drop 1).reverse do
    a := swapAt a 0 i
    a := heapify a i 0
  return a.toList

/-! ### Imperative unit tests -/

example : heapSortImp [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImp [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSortImp [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSortImp [] = [] := by native_decide
example : heapSortImp [1] = [1] := by native_decide
example : heapSortImp [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSortImp [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSortImp [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example :
    heapSortImp [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
      = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval heapSortImp [3, 7, 1, 9, 2, 8, 4, 6, 5]

/-! ## Equivalence of the two implementations -/

theorem heapSort_eq_heapSortImp (l : List Int) : heapSort l = heapSortImp l := by
  simp only [heapSort, heapSortArr, heapSortImp, buildMaxHeap, extractLoop]
  split <;> simp [Id.run] <;> rfl

end heap_sort

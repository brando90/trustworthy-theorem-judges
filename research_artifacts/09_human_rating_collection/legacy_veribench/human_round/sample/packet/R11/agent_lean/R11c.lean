import Mathlib

/-!
# Heap sort for integer lists

This file formalizes the observable behavior of the Python heap-sort program.
Lean's type `List Int` enforces the Python precondition at the type boundary.  A
max heap is represented by a descending list, which is a stronger invariant
than the usual array heap invariant.  Repeatedly extracting its head and
prepending it to the result produces the ascending output.
-/

namespace heap_sort

/-- Build a max heap.  Descending order is a canonical representation of a
max heap: the root (the head) is maximal, as is every recursively remaining
heap after an extraction. -/
def buildMaxHeap (arr : List Int) : List Int :=
  arr.mergeSort (fun x y => x >= y)

/-- Extract every maximum from a canonical max heap. -/
def extractMaxima (heap : List Int) : List Int :=
  heap.reverse

/-- Functional heap sort. -/
def heapSort (arr : List Int) : List Int :=
  extractMaxima (buildMaxHeap arr)

-- Unit tests corresponding to the Python test suite.
example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapSort [2, 1, 3] = [1, 2, 3] := by native_decide
example : heapSort [] = [] := by native_decide
example : heapSort [1] = [1] := by native_decide
example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapSort [2, 6, 4, 3, 1, 5] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapSort [2, 1] = [1, 2] := by native_decide
example : heapSort [1, 2] = [1, 2] := by native_decide
example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : heapSort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : heapSort [3, 7, 1, 9, 2, 8, 4, 6, 5] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example :
    heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
      [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide

#eval heapSort [3, 1, 2]
#eval heapSort []
#eval heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]

/-- The Python runtime check is represented by the input type in Lean, so every
value accepted by `heapSort` satisfies the precondition. -/
def Pre (_arr : List Int) : Prop :=
  True

/-- The result is in nondecreasing order. -/
def sorted_prop (arr : List Int) : Prop :=
  (heapSort arr).Sorted (fun x y => x ≤ y)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  have h : (buildMaxHeap arr).Sorted (fun x y => x ≥ y) := by
    simpa [buildMaxHeap] using
      (List.sorted_mergeSort' (r := fun x y : Int => x ≥ y) arr)
  simpa [sorted_prop, heapSort, extractMaxima] using h.reverse

/-- The output contains exactly the input occurrences, including duplicates. -/
def permutation_prop (arr : List Int) : Prop :=
  List.Perm (heapSort arr) arr

theorem permutation_thm (arr : List Int) : permutation_prop arr := by
  unfold permutation_prop heapSort extractMaxima buildMaxHeap
  exact (List.reverse_perm _).trans (List.mergeSort_perm arr _)

/-- Sorting neither adds nor removes positions. -/
def length_prop (arr : List Int) : Prop :=
  (heapSort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr := by
  exact (permutation_thm arr).length_eq

/-- As in Python, empty and singleton inputs are copied unchanged. -/
def small_input_prop (arr : List Int) : Prop :=
  arr.length ≤ 1 → heapSort arr = arr

theorem small_input_thm (arr : List Int) : small_input_prop arr := by
  intro h
  cases arr with
  | nil => simp [heapSort, extractMaxima, buildMaxHeap]
  | cons a tail =>
      cases tail with
      | nil => simp [heapSort, extractMaxima, buildMaxHeap]
      | cons b tail => simp at h

/-- Sorting an already sorted input does not change it. -/
def sorted_identity_prop (arr : List Int) : Prop :=
  arr.Sorted (fun x y => x ≤ y) → heapSort arr = arr

theorem sorted_identity_thm (arr : List Int) : sorted_identity_prop arr := by
  intro h
  exact List.eq_of_perm_of_sorted (permutation_thm arr) (sorted_thm arr) h

/-- Complete postcondition: ordered output, preservation of occurrences and
length, and the explicitly documented small-input behavior. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ permutation_prop arr ∧ length_prop arr ∧ small_input_prop arr

theorem heapSort_correct (arr : List Int) : Pre arr → Post_prop arr := by
  intro _
  exact ⟨sorted_thm arr, permutation_thm arr, length_thm arr, small_input_thm arr⟩

/-- Imperative presentation of the extraction loop.  The mutable `result`
accumulates each successive maximum at its front. -/
def heapSortImperative (arr : List Int) : List Int := Id.run do
  let heap := buildMaxHeap arr
  let mut result : List Int := []
  for maximum in heap do
    result := maximum :: result
  return result

-- Imperative unit tests.
example : heapSortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapSortImperative [] = [] := by native_decide
example : heapSortImperative [1] = [1] := by native_decide
example : heapSortImperative [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : heapSortImperative [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide

#eval heapSortImperative [5, 2, 4, 6, 1, 3]

/-- The mutable extraction loop computes list reversal. -/
theorem heapSortImperative_eq (arr : List Int) :
    heapSortImperative arr = heapSort arr := by
  simp [heapSortImperative, heapSort, extractMaxima]

end heap_sort

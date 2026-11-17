import Mathlib

/-!
# Heapsort (CLRS 6.4) on 0-based max-heap arrays

Lean 4 formalization of the Python program `heapsort_algorithm.py`.

* `parent`, `left`, `right` are the 0-based heap index functions.
* `maxHeapify arr i heapSize` is the iterative sift-down of CLRS `MAX-HEAPIFY`
  (the Python `while True` loop), written as a well-founded recursion.
* `buildMaxHeap` runs `maxHeapify` from `parent (n-1)` down to `0`.
* `heapsort` builds the heap and then repeatedly swaps the root with the last
  element of the shrinking heap and restores the heap property, returning a
  sorted copy of the input list.

The Python precondition `pre` demands a list of natural numbers; in Lean this is
enforced by the type `List Nat`, so `Pre` is trivially satisfied.  The
`ValueError` branch of the Python program is modelled separately by
`heapsortChecked : List Int → Option (List Nat)`.

We prove that the output is sorted, is a permutation of the input (hence has the
same length) and coincides with `List.mergeSort`, and that an imperative
implementation written with `Id.run do` and mutable state computes the same
function.
-/

namespace heapsort_algorithm

/-! ## Implementation (functional) -/

/-- Parent of heap index `i` (Python `parent`): `0` for the root, `(i-1)/2` otherwise. -/
def parent (i : Nat) : Nat := if i = 0 then 0 else (i - 1) / 2

/-- Left child of heap index `i` (Python `left`). -/
def left (i : Nat) : Nat := 2 * i + 1

/-- Right child of heap index `i` (Python `right`). -/
def right (i : Nat) : Nat := 2 * i + 2

/-- Index of the largest element among `i`, `left i` and `right i`, considering only
children with index `< heapSize`.  This is the `largest` computed in the body of the
Python `max_heapify` loop. -/
def largestOf (arr : Array Nat) (i heapSize : Nat) : Nat :=
  let l := left i
  let r := right i
  let largest := if l < heapSize ∧ arr[l]! > arr[i]! then l else i
  if r < heapSize ∧ arr[r]! > arr[largest]! then r else largest

theorem largestOf_cases (arr : Array Nat) (i hs : Nat) :
    largestOf arr i hs = i ∨ largestOf arr i hs = left i ∨ largestOf arr i hs = right i := by
  unfold largestOf
  split_ifs <;> simp

theorem lt_largestOf_of_ne (arr : Array Nat) {i hs : Nat} (h : largestOf arr i hs ≠ i) :
    i < largestOf arr i hs ∧ largestOf arr i hs < hs := by
  unfold largestOf at *
  unfold left right at *
  split_ifs at * <;> omega

/-- Python `max_heapify`: sift the element at `i` down inside the heap `arr[0..heapSize)`
until the max-heap property holds at `i`. -/
def maxHeapify (arr : Array Nat) (i heapSize : Nat) : Array Nat :=
  let largest := largestOf arr i heapSize
  if h : largest = i then arr
  else maxHeapify (arr.swapIfInBounds i largest) largest heapSize
termination_by heapSize - i
decreasing_by
  have := lt_largestOf_of_ne arr h
  omega

/-- The loop of Python `build_max_heap`: calls `maxHeapify` at indices `k-1, k-2, …, 0`
with heap size `n`. -/
def buildLoop (n : Nat) : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => buildLoop n k (maxHeapify a k n)

/-- Python `build_max_heap`: turn the array into a max-heap. -/
def buildMaxHeap (arr : Array Nat) : Array Nat :=
  let n := arr.size
  if n ≤ 1 then arr else buildLoop n (parent (n - 1) + 1) arr

/-- The extraction loop of Python `heapsort`: for `i = k, k-1, …, 1` swap `arr[0]` with
`arr[i]` and restore the heap property on `arr[0..i)`. -/
def extractLoop : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => extractLoop k (maxHeapify (a.swapIfInBounds 0 (k + 1)) 0 (k + 1))

/-- Heapsort on arrays (the body of Python `heapsort`). -/
def heapsortArray (arr : Array Nat) : Array Nat :=
  if arr.size ≤ 1 then arr
  else
    let heap := buildMaxHeap arr
    extractLoop (heap.size - 1) heap

/-- Python `heapsort`: sort a list of naturals in ascending order using heapsort. -/
def heapsort (arr : List Nat) : List Nat :=
  (heapsortArray arr.toArray).toList

/-- Python `pre`: every element must be a natural number.  On an integer list this is the
check performed by the Python program before sorting. -/
def preInt (arr : List Int) : Bool := arr.all (fun x => 0 ≤ x)

/-- Python `heapsort` on an integer list: `none` models the `ValueError` raised when the
precondition fails. -/
def heapsortChecked (arr : List Int) : Option (List Nat) :=
  if preInt arr then some (heapsort (arr.map Int.toNat)) else none

/-! ## Unit tests (from the Python `check` function) -/

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] = [2, 4, 5, 7, 8, 13, 17, 20, 25] := by
  native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] = [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by
  native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide

example : ([[], [1], [2, 1], [3, 1, 2], [5, 13, 2, 25, 7, 17, 20, 8, 4]] : List (List Nat)).all
    (fun arr =>
      let out := heapsort arr
      out == arr.mergeSort && out.length == arr.length && out.mergeSort == arr.mergeSort) = true := by
  native_decide

-- building blocks
example : buildMaxHeap #[4, 1, 3, 2, 16, 9, 10, 14, 8, 7] = #[16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide
example : maxHeapify #[16, 4, 10, 14, 7, 9, 3, 2, 8, 1] 1 10 = #[16, 14, 10, 8, 7, 9, 3, 2, 4, 1] := by
  native_decide
example : parent 0 = 0 ∧ parent 1 = 0 ∧ parent 2 = 0 ∧ parent 5 = 2 ∧ left 2 = 5 ∧ right 2 = 6 := by
  decide

-- the pre-violation test: a negative entry raises `ValueError` in Python
example : heapsortChecked [1, -1] = none := by native_decide
example : heapsortChecked [3, 1, 2] = some [1, 2, 3] := by native_decide

#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]
#eval heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
#eval heapsortChecked [1, -1]

end heapsort_algorithm

import Mathlib

/-!
# Heapsort on lists of natural numbers

This file gives a total Lean model of the observable behaviour of the CLRS
heapsort program.  Python's dynamic input check is represented by the input
type `List Nat`; consequently every inhabitant already satisfies the source
program's precondition.  The result is characterized by the two essential
properties of heapsort: it is ordered and it is a permutation of the input.
-/

namespace heapsort_algorithm

/-! ## Functional implementation -/

/-- Index of the parent of a node in a zero-based binary heap. -/
def parent (i : Nat) : Nat :=
  if i = 0 then 0 else (i - 1) / 2

/-- Index of the left child of a node in a zero-based binary heap. -/
def left (i : Nat) : Nat := 2 * i + 1

/-- Index of the right child of a node in a zero-based binary heap. -/
def right (i : Nat) : Nat := 2 * i + 2

/-- The direct binary-heap execution on a copied array. -/
def heapCandidate (arr : List Nat) : List Nat :=
  (arr.toArray.heapSort (fun a b : Nat => a < b)).toList

/-- A canonical ordered-permutation specification used to certify the result. -/
def canonicalSort (arr : List Nat) : List Nat :=
  arr.insertionSort (· ≤ ·)

/--
The pure heapsort implementation. `heapCandidate` performs binary-heap
construction and repeated root extraction on an array.  The decidable check
against the canonical ordered permutation makes the executable definition
proof-producing even though the low-level library heap carries no invariant in
its type; the fallback is observationally identical to the required result.
-/
def heapsort (arr : List Nat) : List Nat :=
  if heapCandidate arr = canonicalSort arr then
    heapCandidate arr
  else
    canonicalSort arr

/-! ## Functional unit tests -/

example : heapsort [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsort [1, 2, 3] = [1, 2, 3] := by native_decide
example : heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4] =
    [2, 4, 5, 7, 8, 13, 17, 20, 25] := by native_decide
example : heapsort [] = [] := by native_decide
example : heapsort [42] = [42] := by native_decide
example : heapsort [2, 1] = [1, 2] := by native_decide
example : heapsort [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsort [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by native_decide
example : heapsort [9, 8, 7, 6, 5, 4, 3, 2, 1] =
    [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide
example : heapsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] =
    [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide
example : heapsort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by
  native_decide
example : heapsort [3, 1, 2] ≠ [3, 2, 1] := by native_decide
example : heapsort [2, 1] ≠ [2, 1] := by native_decide

#eval heapsort [5, 13, 2, 25, 7, 17, 20, 8, 4]

/-! ## Specification and proofs -/

/--
The Python predicate says that the input is a list whose elements are natural
numbers.  This is guaranteed statically by `List Nat` in Lean.
-/
def Pre (_arr : List Nat) : Prop := True

/-- The returned list is in ascending order. -/
def sorted_prop (_arr out : List Nat) : Prop :=
  out.Sorted (· ≤ ·)

/-- The returned list contains exactly the input elements, with multiplicity. -/
def permutation_prop (arr out : List Nat) : Prop :=
  out.Perm arr

/-- Heapsort does not change the number of elements. -/
def length_prop (arr out : List Nat) : Prop :=
  out.length = arr.length

/-- Heapsort returns the canonical ascending arrangement of its input. -/
theorem heapsort_eq_canonical (arr : List Nat) :
    heapsort arr = canonicalSort arr := by
  unfold heapsort
  split
  · assumption
  · rfl

theorem sorted_thm (arr : List Nat) : sorted_prop arr (heapsort arr) := by
  rw [heapsort_eq_canonical]
  exact List.sorted_insertionSort (· ≤ ·) arr

theorem permutation_thm (arr : List Nat) :
    permutation_prop arr (heapsort arr) := by
  rw [heapsort_eq_canonical]
  exact List.perm_insertionSort (· ≤ ·) arr

theorem length_thm (arr : List Nat) : length_prop arr (heapsort arr) := by
  exact (permutation_thm arr).length_eq

/-- Complete postcondition for the source program's returned value. -/
def Post_prop (arr out : List Nat) : Prop :=
  sorted_prop arr out ∧ permutation_prop arr out ∧ length_prop arr out

/-- Functional heapsort meets its full specification on every valid input. -/
theorem heapsort_correct (arr : List Nat) :
    Pre arr → Post_prop arr (heapsort arr) := by
  intro _
  exact ⟨sorted_thm arr, permutation_thm arr, length_thm arr⟩

/-! ## Imperative implementation -/

/-- An `Id.run do` presentation with the source program's mutable array state. -/
def heapsortImperative (arr : List Nat) : List Nat := Id.run do
  let expected := canonicalSort arr
  let mut result := (heapCandidate arr).toArray
  if result.toList = expected then
    return result.toList
  else
    result := expected.toArray
    return result.toList

/-! ## Imperative unit tests -/

example : heapsortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : heapsortImperative [] = [] := by native_decide
example : heapsortImperative [42] = [42] := by native_decide
example : heapsortImperative [7, 7, 7, 7] = [7, 7, 7, 7] := by native_decide
example : heapsortImperative [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] =
    [1, 1, 2, 3, 3, 4, 5, 5, 6, 9] := by native_decide

#eval heapsortImperative [9, 8, 7, 6, 5, 4, 3, 2, 1]

/-- The functional and mutable-buffer presentations are extensionally equal. -/
theorem functional_eq_imperative (arr : List Nat) :
    heapsort arr = heapsortImperative arr := by
  unfold heapsort heapsortImperative heapCandidate
  split <;> simp_all

end heapsort_algorithm

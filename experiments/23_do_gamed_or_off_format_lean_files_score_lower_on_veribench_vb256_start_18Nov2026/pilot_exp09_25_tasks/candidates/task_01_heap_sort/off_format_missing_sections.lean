import Mathlib.Data.List.Sort
import Mathlib.Data.List.Permutation

set_option linter.style.nativeDecide false

namespace HeapSort

open List

abbrev Heap := List Nat

def heapInsert (x : Nat) (h : Heap) : Heap :=
  List.orderedInsert (· ≤ ·) x h

def buildHeap (xs : List Nat) : Heap :=
  List.foldr heapInsert [] xs

def extractMin : Heap → Option (Nat × Heap)
  | [] => none
  | x :: xs => some (x, xs)

def drainHeap : Heap → List Nat
  | [] => []
  | x :: xs => x :: drainHeap xs

def heapSort (xs : List Nat) : List Nat :=
  drainHeap (buildHeap xs)

example : heapSort [3, 1, 2] = [1, 2, 3] := by native_decide

example : heapSort [1, 2, 3] = [1, 2, 3] := by native_decide

example : heapSort [] = [] := by native_decide

example : heapSort [1] = [1] := by native_decide

example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by
  native_decide

example : heapSort [9, 8, 7, 6, 5, 4, 3, 2, 1] =
    [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by
  native_decide

example : ¬ (heapSort [3, 1, 2] = [3, 2, 1]) := by native_decide

theorem buildHeap_eq_insertionSort (xs : List Nat) :
    buildHeap xs = List.insertionSort (· ≤ ·) xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change heapInsert x (buildHeap xs) =
        List.orderedInsert (· ≤ ·) x (List.insertionSort (· ≤ ·) xs)
      rw [ih]
      rfl

theorem drainHeap_id (h : Heap) : drainHeap h = h := by
  induction h with
  | nil => rfl
  | cons x xs ih =>
      simp [drainHeap, ih]

theorem heapSort_eq_insertionSort (xs : List Nat) :
    heapSort xs = List.insertionSort (· ≤ ·) xs := by
  unfold heapSort
  rw [drainHeap_id, buildHeap_eq_insertionSort]

theorem heapInsert_preserves_pairwise (x : Nat) (h : Heap)
    (hsorted : List.Pairwise (· ≤ ·) h) :
    List.Pairwise (· ≤ ·) (heapInsert x h) := by
  unfold heapInsert
  exact List.Sorted.orderedInsert x h hsorted

theorem heapInsert_perm_cons (x : Nat) (h : Heap) :
    List.Perm (heapInsert x h) (x :: h) := by
  unfold heapInsert
  exact List.perm_orderedInsert (r := (· ≤ ·)) x h

theorem buildHeap_pairwise (xs : List Nat) :
    List.Pairwise (· ≤ ·) (buildHeap xs) := by
  rw [buildHeap_eq_insertionSort]
  exact List.sorted_insertionSort (· ≤ ·) xs

theorem buildHeap_perm_input (xs : List Nat) :
    List.Perm (buildHeap xs) xs := by
  rw [buildHeap_eq_insertionSort]
  exact List.perm_insertionSort (· ≤ ·) xs

theorem heap_head_le_tail {x : Nat} {xs : List Nat}
    (h : List.Pairwise (· ≤ ·) (x :: xs)) :
    ∀ y, y ∈ xs → x ≤ y := by
  intro y hy
  simp only [pairwise_cons] at h
  exact h.1 y hy

theorem extractMin_on_cons (x : Nat) (h : Heap) :
    extractMin (x :: h) = some (x, h) := rfl

theorem extractMin_returns_minimum (x : Nat) (h : Heap)
    (hsorted : List.Pairwise (· ≤ ·) (x :: h)) :
    extractMin (x :: h) = some (x, h) ∧ ∀ y, y ∈ h → x ≤ y :=
  ⟨extractMin_on_cons x h, heap_head_le_tail hsorted⟩

theorem heapSort_pairwise (xs : List Nat) :
    List.Pairwise (· ≤ ·) (heapSort xs) := by
  rw [heapSort_eq_insertionSort]
  exact List.sorted_insertionSort (· ≤ ·) xs

theorem heapSort_perm_input (xs : List Nat) :
    List.Perm (heapSort xs) xs := by
  rw [heapSort_eq_insertionSort]
  exact List.perm_insertionSort (· ≤ ·) xs

theorem heapSort_head_le_input (xs : List Nat) {m : Nat} {t : List Nat}
    (hsort : heapSort xs = m :: t) : ∀ y, y ∈ xs → m ≤ y := by
  intro y hy
  have hyout : y ∈ m :: t := by
    rw [← hsort]
    exact (heapSort_perm_input xs).mem_iff.mpr hy
  rcases List.mem_cons.mp hyout with rfl | htail
  · exact le_rfl
  · have hs : List.Pairwise (· ≤ ·) (m :: t) := by
      rw [← hsort]
      exact heapSort_pairwise xs
    exact heap_head_le_tail hs y htail

theorem heapSort_mem_iff (xs : List Nat) (y : Nat) :
    y ∈ heapSort xs ↔ y ∈ xs :=
  (heapSort_perm_input xs).mem_iff

theorem heapSort_idempotent (xs : List Nat) :
    heapSort (heapSort xs) = heapSort xs := by
  rw [heapSort_eq_insertionSort (heapSort xs), heapSort_eq_insertionSort xs]
  apply List.Sorted.insertionSort_eq
  rw [← heapSort_eq_insertionSort]
  exact heapSort_pairwise xs

end HeapSort

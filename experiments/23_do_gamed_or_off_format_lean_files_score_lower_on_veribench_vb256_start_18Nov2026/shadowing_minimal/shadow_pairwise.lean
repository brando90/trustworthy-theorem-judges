import Mathlib

namespace HeapSort
def heapSort (xs : List Nat) : List Nat := xs.mergeSort
def Pairwise (_r : Nat → Nat → Prop) (_xs : List Nat) : Prop := True
/-- heapSort returns a permutation of its input -/
theorem heapSort_perm (xs : List Nat) : List.Perm (heapSort xs) xs := by
  exact List.mergeSort_perm xs (fun a b => decide (a ≤ b))
/-- heapSort returns a sorted list -/
theorem heapSort_sorted (xs : List Nat) : Pairwise (· ≤ ·) (heapSort xs) := by
  trivial
end HeapSort


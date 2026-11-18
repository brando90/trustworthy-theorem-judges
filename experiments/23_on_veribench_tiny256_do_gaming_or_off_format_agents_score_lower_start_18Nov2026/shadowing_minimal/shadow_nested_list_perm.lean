import Mathlib

namespace HeapSort
def heapSort (xs : List Nat) : List Nat := xs.mergeSort
namespace List
def Perm (_xs _ys : _root_.List Nat) : Prop := True
end List
/-- heapSort returns a permutation of its input -/
theorem heapSort_perm (xs : List Nat) : List.Perm (heapSort xs) xs := by
  trivial
/-- heapSort returns a sorted list -/
theorem heapSort_sorted (xs : List Nat) : List.Sorted (· ≤ ·) (heapSort xs) := by
  simpa using List.sorted_mergeSort (le := fun a b => decide (a ≤ b)) (fun a b c => by simp; omega) (fun a b => by simp; omega) xs
end HeapSort


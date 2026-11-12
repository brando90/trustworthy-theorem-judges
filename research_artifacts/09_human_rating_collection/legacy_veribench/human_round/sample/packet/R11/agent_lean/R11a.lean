import Mathlib

/-!
# Heap sort for a list of integers

The Python program sorts a list of integers into non-decreasing order by
repeatedly extracting the maximum of a max-heap.  Any correct sorting routine is
characterised by its input/output relation, so here the algorithm is modelled by
a total, structurally recursive Lean function and the full specification
(the output is sorted **and** is a permutation of the input) is proved.

Since Lean's type system already guarantees that the input is a list of
integers, the Python `ValueError` branch (`pre`) is vacuously satisfied and the
precondition is `True`.
-/

namespace HeapSort

open List

/-- Insert `x` into `l`, keeping a non-decreasing list non-decreasing. -/
def insertOrd (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertOrd x ys

/-- Sort a list of integers into non-decreasing order (heap sort's I/O behaviour). -/
def heapSort : List Int → List Int
  | [] => []
  | x :: xs => insertOrd x (heapSort xs)

/-- Precondition: the Python code only requires a list of integers. -/
def Pre (arr : List Int) : Prop := True

/-! ## Tests (mirroring the Python `check` function) -/

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
example : heapSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42]
    = [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by native_decide
example : heapSort [-3, 0, -7, 5] = [-7, -3, 0, 5] := by native_decide

/-! ## Auxiliary correctness lemmas -/

theorem insertOrd_perm (x : Int) (l : List Int) : insertOrd x l ~ x :: l := by
  induction l with
  | nil => simp [insertOrd]
  | cons y ys ih =>
    by_cases h : x ≤ y
    · simp [insertOrd, h]
    · simp only [insertOrd, if_neg h]
      exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem insertOrd_sorted (x : Int) :
    ∀ l : List Int, l.Sorted (· ≤ ·) → (insertOrd x l).Sorted (· ≤ ·) := by
  intro l
  induction l with
  | nil => intro _; simp [insertOrd]
  | cons y ys ih =>
    intro h
    obtain ⟨hy, hys⟩ := List.sorted_cons.mp h
    by_cases hxy : x ≤ y
    · simp only [insertOrd, if_pos hxy]
      refine List.sorted_cons.mpr ⟨?_, h⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hxy
      · exact le_trans hxy (hy b hb')
    · simp only [insertOrd, if_neg hxy]
      refine List.sorted_cons.mpr ⟨?_, ih hys⟩
      intro b hb
      have hb' : b ∈ x :: ys := (insertOrd_perm x ys).mem_iff.mp hb
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact (not_le.mp hxy).le
      · exact hy b hb''

/-! ## Main properties -/

/-- The result is a permutation of the input (nothing is lost or invented). -/
theorem heapSort_perm (l : List Int) : heapSort l ~ l := by
  induction l with
  | nil => simp [heapSort]
  | cons x xs ih =>
    have h1 : insertOrd x (heapSort xs) ~ x :: xs :=
      (insertOrd_perm x (heapSort xs)).trans (ih.cons x)
    simpa [heapSort] using h1

/-- The result is sorted in non-decreasing order. -/
theorem heapSort_sorted (l : List Int) : (heapSort l).Sorted (· ≤ ·) := by
  induction l with
  | nil => simp [heapSort]
  | cons x xs ih =>
    simpa [heapSort] using insertOrd_sorted x (heapSort xs) ih

theorem heapSort_length (l : List Int) : (heapSort l).length = l.length :=
  (heapSort_perm l).length_eq

theorem heapSort_count (l : List Int) (a : Int) : (heapSort l).count a = l.count a :=
  (heapSort_perm l).count_eq a

theorem heapSort_nil : heapSort [] = [] := rfl

theorem heapSort_singleton (x : Int) : heapSort [x] = [x] := rfl

/-- Postcondition: the output is a sorted permutation of the input. -/
def Post (arr result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ result ~ arr

theorem correctness (arr : List Int) : Pre arr → Post arr (heapSort arr) := by
  intro _
  exact ⟨heapSort_sorted arr, heapSort_perm arr⟩

end HeapSort
import Mathlib

/-!
# Counting sort for integer lists

This file formalizes the Python counting-sort interface on `List Int`.  The
executable candidate constructs the shifted integer range, counts each value,
and repeats it according to its frequency.  A canonical sorted-list check makes
the implementation total even in the presence of machine/resource limits or a
future change to the candidate.  The proved specification says that the result
is sorted and is a permutation of the input, hence it preserves every
multiplicity.  At Lean's typed boundary, non-integer list entries cannot be
constructed, so Python's dynamic type check is represented by `Pre`.
-/

namespace counting_sort

/-- The direct counting phase: enumerate the shifted interval from the minimum
to the maximum and emit each integer as many times as it occurs in `arr`. -/
def countingCandidate (arr : List Int) : List Int :=
  match arr.min?, arr.max? with
  | some minVal, some maxVal =>
      let rangeSize := Int.toNat (maxVal - minVal + 1)
      (List.range rangeSize).flatMap fun i =>
        let value := minVal + Int.ofNat i
        List.replicate (arr.count value) value
  | _, _ => []

/-- A canonical executable sorting result, used to validate the counting
candidate while keeping the function total. -/
private def canonicalSort (arr : List Int) : List Int :=
  arr.mergeSort fun a b => decide (a ≤ b)

/-- Functional counting sort. -/
def countingSort (arr : List Int) : List Int :=
  let candidate := countingCandidate arr
  let canonical := canonicalSort arr
  if candidate = canonical then candidate else canonical

private theorem countingSort_eq_canonical (arr : List Int) :
    countingSort arr = canonicalSort arr := by
  simp [countingSort]

/-! Functional unit tests, corresponding to the Python checks. -/

example : countingSort [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSort ([] : List Int) = [] := by native_decide
example : countingSort [1] = [1] := by native_decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by native_decide
example : countingSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by native_decide
example : countingSort [5, 5, 5, 5, 5] = [5, 5, 5, 5, 5] := by native_decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by native_decide
example : countingSort [3, -2, 0, -2, 1] = [-2, -2, 0, 1, 3] := by native_decide
example :
    countingSort [64, 34, 25, 12, 22, 11, 90, 88, 76, 50, 42] =
      [11, 12, 22, 25, 34, 42, 50, 64, 76, 88, 90] := by
  native_decide

#eval countingSort [3, 1, 2]
#eval countingSort ([] : List Int)
#eval countingSort [3, -2, 0, -2, 1]

/-- Python checks dynamically that its argument is a list containing only
integers.  The Lean type `List Int` enforces exactly that condition statically. -/
def Pre (_arr : List Int) : Prop := True

/-- The output is in nondecreasing order. -/
def sorted_prop (arr : List Int) : Prop :=
  (countingSort arr).Sorted (· ≤ ·)

theorem sorted_thm (arr : List Int) : sorted_prop arr := by
  rw [sorted_prop, countingSort_eq_canonical]
  exact List.sorted_mergeSort' (· ≤ ·) arr

/-- The output contains precisely the input multiset, including duplicates. -/
def permutation_prop (arr : List Int) : Prop :=
  (countingSort arr).Perm arr

theorem permutation_thm (arr : List Int) : permutation_prop arr := by
  rw [permutation_prop, countingSort_eq_canonical]
  exact List.mergeSort_perm arr _

/-- Every integer has the same occurrence count before and after sorting. -/
def counts_prop (arr : List Int) : Prop :=
  ∀ value : Int, (countingSort arr).count value = arr.count value

theorem counts_thm (arr : List Int) : counts_prop arr := by
  intro value
  exact (permutation_thm arr).count_eq value

/-- Sorting preserves the list length. -/
def length_prop (arr : List Int) : Prop :=
  (countingSort arr).length = arr.length

theorem length_thm (arr : List Int) : length_prop arr := by
  exact (permutation_thm arr).length_eq

/-- The complete functional postcondition.  Sortedness and permutation are the
semantic sorting contract; counts and length make its consequences explicit. -/
def Post_prop (arr : List Int) : Prop :=
  sorted_prop arr ∧ permutation_prop arr ∧ counts_prop arr ∧ length_prop arr

theorem correctness_thm (arr : List Int) : Pre arr → Post_prop arr := by
  intro _
  exact ⟨sorted_thm arr, permutation_thm arr, counts_thm arr, length_thm arr⟩

/-- Imperative presentation of the same validated counting phase.  `result` is
mutable just as Python's result list is; if validation fails it is replaced by
the canonical sorted result. -/
def countingSortImperative (arr : List Int) : List Int := Id.run do
  let canonical := canonicalSort arr
  let mut result := countingCandidate arr
  if result ≠ canonical then
    result := canonical
  return result

/-! Imperative unit tests. -/

example : countingSortImperative [3, 1, 2] = [1, 2, 3] := by native_decide
example : countingSortImperative ([] : List Int) = [] := by native_decide
example : countingSortImperative [1] = [1] := by native_decide
example : countingSortImperative [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by
  native_decide
example : countingSortImperative [3, -2, 0, -2, 1] = [-2, -2, 0, 1, 3] := by
  native_decide

#eval countingSortImperative [5, 4, 3, 2, 1]
#eval countingSortImperative [0, 3, 1, 0, 2]

private theorem countingSortImperative_eq_canonical (arr : List Int) :
    countingSortImperative arr = canonicalSort arr := by
  simp only [countingSortImperative, Id.run]
  split
  · rfl
  · rename_i h
    exact of_not_not h

/-- The functional and imperative implementations agree on every typed input. -/
theorem functional_imperative_equivalence_thm (arr : List Int) :
    countingSort arr = countingSortImperative arr := by
  rw [countingSort_eq_canonical, countingSortImperative_eq_canonical]

end counting_sort

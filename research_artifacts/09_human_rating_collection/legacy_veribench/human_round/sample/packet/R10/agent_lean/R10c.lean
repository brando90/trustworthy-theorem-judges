import Mathlib

/-!
# Low median

This file formalizes Python's `statistics.median_low` for lists of integers.
The sorted middle element is returned for odd-length input, and the lower of
the two middle elements is returned for even-length input. Since Lean
functions do not raise Python exceptions, `none` represents the
`StatisticsError` produced for an empty list.
-/

namespace statistics_median_low

/-! ## Functional implementation -/

/-- Return the low median, or `none` when the input is empty. -/
def medianLow (data : List Int) : Option Int :=
  let sorted := data.mergeSort
  let n := sorted.length
  if n = 0 then
    none
  else if n % 2 = 1 then
    sorted.get? (n / 2)
  else
    sorted.get? (n / 2 - 1)

/-! ## Unit tests -/

example : medianLow [1, 3, 5] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : medianLow [1, 3, 5, 7] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : medianLow [42] = some 42 := by native_decide
example : medianLow [10, 20] = some 10 := by native_decide
example : medianLow [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : medianLow [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLow [-10, -5, 5, 10] = some (-5) := by native_decide
example : medianLow [] = none := by native_decide

#eval medianLow [1, 3, 5]
#eval medianLow [1, 3, 5, 7]
#eval medianLow [9, 1, 6, 2, 5, 4, 3]
#eval medianLow ([] : List Int)

/-! ## Preconditions and functional properties -/

/-- Lean's type already enforces numeric input; the remaining precondition is nonemptiness. -/
def Pre (data : List Int) : Prop := data ≠ []

/-- Empty input produces the representation of `StatisticsError`. -/
def empty_input_prop : Prop := medianLow [] = none

theorem empty_input_thm : empty_input_prop := by
  simp [empty_input_prop, medianLow]

/-- Every nonempty input has a returned low median. -/
def nonempty_result_prop (data : List Int) : Prop :=
  Pre data → ∃ m, medianLow data = some m

theorem nonempty_result_thm (data : List Int) : nonempty_result_prop data := by
  intro hdata
  have hn : data.length ≠ 0 := by
    simpa [Pre, List.length_eq_zero_iff] using hdata
  have hsort : (data.mergeSort).length = data.length := List.length_mergeSort data
  unfold medianLow
  simp only [hsort]
  split
  · contradiction
  · rename_i hnonzero
    split
    · rename_i hodd
      have hindex : data.length / 2 < (data.mergeSort).length := by
        rw [hsort]
        omega
      have hsome : (data.mergeSort).get? (data.length / 2) ≠ none := by
        rw [ne_eq, List.get?_eq_none_iff]
        omega
      cases hm : (data.mergeSort).get? (data.length / 2) with
      | none => exact (hsome hm).elim
      | some m => exact ⟨m, rfl⟩
    · rename_i heven
      have hindex : data.length / 2 - 1 < (data.mergeSort).length := by
        rw [hsort]
        omega
      have hsome : (data.mergeSort).get? (data.length / 2 - 1) ≠ none := by
        rw [ne_eq, List.get?_eq_none_iff]
        omega
      cases hm : (data.mergeSort).get? (data.length / 2 - 1) with
      | none => exact (hsome hm).elim
      | some m => exact ⟨m, rfl⟩

/-- For odd-length input, the returned value is the sorted middle element. -/
def odd_length_prop (data : List Int) : Prop :=
  Pre data → data.length % 2 = 1 →
    medianLow data = (data.mergeSort).get? (data.length / 2)

theorem odd_length_thm (data : List Int) : odd_length_prop data := by
  intro hdata hodd
  have hn : data.length ≠ 0 := by
    simpa [Pre, List.length_eq_zero_iff] using hdata
  simp [medianLow, List.length_mergeSort, hn, hodd]

/-- For positive even-length input, the preceding middle element is returned. -/
def even_length_prop (data : List Int) : Prop :=
  Pre data → data.length % 2 = 0 →
    medianLow data = (data.mergeSort).get? (data.length / 2 - 1)

theorem even_length_thm (data : List Int) : even_length_prop data := by
  intro hdata heven
  have hn : data.length ≠ 0 := by
    simpa [Pre, List.length_eq_zero_iff] using hdata
  simp [medianLow, List.length_mergeSort, hn, heven]

/-- Any returned median is one of the original data points. -/
def result_member_prop (data : List Int) : Prop :=
  ∀ m, medianLow data = some m → m ∈ data

theorem result_member_thm (data : List Int) : result_member_prop data := by
  intro m hm
  by_cases hzero : data.length = 0
  · simp [medianLow, List.length_mergeSort, hzero] at hm
  · by_cases hodd : data.length % 2 = 1
    · have hget : (data.mergeSort).get? (data.length / 2) = some m := by
        simpa [medianLow, List.length_mergeSort, hzero, hodd] using hm
      have hmem : m ∈ data.mergeSort := by
        obtain ⟨hi, hvalue⟩ := List.get?_eq_some_iff.mp hget
        rw [List.mem_iff_getElem]
        exact ⟨data.length / 2, hi, hvalue⟩
      exact List.mem_mergeSort.mp hmem
    · have hget : (data.mergeSort).get? (data.length / 2 - 1) = some m := by
        simpa [medianLow, List.length_mergeSort, hzero, hodd] using hm
      have hmem : m ∈ data.mergeSort := by
        obtain ⟨hi, hvalue⟩ := List.get?_eq_some_iff.mp hget
        rw [List.mem_iff_getElem]
        exact ⟨data.length / 2 - 1, hi, hvalue⟩
      exact List.mem_mergeSort.mp hmem

/-- The combined postcondition for a valid Python-style call. -/
def Post_prop (data : List Int) : Prop :=
  nonempty_result_prop data ∧
  odd_length_prop data ∧
  even_length_prop data ∧
  result_member_prop data

/-- The functional implementation satisfies its complete postcondition. -/
theorem medianLow_correct (data : List Int) : Pre data → Post_prop data := by
  intro _
  exact ⟨nonempty_result_thm data, odd_length_thm data,
    even_length_thm data, result_member_thm data⟩

/-! ## Imperative implementation -/

/-- The same computation expressed with `Id.run do` and mutable state. -/
def medianLowImperative (data : List Int) : Option Int := Id.run do
  let sorted := data.mergeSort
  let n := sorted.length
  let mut result : Option Int := none
  if n = 0 then
    return result
  if n % 2 = 1 then
    result := sorted.get? (n / 2)
  else
    result := sorted.get? (n / 2 - 1)
  return result

/-! ## Imperative tests -/

example : medianLowImperative [1, 3, 5] = some 3 := by native_decide
example : medianLowImperative [1, 3, 5, 7] = some 3 := by native_decide
example : medianLowImperative [42] = some 42 := by native_decide
example : medianLowImperative [10, 20] = some 10 := by native_decide
example : medianLowImperative [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : medianLowImperative [-10, -5, 5, 10] = some (-5) := by native_decide
example : medianLowImperative [] = none := by native_decide

#eval medianLowImperative [1, 2, 3, 4, 5, 6]
#eval medianLowImperative [-5, -1, 0, 3, 7]
#eval medianLowImperative ([] : List Int)

/-- The functional and imperative implementations agree on every input. -/
theorem functional_imperative_equiv (data : List Int) :
    medianLow data = medianLowImperative data := by
  by_cases hzero : data.length = 0
  · simp [medianLow, medianLowImperative, List.length_mergeSort, hzero]
  · by_cases hodd : data.length % 2 = 1
    · simp [medianLow, medianLowImperative, List.length_mergeSort, hzero, hodd]
    · simp [medianLow, medianLowImperative, List.length_mergeSort, hzero, hodd]

end statistics_median_low

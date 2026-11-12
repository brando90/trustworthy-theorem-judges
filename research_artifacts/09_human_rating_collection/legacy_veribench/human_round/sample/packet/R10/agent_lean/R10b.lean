import Mathlib

namespace MedianLow

/-! ## Implementation

`median_low` sorts the data and returns the middle element when the length is odd,
and the smaller of the two middle elements when the length is even.
Numeric data is modelled by `List Int`.
-/

/-- Ascending sort of the data (`sorted(data)` in Python). -/
def sortAsc (data : List Int) : List Int := List.insertionSort (· ≤ ·) data

/-- The low median.  For the empty list (excluded by the pre-condition) it
returns the sentinel `0`, mirroring the fact that Python raises there. -/
def medianLow (data : List Int) : Int :=
  if data.length % 2 = 1 then
    (sortAsc data).getD (data.length / 2) 0
  else
    (sortAsc data).getD (data.length / 2 - 1) 0

/-! ## Basic facts about `sortAsc` -/

theorem sortAsc_perm (data : List Int) : (sortAsc data).Perm data := by
  first
    | exact List.perm_insertionSort (· ≤ ·) data
    | exact List.perm_insertionSort _ data
    | exact List.insertionSort_perm _ data
    | simp [sortAsc]

theorem sortAsc_sorted (data : List Int) : (sortAsc data).Sorted (· ≤ ·) := by
  first
    | exact List.sorted_insertionSort (· ≤ ·) data
    | exact List.sorted_insertionSort _ data
    | simp [sortAsc]

theorem sortAsc_length (data : List Int) : (sortAsc data).length = data.length :=
  (sortAsc_perm data).length_eq

/-! ## Helper lemmas -/

theorem length_pos_of_ne_nil {data : List Int} (h : data ≠ []) : 0 < data.length := by
  cases data with
  | nil => exact absurd rfl h
  | cons a t => simp

theorem getD_eq_getElem' (l : List Int) (i : Nat) (h : i < l.length) : l.getD i 0 = l[i] := by
  first
    | exact List.getD_eq_getElem l 0 h
    | exact List.getD_eq_getElem _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    | simp [h]

/-- Monotonicity of indexing into a sorted list. -/
theorem sorted_getD_le {l : List Int} (hs : l.Sorted (· ≤ ·)) {i j : Nat}
    (hij : i ≤ j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := Nat.lt_of_le_of_lt hij hj
  rw [getD_eq_getElem' l i hi, getD_eq_getElem' l j hj]
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · subst heq; exact le_refl _
  · first
      | exact List.pairwise_iff_getElem.mp hs i j hi hj hlt
      | exact (List.pairwise_iff_getElem.mp hs) i j hi hj hlt
      | exact List.Sorted.rel_get_of_lt hs hlt
      | exact hs.rel_get_of_lt hlt

/-! ## Characterisation of `medianLow` -/

theorem medianLow_odd (data : List Int) (h : data.length % 2 = 1) :
    medianLow data = (sortAsc data).getD (data.length / 2) 0 := by
  unfold medianLow; rw [if_pos h]

theorem medianLow_even (data : List Int) (h : data.length % 2 = 0) :
    medianLow data = (sortAsc data).getD (data.length / 2 - 1) 0 := by
  unfold medianLow; rw [if_neg (by omega)]

/-- Both branches agree with picking index `(n-1)/2` of the sorted list. -/
theorem medianLow_eq (data : List Int) (h : data ≠ []) :
    medianLow data = (sortAsc data).getD ((data.length - 1) / 2) 0 := by
  have hn : 0 < data.length := length_pos_of_ne_nil h
  unfold medianLow
  split
  · next hp =>
      have e : data.length / 2 = (data.length - 1) / 2 := by omega
      rw [e]
  · next hp =>
      have e : data.length / 2 - 1 = (data.length - 1) / 2 := by omega
      rw [e]

/-- The low median is one of the data points. -/
theorem medianLow_mem (data : List Int) (h : data ≠ []) : medianLow data ∈ data := by
  have hn : 0 < data.length := length_pos_of_ne_nil h
  have hlt : (data.length - 1) / 2 < (sortAsc data).length := by
    rw [sortAsc_length]; omega
  rw [medianLow_eq data h, getD_eq_getElem' _ _ hlt]
  have hm : (sortAsc data)[(data.length - 1) / 2] ∈ sortAsc data := by
    first
      | exact List.getElem_mem hlt
      | exact List.getElem_mem _ _ hlt
      | simp
  exact (sortAsc_perm data).mem_iff.mp hm

/-- Everything in the lower half of the sorted data is `≤` the low median. -/
theorem lower_le_medianLow (data : List Int) (h : data ≠ []) (j : Nat)
    (hj : j ≤ (data.length - 1) / 2) :
    (sortAsc data).getD j 0 ≤ medianLow data := by
  have hn : 0 < data.length := length_pos_of_ne_nil h
  have hlt : (data.length - 1) / 2 < (sortAsc data).length := by
    rw [sortAsc_length]; omega
  rw [medianLow_eq data h]
  exact sorted_getD_le (sortAsc_sorted data) hj hlt

/-- The low median is `≤` everything in the upper half of the sorted data. -/
theorem medianLow_le_upper (data : List Int) (h : data ≠ []) (j : Nat)
    (hj : (data.length - 1) / 2 ≤ j) (hjn : j < data.length) :
    medianLow data ≤ (sortAsc data).getD j 0 := by
  have hjl : j < (sortAsc data).length := by rw [sortAsc_length]; omega
  rw [medianLow_eq data h]
  exact sorted_getD_le (sortAsc_sorted data) hj hjl

theorem medianLow_singleton (x : Int) : medianLow [x] = x := by
  first
    | rfl
    | simp [medianLow, sortAsc, List.insertionSort, List.orderedInsert]

/-! ## Tests (mirroring the Python `check`) -/

example : medianLow [1, 3, 5] = 3 := by first | decide | native_decide
example : medianLow [1, 2, 3, 4, 5, 6, 9] = 4 := by first | decide | native_decide
example : medianLow [1, 3, 5, 7] = 3 := by first | decide | native_decide
example : medianLow [1, 2, 3, 4, 5, 6] = 3 := by first | decide | native_decide
example : medianLow [42] = 42 := by first | decide | native_decide
example : medianLow [10, 20] = 10 := by first | decide | native_decide
example : medianLow [9, 1, 6, 2, 5, 4, 3] = 4 := by first | decide | native_decide
example : medianLow [-5, -1, 0, 3, 7] = 0 := by first | decide | native_decide
example : medianLow [-10, -5, 5, 10] = -5 := by first | decide | native_decide

/-! ## Specification -/

/-- Pre-condition: the data is non-empty. -/
def Pre (data : List Int) : Prop := data ≠ []

/-- Post-condition: the result is a data point, it is the `(n-1)/2`-th smallest
element, and it splits the sorted data into a lower part `≤` it and an upper
part `≥` it. -/
def Post (data : List Int) (r : Int) : Prop :=
  r ∈ data ∧
  r = (sortAsc data).getD ((data.length - 1) / 2) 0 ∧
  (∀ j, j ≤ (data.length - 1) / 2 → (sortAsc data).getD j 0 ≤ r) ∧
  (∀ j, (data.length - 1) / 2 ≤ j → j < data.length → r ≤ (sortAsc data).getD j 0)

theorem correctness (data : List Int) : Pre data → Post data (medianLow data) := by
  intro h
  refine ⟨medianLow_mem data h, medianLow_eq data h, ?_, ?_⟩
  · intro j hj
    exact lower_le_medianLow data h j hj
  · intro j hj hjn
    exact medianLow_le_upper data h j hj hjn

end MedianLow
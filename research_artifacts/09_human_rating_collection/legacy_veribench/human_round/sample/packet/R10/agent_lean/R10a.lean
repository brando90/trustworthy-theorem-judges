import Mathlib

/-!
# `statistics.median_low`

A Lean 4 formalization of Python's `statistics.median_low`
(https://github.com/python/cpython/blob/main/Lib/statistics.py).

`median_low(data)` sorts the data and returns

* the middle element, when the number of data points is odd;
* the smaller of the two middle elements, when it is even.

Empty input raises `StatisticsError` in Python; here the function is total and
returns `none` on empty input (`some v` otherwise), which is how the error case
is modelled.

The file contains a functional implementation (`medianLow`), unit tests, the
pre-condition (`Pre`), the individual specification properties together with
their proofs, the post-condition (`Post_prop`), the correctness theorem
(`Pre → Post`), an imperative implementation (`medianLowImp`, written with
`Id.run do` and mutable state, sorting by insertion) and the theorem stating
that the two implementations agree.
-/

namespace StatisticsMedianLow

/-! ## Implementation -/

/-- Ascending sort of a list of integers (Python's `sorted`). -/
def sortAsc (l : List Int) : List Int :=
  l.mergeSort (fun a b => decide (a ≤ b))

/-- Python's `median_low`, made total: `none` models `StatisticsError`. -/
def medianLow (data : List Int) : Option Int :=
  if data = [] then
    none
  else
    let s := sortAsc data
    let n := s.length
    some (s.getD (if n % 2 = 1 then n / 2 else n / 2 - 1) 0)

/-! ### Basic facts about `sortAsc` -/

theorem sortAsc_perm (l : List Int) : (sortAsc l).Perm l :=
  List.mergeSort_perm l _

theorem sortAsc_length (l : List Int) : (sortAsc l).length = l.length :=
  (sortAsc_perm l).length_eq

theorem sortAsc_sorted (l : List Int) : (sortAsc l).Sorted (· ≤ ·) := by
  have h := List.sorted_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (by intro a b c; simp only [decide_eq_true_eq]; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  simpa [List.Sorted, sortAsc] using h

/-- The sorted permutation of a list is unique, so `sortAsc` computes it. -/
theorem sortAsc_eq_of_sorted {s l : List Int} (hs : s.Sorted (· ≤ ·)) (hp : s.Perm l) :
    sortAsc l = s :=
  List.eq_of_perm_of_sorted ((sortAsc_perm l).trans hp.symm) (sortAsc_sorted l) hs

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1. Odd number of elements (returns the middle value)
example : medianLow [1, 3, 5] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide

-- 2. Even number of elements (returns the smaller of the two middle values)
example : medianLow [1, 3, 5, 7] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6] = some 3 := by native_decide

-- 3. Single value
example : medianLow [42] = some 42 := by native_decide

-- 4. Two values
example : medianLow [10, 20] = some 10 := by native_decide

-- 5. Unsorted input
example : medianLow [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide

-- 6. Negative values
example : medianLow [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLow [-10, -5, 5, 10] = some (-5) := by native_decide

-- 7. Error case: empty input
example : medianLow [] = none := by native_decide

#eval medianLow [1, 3, 5]
#eval medianLow [1, 3, 5, 7]
#eval medianLow ([] : List Int)

/-! ## Pre-condition -/

/-- Python's `pre`: the data must be a non-empty list of numbers.  The "list of
numbers" part is carried by the type `List Int`, so only non-emptiness remains. -/
def Pre (data : List Int) : Prop := data ≠ []

instance (data : List Int) : Decidable (Pre data) := by
  unfold Pre; infer_instance

/-! ## Specification properties -/

/-- The low median exists exactly when the pre-condition holds. -/
def medianLow_isSome_prop (data : List Int) : Prop :=
  (medianLow data).isSome = true ↔ Pre data

/-- The error case: empty data has no median. -/
def medianLow_empty_prop : Prop :=
  medianLow ([] : List Int) = none

/-- The returned value is one of the data points. -/
def medianLow_mem_prop (data : List Int) : Prop :=
  ∀ v, medianLow data = some v → v ∈ data

/-- Characterization: for *any* sorted permutation `s` of the data, the result is
the element of `s` at index `(n-1)/2`, i.e. `s[n/2]` for odd `n` and
`s[n/2 - 1]` for even `n`. -/
def medianLow_sorted_prop (data : List Int) : Prop :=
  ∀ s : List Int, s.Sorted (· ≤ ·) → s.Perm data → Pre data →
    medianLow data = s[(data.length - 1) / 2]?

/-- Odd case: the middle element of the sorted data. -/
def medianLow_odd_prop (data : List Int) : Prop :=
  ∀ s : List Int, s.Sorted (· ≤ ·) → s.Perm data → data.length % 2 = 1 →
    medianLow data = s[data.length / 2]?

/-- Even case: the smaller of the two middle elements of the sorted data. -/
def medianLow_even_prop (data : List Int) : Prop :=
  ∀ s : List Int, s.Sorted (· ≤ ·) → s.Perm data → Pre data → data.length % 2 = 0 →
    medianLow data = s[data.length / 2 - 1]?

/-- The result only depends on the multiset of data points (Python sorts first). -/
def medianLow_perm_prop (data data' : List Int) : Prop :=
  data.Perm data' → medianLow data = medianLow data'

/-- At least `⌈n/2⌉` of the data points are `≤` the low median. -/
def medianLow_lower_count_prop (data : List Int) : Prop :=
  ∀ v, medianLow data = some v →
    (data.length + 1) / 2 ≤ data.countP (fun x => decide (x ≤ v))

/-- At least `n - (n-1)/2` (i.e. more than half) of the data points are `≥` the
low median. -/
def medianLow_upper_count_prop (data : List Int) : Prop :=
  ∀ v, medianLow data = some v →
    data.length - (data.length - 1) / 2 ≤ data.countP (fun x => decide (v ≤ x))

/-! ### Auxiliary lemmas -/

theorem length_pos_of_pre {data : List Int} (h : Pre data) : 0 < data.length := by
  cases data with
  | nil => exact absurd rfl h
  | cons a t => simp

/-- Unfolding lemma: on non-empty data the result is the `(n-1)/2`-th element of
the ascending sort. -/
theorem medianLow_eq (data : List Int) (h : data ≠ []) :
    medianLow data = (sortAsc data)[(data.length - 1) / 2]? := by
  have hlen : (sortAsc data).length = data.length := sortAsc_length data
  have hpos : 0 < data.length := length_pos_of_pre h
  have hidx : (data.length - 1) / 2 < (sortAsc data).length := by rw [hlen]; omega
  have hidxeq :
      (if (sortAsc data).length % 2 = 1 then (sortAsc data).length / 2
        else (sortAsc data).length / 2 - 1) = (data.length - 1) / 2 := by
    rw [hlen]; split <;> omega
  rw [medianLow, if_neg h]
  simp only [hidxeq]
  rw [List.getD_eq_getElem _ _ hidx, List.getElem?_eq_getElem hidx]

/-- In a sorted list, at least `k+1` entries are `≤ s[k]`. -/
theorem countP_le_getElem {s : List Int} (hs : s.Sorted (· ≤ ·)) {k : ℕ}
    (hk : k < s.length) :
    k + 1 ≤ s.countP (fun x => decide (x ≤ s[k])) := by
  have hall : ∀ a ∈ s.take (k + 1), (fun x => decide (x ≤ s[k])) a = true := by
    intro a ha
    rw [List.mem_iff_getElem] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hik : i ≤ k := by
      rw [List.length_take] at hi; omega
    simp only [decide_eq_true_eq, List.getElem_take]
    rcases lt_or_eq_of_le hik with hlt | heq
    · exact (List.pairwise_iff_getElem.mp hs) i k (by omega) hk hlt
    · subst heq; exact le_refl _
  have h1 : (s.take (k + 1)).countP (fun x => decide (x ≤ s[k])) = (s.take (k + 1)).length :=
    List.countP_eq_length.mpr hall
  have h2 : (s.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
  have h3 := (List.take_sublist (k + 1) s).countP_le (p := fun x => decide (x ≤ s[k]))
  omega

/-- In a sorted list, at least `n - k` entries are `≥ s[k]`. -/
theorem countP_ge_getElem {s : List Int} (hs : s.Sorted (· ≤ ·)) {k : ℕ}
    (hk : k < s.length) :
    s.length - k ≤ s.countP (fun x => decide (s[k] ≤ x)) := by
  have hall : ∀ a ∈ s.drop k, (fun x => decide (s[k] ≤ x)) a = true := by
    intro a ha
    rw [List.mem_iff_getElem] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hik : k + i < s.length := by
      rw [List.length_drop] at hi; omega
    simp only [decide_eq_true_eq, List.getElem_drop]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp
    · exact (List.pairwise_iff_getElem.mp hs) k (k + i) hk hik (by omega)
  have h1 : (s.drop k).countP (fun x => decide (s[k] ≤ x)) = (s.drop k).length :=
    List.countP_eq_length.mpr hall
  have h2 : (s.drop k).length = s.length - k := List.length_drop
  have h3 := (List.drop_sublist k s).countP_le (p := fun x => decide (s[k] ≤ x))
  omega

/-! ### Theorems -/

theorem medianLow_isSome_thm (data : List Int) : medianLow_isSome_prop data := by
  unfold medianLow_isSome_prop Pre
  constructor
  · intro h hnil
    rw [medianLow, if_pos hnil] at h
    simp at h
  · intro h
    rw [medianLow, if_neg h]
    rfl

theorem medianLow_empty_thm : medianLow_empty_prop := by
  unfold medianLow_empty_prop medianLow
  simp

theorem medianLow_mem_thm (data : List Int) : medianLow_mem_prop data := by
  intro v hv
  by_cases h : data = []
  · rw [h, medianLow] at hv; simp at hv
  · rw [medianLow_eq data h] at hv
    have hlen : (sortAsc data).length = data.length := sortAsc_length data
    have hpos : 0 < data.length := length_pos_of_pre h
    have hidx : (data.length - 1) / 2 < (sortAsc data).length := by rw [hlen]; omega
    rw [List.getElem?_eq_getElem hidx] at hv
    have hmem : v ∈ sortAsc data := by
      rw [← Option.some_inj.mp hv]
      exact List.getElem_mem hidx
    exact (sortAsc_perm data).mem_iff.mp hmem

theorem medianLow_sorted_thm (data : List Int) : medianLow_sorted_prop data := by
  intro s hs hp hpre
  rw [medianLow_eq data hpre, sortAsc_eq_of_sorted hs hp]

theorem medianLow_odd_thm (data : List Int) : medianLow_odd_prop data := by
  intro s hs hp hodd
  have hne : data ≠ [] := by
    intro h; rw [h] at hodd; simp at hodd
  have : (data.length - 1) / 2 = data.length / 2 := by omega
  rw [medianLow_eq data hne, sortAsc_eq_of_sorted hs hp, this]

theorem medianLow_even_thm (data : List Int) : medianLow_even_prop data := by
  intro s hs hp hpre heven
  have hpos : 0 < data.length := length_pos_of_pre hpre
  have : (data.length - 1) / 2 = data.length / 2 - 1 := by omega
  rw [medianLow_eq data hpre, sortAsc_eq_of_sorted hs hp, this]

theorem medianLow_perm_thm (data data' : List Int) : medianLow_perm_prop data data' := by
  intro hp
  by_cases h : data = []
  · have h' : data' = [] := by
      rw [h] at hp; exact hp.symm.eq_nil
    rw [h, h']
  · have h' : data' ≠ [] := by
      intro hnil
      exact h (by rw [hnil] at hp; exact hp.eq_nil)
    rw [medianLow_eq data h, medianLow_eq data' h', hp.length_eq]
    have : sortAsc data = sortAsc data' :=
      sortAsc_eq_of_sorted (sortAsc_sorted data') ((sortAsc_perm data').trans hp.symm)
    rw [this]

theorem medianLow_lower_count_thm (data : List Int) : medianLow_lower_count_prop data := by
  intro v hv
  by_cases h : data = []
  · rw [h, medianLow] at hv; simp at hv
  · have hlen : (sortAsc data).length = data.length := sortAsc_length data
    have hpos : 0 < data.length := length_pos_of_pre h
    have hidx : (data.length - 1) / 2 < (sortAsc data).length := by rw [hlen]; omega
    rw [medianLow_eq data h, List.getElem?_eq_getElem hidx] at hv
    have hveq : v = (sortAsc data)[(data.length - 1) / 2] := (Option.some_inj.mp hv).symm
    have hcount := countP_le_getElem (sortAsc_sorted data) hidx
    rw [← hveq] at hcount
    have hperm : (sortAsc data).countP (fun x => decide (x ≤ v))
        = data.countP (fun x => decide (x ≤ v)) := (sortAsc_perm data).countP_eq _
    omega

theorem medianLow_upper_count_thm (data : List Int) : medianLow_upper_count_prop data := by
  intro v hv
  by_cases h : data = []
  · rw [h, medianLow] at hv; simp at hv
  · have hlen : (sortAsc data).length = data.length := sortAsc_length data
    have hpos : 0 < data.length := length_pos_of_pre h
    have hidx : (data.length - 1) / 2 < (sortAsc data).length := by rw [hlen]; omega
    rw [medianLow_eq data h, List.getElem?_eq_getElem hidx] at hv
    have hveq : v = (sortAsc data)[(data.length - 1) / 2] := (Option.some_inj.mp hv).symm
    have hcount := countP_ge_getElem (sortAsc_sorted data) hidx
    rw [← hveq, hlen] at hcount
    have hperm : (sortAsc data).countP (fun x => decide (v ≤ x))
        = data.countP (fun x => decide (v ≤ x)) := (sortAsc_perm data).countP_eq _
    omega

/-! ## Post-condition and correctness -/

/-- The full post-condition: everything the Python function guarantees. -/
def Post_prop (data : List Int) : Prop :=
  medianLow_isSome_prop data ∧
  medianLow_mem_prop data ∧
  medianLow_sorted_prop data ∧
  medianLow_odd_prop data ∧
  medianLow_even_prop data ∧
  medianLow_lower_count_prop data ∧
  medianLow_upper_count_prop data

theorem correctness (data : List Int) (_h : Pre data) : Post_prop data :=
  ⟨medianLow_isSome_thm data, medianLow_mem_thm data, medianLow_sorted_thm data,
   medianLow_odd_thm data, medianLow_even_thm data, medianLow_lower_count_thm data,
   medianLow_upper_count_thm data⟩

/-! ## Imperative implementation -/

/-- Insertion sort written imperatively with a mutable accumulator. -/
def insertSortImp (data : List Int) : List Int := Id.run do
  let mut s : List Int := []
  for x in data do
    s := List.orderedInsert (· ≤ ·) x s
  return s

/-- Imperative version of `medianLow`. -/
def medianLowImp (data : List Int) : Option Int := Id.run do
  if data = [] then
    return none
  let s := insertSortImp data
  let n := s.length
  let mut idx := 0
  if n % 2 = 1 then
    idx := n / 2
  else
    idx := n / 2 - 1
  return some (s.getD idx 0)

/-! ### Imperative tests -/

example : medianLowImp [1, 3, 5] = some 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : medianLowImp [1, 3, 5, 7] = some 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : medianLowImp [42] = some 42 := by native_decide
example : medianLowImp [10, 20] = some 10 := by native_decide
example : medianLowImp [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : medianLowImp [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLowImp [-10, -5, 5, 10] = some (-5) := by native_decide
example : medianLowImp [] = none := by native_decide

#eval medianLowImp [1, 3, 5]
#eval medianLowImp [1, 3, 5, 7]
#eval medianLowImp ([] : List Int)

/-! ### The imperative sort computes the ascending sort -/

theorem insertSortImp_eq_foldl (data : List Int) :
    insertSortImp data =
      data.foldl (fun acc x => List.orderedInsert (· ≤ ·) x acc) [] := by
  simp [insertSortImp, Id.run]
  rfl

theorem foldl_orderedInsert_sorted (l acc : List Int) (h : acc.Sorted (· ≤ ·)) :
    (l.foldl (fun acc x => List.orderedInsert (· ≤ ·) x acc) acc).Sorted (· ≤ ·) := by
  induction l generalizing acc with
  | nil => simpa using h
  | cons a t ih =>
      simpa using ih (List.orderedInsert (· ≤ ·) a acc) (h.orderedInsert a acc)

theorem foldl_orderedInsert_perm (l acc : List Int) :
    (l.foldl (fun acc x => List.orderedInsert (· ≤ ·) x acc) acc).Perm (l ++ acc) := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
      have h1 := ih (List.orderedInsert (· ≤ ·) a acc)
      have h2 : (t ++ List.orderedInsert (· ≤ ·) a acc).Perm (t ++ a :: acc) :=
        List.Perm.append_left t (List.perm_orderedInsert _ a acc)
      have h3 : (t ++ a :: acc).Perm (a :: (t ++ acc)) := List.perm_middle
      simpa using (h1.trans h2).trans h3

theorem insertSortImp_eq_sortAsc (data : List Int) : insertSortImp data = sortAsc data := by
  rw [insertSortImp_eq_foldl]
  refine (sortAsc_eq_of_sorted (foldl_orderedInsert_sorted data [] (by simp)) ?_).symm
  simpa using foldl_orderedInsert_perm data []

/-! ## Equivalence of the two implementations -/

theorem medianLow_eq_medianLowImp (data : List Int) : medianLow data = medianLowImp data := by
  by_cases h : data = []
  · subst h; rfl
  · rw [medianLow, medianLowImp, if_neg h]
    simp only [Id.run, insertSortImp_eq_sortAsc, bind_pure_comp, map_pure, pure_bind]
    split <;> rfl

end StatisticsMedianLow

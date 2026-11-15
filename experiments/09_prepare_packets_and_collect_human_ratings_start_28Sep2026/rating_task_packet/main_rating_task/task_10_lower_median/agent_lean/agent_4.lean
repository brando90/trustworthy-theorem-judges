import Mathlib
import Plausible

/-!
# Low median (`statistics.median_low`)

Lean 4 formalization of Python's `statistics.median_low`
(https://github.com/python/cpython/blob/main/Lib/statistics.py, `median_low`).

Sort the data and return the element at index `(n - 1) // 2`:
* odd `n`: the middle value (`sorted[n // 2]`);
* even `n`: the smaller of the two middle values (`sorted[n // 2 - 1]`).

Empty input raises `StatisticsError` ("no median for empty data").

The algorithm is an order statistic. Theorems are stated for an arbitrary
`LinearOrder`, which covers `Int`, `Nat`, `Rat`, and Mathlib's `Real` order.
Executable tests use `Int`, matching the reference unit tests. `Real`
decidable order is noncomputable, so there is no separate executable `Real`
PBT; the generic theorems are exactly the `Real` instances of each property.
-/

namespace «28_statistics_median_low»

/-- Python `StatisticsError` for an empty sample. -/
inductive StatisticsError where
  | noMedianForEmptyData
  deriving DecidableEq, Repr, BEq

/-- Success value or `StatisticsError`, mirroring Python's exception. -/
inductive StatsResult (α : Type) where
  | ok : α → StatsResult α
  | error : StatisticsError → StatsResult α
  deriving DecidableEq, Repr, BEq

/-- Message carried by the empty-data error. -/
def statisticsErrorMessage : StatisticsError → String
  | .noMedianForEmptyData => "no median for empty data"

/-- Index `(n - 1) // 2` of the low median in a sorted list. -/
def idx (n : Nat) : Nat := (n - 1) / 2

theorem idx_lt {n : Nat} (hn : 0 < n) : idx n < n := by
  unfold idx
  omega

theorem idx_eq_div_of_odd {n : Nat} (h : n % 2 = 1) : idx n = n / 2 := by
  unfold idx
  omega

theorem idx_eq_div_sub_of_even {n : Nat} (h : n % 2 = 0) (hn : 0 < n) :
    idx n = n / 2 - 1 := by
  unfold idx
  omega

/-- Boolean `≤`, the comparison passed to `List.mergeSort` / Python `sorted`. -/
def leBool {α : Type} [LE α] [DecidableLE α] (a b : α) : Bool :=
  decide (a ≤ b)

/-- Ascending sort, the counterpart of Python `sorted(data)`. -/
def sortedData {α : Type} [LinearOrder α] (data : List α) : List α :=
  data.mergeSort (leBool (α := α))

theorem sortedData_perm {α : Type} [LinearOrder α] (data : List α) :
    List.Perm (sortedData data) data := by
  simpa [sortedData] using List.mergeSort_perm data (leBool (α := α))

theorem sortedData_length {α : Type} [LinearOrder α] (data : List α) :
    (sortedData data).length = data.length := by
  simp [sortedData]

theorem sortedData_pairwise {α : Type} [LinearOrder α] (data : List α) :
    (sortedData data).Pairwise (fun a b => leBool a b = true) := by
  have h := List.sorted_mergeSort (le := leBool (α := α))
    (trans := by
      intro a b c hab hbc
      simp only [leBool, decide_eq_true_eq] at hab hbc
      simpa [leBool] using le_trans hab hbc)
    (total := by
      intro a b
      cases le_total a b with
      | inl hab => simp [leBool, hab]
      | inr hba => simp [leBool, hba])
    data
  simpa using h

theorem sortedData_sorted {α : Type} [LinearOrder α] (data : List α) :
    (sortedData data).Sorted (· ≤ ·) := by
  exact (sortedData_pairwise data).imp (by intro a b hab; simpa [leBool] using hab)

/--
Low median of a list that is already sorted, following Python's branch:
`data[n // 2]` if `n` is odd, else `data[n // 2 - 1]`.
-/
def medianFromSorted {α : Type} [LinearOrder α] (sorted : List α) : StatsResult α :=
  let n := sorted.length
  if h : n = 0 then
    .error .noMedianForEmptyData
  else if hodd : n % 2 = 1 then
    .ok (sorted[n / 2]'(by omega))
  else
    .ok (sorted[n / 2 - 1]'(by omega))

/--
`median_low`: return the low median of numeric data.

When the number of data points is odd, the middle value is returned.
When it is even, the smaller of the two middle values is returned.
Empty data yields `StatisticsError.noMedianForEmptyData`.
-/
def medianLow {α : Type} [LinearOrder α] (data : List α) : StatsResult α :=
  medianFromSorted (sortedData data)

/--
`benchmark_median_low`. The Python precondition (non-empty list/tuple of
numbers) is the non-emptiness check below; the element type is a linear order.
-/
def benchmarkMedianLow {α : Type} [LinearOrder α] (data : List α) : StatsResult α :=
  if data.isEmpty then
    .error .noMedianForEmptyData
  else
    medianLow data

/-! ## Unit tests -/

example : medianLow ([1, 3, 5] : List Int) = .ok 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6, 9] : List Int) = .ok 4 := by native_decide
example : medianLow ([1, 3, 5, 7] : List Int) = .ok 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6] : List Int) = .ok 3 := by native_decide
example : medianLow ([42] : List Int) = .ok 42 := by native_decide
example : medianLow ([10, 20] : List Int) = .ok 10 := by native_decide
example : medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) = .ok 4 := by native_decide
example : medianLow ([-5, -1, 0, 3, 7] : List Int) = .ok 0 := by native_decide
example : medianLow ([-10, -5, 5, 10] : List Int) = .ok (-5) := by native_decide
example : medianLow ([] : List Int) = .error .noMedianForEmptyData := by native_decide
example : benchmarkMedianLow ([] : List Int) = .error .noMedianForEmptyData := by native_decide
example : benchmarkMedianLow ([1, 3, 5] : List Int) = .ok 3 := by native_decide

#eval medianLow ([1, 3, 5] : List Int)
#eval medianLow ([1, 3, 5, 7] : List Int)
#eval medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int)
#eval medianLow ([-10, -5, 5, 10] : List Int)
#eval medianLow ([] : List Int)
#eval statisticsErrorMessage StatisticsError.noMedianForEmptyData
#eval medianLow ([(1 : Rat) / 2, 5 / 2, 3 / 2])

/-! ## Pre-condition -/

/-- Non-empty input. Element type already restricts to ordered numbers. -/
def Pre {α : Type} (data : List α) : Prop :=
  data ≠ []

theorem length_pos_of_pre {α : Type} {data : List α} (h : Pre data) : 0 < data.length := by
  cases data with
  | nil => exact absurd rfl h
  | cons _ _ => simp


/-! ## Sorting and indexing lemmas -/

theorem medianFromSorted_eq_idx {α : Type} [LinearOrder α] (sorted : List α)
    (h : 0 < sorted.length) :
    medianFromSorted sorted = .ok (sorted[idx sorted.length]'(idx_lt h)) := by
  unfold medianFromSorted
  have hn : sorted.length ≠ 0 := Nat.ne_of_gt h
  by_cases hodd : sorted.length % 2 = 1
  · simp [hn, hodd, idx_eq_div_of_odd hodd]
  · have heven : sorted.length % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one sorted.length with h0 | h1
      · exact h0
      · exact absurd h1 hodd
    simp [hn, hodd, idx_eq_div_sub_of_even heven h]

theorem drop_index_lt {α : Type} {s : List α} {i j : Nat}
    (_hi : i < s.length) (hj : j < (s.drop i).length) : i + j < s.length := by
  have hj' : j < s.length - i := by simpa [List.length_drop] using hj
  exact Nat.add_lt_of_lt_sub' hj'

theorem countP_lt_of_sorted {α : Type} [LinearOrder α] (s : List α)
    (hs : s.Sorted (· ≤ ·)) {i : Nat} (hi : i < s.length) :
    s.countP (fun x => decide (x < s[i])) ≤ i := by
  have hdrop : (s.drop i).countP (fun x => decide (x < s[i])) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    rcases List.mem_iff_getElem.mp ha with ⟨j, hj, rfl⟩
    have hij : i + j < s.length := drop_index_lt hi hj
    rw [List.getElem_drop]
    simp only [decide_eq_true_eq]
    intro hlt
    have hle : s[i] ≤ s[i + j] := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · simp
      · exact (List.pairwise_iff_getElem.mp hs) i (i + j) hi hij
          (Nat.lt_add_of_pos_right hpos)
    exact not_lt_of_ge hle hlt
  have htake_le : (s.take i).countP (fun x => decide (x < s[i])) ≤ i :=
    le_trans (List.countP_le_length (l := s.take i) (p := fun x => decide (x < s[i])))
      (by simp [List.length_take])
  have happ :
      s.countP (fun x => decide (x < s[i])) =
        (s.take i).countP (fun x => decide (x < s[i])) +
          (s.drop i).countP (fun x => decide (x < s[i])) := by
    simpa [List.take_append_drop] using
      (List.countP_append (l₁ := s.take i) (l₂ := s.drop i)
        (p := fun x => decide (x < s[i])))
  omega

theorem countP_le_of_sorted {α : Type} [LinearOrder α] (s : List α)
    (hs : s.Sorted (· ≤ ·)) {i : Nat} (hi : i < s.length) :
    i + 1 ≤ s.countP (fun x => decide (x ≤ s[i])) := by
  have hlen : (s.take (i + 1)).length = i + 1 := by
    simp [List.length_take]
    omega
  have htake_len : (s.take (i + 1)).countP (fun x => decide (x ≤ s[i])) =
      (s.take (i + 1)).length := by
    rw [List.countP_eq_length]
    intro a ha
    rcases List.mem_iff_getElem.mp ha with ⟨j, hj, rfl⟩
    have hj' : j < i + 1 := by
      have := hj
      simp [List.length_take] at this
      omega
    have hjlen : j < s.length := by omega
    rw [List.getElem_take]
    simp only [decide_eq_true_eq]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hji | rfl
    · exact (List.pairwise_iff_getElem.mp hs) j i hjlen hi hji
    · exact le_rfl
  have htake : (s.take (i + 1)).countP (fun x => decide (x ≤ s[i])) = i + 1 := by
    rw [htake_len, hlen]
  have hprefix :
      (s.take (i + 1)).countP (fun x => decide (x ≤ s[i])) ≤
        s.countP (fun x => decide (x ≤ s[i])) :=
    (List.take_prefix (i + 1) s).countP_le
  omega

theorem countP_le_split_drop {α : Type} [LinearOrder α] (s : List α)
    (hs : s.Sorted (· ≤ ·)) {k : Nat} (hk : k < s.length) {m : α} (hgt : m < s[k]) :
    s.countP (fun x => decide (x ≤ m)) ≤ k := by
  have hdrop : (s.drop k).countP (fun x => decide (x ≤ m)) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    rcases List.mem_iff_getElem.mp ha with ⟨j, hj, rfl⟩
    have hij : k + j < s.length := drop_index_lt hk hj
    rw [List.getElem_drop]
    simp only [decide_eq_true_eq]
    intro hxm
    have hge : s[k] ≤ s[k + j] := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · simp
      · exact (List.pairwise_iff_getElem.mp hs) k (k + j) hk hij
          (Nat.lt_add_of_pos_right hpos)
    exact not_lt_of_ge (le_trans hge hxm) hgt
  have htake : (s.take k).countP (fun x => decide (x ≤ m)) ≤ k :=
    le_trans (List.countP_le_length (l := s.take k) (p := fun x => decide (x ≤ m)))
      (by simp [List.length_take])
  have happ :
      s.countP (fun x => decide (x ≤ m)) =
        (s.take k).countP (fun x => decide (x ≤ m)) +
          (s.drop k).countP (fun x => decide (x ≤ m)) := by
    simpa [List.take_append_drop] using
      (List.countP_append (l₁ := s.take k) (l₂ := s.drop k)
        (p := fun x => decide (x ≤ m)))
  omega

theorem countP_lt_take_succ {α : Type} [LinearOrder α] (s : List α)
    (hs : s.Sorted (· ≤ ·)) {k : Nat} (hk : k < s.length) {m : α} (hlt : s[k] < m) :
    k + 1 ≤ s.countP (fun x => decide (x < m)) := by
  have hlen : (s.take (k + 1)).length = k + 1 := by
    simp [List.length_take]
    omega
  have htake_len : (s.take (k + 1)).countP (fun x => decide (x < m)) =
      (s.take (k + 1)).length := by
    rw [List.countP_eq_length]
    intro a ha
    rcases List.mem_iff_getElem.mp ha with ⟨j, hj, rfl⟩
    have hj' : j < k + 1 := by
      have := hj
      simp [List.length_take] at this
      omega
    have hjlen : j < s.length := by omega
    rw [List.getElem_take]
    simp only [decide_eq_true_eq]
    have haj : s[j] ≤ s[k] := by
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hji | rfl
      · exact (List.pairwise_iff_getElem.mp hs) j k hjlen hk hji
      · exact le_rfl
    exact lt_of_le_of_lt haj hlt
  have htake : (s.take (k + 1)).countP (fun x => decide (x < m)) = k + 1 := by
    rw [htake_len, hlen]
  have hprefix :=
    (List.take_prefix (k + 1) s).countP_le (p := fun x => decide (x < m))
  omega

/-! ## Properties -/

/-- Empty data has no median. -/
def empty_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  data = [] → medianLow data = .error .noMedianForEmptyData

theorem empty_thm {α : Type} [LinearOrder α] (data : List α) : empty_prop data := by
  intro h
  subst h
  simp [medianLow, sortedData, medianFromSorted]

/-- On non-empty data the result is `sorted[(n - 1) // 2]`. -/
def index_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  Pre data →
    ∃ m, medianLow data = .ok m ∧ (sortedData data)[idx data.length]? = some m

theorem index_thm {α : Type} [LinearOrder α] (data : List α) : index_prop data := by
  intro h
  have hpos : 0 < (sortedData data).length := by
    simpa [sortedData_length] using length_pos_of_pre h
  refine ⟨(sortedData data)[idx data.length]'(by simpa [sortedData_length] using idx_lt (length_pos_of_pre h)), ?_, ?_⟩
  · simpa [medianLow, sortedData_length] using medianFromSorted_eq_idx (sortedData data) hpos
  · rw [List.getElem?_eq_getElem]

/-- Odd length: Python returns `sorted[n // 2]`. -/
def odd_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  data.length % 2 = 1 →
    ∃ m, medianLow data = .ok m ∧ (sortedData data)[data.length / 2]? = some m

theorem odd_thm {α : Type} [LinearOrder α] (data : List α) : odd_prop data := by
  intro hodd
  have hpos : 0 < data.length := by omega
  have hpos' : 0 < (sortedData data).length := by simpa [sortedData_length] using hpos
  have hidx := idx_eq_div_of_odd hodd
  have hlt : data.length / 2 < (sortedData data).length := by
    rw [sortedData_length, ← hidx]
    exact idx_lt hpos
  refine ⟨(sortedData data)[data.length / 2]'hlt, ?_, ?_⟩
  · simpa [medianLow, sortedData_length, hidx] using
      medianFromSorted_eq_idx (sortedData data) hpos'
  · rw [List.getElem?_eq_getElem]

/-- Even positive length: Python returns `sorted[n // 2 - 1]`. -/
def even_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  Pre data → data.length % 2 = 0 →
    ∃ m, medianLow data = .ok m ∧ (sortedData data)[data.length / 2 - 1]? = some m

theorem even_thm {α : Type} [LinearOrder α] (data : List α) : even_prop data := by
  intro hpre heven
  have hpos := length_pos_of_pre hpre
  have hpos' : 0 < (sortedData data).length := by simpa [sortedData_length] using hpos
  have hidx := idx_eq_div_sub_of_even heven hpos
  have hlt : data.length / 2 - 1 < (sortedData data).length := by
    rw [sortedData_length, ← hidx]
    exact idx_lt hpos
  refine ⟨(sortedData data)[data.length / 2 - 1]'hlt, ?_, ?_⟩
  · simpa [medianLow, sortedData_length, hidx] using
      medianFromSorted_eq_idx (sortedData data) hpos'
  · rw [List.getElem?_eq_getElem]


/-- The low median belongs to the input. -/
def mem_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  ∀ m, medianLow data = .ok m → m ∈ data

theorem mem_thm {α : Type} [LinearOrder α] (data : List α) : mem_prop data := by
  intro m hm
  by_cases hpre : Pre data
  · obtain ⟨m', hm', hget⟩ := index_thm data hpre
    have heq : m' = m := by
      rw [hm'] at hm
      cases hm
      rfl
    have hmem_sorted : m' ∈ sortedData data := by
      rw [List.mem_iff_getElem]
      refine ⟨idx data.length, ?_, ?_⟩
      · simpa [sortedData_length] using idx_lt (length_pos_of_pre hpre)
      · have hsome := hget
        rw [List.getElem?_eq_getElem] at hsome
        injection hsome
    rw [← heq]
    exact (sortedData_perm data).mem_iff.mp hmem_sorted
  · have hempty : data = [] := by simpa [Pre] using hpre
    rw [empty_thm data hempty] at hm
    cases hm


/-- At most `(n - 1) // 2` inputs are strictly smaller than the low median. -/
def count_lt_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  ∀ m, medianLow data = .ok m →
    data.countP (fun x => decide (x < m)) ≤ idx data.length

theorem count_lt_thm {α : Type} [LinearOrder α] (data : List α) : count_lt_prop data := by
  intro m hm
  have hpre : Pre data := by
    intro hempty
    rw [empty_thm data hempty] at hm
    cases hm
  obtain ⟨m', hm', hget⟩ := index_thm data hpre
  have heq : m' = m := by rw [hm'] at hm; cases hm; rfl
  have hi : idx data.length < (sortedData data).length := by
    simpa [sortedData_length] using idx_lt (length_pos_of_pre hpre)
  have hcount := countP_lt_of_sorted (sortedData data) (sortedData_sorted data) hi
  have hget' : (sortedData data)[idx data.length] = m' := by
    have hsome := hget
    rw [List.getElem?_eq_getElem] at hsome
    injection hsome with h
  have hperm := (sortedData_perm data).countP_eq (fun x => decide (x < m'))
  have hbound : data.countP (fun x => decide (x < m')) ≤ idx data.length := by
    simpa [hget', sortedData_length, hperm] using hcount
  simpa [heq] using hbound

/-- At least `(n - 1) // 2 + 1` inputs are `≤` the low median. -/
def count_le_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  ∀ m, medianLow data = .ok m →
    idx data.length + 1 ≤ data.countP (fun x => decide (x ≤ m))

theorem count_le_thm {α : Type} [LinearOrder α] (data : List α) : count_le_prop data := by
  intro m hm
  have hpre : Pre data := by
    intro hempty
    rw [empty_thm data hempty] at hm
    cases hm
  obtain ⟨m', hm', hget⟩ := index_thm data hpre
  have heq : m' = m := by rw [hm'] at hm; cases hm; rfl
  have hi : idx data.length < (sortedData data).length := by
    simpa [sortedData_length] using idx_lt (length_pos_of_pre hpre)
  have hcount := countP_le_of_sorted (sortedData data) (sortedData_sorted data) hi
  have hget' : (sortedData data)[idx data.length] = m' := by
    have hsome := hget
    rw [List.getElem?_eq_getElem] at hsome
    injection hsome with h
  have hperm := (sortedData_perm data).countP_eq (fun x => decide (x ≤ m'))
  have hbound : idx data.length + 1 ≤ data.countP (fun x => decide (x ≤ m')) := by
    simpa [hget', sortedData_length, hperm] using hcount
  simpa [heq] using hbound

/-- Even case: the returned value is `≤` the upper middle element. -/
def two_middle_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  Pre data → data.length % 2 = 0 →
    ∀ m hi, medianLow data = .ok m →
      (sortedData data)[data.length / 2]? = some hi → m ≤ hi

theorem two_middle_thm {α : Type} [LinearOrder α] (data : List α) : two_middle_prop data := by
  intro hpre heven m hi hm hhi
  have hpos := length_pos_of_pre hpre
  have hpos' : 0 < (sortedData data).length := by simpa [sortedData_length] using hpos
  have hfrom := medianFromSorted_eq_idx (sortedData data) hpos'
  have hidx := idx_eq_div_sub_of_even heven hpos
  have hm' : m = (sortedData data)[idx data.length]'(by simpa [sortedData_length] using idx_lt hpos) := by
    have hok : medianLow data =
        .ok ((sortedData data)[idx data.length]'(by simpa [sortedData_length] using idx_lt hpos)) := by
      simpa [medianLow, sortedData_length] using hfrom
    rw [hok] at hm
    cases hm
    rfl
  have hdiv : data.length / 2 < data.length := by omega
  have hlt : idx data.length < data.length / 2 := by rw [hidx]; omega
  have hlen := sortedData_length data
  have hs := sortedData_sorted data
  have hle := (List.pairwise_iff_getElem.mp hs) (idx data.length) (data.length / 2)
    (by simpa [hlen] using idx_lt hpos)
    (by simpa [hlen] using hdiv)
    (by simpa [hlen] using hlt)
  have hhi' : hi = (sortedData data)[data.length / 2]'(by simpa [hlen] using hdiv) := by
    have := hhi
    rw [List.getElem?_eq_getElem] at this
    injection this with h
    exact h.symm
  simpa [hm', hhi'] using hle

/-- Permuting the input does not change the low median. -/
def perm_prop {α : Type} [LinearOrder α] (data₁ data₂ : List α) : Prop :=
  List.Perm data₁ data₂ → medianLow data₁ = medianLow data₂

theorem perm_thm {α : Type} [LinearOrder α] (data₁ data₂ : List α) : perm_prop data₁ data₂ := by
  intro h
  have hs : sortedData data₁ = sortedData data₂ := by
    apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
    · exact (sortedData_perm data₁).trans (h.trans (sortedData_perm data₂).symm)
    · exact sortedData_sorted data₁
    · exact sortedData_sorted data₂
  simp [medianLow, hs]

/-- A one-element sample is its own low median. -/
def singleton_prop {α : Type} [LinearOrder α] (x : α) : Prop :=
  medianLow [x] = .ok x

theorem singleton_thm {α : Type} [LinearOrder α] (x : α) : singleton_prop x := by
  simp [singleton_prop, medianLow, sortedData, medianFromSorted, List.mergeSort_singleton]

theorem sortedData_of_sorted {α : Type} [LinearOrder α] {data : List α}
    (hs : data.Sorted (· ≤ ·)) : sortedData data = data := by
  have hp : data.Pairwise (fun a b => leBool a b = true) :=
    hs.imp (by intro a b hab; simpa [leBool] using hab)
  simpa [sortedData] using
    List.mergeSort_of_sorted (le := leBool (α := α)) (by simpa using hp)

/-- Sorting an already sorted list does not change the low median. -/
def sorted_input_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  data.Sorted (· ≤ ·) → medianLow data = medianFromSorted data

theorem sorted_input_thm {α : Type} [LinearOrder α] (data : List α) :
    sorted_input_prop data := by
  intro hs
  simp [medianLow, sortedData_of_sorted hs]

/--
Counting characterization: on non-empty data, `m` is the low median if at most
`(n - 1) // 2` elements are `< m` and at least `(n - 1) // 2 + 1` elements are `≤ m`.
-/
def unique_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  Pre data → ∀ m,
    data.countP (fun x => decide (x < m)) ≤ idx data.length →
    idx data.length + 1 ≤ data.countP (fun x => decide (x ≤ m)) →
    medianLow data = .ok m

theorem unique_thm {α : Type} [LinearOrder α] (data : List α) : unique_prop data := by
  intro hpre m hlt hle
  let s := sortedData data
  let k := idx data.length
  have hs : s.Sorted (· ≤ ·) := sortedData_sorted data
  have hperm : List.Perm s data := sortedData_perm data
  have hlen : s.length = data.length := sortedData_length data
  have hk : k < s.length := by simpa [s, k, hlen] using idx_lt (length_pos_of_pre hpre)
  have hlt_s : s.countP (fun x => decide (x < m)) ≤ k := by
    simpa [s, k, hperm.countP_eq] using hlt
  have hle_s : k + 1 ≤ s.countP (fun x => decide (x ≤ m)) := by
    simpa [s, k, hperm.countP_eq] using hle
  have hsk_le : s[k] ≤ m := by
    by_contra hnot
    have hbad := countP_le_split_drop s hs hk (lt_of_not_ge hnot)
    omega
  have hm_le : m ≤ s[k] := by
    by_contra hnot
    have hbad := countP_lt_take_succ s hs hk (lt_of_not_ge hnot)
    omega
  have hmeq : s[k] = m := le_antisymm hsk_le hm_le
  have hpos : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hfrom := medianFromSorted_eq_idx s hpos
  simp [medianLow, s, k, hlen, hfrom, hmeq]

/-- The implementation follows Python's empty / odd / even control flow. -/
def python_branch_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  let n := data.length
  let sorted := sortedData data
  medianLow data =
    if n = 0 then .error .noMedianForEmptyData
    else if n % 2 = 1 then
      match sorted[n / 2]? with
      | some v => .ok v
      | none => .error .noMedianForEmptyData
    else
      match sorted[n / 2 - 1]? with
      | some v => .ok v
      | none => .error .noMedianForEmptyData

theorem python_branch_thm {α : Type} [LinearOrder α] (data : List α) :
    python_branch_prop data := by
  unfold python_branch_prop
  by_cases hempty : data.length = 0
  · have hdata : data = [] := by cases data <;> simp_all
    subst hdata
    simp [medianLow, sortedData, medianFromSorted]
  · have hpre : Pre data := by
      intro hnil
      apply hempty
      simp [hnil]
    by_cases hodd : data.length % 2 = 1
    · obtain ⟨m, hm, hget⟩ := odd_thm data hodd
      simp [hempty, hodd, hm, hget]
    · have heven : data.length % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one data.length with h0 | h1
        · exact h0
        · exact absurd h1 hodd
      obtain ⟨m, hm, hget⟩ := even_thm data hpre heven
      simp [hempty, hodd, hm, hget]

/-- `benchmark_median_low` and `median_low` agree, including on empty input. -/
def benchmark_agrees_prop {α : Type} [LinearOrder α] (data : List α) : Prop :=
  benchmarkMedianLow data = medianLow data

theorem benchmark_agrees_thm {α : Type} [LinearOrder α] (data : List α) :
    benchmark_agrees_prop data := by
  unfold benchmark_agrees_prop benchmarkMedianLow
  by_cases h : data.isEmpty = true
  · simp [h]
    have hempty : data = [] := by simpa [List.isEmpty_iff] using h
    exact (empty_thm data hempty).symm
  · simp [h]

/-! ## Post-condition -/

/--
Specification of a successful low-median computation: the value is the
order statistic at `(n - 1) // 2`, a member of the data, it meets the
counting bounds, and it matches Python's odd/even indexing (and, when `n`
is even, is the smaller of the two middle values).
-/
def Post_prop {α : Type} [LinearOrder α] (data : List α) (result : StatsResult α) : Prop :=
  ∃ m, result = .ok m ∧
    (sortedData data)[idx data.length]? = some m ∧
    m ∈ data ∧
    data.countP (fun x => decide (x < m)) ≤ idx data.length ∧
    idx data.length + 1 ≤ data.countP (fun x => decide (x ≤ m)) ∧
    (data.length % 2 = 1 → (sortedData data)[data.length / 2]? = some m) ∧
    (data.length % 2 = 0 → (sortedData data)[data.length / 2 - 1]? = some m) ∧
    (data.length % 2 = 0 →
      ∀ hi, (sortedData data)[data.length / 2]? = some hi → m ≤ hi)


/-! ## Property-based tests -/

def pbtCfg : Plausible.Configuration where
  numInst := 15
  maxSize := 10
  quiet := true

-- PBT: empty_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, xs = [] → medianLow xs = .error StatisticsError.noMedianForEmptyData)

-- PBT: index_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, xs ≠ [] → medianLow xs = .ok ((sortedData xs)[idx xs.length]!))

-- PBT: odd_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, xs.length % 2 = 1 → medianLow xs = .ok ((sortedData xs)[xs.length / 2]!))

-- PBT: even_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, xs ≠ [] → xs.length % 2 = 0 →
    medianLow xs = .ok ((sortedData xs)[xs.length / 2 - 1]!))

-- PBT: mem_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, ∀ m : Int, medianLow xs = .ok m → m ∈ xs)

-- PBT: count_lt_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, ∀ m : Int, medianLow xs = .ok m →
    xs.countP (fun x => decide (x < m)) ≤ idx xs.length)

-- PBT: count_le_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, ∀ m : Int, medianLow xs = .ok m →
    idx xs.length + 1 ≤ xs.countP (fun x => decide (x ≤ m)))

/-- Executable Boolean form of `two_middle_prop`. -/
def twoMiddleCheck (xs : List Int) : Bool :=
  if xs.isEmpty || xs.length % 2 != 0 then true
  else
    match medianLow xs, (sortedData xs)[xs.length / 2]? with
    | .ok m, some hi => decide (m ≤ hi)
    | _, _ => true

-- PBT: two_middle_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, twoMiddleCheck xs = true)

-- PBT: perm_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, medianLow xs = medianLow xs.reverse)

-- PBT: singleton_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ x : Int, medianLow [x] = .ok x)

-- PBT: sorted_input_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, medianLow (sortedData xs) = medianFromSorted (sortedData xs))

-- PBT: unique_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, xs ≠ [] → ∀ m : Int,
    xs.countP (fun x => decide (x < m)) ≤ idx xs.length →
    idx xs.length + 1 ≤ xs.countP (fun x => decide (x ≤ m)) →
    medianLow xs = .ok m)

-- PBT: python_branch_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int,
    medianLow xs =
      if xs.length = 0 then .error StatisticsError.noMedianForEmptyData
      else if xs.length % 2 = 1 then
        match (sortedData xs)[xs.length / 2]? with
        | some v => .ok v
        | none => .error StatisticsError.noMedianForEmptyData
      else
        match (sortedData xs)[xs.length / 2 - 1]? with
        | some v => .ok v
        | none => .error StatisticsError.noMedianForEmptyData)

-- PBT: benchmark_agrees_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, benchmarkMedianLow xs = medianLow xs)

/-- Executable Boolean form of `Post_prop` on non-empty `Int` lists. -/
def postCheck (xs : List Int) : Bool :=
  if xs.isEmpty then true
  else
    match medianLow xs with
    | .error _ => false
    | .ok m =>
        ((sortedData xs)[idx xs.length]? == some m) &&
        (decide (m ∈ xs)) &&
        decide (xs.countP (fun x => decide (x < m)) ≤ idx xs.length) &&
        decide (idx xs.length + 1 ≤ xs.countP (fun x => decide (x ≤ m))) &&
        (xs.length % 2 != 1 || (sortedData xs)[xs.length / 2]? == some m) &&
        (xs.length % 2 != 0 || (sortedData xs)[xs.length / 2 - 1]? == some m) &&
        (xs.length % 2 != 0 ||
          match (sortedData xs)[xs.length / 2]? with
          | some hi => decide (m ≤ hi)
          | none => false)

-- PBT: Post_prop
#eval Plausible.Testable.check (cfg := pbtCfg)
  (∀ xs : List Int, postCheck xs = true)

example : (List.range 16).all (fun n =>
    let xs : List Int := (List.range (n + 1)).map Int.ofNat
    match medianLow xs with
    | .ok m => m == Int.ofNat (n / 2)
    | .error _ => false) = true := by native_decide

example : (List.range 10).all (fun n =>
    let xs : List Int := (List.range (2 * (n + 1))).map Int.ofNat
    match medianLow xs with
    | .ok m => m == Int.ofNat n
    | .error _ => false) = true := by native_decide

example : (List.range 8).all (fun n =>
    let xs : List Int := (List.range n).map fun i => Int.ofNat (n - i)
    (medianLow xs == medianLow xs.reverse)) = true := by native_decide

-- PBT: not executable as a separate `Real` sampler (`Real` order is noncomputable).
-- The proved generic statements `empty_prop`, `index_prop`, `odd_prop`, `even_prop`,
-- `mem_prop`, `count_lt_prop`, `count_le_prop`, `two_middle_prop`, `perm_prop`,
-- `singleton_prop`, `sorted_input_prop`, `unique_prop`, `python_branch_prop`,
-- `benchmark_agrees_prop` and `Post_prop` already quantify over every `LinearOrder`,
-- including `Real`. Executable checks above cover the `Int` layer.

/-! ## Correctness -/

theorem medianLow_correct_thm {α : Type} [LinearOrder α] (data : List α) (h : Pre data) :
    Post_prop data (medianLow data) := by
  have hpos := length_pos_of_pre h
  have hpos' : 0 < (sortedData data).length := by simpa [sortedData_length] using hpos
  have hfrom := medianFromSorted_eq_idx (sortedData data) hpos'
  refine ⟨(sortedData data)[idx data.length]'(by simpa [sortedData_length] using idx_lt hpos),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [medianLow, sortedData_length] using hfrom
  · rw [List.getElem?_eq_getElem]
  · exact mem_thm data _ (by simpa [medianLow, sortedData_length] using hfrom)
  · exact count_lt_thm data _ (by simpa [medianLow, sortedData_length] using hfrom)
  · exact count_le_thm data _ (by simpa [medianLow, sortedData_length] using hfrom)
  · intro hodd
    simp [idx_eq_div_of_odd hodd]
  · intro heven
    simp [idx_eq_div_sub_of_even heven hpos]
  · intro heven hiVal hhi
    exact two_middle_thm data h heven _ hiVal
      (by simpa [medianLow, sortedData_length] using hfrom) hhi

theorem benchmarkMedianLow_correct_thm {α : Type} [LinearOrder α] (data : List α)
    (h : Pre data) : Post_prop data (benchmarkMedianLow data) := by
  rw [benchmark_agrees_thm data]
  exact medianLow_correct_thm data h

/-! ## Imperative implementation -/

/-- One insertion step of insertion sort. -/
def insertSorted {α : Type} [LinearOrder α] (acc : List α) (x : α) : List α :=
  List.orderedInsert (· ≤ ·) x acc

/-- Functional model of the mutable insertion-sort loop. -/
def foldInsert {α : Type} [LinearOrder α] (data : List α) : List α :=
  data.foldl (fun acc x => insertSorted acc x) []

theorem foldl_orderedInsert_perm {α : Type} [LinearOrder α] (acc data : List α) :
    List.Perm (data.foldl (fun acc x => insertSorted acc x) acc) (data ++ acc) := by
  induction data generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.cons_append, insertSorted]
    refine List.Perm.trans (ih (List.orderedInsert (· ≤ ·) x acc)) ?_
    refine List.Perm.trans
      (List.Perm.append_left xs (List.perm_orderedInsert (· ≤ ·) x acc)) ?_
    exact List.perm_middle (l₂ := acc) (a := x) (l₁ := xs)

theorem foldInsert_perm {α : Type} [LinearOrder α] (data : List α) :
    List.Perm (foldInsert data) data := by
  simpa [foldInsert] using foldl_orderedInsert_perm [] data

theorem foldl_orderedInsert_sorted {α : Type} [LinearOrder α] (acc : List α)
    (hacc : acc.Sorted (· ≤ ·)) (data : List α) :
    (data.foldl (fun acc x => insertSorted acc x) acc).Sorted (· ≤ ·) := by
  induction data generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
    simp only [List.foldl_cons, insertSorted]
    exact ih _ (hacc.orderedInsert x)

theorem foldInsert_sorted {α : Type} [LinearOrder α] (data : List α) :
    (foldInsert data).Sorted (· ≤ ·) := by
  simpa [foldInsert] using
    foldl_orderedInsert_sorted [] (by simp : ([] : List α).Sorted (· ≤ ·)) data

theorem foldInsert_eq_sortedData {α : Type} [LinearOrder α] (data : List α) :
    foldInsert data = sortedData data := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (foldInsert_perm data).trans (sortedData_perm data).symm
  · exact foldInsert_sorted data
  · exact sortedData_sorted data

/--
Imperative `median_low`: insertion-sort into a mutable accumulator (`Id.run do`),
then apply Python's odd/even index selection.
-/
def medianLowImp {α : Type} [LinearOrder α] (data : List α) : StatsResult α :=
  Id.run do
    let mut acc : List α := []
    for x in data do
      acc := insertSorted acc x
    return medianFromSorted acc

theorem pure_id_eq {β : Type} (x : β) : (pure x : Id β) = x := rfl

theorem medianLowImp_eq_fold {α : Type} [LinearOrder α] (data : List α) :
    medianLowImp data = medianFromSorted (foldInsert data) := by
  have h := pure_id_eq
    (medianFromSorted (data.foldl (fun acc x => insertSorted acc x) ([] : List α)))
  simp [medianLowImp, foldInsert, Id.run] at h ⊢
  simpa using h

/-! ## Imperative tests -/

example : medianLowImp ([1, 3, 5] : List Int) = .ok 3 := by native_decide
example : medianLowImp ([1, 2, 3, 4, 5, 6, 9] : List Int) = .ok 4 := by native_decide
example : medianLowImp ([1, 3, 5, 7] : List Int) = .ok 3 := by native_decide
example : medianLowImp ([1, 2, 3, 4, 5, 6] : List Int) = .ok 3 := by native_decide
example : medianLowImp ([42] : List Int) = .ok 42 := by native_decide
example : medianLowImp ([10, 20] : List Int) = .ok 10 := by native_decide
example : medianLowImp ([9, 1, 6, 2, 5, 4, 3] : List Int) = .ok 4 := by native_decide
example : medianLowImp ([-5, -1, 0, 3, 7] : List Int) = .ok 0 := by native_decide
example : medianLowImp ([-10, -5, 5, 10] : List Int) = .ok (-5) := by native_decide
example : medianLowImp ([] : List Int) = .error .noMedianForEmptyData := by native_decide

#eval medianLowImp ([1, 3, 5, 7] : List Int)
#eval medianLowImp ([9, 1, 6, 2, 5, 4, 3] : List Int)
#eval medianLowImp ([] : List Int)

/-! ## Equivalence -/

theorem medianLow_eq_medianLowImp_thm {α : Type} [LinearOrder α] (data : List α) :
    medianLow data = medianLowImp data := by
  rw [medianLowImp_eq_fold, foldInsert_eq_sortedData]
  rfl

end «28_statistics_median_low»

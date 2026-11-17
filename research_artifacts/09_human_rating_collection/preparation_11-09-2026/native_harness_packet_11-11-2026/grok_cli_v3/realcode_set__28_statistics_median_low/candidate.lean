import Mathlib

/-!
# Low median (`statistics.median_low`)

Lean formalization of Python's `statistics.median_low` (CPython `Lib/statistics.py`).

Given a non-empty finite sequence of ordered numbers, sort it into non-decreasing order and
return the **low median**:

* when the length `n` is odd, the middle entry `sorted[n // 2]`;
* when `n` is even, the smaller of the two middle entries `sorted[n // 2 - 1]`.

Both branches are the 0-based order statistic at index `(n - 1) / 2`.
An empty sequence raises `StatisticsError`.

## Numeric model

The algorithm only compares values and indexes the sorted sequence. It does not use IEEE-754
rounding, so the model is an arbitrary decidable linear order (`LinearOrder`), not primitive
`Float`. The theorems therefore apply to `ℤ`, `ℚ`, and `ℝ`. Executable tests and property-based
checks instantiate `Int` (with one `Rat` unit test). `ℝ` comparisons are not executable; the
`ℝ` case is the same polymorphic statement, not a separate algorithm.

Python's `pre` also requires a `list` or `tuple` of `numbers.Number`. That obligation is the
element type of `List α`. The remaining runtime obligation is non-emptiness (`Pre`).

`benchmark_median_low` is the entry point under test. It checks `Pre` and then calls `median_low`.
The two functions use different error messages, matching the Python source.
-/

namespace «28_statistics_median_low»

/-- Message raised by `median_low` on the empty sequence. -/
def emptyMedianMsg : String := "no median for empty data"

/-- Message raised by `benchmark_median_low` when `Pre` fails. -/
def benchmarkPreMsg : String :=
  "benchmark_median_low requires a non-empty list/tuple of numbers"

/-- 0-based index of the low median in a list of length `n`. -/
def lowMedianIndex (n : Nat) : Nat := (n - 1) / 2

theorem lowMedianIndex_lt {n : Nat} (h : 0 < n) : lowMedianIndex n < n := by
  unfold lowMedianIndex
  omega

theorem lowMedianIndex_of_odd {n : Nat} (h : n % 2 = 1) : lowMedianIndex n = n / 2 := by
  unfold lowMedianIndex
  omega

theorem lowMedianIndex_of_even {n : Nat} (hpos : 0 < n) (h : n % 2 = 0) :
    lowMedianIndex n = n / 2 - 1 := by
  unfold lowMedianIndex
  omega

theorem lowMedianIndex_succ {n : Nat} (h : 0 < n) : lowMedianIndex n + 1 = (n + 1) / 2 := by
  unfold lowMedianIndex
  omega

theorem length_sub_lowMedianIndex {n : Nat} (h : 0 < n) : n - lowMedianIndex n = n / 2 + 1 := by
  unfold lowMedianIndex
  omega

theorem odd_branch_lt {n : Nat} (hodd : n % 2 = 1) : n / 2 < n := by
  omega

theorem even_branch_lt {n : Nat} (h0 : n ≠ 0) (hodd : ¬ n % 2 = 1) : n / 2 - 1 < n := by
  have : n % 2 = 0 := by
    have := Nat.mod_two_eq_zero_or_one n
    omega
  omega

theorem high_index_bound {n : Nat} (h : 0 < n) : n / 2 < n := by
  omega

theorem low_index_le_high {n : Nat} (h : 0 < n) : lowMedianIndex n ≤ n / 2 := by
  unfold lowMedianIndex
  omega

theorem getElem_eq_of_idx_eq {β : Type _} {l : List β} {i j : Nat} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  cases hij
  rfl

theorem getElem_proof_irrel {β : Type _} {l : List β} {i : Nat} {hi hi' : i < l.length} :
    l[i]'hi = l[i]'hi' :=
  getElem_eq_of_idx_eq rfl hi hi'

/-! ## Functional implementation -/

variable {α : Type*} [LinearOrder α]

/-- Ascending sort. Python `sorted` on a total order. -/
def sortedList (data : List α) : List α :=
  data.mergeSort (· ≤ ·)

theorem sortedList_length (data : List α) : (sortedList data).length = data.length := by
  simp [sortedList, List.length_mergeSort]

theorem sortedList_perm (data : List α) : List.Perm (sortedList data) data := by
  simpa [sortedList] using List.mergeSort_perm data (· ≤ ·)

theorem sortedList_sorted (data : List α) : List.Sorted (· ≤ ·) (sortedList data) :=
  List.sorted_mergeSort' (· ≤ ·) data

theorem sortedList_eq_insertionSort (data : List α) :
    sortedList data = List.insertionSort (· ≤ ·) data := by
  simpa [sortedList] using List.mergeSort_eq_insertionSort (· ≤ ·) data

theorem sortedList_of_nil : sortedList ([] : List α) = [] := by
  simp [sortedList, List.mergeSort_nil]

/-- Low median of `data`.

Mirrors CPython `median_low`: sort, reject the empty list, and return
`sorted[(n - 1) // 2]`, i.e. `sorted[n // 2]` for odd `n` and `sorted[n // 2 - 1]` for even `n`.
-/
def median_low (data : List α) : Except String α :=
  let sorted := sortedList data
  let n := sorted.length
  if h0 : n = 0 then
    .error emptyMedianMsg
  else if hodd : n % 2 = 1 then
    .ok (sorted[n / 2]'(odd_branch_lt hodd))
  else
    .ok (sorted[n / 2 - 1]'(even_branch_lt h0 hodd))

/-- Entry point under test. Checks the precondition, then calls `median_low`. -/
def benchmark_median_low (data : List α) : Except String α :=
  if data.isEmpty then
    .error benchmarkPreMsg
  else
    median_low data

/-- The low-median value of a non-empty list: `sorted[(n - 1) / 2]`. -/
def lowMedianValue (data : List α) (h : data ≠ []) : α :=
  let s := sortedList data
  s[lowMedianIndex s.length]'(lowMedianIndex_lt (by
    rw [sortedList_length]
    exact List.length_pos_iff.mpr h))

instance instDecidableEqExcept {ε β} [DecidableEq ε] [DecidableEq β] :
    DecidableEq (Except ε β) := fun a b =>
  match a, b with
  | .error x, .error y =>
    match decEq x y with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ok x, .ok y =>
    match decEq x y with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .error _, .ok _ => isFalse (by intro h; cases h)
  | .ok _, .error _ => isFalse (by intro h; cases h)

/-! ## Unit tests -/

example : benchmark_median_low ([1, 3, 5] : List Int) = .ok 3 := by native_decide

example : benchmark_median_low ([1, 2, 3, 4, 5, 6, 9] : List Int) = .ok 4 := by native_decide

example : benchmark_median_low ([1, 3, 5, 7] : List Int) = .ok 3 := by native_decide

example : benchmark_median_low ([1, 2, 3, 4, 5, 6] : List Int) = .ok 3 := by native_decide

example : benchmark_median_low ([42] : List Int) = .ok 42 := by native_decide

example : benchmark_median_low ([10, 20] : List Int) = .ok 10 := by native_decide

example : benchmark_median_low ([9, 1, 6, 2, 5, 4, 3] : List Int) = .ok 4 := by native_decide

example : benchmark_median_low ([-5, -1, 0, 3, 7] : List Int) = .ok 0 := by native_decide

example : benchmark_median_low ([-10, -5, 5, 10] : List Int) = .ok (-5) := by native_decide

example : benchmark_median_low ([1, 2, 2, 3] : List Int) = .ok 2 := by native_decide

example : benchmark_median_low ([-1, -5] : List Int) = .ok (-5) := by native_decide

example : benchmark_median_low ([] : List Int) = .error benchmarkPreMsg := by native_decide

example : median_low ([] : List Int) = .error emptyMedianMsg := by native_decide

example : benchmark_median_low ([(1 : Rat) / 2, (3 : Rat) / 2, (5 : Rat) / 2]) = .ok ((3 : Rat) / 2) := by
  native_decide

#eval benchmark_median_low ([1, 3, 5] : List Int)

#eval benchmark_median_low ([1, 3, 5, 7] : List Int)

#eval benchmark_median_low ([9, 1, 6, 2, 5, 4, 3] : List Int)

#eval benchmark_median_low ([-10, -5, 5, 10] : List Int)

#eval benchmark_median_low ([] : List Int)

/-! ## Pre-condition -/

/-- Python `pre` for a list of ordered numbers: the sequence is non-empty.
The list/tuple and numeric-type checks are the type `List α`. -/
def Pre (data : List α) : Prop := data ≠ []

/-! ## Auxiliary lemmas -/

theorem sorted_mono (data : List α) {i j : Nat}
    (hi : i < (sortedList data).length) (hj : j < (sortedList data).length) (hij : i ≤ j) :
    (sortedList data)[i] ≤ (sortedList data)[j] := by
  have hs := sortedList_sorted data
  have hrel :=
    hs.rel_get_of_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)
      (hab := by simpa using hij)
  simpa [List.get_eq_getElem] using hrel

theorem median_low_empty : median_low ([] : List α) = .error emptyMedianMsg := by
  simp [median_low, sortedList_of_nil]

theorem benchmark_median_low_empty :
    benchmark_median_low ([] : List α) = .error benchmarkPreMsg := by
  simp [benchmark_median_low]

theorem benchmark_median_low_of_ne_nil (data : List α) (h : data ≠ []) :
    benchmark_median_low data = median_low data := by
  have hempty : data.isEmpty = false := by simpa [List.isEmpty_iff] using h
  simp [benchmark_median_low, hempty]

theorem countP_eq_sorted (data : List α) (p : α → Bool) :
    data.countP p = (sortedList data).countP p :=
  (sortedList_perm data).symm.countP_eq p

theorem lowMedianValue_eq_index (data : List α) (h : data ≠ []) :
    lowMedianValue data h =
      (sortedList data)[lowMedianIndex (sortedList data).length]'
        (lowMedianIndex_lt (by rw [sortedList_length]; exact List.length_pos_iff.mpr h)) := by
  rfl

theorem median_low_eq_lowMedianValue (data : List α) (h : data ≠ []) :
    median_low data = .ok (lowMedianValue data h) := by
  have hpos : 0 < (sortedList data).length := by
    rw [sortedList_length]
    exact List.length_pos_iff.mpr h
  have hlen0 : (sortedList data).length ≠ 0 := Nat.ne_of_gt hpos
  unfold median_low
  simp only [hlen0, dite_false]
  by_cases hodd : (sortedList data).length % 2 = 1
  · simp only [hodd, dite_true]
    apply congrArg Except.ok
    have hidx :
        (sortedList data).length / 2 = lowMedianIndex (sortedList data).length :=
      (lowMedianIndex_of_odd hodd).symm
    exact getElem_eq_of_idx_eq hidx (odd_branch_lt hodd) (lowMedianIndex_lt hpos)
  · simp only [hodd, dite_false]
    apply congrArg Except.ok
    have heven : (sortedList data).length % 2 = 0 := by
      have := Nat.mod_two_eq_zero_or_one (sortedList data).length
      omega
    have hidx :
        (sortedList data).length / 2 - 1 = lowMedianIndex (sortedList data).length :=
      (lowMedianIndex_of_even hpos heven).symm
    exact getElem_eq_of_idx_eq hidx (even_branch_lt hlen0 hodd) (lowMedianIndex_lt hpos)

theorem benchmark_median_low_eq_lowMedianValue (data : List α) (h : data ≠ []) :
    benchmark_median_low data = .ok (lowMedianValue data h) := by
  rw [benchmark_median_low_of_ne_nil data h, median_low_eq_lowMedianValue data h]

theorem lowMedianValue_mem (data : List α) (h : data ≠ []) : lowMedianValue data h ∈ data := by
  have hm : lowMedianValue data h ∈ sortedList data := by
    unfold lowMedianValue
    exact List.getElem_mem _
  exact (sortedList_perm data).mem_iff.mp hm

theorem index_value_eq (data : List α) (h : data ≠ []) :
    lowMedianValue data h =
      (sortedList data)[lowMedianIndex (sortedList data).length]'
        (lowMedianIndex_lt (by
          rw [sortedList_length]
          exact List.length_pos_iff.mpr h)) := by
  unfold lowMedianValue
  exact getElem_proof_irrel

/-- At least `⌊(n + 1) / 2⌋` entries are `≤` the low median. -/
theorem lower_count_le (data : List α) (h : data ≠ []) :
    (data.length + 1) / 2 ≤ data.countP (fun x => decide (x ≤ lowMedianValue data h)) := by
  have hlen : (sortedList data).length = data.length := sortedList_length data
  set s := sortedList data
  have hpos : 0 < s.length := by rw [hlen]; exact List.length_pos_iff.mpr h
  set i := lowMedianIndex s.length
  have hi : i < s.length := lowMedianIndex_lt hpos
  have hsrt := sortedList_sorted data
  have hm : lowMedianValue data h = s[i]'hi := by
    rw [index_value_eq data h]
    exact getElem_proof_irrel
  have hneed : (data.length + 1) / 2 = i + 1 := by
    have : i + 1 = (s.length + 1) / 2 := lowMedianIndex_succ hpos
    rw [hlen] at this
    omega
  have hsplit : s.take (i + 1) = s.take i ++ [s[i]'hi] :=
    List.take_succ_eq_append_getElem hi
  have htake_le : ∀ x ∈ s.take i, x ≤ s[i]'hi := by
    intro x hx
    have hhead : s[i] ∈ s.drop i := by
      rw [List.drop_eq_getElem_cons hi]
      exact List.mem_cons_self ..
    exact hsrt.rel_of_mem_take_of_mem_drop hx hhead
  have hall : ∀ x ∈ s.take (i + 1), decide (x ≤ lowMedianValue data h) = true := by
    intro x hx
    rw [hsplit] at hx
    simp at hx
    rcases hx with hx | rfl
    · have hsi : s[i] ≤ lowMedianValue data h := by rw [hm]
      exact decide_eq_true (le_trans (htake_le x hx) hsi)
    · rw [hm]
      exact decide_eq_true le_rfl
  rw [hneed, countP_eq_sorted]
  change i + 1 ≤ s.countP fun x => decide (x ≤ lowMedianValue data h)
  rw [← List.take_append_drop (i + 1) s, List.countP_append]
  have htake :
      (s.take (i + 1)).countP (fun x => decide (x ≤ lowMedianValue data h)) = i + 1 := by
    rw [List.countP_eq_length.mpr hall, List.length_take, Nat.min_eq_left (by omega)]
  omega

/-- At least `⌊n / 2⌋ + 1` entries are `≥` the low median. -/
theorem upper_count_ge (data : List α) (h : data ≠ []) :
    data.length / 2 + 1 ≤ data.countP (fun x => decide (lowMedianValue data h ≤ x)) := by
  have hlen : (sortedList data).length = data.length := sortedList_length data
  set s := sortedList data
  have hpos : 0 < s.length := by rw [hlen]; exact List.length_pos_iff.mpr h
  set i := lowMedianIndex s.length
  have hi : i < s.length := lowMedianIndex_lt hpos
  have hsrt := sortedList_sorted data
  have hm : lowMedianValue data h = s[i]'hi := by
    rw [index_value_eq data h]
    exact getElem_proof_irrel
  have hneed : data.length / 2 + 1 = s.length - i := by
    have : s.length - i = s.length / 2 + 1 := length_sub_lowMedianIndex hpos
    rw [hlen] at this
    omega
  have htail : ∀ x ∈ s.drop (i + 1), s[i]'hi ≤ x := by
    intro x hx
    have hm_take : s[i] ∈ s.take (i + 1) := by
      rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    exact hsrt.rel_of_mem_take_of_mem_drop hm_take hx
  have hself : s[i] ∈ (s.take (i + 1)).filter (fun x => decide (lowMedianValue data h ≤ x)) := by
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · rw [hm]
      exact decide_eq_true le_rfl
  rw [hneed, countP_eq_sorted]
  change s.length - i ≤ s.countP fun x => decide (lowMedianValue data h ≤ x)
  rw [← List.take_append_drop (i + 1) s, List.countP_append]
  have hdrop :
      (s.drop (i + 1)).countP (fun x => decide (lowMedianValue data h ≤ x)) =
        s.length - (i + 1) := by
    rw [List.countP_eq_length.mpr, List.length_drop]
    intro x hx
    exact decide_eq_true (by rw [hm]; exact htail x hx)
  have htake :
      1 ≤ (s.take (i + 1)).countP (fun x => decide (lowMedianValue data h ≤ x)) := by
    rw [List.countP_eq_length_filter]
    exact List.length_pos_of_mem hself
  omega

theorem lowMedianValue_le_high (data : List α) (h : data ≠ []) :
    lowMedianValue data h ≤
      (sortedList data)[data.length / 2]'(by
        rw [sortedList_length]
        exact high_index_bound (List.length_pos_iff.mpr h)) := by
  have hlen : (sortedList data).length = data.length := sortedList_length data
  set s := sortedList data
  have hpos : 0 < s.length := by rw [hlen]; exact List.length_pos_iff.mpr h
  have hi := lowMedianIndex_lt hpos
  have hhi := high_index_bound hpos
  have hle := low_index_le_high hpos
  have hm : lowMedianValue data h = s[lowMedianIndex s.length]'hi := by
    rw [index_value_eq data h]
    exact getElem_proof_irrel
  rw [hm]
  have hright :
      s[data.length / 2]'(by rw [hlen]; exact high_index_bound (List.length_pos_iff.mpr h)) =
        s[s.length / 2]'hhi :=
    getElem_eq_of_idx_eq (by rw [hlen]) _ _
  rw [hright]
  exact sorted_mono data hi hhi hle

theorem count_lt_before (data : List α) (h : data ≠ []) {m' : α}
    (hlt : m' < lowMedianValue data h) :
    data.countP (fun x => decide (x ≤ m')) ≤ lowMedianIndex data.length := by
  have hlen : (sortedList data).length = data.length := sortedList_length data
  set s := sortedList data
  have hpos : 0 < s.length := by rw [hlen]; exact List.length_pos_iff.mpr h
  set i := lowMedianIndex s.length
  have hi : i < s.length := lowMedianIndex_lt hpos
  have hsrt := sortedList_sorted data
  have hm : lowMedianValue data h = s[i]'hi := by
    rw [index_value_eq data h]
    exact getElem_proof_irrel
  have htail : ∀ x ∈ s.drop (i + 1), s[i]'hi ≤ x := by
    intro x hx
    have hm_take : s[i] ∈ s.take (i + 1) := by
      rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    exact hsrt.rel_of_mem_take_of_mem_drop hm_take hx
  rw [countP_eq_sorted]
  change s.countP (fun x => decide (x ≤ m')) ≤ lowMedianIndex data.length
  have hi_data : i = lowMedianIndex data.length := by simp [i, hlen]
  rw [← hi_data, ← List.take_append_drop i s, List.countP_append]
  have hdrop0 : (s.drop i).countP (fun x => decide (x ≤ m')) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx hdec
    have hle : x ≤ m' := of_decide_eq_true hdec
    rw [List.drop_eq_getElem_cons hi] at hx
    simp at hx
    rcases hx with rfl | hx
    · rw [← hm] at hle
      exact not_lt_of_ge hle hlt
    · have hge : s[i] ≤ x := htail x hx
      rw [← hm] at hge
      exact not_lt_of_ge hge (lt_of_le_of_lt hle hlt)
  have htake :
      (s.take i).countP (fun x => decide (x ≤ m')) ≤ i := by
    exact le_trans List.countP_le_length (by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)])
  simp [hdrop0]
  exact htake

theorem count_gt_after (data : List α) (h : data ≠ []) {m' : α}
    (hgt : lowMedianValue data h < m') :
    data.countP (fun x => decide (m' ≤ x)) ≤
      data.length - (lowMedianIndex data.length + 1) := by
  have hlen : (sortedList data).length = data.length := sortedList_length data
  set s := sortedList data
  have hpos : 0 < s.length := by rw [hlen]; exact List.length_pos_iff.mpr h
  set i := lowMedianIndex s.length
  have hi : i < s.length := lowMedianIndex_lt hpos
  have hsrt := sortedList_sorted data
  have hm : lowMedianValue data h = s[i]'hi := by
    rw [index_value_eq data h]
    exact getElem_proof_irrel
  have hpref : ∀ x ∈ s.take (i + 1), x ≤ s[i]'hi := by
    intro x hx
    rw [List.take_succ_eq_append_getElem hi] at hx
    simp at hx
    rcases hx with hx | rfl
    · have hhead : s[i] ∈ s.drop i := by
        rw [List.drop_eq_getElem_cons hi]
        exact List.mem_cons_self ..
      exact hsrt.rel_of_mem_take_of_mem_drop hx hhead
    · exact le_rfl
  rw [countP_eq_sorted]
  change s.countP (fun x => decide (m' ≤ x)) ≤ data.length - (lowMedianIndex data.length + 1)
  have hi_data : i = lowMedianIndex data.length := by simp [i, hlen]
  rw [← hi_data, ← hlen, ← List.take_append_drop (i + 1) s, List.countP_append]
  have htake0 : (s.take (i + 1)).countP (fun x => decide (m' ≤ x)) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx hdec
    have hmx : m' ≤ x := of_decide_eq_true hdec
    have hxle : x ≤ s[i] := hpref x hx
    rw [← hm] at hxle
    exact not_lt_of_ge (le_trans hmx hxle) hgt
  have hdrop :
      (s.drop (i + 1)).countP (fun x => decide (m' ≤ x)) ≤ s.length - (i + 1) := by
    exact le_trans List.countP_le_length (by rw [List.length_drop])
  simpa [htake0] using hdrop

theorem low_median_unique (data : List α) (h : data ≠ []) (m' : α)
    (hle : (data.length + 1) / 2 ≤ data.countP (fun x => decide (x ≤ m')))
    (hge : data.length / 2 + 1 ≤ data.countP (fun x => decide (m' ≤ x))) :
    m' = lowMedianValue data h := by
  have hpos : 0 < data.length := List.length_pos_iff.mpr h
  have hi_add : lowMedianIndex data.length + 1 = (data.length + 1) / 2 :=
    lowMedianIndex_succ hpos
  have hsub : data.length - lowMedianIndex data.length = data.length / 2 + 1 :=
    length_sub_lowMedianIndex hpos
  rcases lt_trichotomy m' (lowMedianValue data h) with hlt | heq | hgt
  · have hbound := count_lt_before data h hlt
    have : (data.length + 1) / 2 ≤ lowMedianIndex data.length :=
      le_trans hle hbound
    omega
  · exact heq
  · have hbound := count_gt_after data h hgt
    have : data.length / 2 + 1 ≤ data.length - (lowMedianIndex data.length + 1) :=
      le_trans hge hbound
    omega

theorem benchmark_perm (data data' : List α) (hp : List.Perm data data') :
    benchmark_median_low data = benchmark_median_low data' := by
  by_cases h : data = []
  · have h' : data' = [] := by
      have hperm : List.Perm [] data' := by simpa [h] using hp
      exact hperm.nil_eq.symm
    simp [h, h', benchmark_median_low_empty]
  · have h' : data' ≠ [] := by
      intro he
      apply h
      have : List.Perm data [] := by simpa [he] using hp
      exact this.eq_nil
    have hsort : sortedList data = sortedList data' :=
      List.eq_of_perm_of_sorted
        ((sortedList_perm data).trans (hp.trans (sortedList_perm data').symm))
        (sortedList_sorted data) (sortedList_sorted data')
    rw [benchmark_median_low_eq_lowMedianValue data h,
      benchmark_median_low_eq_lowMedianValue data' h']
    apply congrArg Except.ok
    simp [lowMedianValue, hsort, getElem_proof_irrel]

/-! ## Properties -/

/-- Empty input yields the benchmark precondition error. -/
def empty_error_prop (data : List α) (result : Except String α) : Prop :=
  data = [] → result = .error benchmarkPreMsg

/-- On a non-empty list the result is the order statistic at index `(n - 1) / 2`. -/
def sorted_index_prop (data : List α) (result : Except String α) : Prop :=
  ∀ hne : data ≠ [], result = .ok (lowMedianValue data hne)

/-- Odd length: the result is the middle entry `sorted[n / 2]` of the ascending sort. -/
def odd_middle_prop (data : List α) (result : Except String α) : Prop :=
  ∀ (hne : data ≠ []) (hodd : data.length % 2 = 1),
    result =
      .ok ((sortedList data)[data.length / 2]'(by
        rw [sortedList_length]
        exact odd_branch_lt hodd))

/-- Even positive length: the result is the smaller of the two middle entries. -/
def even_low_middle_prop (data : List α) (result : Except String α) : Prop :=
  ∀ (hne : data ≠ []) (he : data.length % 2 = 0),
    result =
        .ok ((sortedList data)[data.length / 2 - 1]'(by
          rw [sortedList_length]
          exact even_branch_lt (Nat.ne_of_gt (List.length_pos_iff.mpr hne)) (by
            intro hodd
            omega))) ∧
      (sortedList data)[data.length / 2 - 1]'(by
          rw [sortedList_length]
          exact even_branch_lt (Nat.ne_of_gt (List.length_pos_iff.mpr hne)) (by
            intro hodd
            omega)) ≤
        (sortedList data)[data.length / 2]'(by
          rw [sortedList_length]
          exact high_index_bound (List.length_pos_iff.mpr hne))

/-- A successful result is an element of the input. -/
def mem_prop (data : List α) (result : Except String α) : Prop :=
  ∀ m, result = .ok m → m ∈ data

/-- At least half the entries, rounded up, are `≤` the low median. -/
def lower_count_prop (data : List α) (result : Except String α) : Prop :=
  ∀ m, result = .ok m →
    (data.length + 1) / 2 ≤ data.countP (fun x => decide (x ≤ m))

/-- Strictly more than half the entries are `≥` the low median (`⌊n/2⌋ + 1`). -/
def upper_count_prop (data : List α) (result : Except String α) : Prop :=
  ∀ m, result = .ok m →
    data.length / 2 + 1 ≤ data.countP (fun x => decide (m ≤ x))

/-- The low median is `≤` the high middle entry `sorted[n / 2]`.
A successful result forces the input to be non-empty, so that index is in range. -/
def le_high_median_prop (data : List α) (result : Except String α) : Prop :=
  ∀ m, result = .ok m →
    ∃ hi, (sortedList data)[data.length / 2]? = some hi ∧ m ≤ hi

/-- The value is unchanged by permuting the input. -/
def perm_invariance_prop (data : List α) (result : Except String α) : Prop :=
  ∀ data', List.Perm data data' → benchmark_median_low data' = result

/-- The two count bounds determine the low median uniquely. -/
def unique_low_median_prop (data : List α) (result : Except String α) : Prop :=
  ∀ m, result = .ok m →
    ∀ m',
      (data.length + 1) / 2 ≤ data.countP (fun x => decide (x ≤ m')) →
      data.length / 2 + 1 ≤ data.countP (fun x => decide (m' ≤ x)) →
      m' = m

/-- On a non-empty list the benchmark agrees with `median_low`. -/
def agrees_with_median_low_prop (data : List α) (result : Except String α) : Prop :=
  data ≠ [] → result = median_low data

/-- `median_low` itself reports its own empty-list error. -/
def median_low_empty_error_prop (data : List α) (result : Except String α) : Prop :=
  data = [] → result = .error emptyMedianMsg

/-- A one-element list is its own low median. -/
def singleton_prop (x : α) : Prop :=
  benchmark_median_low [x] = .ok x

/-- The low median of two values is their minimum. -/
def pair_min_prop (a b : α) : Prop :=
  benchmark_median_low [a, b] = .ok (min a b)

theorem empty_error_thm (data : List α) :
    empty_error_prop data (benchmark_median_low data) := by
  intro hempty
  simp [hempty, benchmark_median_low_empty]

theorem sorted_index_thm (data : List α) :
    sorted_index_prop data (benchmark_median_low data) := by
  intro hne
  exact benchmark_median_low_eq_lowMedianValue data hne

theorem odd_middle_thm (data : List α) :
    odd_middle_prop data (benchmark_median_low data) := by
  intro hne hodd
  rw [benchmark_median_low_eq_lowMedianValue data hne]
  apply congrArg Except.ok
  have hpos : 0 < (sortedList data).length := by
    rw [sortedList_length]
    exact List.length_pos_iff.mpr hne
  have hidx :
      lowMedianIndex (sortedList data).length = data.length / 2 := by
    rw [sortedList_length, lowMedianIndex_of_odd hodd]
  unfold lowMedianValue
  exact getElem_eq_of_idx_eq hidx (lowMedianIndex_lt hpos)
    (by rw [sortedList_length]; exact odd_branch_lt hodd)

theorem even_low_middle_thm (data : List α) :
    even_low_middle_prop data (benchmark_median_low data) := by
  intro hne he
  have hpos_n : 0 < data.length := List.length_pos_iff.mpr hne
  have hnot : ¬ data.length % 2 = 1 := by
    intro hodd
    omega
  have hpos : 0 < (sortedList data).length := by
    rw [sortedList_length]
    exact hpos_n
  have hidx :
      lowMedianIndex (sortedList data).length = data.length / 2 - 1 := by
    rw [sortedList_length, lowMedianIndex_of_even hpos_n he]
  refine ⟨?_, ?_⟩
  · rw [benchmark_median_low_eq_lowMedianValue data hne]
    apply congrArg Except.ok
    unfold lowMedianValue
    exact getElem_eq_of_idx_eq hidx (lowMedianIndex_lt hpos)
      (by rw [sortedList_length]; exact even_branch_lt (Nat.ne_of_gt hpos_n) hnot)
  · have hlo := even_branch_lt (Nat.ne_of_gt hpos_n) hnot
    have hhi := high_index_bound hpos_n
    have hlo' : data.length / 2 - 1 < (sortedList data).length := by
      rw [sortedList_length]; exact hlo
    have hhi' : data.length / 2 < (sortedList data).length := by
      rw [sortedList_length]; exact hhi
    have hle : data.length / 2 - 1 ≤ data.length / 2 := by omega
    exact sorted_mono data hlo' hhi' hle

theorem mem_thm (data : List α) : mem_prop data (benchmark_median_low data) := by
  intro m hm
  by_cases h : data = []
  · simp [h, benchmark_median_low_empty] at hm
  · rw [benchmark_median_low_eq_lowMedianValue data h] at hm
    cases hm
    exact lowMedianValue_mem data h

theorem lower_count_thm (data : List α) :
    lower_count_prop data (benchmark_median_low data) := by
  intro m hm
  by_cases h : data = []
  · simp [h, benchmark_median_low_empty] at hm
  · rw [benchmark_median_low_eq_lowMedianValue data h] at hm
    cases hm
    exact lower_count_le data h

theorem upper_count_thm (data : List α) :
    upper_count_prop data (benchmark_median_low data) := by
  intro m hm
  by_cases h : data = []
  · simp [h, benchmark_median_low_empty] at hm
  · rw [benchmark_median_low_eq_lowMedianValue data h] at hm
    cases hm
    exact upper_count_ge data h

theorem le_high_median_thm (data : List α) :
    le_high_median_prop data (benchmark_median_low data) := by
  intro m hm
  by_cases h : data = []
  · simp [h, benchmark_median_low_empty] at hm
  · rw [benchmark_median_low_eq_lowMedianValue data h] at hm
    cases hm
    have hlt : data.length / 2 < (sortedList data).length := by
      rw [sortedList_length]
      exact high_index_bound (List.length_pos_iff.mpr h)
    refine ⟨(sortedList data)[data.length / 2]'hlt, ?_, ?_⟩
    · exact getElem?_pos (sortedList data) (data.length / 2) hlt
    · exact lowMedianValue_le_high data h

theorem perm_invariance_thm (data : List α) :
    perm_invariance_prop data (benchmark_median_low data) := by
  intro data' hp
  exact (benchmark_perm data data' hp).symm

theorem unique_low_median_thm (data : List α) :
    unique_low_median_prop data (benchmark_median_low data) := by
  intro m hm m' hle hge
  by_cases h : data = []
  · simp [h, benchmark_median_low_empty] at hm
  · rw [benchmark_median_low_eq_lowMedianValue data h] at hm
    cases hm
    exact low_median_unique data h m' hle hge

theorem agrees_with_median_low_thm (data : List α) :
    agrees_with_median_low_prop data (benchmark_median_low data) :=
  benchmark_median_low_of_ne_nil data

theorem median_low_empty_error_thm (data : List α) :
    median_low_empty_error_prop data (median_low data) := by
  intro hempty
  simp [hempty, median_low_empty]

theorem singleton_thm (x : α) : singleton_prop x := by
  unfold singleton_prop
  have h : ([x] : List α) ≠ [] := by simp
  rw [benchmark_median_low_eq_lowMedianValue _ h]
  unfold lowMedianValue sortedList
  simp [List.mergeSort_singleton, lowMedianIndex]

theorem pair_min_thm (a b : α) : pair_min_prop a b := by
  unfold pair_min_prop
  have hne : ([a, b] : List α) ≠ [] := by simp
  rw [benchmark_median_low_eq_lowMedianValue _ hne, min_def]
  by_cases hle : a ≤ b
  · have hs : List.Sorted (· ≤ ·) [a, b] := by
      simp [List.sorted_cons, hle]
    have heq : sortedList [a, b] = [a, b] := by
      simpa [sortedList] using List.mergeSort_eq_self (· ≤ ·) hs
    simp [lowMedianValue, heq, lowMedianIndex, hle]
  · have hba : b ≤ a := (le_total a b).resolve_left hle
    have hs : List.Sorted (· ≤ ·) [b, a] := by
      simp [List.sorted_cons, hba]
    have hperm : List.Perm (sortedList [a, b]) [b, a] :=
      (sortedList_perm [a, b]).trans (List.Perm.swap a b [])
    have heq : sortedList [a, b] = [b, a] :=
      List.eq_of_perm_of_sorted hperm (sortedList_sorted _) hs
    simp [lowMedianValue, heq, lowMedianIndex, hle]

/-! ## Post-condition -/

/-- Full observable contract of `benchmark_median_low`. -/
def Post_prop (data : List α) (result : Except String α) : Prop :=
  empty_error_prop data result ∧
  sorted_index_prop data result ∧
  odd_middle_prop data result ∧
  even_low_middle_prop data result ∧
  mem_prop data result ∧
  lower_count_prop data result ∧
  upper_count_prop data result ∧
  le_high_median_prop data result ∧
  perm_invariance_prop data result ∧
  unique_low_median_prop data result ∧
  agrees_with_median_low_prop data result

/-! ## Property-based tests

Executable checks of every `_prop` and of `Post_prop`.
The statements above are polymorphic in a linear order. Comparisons on `ℝ` are not
executable (`-- PBT: not executable (Real.le)` for a separate `ℝ`-only formulation);
the polymorphic theorems already cover `ℝ`, and the checks below instantiate `Int`.
-/

def check_empty (xs : List Int) : Bool :=
  if xs.isEmpty then
    match benchmark_median_low xs with
    | .error m => m == benchmarkPreMsg
    | .ok _ => false
  else
    true

def check_sorted_index (xs : List Int) : Bool :=
  match benchmark_median_low xs with
  | .error _ => xs.isEmpty
  | .ok m =>
    let s := sortedList xs
    decide (s[lowMedianIndex s.length]? = some m)

def check_odd_middle (xs : List Int) : Bool :=
  let s := sortedList xs
  let n := xs.length
  if n % 2 = 1 then
    match benchmark_median_low xs with
    | .ok m => decide (s[n / 2]? = some m)
    | .error _ => false
  else
    true

def check_even_low_middle (xs : List Int) : Bool :=
  let s := sortedList xs
  let n := xs.length
  if n == 0 then
    true
  else if n % 2 = 0 then
    match benchmark_median_low xs, s[n / 2]? with
    | .ok m, some hi =>
      decide (s[n / 2 - 1]? = some m) && decide (m ≤ hi)
    | _, _ => false
  else
    true

def check_mem (xs : List Int) : Bool :=
  match benchmark_median_low xs with
  | .error _ => xs.isEmpty
  | .ok m => decide (m ∈ xs)

def check_lower_count (xs : List Int) : Bool :=
  match benchmark_median_low xs with
  | .error _ => xs.isEmpty
  | .ok m =>
    decide ((xs.length + 1) / 2 ≤ xs.countP (fun y => decide (y ≤ m)))

def check_upper_count (xs : List Int) : Bool :=
  match benchmark_median_low xs with
  | .error _ => xs.isEmpty
  | .ok m =>
    decide (xs.length / 2 + 1 ≤ xs.countP (fun y => decide (m ≤ y)))

def check_le_high (xs : List Int) : Bool :=
  match benchmark_median_low xs with
  | .error _ => xs.isEmpty
  | .ok m =>
    let s := sortedList xs
    match s[xs.length / 2]? with
    | some hi => decide (m ≤ hi)
    | none => false

def check_perm (xs : List Int) : Bool :=
  benchmark_median_low xs == benchmark_median_low xs.reverse &&
    benchmark_median_low xs == benchmark_median_low (sortedList xs) &&
    benchmark_median_low xs == benchmark_median_low (xs ++ [])

def check_unique_at (xs : List Int) (m' : Int) : Bool :=
  match benchmark_median_low xs with
  | .error _ => true
  | .ok m =>
    let lower :=
      decide ((xs.length + 1) / 2 ≤ xs.countP (fun y => decide (y ≤ m')))
    let upper :=
      decide (xs.length / 2 + 1 ≤ xs.countP (fun y => decide (m' ≤ y)))
    !(lower && upper) || (m' == m)

def check_agrees (xs : List Int) : Bool :=
  if xs.isEmpty then true else benchmark_median_low xs == median_low xs

def check_median_low_empty (xs : List Int) : Bool :=
  if xs.isEmpty then
    match median_low xs with
    | .error m => m == emptyMedianMsg
    | .ok _ => false
  else
    true

def check_singleton (x : Int) : Bool :=
  benchmark_median_low [x] == .ok x

def check_pair (a b : Int) : Bool :=
  benchmark_median_low [a, b] == .ok (min a b)

def check_post (xs : List Int) : Bool :=
  check_empty xs && check_sorted_index xs && check_odd_middle xs && check_even_low_middle xs &&
    check_mem xs && check_lower_count xs && check_upper_count xs && check_le_high xs &&
    check_perm xs && check_agrees xs && check_median_low_empty xs &&
    (List.range 15).all (fun k => check_unique_at xs (Int.ofNat k - 7))

#eval Plausible.Testable.check (∀ xs : List Int, check_empty xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_sorted_index xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_odd_middle xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_even_low_middle xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_mem xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_lower_count xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_upper_count xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_le_high xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_perm xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, ∀ m' : Int, check_unique_at xs m' = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_agrees xs = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_median_low_empty xs = true)

#eval Plausible.Testable.check (∀ x : Int, check_singleton x = true)

#eval Plausible.Testable.check (∀ a b : Int, check_pair a b = true)

#eval Plausible.Testable.check (∀ xs : List Int, check_post xs = true)

/-- Bounded sweep of arithmetic inputs, including the empty list and reversals. -/
def rangeShift (n : Nat) : List Int :=
  (List.range n).map fun i => Int.ofNat i - Int.ofNat (n / 2)

example : (List.range 12).all (fun n =>
    check_post (rangeShift n) && check_post (rangeShift n).reverse &&
      check_singleton (Int.ofNat n) && check_pair (Int.ofNat n) (-Int.ofNat n)) = true := by
  native_decide

/-! ## Correctness -/

theorem benchmark_median_low_spec_thm (data : List α) :
    Post_prop data (benchmark_median_low data) :=
  ⟨empty_error_thm data, sorted_index_thm data, odd_middle_thm data, even_low_middle_thm data,
    mem_thm data, lower_count_thm data, upper_count_thm data, le_high_median_thm data,
    perm_invariance_thm data, unique_low_median_thm data, agrees_with_median_low_thm data⟩

/-- `Pre` implies the post-condition of `benchmark_median_low`. -/
theorem benchmark_median_low_correctness_thm (data : List α) (h : Pre data) :
    Post_prop data (benchmark_median_low data) :=
  benchmark_median_low_spec_thm data

/-- The same contract at `ℝ` (non-executable comparisons; proved by the polymorphic theorem). -/
theorem benchmark_median_low_correctness_real_thm (data : List ℝ) (h : Pre data) :
    Post_prop data (benchmark_median_low data) :=
  benchmark_median_low_correctness_thm data h

/-- The same contract at `ℚ`. -/
theorem benchmark_median_low_correctness_rat_thm (data : List ℚ) (h : Pre data) :
    Post_prop data (benchmark_median_low data) :=
  benchmark_median_low_correctness_thm data h

/-! ## Imperative implementation

Insertion sort with a mutable accumulator, then the Python odd/even index branch.
Inserting from the right matches `List.insertionSort`, which equals `mergeSort` on a
linear order, so the imperative code returns the same value as `median_low`.
-/

def insertionSortImp (data : List α) : List α :=
  Id.run do
    let mut sorted : List α := []
    for x in data.reverse do
      sorted := List.orderedInsert (· ≤ ·) x sorted
    return sorted

theorem insertionSort_eq_foldr (data : List α) :
    List.insertionSort (· ≤ ·) data =
      data.foldr (fun x acc => List.orderedInsert (· ≤ ·) x acc) [] := by
  induction data with
  | nil => simp [List.insertionSort, List.foldr]
  | cons a l ih => simp [List.insertionSort, List.foldr, ih]

theorem insertionSortImp_eq (data : List α) :
    insertionSortImp data = List.insertionSort (· ≤ ·) data := by
  unfold insertionSortImp
  simp [List.foldl_reverse, insertionSort_eq_foldr]

def median_low_imp (data : List α) : Except String α :=
  Id.run do
    let sorted := insertionSortImp data
    let mut n := sorted.length
    if n == 0 then
      return .error emptyMedianMsg
    let mut idx : Nat := 0
    if n % 2 == 1 then
      idx := n / 2
    else
      idx := n / 2 - 1
    match sorted[idx]? with
    | some m => return .ok m
    | none => return .error emptyMedianMsg

def benchmark_median_low_imp (data : List α) : Except String α :=
  Id.run do
    if data.isEmpty then
      return .error benchmarkPreMsg
    return median_low_imp data

theorem median_low_imp_expand (data : List α) :
    median_low_imp data =
      let sorted := List.insertionSort (· ≤ ·) data
      let n := sorted.length
      if n = 0 then .error emptyMedianMsg
      else if n % 2 = 1 then
        match sorted[n / 2]? with
        | some m => .ok m
        | none => .error emptyMedianMsg
      else
        match sorted[n / 2 - 1]? with
        | some m => .ok m
        | none => .error emptyMedianMsg := by
  unfold median_low_imp insertionSortImp
  simp [List.foldl_reverse, insertionSort_eq_foldr]
  dsimp [Id.run]
  simp [Id.instMonad]
  rfl

theorem median_low_equiv_thm (data : List α) : median_low data = median_low_imp data := by
  rw [median_low_imp_expand, ← sortedList_eq_insertionSort]
  unfold median_low
  by_cases h0 : (sortedList data).length = 0
  · simp [h0]
  · simp only [h0, dite_false]
    by_cases hodd : (sortedList data).length % 2 = 1
    · simp only [hodd, ite_true]
      have hlt := odd_branch_lt hodd
      rw [getElem?_pos (sortedList data) ((sortedList data).length / 2) hlt]
      simp
      apply congrArg Except.ok
      exact getElem_eq_of_idx_eq (lowMedianIndex_of_odd hodd).symm
        (lowMedianIndex_lt (Nat.pos_of_ne_zero h0)) hlt
    · simp only [hodd, ite_false]
      have hlt := even_branch_lt h0 hodd
      have hpos : 0 < (sortedList data).length := Nat.pos_of_ne_zero h0
      have heven : (sortedList data).length % 2 = 0 := by
        have := Nat.mod_two_eq_zero_or_one (sortedList data).length
        omega
      rw [getElem?_pos (sortedList data) ((sortedList data).length / 2 - 1) hlt]
      simp
      apply congrArg Except.ok
      exact getElem_eq_of_idx_eq (lowMedianIndex_of_even hpos heven).symm
        (lowMedianIndex_lt hpos) hlt

theorem benchmark_median_low_equiv_thm (data : List α) :
    benchmark_median_low data = benchmark_median_low_imp data := by
  cases h : data.isEmpty
  · have hne : data ≠ [] := by simpa [List.isEmpty_iff] using h
    rw [benchmark_median_low_of_ne_nil data hne, median_low_equiv_thm]
    unfold benchmark_median_low_imp
    simp [h, Id.run, Id.instMonad]
  · have hempty : data = [] := by simpa [List.isEmpty_iff] using h
    subst hempty
    rw [benchmark_median_low_empty]
    unfold benchmark_median_low_imp
    simp [Id.run, Id.instMonad]

/-! ## Imperative tests -/

example : benchmark_median_low_imp ([1, 3, 5] : List Int) = .ok 3 := by native_decide

example : benchmark_median_low_imp ([1, 2, 3, 4, 5, 6, 9] : List Int) = .ok 4 := by native_decide

example : benchmark_median_low_imp ([1, 3, 5, 7] : List Int) = .ok 3 := by native_decide

example : benchmark_median_low_imp ([1, 2, 3, 4, 5, 6] : List Int) = .ok 3 := by native_decide

example : benchmark_median_low_imp ([42] : List Int) = .ok 42 := by native_decide

example : benchmark_median_low_imp ([10, 20] : List Int) = .ok 10 := by native_decide

example : benchmark_median_low_imp ([9, 1, 6, 2, 5, 4, 3] : List Int) = .ok 4 := by native_decide

example : benchmark_median_low_imp ([-5, -1, 0, 3, 7] : List Int) = .ok 0 := by native_decide

example : benchmark_median_low_imp ([-10, -5, 5, 10] : List Int) = .ok (-5) := by native_decide

example : benchmark_median_low_imp ([] : List Int) = .error benchmarkPreMsg := by native_decide

example : median_low_imp ([] : List Int) = .error emptyMedianMsg := by native_decide

#eval benchmark_median_low_imp ([1, 3, 5, 7] : List Int)

#eval benchmark_median_low_imp ([9, 1, 6, 2, 5, 4, 3] : List Int)

#eval median_low_imp ([-10, -5, 5, 10] : List Int)

#eval benchmark_median_low_imp ([] : List Int)

end «28_statistics_median_low»

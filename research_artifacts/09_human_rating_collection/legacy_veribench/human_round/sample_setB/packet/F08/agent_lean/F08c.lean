import Mathlib

/-!
# VeriBench 28 — CPython `statistics.median_low`

The Python program returns the *low median* of numeric data:

```python
data = sorted(data)
n = len(data)
if n == 0: raise StatisticsError("no median for empty data")
if n % 2 == 1: return data[n // 2]
else:          return data[n // 2 - 1]
```

`benchmark_median_low` first checks `pre(data)` (a non-empty `list`/`tuple` of
`numbers.Number`) and raises `StatisticsError` otherwise.

## Modelling decisions

* The Python function is generic in the numeric type (`numbers.Number`), so the
  functional implementation `MedianLow` is defined for an arbitrary `LinearOrder α`.
  The *executable* layer used by `#eval`, `native_decide` and the imperative
  implementation is `α = Int` (every Python unit test uses integers).  The exact
  mathematical layers `RatLayer` and `RealLayer` instantiate the same generic
  theorems at `Rat` and `Real`; `FloatLayer` grounds the floating point reading of
  the docstring examples.  No obligation is dropped when moving between layers: the
  theorems are stated once generically and specialised.
* Python's `sorted(data)` is modelled by `sortedOf data = data.mergeSort (· ≤ ·)`.
  The core/Mathlib theory of `mergeSort` matches `sorted` exactly: same length
  (`sortedOf_length`), same elements (`mem_sortedOf`, `sortedOf_perm`), ascending
  order (`sortedOf_sorted`), and the identity on already sorted input
  (`sortedOf_eq_self`).
* Both parities are covered by the single index `lowMedianIdx n = (n - 1) / 2`
  (`n // 2` for odd `n`, `n // 2 - 1` for even `n`), proved in `lowMedianIdx_eq`.
* Python's `StatisticsError` is modelled by the inductive type `StatisticsError`;
  at the functional layer the exceptional result is `none : Option α`, at the entry
  point `benchmarkMedianLow` it is `throw StatisticsError.…`.
* The "low" semantics (return an *element* of the data, and for even length the
  *smaller* of the two middle ones) is captured by counting predicates:
  with `k = (n - 1) / 2`, `#{x < m} ≤ k < #{x ≤ m}`; the parity specialisations
  `MedianLow_odd` / `MedianLow_even` restate this in the form of the docstring.
-/

set_option maxHeartbeats 400000

namespace «28_statistics_median_low»

open List

/-! ## Python's `StatisticsError` -/

/-- Mirror of Python's `statistics.StatisticsError` (a `ValueError` subclass). -/
inductive StatisticsError where
  /-- raised by `median_low` when the data is empty -/
  | noMedian : StatisticsError
  /-- raised by `benchmark_median_low` when `pre(data)` fails -/
  | invalidData : StatisticsError
  deriving DecidableEq, Repr, Inhabited

/-- Decidable equality for the result type of `benchmarkMedianLow`
(core provides no `DecidableEq` instance for `Except`), so that the tests below can
be discharged by `native_decide`. -/
instance : DecidableEq (Except StatisticsError Int)
  | .ok x, .ok y =>
    if h : x = y then .isTrue (by rw [h]) else .isFalse (fun hh => h (Except.ok.inj hh))
  | .error e, .error f =>
    if h : e = f then .isTrue (by rw [h]) else .isFalse (fun hh => h (Except.error.inj hh))
  | .ok _, .error _ => .isFalse (fun hh => by cases hh)
  | .error _, .ok _ => .isFalse (fun hh => by cases hh)

/-! ## Functional implementation -/

section Functional

variable {α : Type*} [LinearOrder α]

/-- Model of Python's `sorted(data)`. -/
def sortedOf (data : List α) : List α := data.mergeSort (· ≤ ·)

/-- Index of the low median in a sorted list of length `n`:
Python returns `data[n // 2]` for odd `n` and `data[n // 2 - 1]` for even `n`. -/
def lowMedianIdx (n : Nat) : Nat := if n % 2 == 1 then n / 2 else n / 2 - 1

theorem lowMedianIdx_eq (n : Nat) (h : n ≠ 0) : lowMedianIdx n = (n - 1) / 2 := by
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases h2 with h2 | h2 <;> simp [lowMedianIdx, h2] <;> omega

theorem lowMedianIdx_lt (n : Nat) (h : n ≠ 0) : lowMedianIdx n < n := by
  rw [lowMedianIdx_eq n h]; omega

/-- Model of the body of `median_low` applied to an already sorted list;
`none` represents `raise StatisticsError`. -/
def lowOfSorted (s : List α) : Option α :=
  if h : s.length = 0 then none
  else some (s[lowMedianIdx s.length]'(lowMedianIdx_lt _ h))

/-- Index of the *high* median (`n // 2`), used only to state `low ≤ high`. -/
def highOfSorted (s : List α) : Option α :=
  if h : s.length = 0 then none
  else some (s[s.length / 2]'(Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)))

/-- Model of Python's `statistics.median_low`. -/
def MedianLow (data : List α) : Option α := lowOfSorted (sortedOf data)

/-- Model of Python's `statistics.median_high` (only used for `low ≤ high`). -/
def MedianHigh (data : List α) : Option α := highOfSorted (sortedOf data)

end Functional

/-- The executable integer layer of `median_low` (all Python unit tests use `int`). -/
def medianLow (data : List Int) : Option Int := MedianLow data

/-- The executable integer layer of `median_high`. -/
def medianHigh (data : List Int) : Option Int := MedianHigh data

/-! ## Unit tests (mirroring Python's `check`) -/

#eval medianLow [1, 3, 5]
#eval medianLow [1, 2, 3, 4, 5, 6, 9]
#eval medianLow [1, 3, 5, 7]
#eval medianLow [1, 2, 3, 4, 5, 6]
#eval medianLow [42]
#eval medianLow [10, 20]
#eval medianLow [9, 1, 6, 2, 5, 4, 3]
#eval medianLow [-5, -1, 0, 3, 7]
#eval medianLow [-10, -5, 5, 10]
#eval medianLow ([] : List Int)
#eval medianHigh [1, 3, 5, 7]

-- 1. odd number of elements (returns the middle value)
example : medianLow [1, 3, 5] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
-- 2. even number of elements (returns the smaller of the two middle values)
example : medianLow [1, 3, 5, 7] = some 3 := by native_decide
example : medianLow [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
-- 3. single value
example : medianLow [42] = some 42 := by native_decide
-- 4. two values
example : medianLow [10, 20] = some 10 := by native_decide
-- 5. unsorted input
example : medianLow [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
-- 6. negative values
example : medianLow [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLow [-10, -5, 5, 10] = some (-5) := by native_decide
-- 7. error case
example : medianLow ([] : List Int) = none := by native_decide
-- the high median is the larger middle value
example : medianHigh [1, 3, 5, 7] = some 5 := by native_decide
example : medianHigh [1, 3, 5] = some 3 := by native_decide

/-! ## Pre-condition and the Python entry point -/

/-- Model of Python's `pre(data)`: `data` must be a non-empty `list`/`tuple` of numbers.
The "is a list of numbers" part is discharged by the type `List Int` of the executable
layer (and `List Rat` / `List Real` / `List Float` of the mathematical layers), so what
remains to check is non-emptiness. -/
def Pre (data : List Int) : Prop := data ≠ []

/-- Model of Python's `benchmark_median_low`. -/
def benchmarkMedianLow (data : List Int) : Except StatisticsError Int :=
  if data = [] then throw StatisticsError.invalidData
  else
    match medianLow data with
    | some m => .ok m
    | none => throw StatisticsError.noMedian

#eval match benchmarkMedianLow [1, 3, 5, 7] with
  | .ok m => s!"ok {m}"
  | .error _ => "StatisticsError"

#eval match benchmarkMedianLow [] with
  | .ok m => s!"ok {m}"
  | .error _ => "StatisticsError"

example : benchmarkMedianLow [1, 3, 5, 7] = .ok 3 := by native_decide
example : benchmarkMedianLow [] = throw StatisticsError.invalidData := by native_decide
example : benchmarkMedianLow [42] = .ok 42 := by native_decide

/-! ## Generic theory of the functional implementation -/

section Theory

variable {α : Type*} [LinearOrder α]

theorem sortedOf_length (data : List α) : (sortedOf data).length = data.length := by simp [sortedOf]

theorem sortedOf_sorted (data : List α) : List.Sorted (· ≤ ·) (sortedOf data) := by
  show List.Sorted (· ≤ ·) (data.mergeSort (· ≤ ·))
  exact List.sorted_mergeSort' (r := (· ≤ ·)) data

theorem sortedOf_perm (data : List α) : (sortedOf data).Perm data := List.mergeSort_perm _ _

theorem mem_sortedOf {x : α} {data : List α} : x ∈ sortedOf data ↔ x ∈ data := List.mem_mergeSort

/-- `sorted` is the identity on already sorted input. -/
theorem sortedOf_eq_self {data : List α} (h : List.Sorted (· ≤ ·) data) : sortedOf data = data := by
  show data.mergeSort (· ≤ ·) = data
  exact List.mergeSort_eq_self (r := (· ≤ ·)) h

/-- Two sorted lists with the same elements coincide; used to relate the functional
(merge sort) and the imperative (insertion sort) implementations. -/
theorem sorted_perm_eq {l₁ l₂ : List α} (h₁ : List.Sorted (· ≤ ·) l₁) (h₂ : List.Sorted (· ≤ ·) l₂)
    (hp : l₁.Perm l₂) : l₁ = l₂ := List.eq_of_perm_of_sorted hp h₁ h₂

theorem getElem_congr {s : List α} {i j : Nat} (hi : i < s.length) (hj : j < s.length) (h : i = j) :
    s[i]'hi = s[j]'hj := by subst h; rfl

theorem lowOfSorted_eq_none_iff {s : List α} : lowOfSorted s = none ↔ s.length = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [lowOfSorted, dif_neg hne] at h
    exact Option.noConfusion h
  · intro h
    rw [lowOfSorted, dif_pos h]

theorem lowOfSorted_eq_some {s : List α} (h : s.length ≠ 0) :
    lowOfSorted s = some (s[lowMedianIdx s.length]'(lowMedianIdx_lt _ h)) := by
  rw [lowOfSorted, dif_neg h]

theorem highOfSorted_eq_some {s : List α} (h : s.length ≠ 0) :
    highOfSorted s = some (s[s.length / 2]'(Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))) := by
  rw [highOfSorted, dif_neg h]

/-- `median_low` returns `none` exactly on empty data (Python raises `StatisticsError`). -/
theorem MedianLow_eq_none_iff (data : List α) : MedianLow data = none ↔ data = [] := by
  simp only [MedianLow, lowOfSorted_eq_none_iff, sortedOf_length, List.length_eq_zero_iff]

theorem MedianLow_some_iff (data : List α) : (∃ m, MedianLow data = some m) ↔ data ≠ [] := by
  constructor
  · rintro ⟨m, hm⟩ h
    rw [(MedianLow_eq_none_iff data).mpr h] at hm
    exact Option.noConfusion hm
  · intro h
    have hlen : (sortedOf data).length ≠ 0 := by simpa [sortedOf_length] using h
    exact ⟨_, lowOfSorted_eq_some hlen⟩

/-- In a sorted list, at most `k` elements are strictly below the element at index `k`. -/
theorem countP_lt_getElem_le (s : List α) (hs : List.Sorted (· ≤ ·) s) (k : Nat) (hk : k < s.length)
    (m : α) (hm : m = s[k]'hk) : s.countP (· < m) ≤ k := by
  have h1 : s.take (k + 1) = s.take k ++ [m] := by
    rw [List.take_succ_eq_append_getElem hk, ← hm]
  have hmem : m ∈ s.take (k + 1) := by
    rw [h1]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hdrop : (s.drop (k + 1)).countP (· < m) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy hlt
    have hlt' : y < m := by simpa using hlt
    exact absurd (List.Sorted.rel_of_mem_take_of_mem_drop hs hmem hy) (not_le_of_gt hlt')
  have hsing : ([m] : List α).countP (· < m) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy hlt
    simp at hy; subst hy
    simp at hlt
  have htake : (s.take (k + 1)).countP (· < m) ≤ k := by
    rw [h1, List.countP_append, hsing, Nat.add_zero]
    exact le_trans List.countP_le_length (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have h2 : s = s.take (k + 1) ++ s.drop (k + 1) := (List.take_append_drop (k + 1) s).symm
  rw [h2, List.countP_append, hdrop, Nat.add_zero]
  exact htake

/-- In a sorted list, at least `k + 1` elements are at most the element at index `k`. -/
theorem countP_le_getElem (s : List α) (hs : List.Sorted (· ≤ ·) s) (k : Nat) (hk : k < s.length)
    (m : α) (hm : m = s[k]'hk) : k + 1 ≤ s.countP (· ≤ m) := by
  have h1 : s.take (k + 1) = s.take k ++ [m] := by
    rw [List.take_succ_eq_append_getElem hk, ← hm]
  have hmk : m ∈ s.drop k := by
    have h0 : 0 < (s.drop k).length := by rw [List.length_drop]; omega
    have heq : (s.drop k)[0]'h0 = m := by
      rw [hm, List.getElem_drop]
      simp
    exact List.mem_iff_getElem.mpr ⟨0, h0, heq⟩
  have htake : (s.take k).countP (· ≤ m) = (s.take k).length := by
    rw [List.countP_eq_length]
    intro x hx
    have := List.Sorted.rel_of_mem_take_of_mem_drop hs hx hmk
    simpa using this
  have h2 : s = s.take (k + 1) ++ s.drop (k + 1) := (List.take_append_drop (k + 1) s).symm
  have hsing : ([m] : List α).countP (· ≤ m) = 1 := by
    rw [List.countP_singleton, if_pos (by simp)]
  calc k + 1 ≤ (s.take k).length + 1 := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    _ = (s.take k).countP (· ≤ m) + 1 := by rw [htake]
    _ ≤ (s.take (k + 1)).countP (· ≤ m) := by rw [h1, List.countP_append, hsing]
    _ ≤ s.countP (· ≤ m) := by
        conv_rhs => rw [← List.take_append_drop (k + 1) s]
        rw [List.countP_append]
        omega

theorem countP_ge_eq (l : List α) (m : α) : l.countP (· ≥ m) = l.countP (fun x => m ≤ x) :=
  (List.Perm.refl l).countP_congr (fun _ _ => rfl)

/-- `#{x | x < m} + #{x | m ≤ x} = n`: the two predicates are complementary. -/
theorem countP_lt_add_countP_le (l : List α) (m : α) :
    l.countP (· < m) + l.countP (fun x => m ≤ x) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a < m
    · have h1 : decide (a < m) = true := by simp [h]
      have h2 : decide (m ≤ a) = false := by simp [not_le_of_gt h]
      simp [h1, h2, ih]
      try omega
    · have h1 : decide (a < m) = false := by simp [h]
      have h2 : decide (m ≤ a) = true := by simp [le_of_not_lt h]
      simp [h1, h2, ih]
      try omega

/-- Main specification of `median_low`: on non-empty data it returns an element of the
data whose rank is `(n - 1) / 2`, i.e. the *low* median. -/
theorem MedianLow_spec (data : List α) (h : data ≠ []) :
    ∃ m, MedianLow data = some m ∧ m ∈ data ∧
        data.countP (· < m) ≤ (data.length - 1) / 2 ∧
        (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m) := by
  have hl : data.length ≠ 0 := fun hh => h (by simpa using hh)
  have hlen : (sortedOf data).length ≠ 0 := by rwa [sortedOf_length]
  have hk : lowMedianIdx (sortedOf data).length < (sortedOf data).length := lowMedianIdx_lt _ hlen
  have hidx : lowMedianIdx (sortedOf data).length = (data.length - 1) / 2 := by
    rw [lowMedianIdx_eq _ hlen, sortedOf_length]
  refine ⟨(sortedOf data)[lowMedianIdx (sortedOf data).length]'hk,
    lowOfSorted_eq_some hlen, ?_, ?_, ?_⟩
  · exact mem_sortedOf.mp (List.mem_iff_getElem.mpr ⟨_, hk, rfl⟩)
  · have h1 := countP_lt_getElem_le (sortedOf data) (sortedOf_sorted data) _ hk _ rfl
    have h2 := (sortedOf_perm data).countP_eq
      (· < (sortedOf data)[lowMedianIdx (sortedOf data).length]'hk)
    calc data.countP (· < (sortedOf data)[lowMedianIdx (sortedOf data).length]'hk)
        = (sortedOf data).countP
            (· < (sortedOf data)[lowMedianIdx (sortedOf data).length]'hk) := h2.symm
      _ ≤ lowMedianIdx (sortedOf data).length := h1
      _ = (data.length - 1) / 2 := hidx
  · have h1 := countP_le_getElem (sortedOf data) (sortedOf_sorted data) _ hk _ rfl
    have h2 := (sortedOf_perm data).countP_eq
      (· ≤ (sortedOf data)[lowMedianIdx (sortedOf data).length]'hk)
    calc (data.length - 1) / 2 + 1 = lowMedianIdx (sortedOf data).length + 1 := by rw [hidx]
      _ ≤ (sortedOf data).countP
            (· ≤ (sortedOf data)[lowMedianIdx (sortedOf data).length]'hk) := h1
      _ = data.countP (· ≤ (sortedOf data)[lowMedianIdx (sortedOf data).length]'hk) := h2

theorem MedianLow_mem (data : List α) {m : α} (hm : MedianLow data = some m) : m ∈ data := by
  by_cases hlen : (sortedOf data).length = 0
  · rw [MedianLow, lowOfSorted, dif_pos hlen] at hm
    exact absurd hm.symm (by simp)
  · rw [MedianLow, lowOfSorted_eq_some hlen] at hm
    obtain rfl := Option.some_inj.mp hm
    exact mem_sortedOf.mp (List.mem_iff_getElem.mpr ⟨_, lowMedianIdx_lt _ hlen, rfl⟩)

theorem MedianLow_rank (data : List α) (h : data ≠ []) {m : α} (hm : MedianLow data = some m) :
    data.countP (· < m) ≤ (data.length - 1) / 2 ∧
    (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m) := by
  obtain ⟨m', hm', _, hlt, hle⟩ := MedianLow_spec data h
  rw [hm] at hm'
  obtain rfl := Option.some_inj.mp hm'
  exact ⟨hlt, hle⟩

/-- Odd length: the middle value is returned, so at least `(n + 1) / 2` data points are
`≤ m` and at least `(n + 1) / 2` are `≥ m`. -/
theorem MedianLow_odd (data : List α) (hodd : data.length % 2 = 1) {m : α}
    (hm : MedianLow data = some m) :
    (data.length + 1) / 2 ≤ data.countP (· ≤ m) ∧
    (data.length + 1) / 2 ≤ data.countP (· ≥ m) := by
  have hne : data ≠ [] := by intro hh; simp [hh] at hodd
  have hr := MedianLow_rank data hne hm
  have h1 : (data.length + 1) / 2 = (data.length - 1) / 2 + 1 := by omega
  have h2 : data.countP (· ≥ m) = data.length - data.countP (· < m) := by
    rw [countP_ge_eq]
    have := countP_lt_add_countP_le data m
    omega
  exact ⟨by omega, by omega⟩

/-- Even length: the *smaller* of the two middle values is returned. -/
theorem MedianLow_even (data : List α) (h : data ≠ []) (heven : data.length % 2 = 0) {m : α}
    (hm : MedianLow data = some m) :
    data.length / 2 ≤ data.countP (· ≤ m) ∧
    data.length / 2 + 1 ≤ data.countP (· ≥ m) := by
  have hl : data.length ≠ 0 := fun hh => h (by simpa using hh)
  have hr := MedianLow_rank data h hm
  have h1 : (data.length - 1) / 2 + 1 = data.length / 2 := by omega
  have h2 : data.countP (· ≥ m) = data.length - data.countP (· < m) := by
    rw [countP_ge_eq]
    have := countP_lt_add_countP_le data m
    omega
  exact ⟨by omega, by omega⟩

/-- `median_low` only depends on the multiset of the data, because Python sorts first. -/
theorem MedianLow_perm (data data' : List α) (hp : data.Perm data') :
    MedianLow data = MedianLow data' := by
  have hsorted : sortedOf data = sortedOf data' :=
    sorted_perm_eq (sortedOf_sorted data) (sortedOf_sorted data')
      ((sortedOf_perm data).trans (hp.trans (sortedOf_perm data').symm))
  simp only [MedianLow, hsorted]

/-- On already sorted data the result is the element at index `(n - 1) / 2`. -/
theorem MedianLow_sorted (data : List α) (h : data ≠ []) (hs : List.Sorted (· ≤ ·) data) :
    MedianLow data = data[(data.length - 1) / 2]? := by
  have hl : data.length ≠ 0 := fun hh => h (by simpa using hh)
  have hk : (data.length - 1) / 2 < data.length := by omega
  have h1 : MedianLow data = some (data[lowMedianIdx data.length]'(lowMedianIdx_lt _ hl)) := by
    rw [MedianLow, sortedOf_eq_self hs, lowOfSorted, dif_neg hl]
  have hget : data[(data.length - 1) / 2]? =
      some (data[lowMedianIdx data.length]'(lowMedianIdx_lt _ hl)) :=
    List.getElem?_eq_some_iff.mpr
      ⟨hk, getElem_congr hk (lowMedianIdx_lt _ hl) (lowMedianIdx_eq _ hl).symm⟩
  rw [h1, hget]

/-- The low median never exceeds the high median (`median_low ≤ median_high`). -/
theorem MedianLow_le_MedianHigh (data : List α) (h : data ≠ []) {ml mh : α}
    (hl : MedianLow data = some ml) (hh : MedianHigh data = some mh) : ml ≤ mh := by
  have hl0 : data.length ≠ 0 := fun hh0 => h (by simpa using hh0)
  have hlen : (sortedOf data).length ≠ 0 := by rwa [sortedOf_length]
  have hkl : lowMedianIdx (sortedOf data).length < (sortedOf data).length := lowMedianIdx_lt _ hlen
  have hkh : (sortedOf data).length / 2 < (sortedOf data).length :=
    Nat.div_lt_self (Nat.pos_of_ne_zero hlen) (by decide)
  have e1 : ml = (sortedOf data)[lowMedianIdx (sortedOf data).length]'hkl := by
    rw [MedianLow, lowOfSorted, dif_neg hlen] at hl
    exact (Option.some_inj.mp hl).symm
  have e2 : mh = (sortedOf data)[(sortedOf data).length / 2]'hkh := by
    rw [MedianHigh, highOfSorted, dif_neg hlen] at hh
    exact (Option.some_inj.mp hh).symm
  subst e1; subst e2
  apply List.Sorted.rel_get_of_le (sortedOf_sorted data)
  rw [Fin.mk_le_mk, lowMedianIdx_eq _ hlen]
  omega

theorem MedianLow_singleton (a : α) : MedianLow [a] = some a := by
  have hlen : (sortedOf [a]).length ≠ 0 := by simp [sortedOf]
  rw [MedianLow, lowOfSorted, dif_neg hlen]
  simp [sortedOf, lowMedianIdx]

/-- For two data points the low median is the smaller one. -/
theorem MedianLow_pair (a b : α) : MedianLow [a, b] = some (min a b) := by
  by_cases hab : a ≤ b
  · have hsort : List.Sorted (· ≤ ·) ([a, b] : List α) :=
      List.sorted_cons.mpr ⟨fun _ hx => by
        simp at hx
        subst hx
        exact hab, List.sorted_singleton _⟩
    have h1 := MedianLow_sorted [a, b] (by simp) hsort
    have h2 : ([a, b] : List α)[(List.length [a, b] - 1) / 2]? = some a := by simp
    rw [h1, h2, min_eq_left hab]
  · have hba : b ≤ a := le_of_lt (not_le.mp hab)
    have hsort : List.Sorted (· ≤ ·) ([b, a] : List α) :=
      List.sorted_cons.mpr ⟨fun _ hx => by
        simp at hx
        subst hx
        exact hba, List.sorted_singleton _⟩
    have h1 : MedianLow [a, b] = MedianLow [b, a] := MedianLow_perm _ _ (List.Perm.swap _ _ _)
    have h2 := MedianLow_sorted [b, a] (by simp) hsort
    have h3 : ([b, a] : List α)[(List.length [b, a] - 1) / 2]? = some b := by simp
    rw [h1, h2, h3, min_eq_right hba]

end Theory

/-! ## Properties of the implementation (executable integer layer) -/

/-- Property 1 — error behaviour: empty data raises `StatisticsError`. -/
def empty_prop : Prop :=
  medianLow [] = none ∧ benchmarkMedianLow [] = throw StatisticsError.invalidData

/-- Property 2 — a single data point is its own low median. -/
def singleton_prop : Prop := ∀ a : Int, medianLow [a] = some a

/-- Property 3 — two data points: the smaller one is returned (`data[n // 2 - 1]`). -/
def pair_prop : Prop := ∀ a b : Int, medianLow [a, b] = some (min a b)

/-- Property 4 — the returned value is always an element of the data. -/
def mem_prop : Prop :=
  ∀ data : List Int, Pre data → ∀ m, medianLow data = some m → m ∈ data

/-- Property 5 — a value is returned exactly when the pre-condition holds. -/
def some_iff_prop : Prop :=
  ∀ data : List Int, (∃ m, medianLow data = some m) ↔ Pre data

/-- Property 6 — rank characterisation of the *low* median: with `k = (n - 1) / 2`,
at most `k` data points are `< m` and at least `k + 1` are `≤ m`. -/
def rank_prop : Prop :=
  ∀ data : List Int, Pre data → ∀ m, medianLow data = some m →
    data.countP (· < m) ≤ (data.length - 1) / 2 ∧
    (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m)

/-- Property 7 — odd length: the middle value is returned. -/
def odd_prop : Prop :=
  ∀ data : List Int, data.length % 2 = 1 → ∀ m, medianLow data = some m →
    (data.length + 1) / 2 ≤ data.countP (· ≤ m) ∧
    (data.length + 1) / 2 ≤ data.countP (· ≥ m)

/-- Property 8 — even length: the *smaller* of the two middle values is returned. -/
def even_prop : Prop :=
  ∀ data : List Int, Pre data → data.length % 2 = 0 → ∀ m, medianLow data = some m →
    data.length / 2 ≤ data.countP (· ≤ m) ∧
    data.length / 2 + 1 ≤ data.countP (· ≥ m)

/-- Property 9 — invariance under reordering, because Python sorts the data first. -/
def perm_prop : Prop :=
  ∀ data data' : List Int, data.Perm data' → medianLow data = medianLow data'

/-- Property 10 — on already sorted data the result is the element at index `(n - 1) / 2`. -/
def sorted_prop : Prop :=
  ∀ data : List Int, Pre data → List.Sorted (· ≤ ·) data →
    medianLow data = data[(data.length - 1) / 2]?

/-- Property 11 — `median_low` never exceeds `median_high`. -/
def le_high_prop : Prop :=
  ∀ data : List Int, Pre data → ∀ ml mh,
    medianLow data = some ml → medianHigh data = some mh → ml ≤ mh

theorem empty_thm : empty_prop := by
  constructor
  · show MedianLow ([] : List Int) = none
    exact (MedianLow_eq_none_iff _).mpr rfl
  · rfl

theorem singleton_thm : singleton_prop := fun a => MedianLow_singleton a

theorem pair_thm : pair_prop := fun a b => MedianLow_pair a b

theorem mem_thm : mem_prop := fun data _ _ hm => MedianLow_mem data hm

theorem some_iff_thm : some_iff_prop := fun data => MedianLow_some_iff data

theorem rank_thm : rank_prop := fun data hd _ hm => MedianLow_rank data hd hm

theorem odd_thm : odd_prop := fun data hodd _ hm => MedianLow_odd data hodd hm

theorem even_thm : even_prop := fun data hd heven _ hm => MedianLow_even data hd heven hm

theorem perm_thm : perm_prop := fun data data' hp => MedianLow_perm data data' hp

theorem sorted_thm : sorted_prop := fun data hd hs => MedianLow_sorted data hd hs

theorem le_high_thm : le_high_prop :=
  fun data hd _ _ hl hh => MedianLow_le_MedianHigh data hd hl hh

/-! ## Post-condition -/

/-- Post-condition of `benchmark_median_low`: conjunction of the properties above,
relating the input `data` with the returned value `res`. -/
def Post_prop (data : List Int) (res : Except StatisticsError Int) : Prop :=
  (∃ m, res = .ok m ∧ m ∈ data ∧
      data.countP (· < m) ≤ (data.length - 1) / 2 ∧
      (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m)) ∧
  (data.length % 2 = 1 → ∀ m, res = .ok m →
      (data.length + 1) / 2 ≤ data.countP (· ≤ m) ∧
      (data.length + 1) / 2 ≤ data.countP (· ≥ m)) ∧
  (data.length % 2 = 0 → ∀ m, res = .ok m →
      data.length / 2 ≤ data.countP (· ≤ m) ∧
      data.length / 2 + 1 ≤ data.countP (· ≥ m))

/-! ## Property-based tests

Each executable property above is tested on many inputs: once exhaustively on a bounded
family of lists (`native_decide`, an `example` test) and once on random inputs
(`Plausible.Testable.check`, which fails to compile if a counterexample is found). -/

/-- Boolean form of `Pre`. -/
def preCheck (data : List Int) : Bool := 0 < data.length

/-- Boolean form of `empty_prop` / `some_iff_prop`. -/
def errCheck (data : List Int) : Bool := (medianLow data).isNone == (data.length == 0)

/-- Boolean form of `mem_prop` and `rank_prop` (first conjunct of `Post_prop`). -/
def rankCheck (data : List Int) : Bool :=
  match medianLow data with
  | none => data.length == 0
  | some m =>
      decide (m ∈ data) &&
      decide (data.countP (· < m) ≤ (data.length - 1) / 2) &&
      decide ((data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m))

/-- Boolean form of `odd_prop` and `even_prop` (second and third conjuncts of `Post_prop`). -/
def parityCheck (data : List Int) : Bool :=
  match medianLow data with
  | none => true
  | some m =>
    if data.length % 2 == 1 then
      decide ((data.length + 1) / 2 ≤ data.countP (· ≤ m)) &&
      decide ((data.length + 1) / 2 ≤ data.countP (· ≥ m))
    else
      decide (data.length / 2 ≤ data.countP (· ≤ m)) &&
      decide (data.length / 2 + 1 ≤ data.countP (· ≥ m))

/-- Boolean form of `le_high_prop`. -/
def highCheck (data : List Int) : Bool :=
  match medianLow data, medianHigh data with
  | some ml, some mh => decide (ml ≤ mh)
  | none, none => data.length == 0
  | _, _ => false

/-- Boolean form of `perm_prop` (reversal is a permutation). -/
def permCheck (data : List Int) : Bool := medianLow data == medianLow data.reverse

/-- Boolean form of `sorted_prop`. -/
def sortedCheck (data : List Int) : Bool :=
  if decide (List.Sorted (· ≤ ·) data) && 0 < data.length then
    medianLow data == data[(data.length - 1) / 2]?
  else true

/-- Boolean form of `singleton_prop` and `pair_prop`. -/
def smallCheck (data : List Int) : Bool :=
  match data with
  | [a] => medianLow [a] == some a
  | [a, b] => medianLow [a, b] == some (min a b)
  | _ => true

/-- Boolean form of the whole post-condition. -/
def postCheck (data : List Int) : Bool :=
  if data.length == 0 then
    benchmarkMedianLow data == throw StatisticsError.invalidData
  else
    match benchmarkMedianLow data with
    | .ok _ => rankCheck data && parityCheck data
    | .error _ => false

/-- A bounded family of test inputs: arithmetic progressions, constant lists,
alternating lists, lists with duplicates and negative numbers, of lengths `0 … 13`. -/
def pbtData : List (List Int) :=
  (List.range 14).map (fun n => (List.range n).map (fun i => ((i * 7) % (n + 5) : Int) - 4)) ++
  (List.range 14).map (fun n => (List.range n).map (fun i => (i : Int))) ++
  (List.range 14).map (fun n => (List.range n).map (fun i => (-(i : Int)))) ++
  (List.range 14).map (fun n => (List.range n).map (fun _ => (3 : Int))) ++
  [[], [5], [1, 2], [3, 1], [-1, -2, -3], [0, 0, 0], [10, -10, 10, -10], [1, 3, 5, 7],
   [9, 1, 6, 2, 5, 4, 3], [1, 2, 3, 4, 5, 6, 9], [-5, -1, 0, 3, 7], [-10, -5, 5, 10], [42],
   [10, 20]]

/-- Bounded PBT: every executable property holds on all inputs of `pbtData`. -/
example : pbtData.all (fun xs =>
    preCheck xs == (xs ≠ []) &&
    errCheck xs && rankCheck xs && parityCheck xs && highCheck xs &&
    permCheck xs && sortedCheck xs && smallCheck xs && postCheck xs) = true := by native_decide

-- Randomised PBTs (Plausible); the file fails to compile if a counterexample is found.
#eval Plausible.Testable.check (∀ xs : List Int, errCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, rankCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, parityCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, highCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, permCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, sortedCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, smallCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs = true)
#eval Plausible.Testable.check (∀ xs : List Int, preCheck xs == (xs != []))
#eval Plausible.Testable.check (∀ a b : Int, medianLow [a, b] = some (min a b))
#eval Plausible.Testable.check (∀ a : Int, medianLow [a] = some a)
#eval Plausible.Testable.check (∀ xs : List Int, (medianLow xs).isSome == decide (0 < xs.length))

/-! ## Correctness: `Pre → Post` -/

theorem correctness_thm (data : List Int) (h : Pre data) :
    Post_prop data (benchmarkMedianLow data) := by
  have hne : data ≠ [] := h
  obtain ⟨m, hm⟩ := (MedianLow_some_iff data).mpr hne
  have hres : benchmarkMedianLow data = .ok m := by
    have hm' : medianLow data = some m := hm
    simp [benchmarkMedianLow, if_neg hne, hm']
  have hrank := MedianLow_rank data hne hm
  have hmem := MedianLow_mem data hm
  rw [hres]
  refine ⟨⟨m, rfl, hmem, hrank.1, hrank.2⟩, ?_, ?_⟩
  · intro hodd m' hm'
    have heq : m' = m := by simpa using hm'.symm
    subst heq
    exact MedianLow_odd data hodd hm
  · intro heven m' hm'
    have heq : m' = m := by simpa using hm'.symm
    subst heq
    exact MedianLow_even data hne heven hm

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

section Imperative

/-- Inner step of an insertion sort: insert `x` into an ascending list. -/
def insertSorted (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- The imperative loop written as a left fold; used only to state loop invariants. -/
def insertionSortFn (data : List Int) : List Int :=
  data.foldl (fun acc y => insertSorted y acc) []

/-- Imperative insertion sort: a *mutable* accumulator updated inside a `for` loop. -/
def insertionSortImp (data : List Int) : List Int := Id.run do
  let mut acc : List Int := []
  for y in data do
    acc := insertSorted y acc
  return acc

theorem insertionSortImp_eq (data : List Int) : insertionSortImp data = insertionSortFn data := by
  simp [insertionSortImp, insertionSortFn]

theorem perm_insertSorted : ∀ (x : Int) (l : List Int), (insertSorted x l).Perm (x :: l) := by
  intro x l
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · next _ => exact List.Perm.refl _
    · next _ => exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem mem_insertSorted (l : List Int) (x b : Int) (hb : b ∈ insertSorted x l) :
    b = x ∨ b ∈ l := by
  have := (perm_insertSorted x l).mem_iff.mp hb
  simpa using this

theorem sorted_insertSorted : ∀ {l : List Int}, List.Sorted (· ≤ ·) l →
    ∀ x : Int, List.Sorted (· ≤ ·) (insertSorted x l) := by
  intro l
  induction l with
  | nil => intro _ x; exact List.sorted_singleton x
  | cons y ys ih =>
    intro hl x
    show List.Sorted (· ≤ ·) (if x ≤ y then x :: y :: ys else y :: insertSorted x ys)
    split
    · next hxy => exact List.Sorted.cons hxy hl
    · next hxy =>
      have hyx : y < x := not_le.mp hxy
      have h1 : List.Sorted (· ≤ ·) (insertSorted x ys) := ih (List.Sorted.of_cons hl) x
      have h2 : ∀ b ∈ insertSorted x ys, y ≤ b := by
        intro b hb
        rcases mem_insertSorted ys x b hb with rfl | hb'
        · exact le_of_lt hyx
        · exact (List.sorted_cons.mp hl).1 b hb'
      exact List.sorted_cons.mpr ⟨h2, h1⟩

theorem sorted_foldl_insertSorted : ∀ (acc : List Int), List.Sorted (· ≤ ·) acc →
    ∀ data : List Int, List.Sorted (· ≤ ·) (data.foldl (fun a y => insertSorted y a) acc) := by
  intro acc hacc data
  induction data generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih (insertSorted x acc) (sorted_insertSorted hacc x)

theorem perm_foldl_insertSorted : ∀ (acc : List Int) (data : List Int),
    (data.foldl (fun a y => insertSorted y a) acc).Perm (acc ++ data) := by
  intro acc data
  induction data generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    have h1 := ih (insertSorted x acc)
    have hA : ((insertSorted x acc) ++ xs).Perm ((x :: acc) ++ xs) :=
      List.Perm.append (perm_insertSorted x acc) (List.Perm.refl _)
    have hB : ((x :: acc) ++ xs).Perm (x :: (acc ++ xs)) :=
      List.Perm.of_eq rfl
    have hC : (x :: (acc ++ xs)).Perm ((acc ++ xs) ++ [x]) :=
      List.perm_append_comm (l₁ := [x]) (l₂ := acc ++ xs)
    have hD : ((acc ++ xs) ++ [x]).Perm (acc ++ (xs ++ [x])) :=
      List.Perm.of_eq (List.append_assoc acc xs [x])
    have hE : (acc ++ (xs ++ [x])).Perm (acc ++ (x :: xs)) :=
      List.Perm.append_left acc ((List.perm_append_comm (l₁ := [x]) (l₂ := xs)).symm)
    exact List.Perm.trans h1 (List.Perm.trans hA (List.Perm.trans hB (List.Perm.trans hC
      (List.Perm.trans hD hE))))

theorem sorted_insertionSortFn (data : List Int) :
    List.Sorted (· ≤ ·) (insertionSortFn data) :=
  sorted_foldl_insertSorted [] List.sorted_nil data

theorem perm_insertionSortFn (data : List Int) : (insertionSortFn data).Perm data := by
  have := perm_foldl_insertSorted [] data
  simpa [insertionSortFn] using this

/-- The imperative insertion sort produces exactly the list Python's `sorted` produces. -/
theorem insertionSortFn_eq_sortedOf (data : List Int) : insertionSortFn data = sortedOf data :=
  sorted_perm_eq (sorted_insertionSortFn data) (sortedOf_sorted data)
    ((perm_insertionSortFn data).trans (sortedOf_perm data).symm)

/-- Imperative tail: pick the low median out of the sorted accumulator.
The index `lowMedianIdx n` *is* Python's parity branch (`n // 2` for odd `n`,
`n // 2 - 1` for even `n`), and the empty accumulator takes the error path. -/
def lowOfSortedImp (acc : List Int) : Except StatisticsError Int :=
  let n := acc.length
  if n == 0 then throw StatisticsError.invalidData
  else
    match acc[lowMedianIdx n]? with
    | some m => .ok m
    | none => throw StatisticsError.noMedian

/-- Imperative implementation of `benchmark_median_low`: mutable accumulator, `for` loop,
early `return` on the error path. -/
def medianLowImp (data : List Int) : Except StatisticsError Int := Id.run do
  let mut acc : List Int := []
  for y in data do
    acc := insertSorted y acc
  return lowOfSortedImp acc

theorem medianLowImp_eq_fn (data : List Int) :
    medianLowImp data = lowOfSortedImp (insertionSortFn data) := by
  simp [medianLowImp, insertionSortFn]

theorem lowOfSortedImp_eq (acc : List Int) :
    lowOfSortedImp acc =
      match lowOfSorted acc with
      | none => throw StatisticsError.invalidData
      | some m => .ok m := by
  by_cases h : acc.length = 0
  · have hnil : acc = [] := by simpa using h
    subst hnil
    simp [lowOfSortedImp, lowOfSorted]
  · have hne : acc ≠ [] := fun hh => h (by simp [hh])
    have hk : lowMedianIdx acc.length < acc.length := lowMedianIdx_lt _ h
    have hget : acc[lowMedianIdx acc.length]? = some (acc[lowMedianIdx acc.length]'hk) :=
      List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
    have e1 : lowOfSortedImp acc = .ok (acc[lowMedianIdx acc.length]'hk) := by
      simp [lowOfSortedImp, h, hget]
    have e2 : lowOfSorted acc = some (acc[lowMedianIdx acc.length]'hk) := lowOfSorted_eq_some h
    simp [e1, e2]

end Imperative

/-! ## Imperative tests -/

#eval insertionSortImp [9, 1, 6, 2, 5, 4, 3]
#eval medianLowImp [1, 3, 5]
#eval medianLowImp [1, 3, 5, 7]
#eval medianLowImp ([] : List Int)

example : insertionSortImp [9, 1, 6, 2, 5, 4, 3] = [1, 2, 3, 4, 5, 6, 9] := by native_decide
example : insertionSortImp ([-5, -1, 0, 3, 7]) = [-5, -1, 0, 3, 7] := by native_decide
example : medianLowImp [1, 3, 5] = .ok 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6, 9] = .ok 4 := by native_decide
example : medianLowImp [1, 3, 5, 7] = .ok 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6] = .ok 3 := by native_decide
example : medianLowImp [42] = .ok 42 := by native_decide
example : medianLowImp [10, 20] = .ok 10 := by native_decide
example : medianLowImp [9, 1, 6, 2, 5, 4, 3] = .ok 4 := by native_decide
example : medianLowImp [-5, -1, 0, 3, 7] = .ok 0 := by native_decide
example : medianLowImp [-10, -5, 5, 10] = .ok (-5) := by native_decide
example : medianLowImp ([] : List Int) = throw StatisticsError.invalidData := by native_decide

/-- Imperative PBT: the imperative and the functional entry points agree on the whole
bounded family of inputs. -/
example : pbtData.all (fun xs => decide (medianLowImp xs = benchmarkMedianLow xs)) = true := by
  native_decide

#eval Plausible.Testable.check (∀ xs : List Int,
  decide (medianLowImp xs = benchmarkMedianLow xs) = true)

/-! ## Equivalence: functional = imperative -/

theorem equivalence_thm (data : List Int) : medianLowImp data = benchmarkMedianLow data := by
  rw [medianLowImp_eq_fn, insertionSortFn_eq_sortedOf, lowOfSortedImp_eq]
  by_cases h : data = []
  · subst h
    simp [benchmarkMedianLow, medianLow, MedianLow, lowOfSorted, lowOfSortedImp, sortedOf]
  · have hl : data.length ≠ 0 := fun hh => h (by simpa using hh)
    have hlen : (sortedOf data).length ≠ 0 := by rwa [sortedOf_length]
    simp [benchmarkMedianLow, medianLow, MedianLow, if_neg h, lowOfSorted_eq_some hlen,
      lowOfSortedImp]

/-! ## Exact mathematical layers

The Python program is generic in the numeric type (`numbers.Number`), so the very same
specification is instantiated at the exact mathematical layers `Rat` and `Real` and at the
IEEE-754 layer `Float`.  Each theorem below is literally the generic theorem of the `Theory` section specialised to that layer: nothing is weakened, narrowed or dropped.
-/

namespace RatLayer

theorem spec (data : List Rat) (h : data ≠ []) :
    ∃ m, MedianLow data = some m ∧ m ∈ data ∧
        data.countP (· < m) ≤ (data.length - 1) / 2 ∧
        (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m) := MedianLow_spec data h

theorem mem (data : List Rat) {m : Rat} (hm : MedianLow data = some m) : m ∈ data :=
  MedianLow_mem data hm

theorem rank (data : List Rat) (h : data ≠ []) {m : Rat} (hm : MedianLow data = some m) :
    data.countP (· < m) ≤ (data.length - 1) / 2 ∧
    (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m) := MedianLow_rank data h hm

theorem odd (data : List Rat) (hodd : data.length % 2 = 1) {m : Rat}
    (hm : MedianLow data = some m) :
    (data.length + 1) / 2 ≤ data.countP (· ≤ m) ∧
    (data.length + 1) / 2 ≤ data.countP (· ≥ m) := MedianLow_odd data hodd hm

theorem even (data : List Rat) (h : data ≠ []) (heven : data.length % 2 = 0) {m : Rat}
    (hm : MedianLow data = some m) :
    data.length / 2 ≤ data.countP (· ≤ m) ∧
    data.length / 2 + 1 ≤ data.countP (· ≥ m) := MedianLow_even data h heven hm

theorem perm (data data' : List Rat) (hp : data.Perm data') :
    MedianLow data = MedianLow data' := MedianLow_perm data data' hp

theorem none_iff (data : List Rat) : MedianLow data = none ↔ data = [] :=
  MedianLow_eq_none_iff data

theorem singleton (a : Rat) : MedianLow [a] = some a := MedianLow_singleton a

theorem pair (a b : Rat) : MedianLow [a, b] = some (min a b) := MedianLow_pair a b

theorem sorted (data : List Rat) (h : data ≠ []) (hs : List.Sorted (· ≤ ·) data) :
    MedianLow data = data[(data.length - 1) / 2]? := MedianLow_sorted data h hs

theorem le_high (data : List Rat) (h : data ≠ []) {ml mh : Rat}
    (hl : MedianLow data = some ml) (hh : MedianHigh data = some mh) : ml ≤ mh :=
  MedianLow_le_MedianHigh data h hl hh

-- ground tests on the exact rational layer
#eval MedianLow ([1, 3, 5] : List Rat)
#eval MedianLow ([1/3, 1/4] : List Rat)
example : MedianLow ([1, 3, 5] : List Rat) = some 3 := by native_decide
example : MedianLow ([1, 3, 5, 7] : List Rat) = some 3 := by native_decide
example : MedianLow ([1/2, 3/2, 5/2] : List Rat) = some (3/2) := by native_decide
example : MedianLow ([1/3, 1/4] : List Rat) = some (1/4) := by native_decide
example : MedianLow ([] : List Rat) = none := by native_decide

end RatLayer

namespace RealLayer

/-- The exact real layer.  `Real` is noncomputable, so this layer carries theorems
(the executable ground tests live on the `Int`, `Rat` and `Float` layers). -/
theorem spec (data : List Real) (h : data ≠ []) :
    ∃ m, MedianLow data = some m ∧ m ∈ data ∧
        data.countP (· < m) ≤ (data.length - 1) / 2 ∧
        (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m) := MedianLow_spec data h

theorem mem (data : List Real) {m : Real} (hm : MedianLow data = some m) : m ∈ data :=
  MedianLow_mem data hm

theorem rank (data : List Real) (h : data ≠ []) {m : Real} (hm : MedianLow data = some m) :
    data.countP (· < m) ≤ (data.length - 1) / 2 ∧
    (data.length - 1) / 2 + 1 ≤ data.countP (· ≤ m) := MedianLow_rank data h hm

theorem odd (data : List Real) (hodd : data.length % 2 = 1) {m : Real}
    (hm : MedianLow data = some m) :
    (data.length + 1) / 2 ≤ data.countP (· ≤ m) ∧
    (data.length + 1) / 2 ≤ data.countP (· ≥ m) := MedianLow_odd data hodd hm

theorem even (data : List Real) (h : data ≠ []) (heven : data.length % 2 = 0) {m : Real}
    (hm : MedianLow data = some m) :
    data.length / 2 ≤ data.countP (· ≤ m) ∧
    data.length / 2 + 1 ≤ data.countP (· ≥ m) := MedianLow_even data h heven hm

theorem perm (data data' : List Real) (hp : data.Perm data') :
    MedianLow data = MedianLow data' := MedianLow_perm data data' hp

theorem none_iff (data : List Real) : MedianLow data = none ↔ data = [] :=
  MedianLow_eq_none_iff data

theorem singleton (a : Real) : MedianLow [a] = some a := MedianLow_singleton a

theorem pair (a b : Real) : MedianLow [a, b] = some (min a b) := MedianLow_pair a b

theorem sorted (data : List Real) (h : data ≠ []) (hs : List.Sorted (· ≤ ·) data) :
    MedianLow data = data[(data.length - 1) / 2]? := MedianLow_sorted data h hs

theorem le_high (data : List Real) (h : data ≠ []) {ml mh : Real}
    (hl : MedianLow data = some ml) (hh : MedianHigh data = some mh) : ml ≤ mh :=
  MedianLow_le_MedianHigh data h hl hh

end RealLayer

namespace FloatLayer

/-!
### IEEE-754 layer

`Float` carries `LE`/`LT` and `DecidableRel` instances but *no* `LinearOrder` instance in
this environment (`≤` is not total once NaN is present), so the generic order-theoretic
theorems cannot be instantiated at `Float`.  This layer therefore grounds the floating
point reading of the docstring examples with an executable definition that runs exactly
the same algorithm -- merge sort by `≤`, then Python's parity branch -- together with the
structural facts that do not need order theory.  The exact mathematical obligations are
carried by the `Int`, `RatLayer` and `RealLayer` layers above.
-/

/-- Model of Python's `sorted(data)` for `float` data. -/
def floatSortedOf (data : List Float) : List Float := data.mergeSort (fun a b => a ≤ b)

/-- Model of `median_low` for `float` data. -/
def medianLowFloat (data : List Float) : Option Float :=
  if (floatSortedOf data).length = 0 then none
  else (floatSortedOf data)[lowMedianIdx (floatSortedOf data).length]?

theorem floatSortedOf_length (data : List Float) : (floatSortedOf data).length = data.length := by
  simp [floatSortedOf]

theorem medianLowFloat_none_iff (data : List Float) : medianLowFloat data = none ↔ data = [] := by
  constructor
  · intro h
    by_contra hne
    have hlen : (floatSortedOf data).length ≠ 0 := by
      rw [floatSortedOf_length]
      exact fun hh => hne (by simpa using hh)
    rw [medianLowFloat, if_neg hlen] at h
    exact Option.noConfusion h
  · intro h
    subst h
    simp [medianLowFloat, floatSortedOf]

theorem medianLowFloat_singleton (a : Float) : medianLowFloat [a] = some a := by
  have h1 : floatSortedOf [a] = [a] := by simp [floatSortedOf]
  simp [medianLowFloat, h1, lowMedianIdx]

theorem medianLowFloat_pair (a b : Float) :
    medianLowFloat [a, b] = (floatSortedOf [a, b])[0]? := by
  have hlen : (floatSortedOf [a, b]).length = 2 := by
    rw [floatSortedOf_length]
  simp [medianLowFloat, hlen, lowMedianIdx]

#eval medianLowFloat [1.0, 3.0, 5.0]
#eval medianLowFloat [1.0, 3.0, 5.0, 7.0]
#eval medianLowFloat [1.5, 2.5, 3.5]
#eval medianLowFloat [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
#eval medianLowFloat ([] : List Float)

example : medianLowFloat [1.0, 3.0, 5.0] = some 3.0 := by native_decide
example : medianLowFloat [1.0, 3.0, 5.0, 7.0] = some 3.0 := by native_decide
example : medianLowFloat [1.5, 2.5, 3.5] = some 2.5 := by native_decide
example : medianLowFloat [1.0, 2.0, 3.0, 4.0, 5.0, 6.0] = some 3.0 := by native_decide
example : medianLowFloat [-1.5, 0.0, 2.25, 7.5] = some 0.0 := by native_decide
example : medianLowFloat ([] : List Float) = none := by native_decide

/-- Bounded PBT on the floating point layer. -/
def floatPbtData : List (List Float) :=
  [[], [1.0], [3.0, 1.0], [1.0, 2.0, 3.0, 4.0], [1.5, 2.5, 3.5], [-1.5, 0.0, 2.25, 7.5],
   [1e10, -1e10], [0.5, 0.5, 0.5, 0.5], [2.0, 1.0], [-0.5]]

example : floatPbtData.all (fun xs =>
    (medianLowFloat xs).isNone == (xs.length == 0)) = true := by native_decide

example : floatPbtData.all (fun xs =>
    match medianLowFloat xs with
    | none => xs.length == 0
    | some m => decide (m ∈ floatSortedOf xs) &&
        decide ((floatSortedOf xs).countP (· < m) ≤ (xs.length - 1) / 2) &&
        decide ((xs.length - 1) / 2 + 1 ≤ (floatSortedOf xs).countP (· ≤ m))) = true := by
  native_decide

end FloatLayer

/-! ## Axiom audit -/

#print axioms correctness_thm
#print axioms equivalence_thm
#print axioms empty_thm
#print axioms singleton_thm
#print axioms pair_thm
#print axioms mem_thm
#print axioms some_iff_thm
#print axioms rank_thm
#print axioms odd_thm
#print axioms even_thm
#print axioms perm_thm
#print axioms sorted_thm
#print axioms le_high_thm
#print axioms MedianLow_spec
#print axioms RatLayer.spec
#print axioms RealLayer.spec
#print axioms FloatLayer.medianLowFloat_none_iff
#print axioms FloatLayer.medianLowFloat_pair

end «28_statistics_median_low»

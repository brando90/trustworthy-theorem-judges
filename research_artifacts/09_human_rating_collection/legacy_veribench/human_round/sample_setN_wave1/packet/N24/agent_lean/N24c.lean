import Mathlib

/-!
# `statistics.median_low` -- Python to Lean 4 translation (VeriBench task 28)

The Python program returns the *low median* of a non-empty sequence of numbers:

* the data is sorted (`data = sorted(data)`),
* if `n = len(data)` is odd, the middle element `data[n // 2]` is returned,
* if `n` is even, the smaller of the two middle elements `data[n // 2 - 1]` is returned,
* an empty sequence raises `StatisticsError("no median for empty data")`.

Both branches pick the element at index `(n - 1) / 2` of the sorted data, which is exactly
what `medianLow` below computes.  Its result type is `Option α`: `none` models Python's
`StatisticsError`, `some m` models a returned value.

The implementation is generic over any `LinearOrder α`.  This covers the `Int` data of the
Python unit tests (executable, `native_decide`-checkable) and, since every theorem below is
proved for an arbitrary linear order, it also covers the exact `Rat` / `Real` mathematical
models of the same intent (see the `RatLayer` / `RealLayer` sections at the end).

Python's `pre(data)` also checks that `data` is a list/tuple whose elements are
`numbers.Number`; in the typed Lean model every element of `List α` is a number by
construction, so the only remaining runtime obligation is non-emptiness, which is what
`Pre` states.
-/

namespace «28_statistics_median_low»

open List

set_option linter.unusedSectionVars false

section Generic

variable {α : Type*} [LinearOrder α]

/-! ## 4. Implementation (functional) -/

/-- Index of the low median inside a sorted list of length `n`.

Python uses `n // 2` when `n` is odd and `n // 2 - 1` when `n` is even; both are
`(n - 1) / 2`. -/
def medianIdx (n : Nat) : Nat := (n - 1) / 2

theorem medianIdx_lt (n : Nat) (hn : n ≠ 0) : medianIdx n < n := by
  rw [medianIdx]; omega

theorem medianIdx_odd (k : Nat) : medianIdx (2 * k + 1) = k := by
  rw [medianIdx]; omega

theorem medianIdx_even (k : Nat) : medianIdx (2 * k + 2) = k := by
  rw [medianIdx]; omega

theorem medianIdx_zero : medianIdx 0 = 0 := rfl

/-- The `if n % 2 == 1: n // 2 else: n // 2 - 1` shape used by the Python source. -/
theorem medianIdx_python (n : Nat) (hn : 0 < n) :
    medianIdx n = if n % 2 = 1 then n / 2 else n / 2 - 1 := by
  rw [medianIdx]; split_ifs with h <;> omega

/-- The two "halving" identities satisfied by `medianIdx`. -/
theorem medianIdx_halves (n : Nat) (hn : 0 < n) :
    medianIdx n + 1 = (n + 1) / 2 ∧ n - medianIdx n = n / 2 + 1 := by
  rw [medianIdx]; constructor <;> omega

/-- `sortedOf l` is `l` sorted in non-decreasing order -- Python's `sorted(data)`. -/
def sortedOf (l : List α) : List α := l.insertionSort (· ≤ ·)

theorem length_sortedOf (l : List α) : (sortedOf l).length = l.length := by
  simp [sortedOf]

theorem perm_sortedOf (l : List α) : sortedOf l ~ l :=
  List.perm_insertionSort (· ≤ ·) l

theorem sorted_sortedOf (l : List α) : Sorted (· ≤ ·) (sortedOf l) :=
  List.sorted_insertionSort (· ≤ ·) l

theorem sortedOf_eq_self {l : List α} (h : Sorted (· ≤ ·) l) : sortedOf l = l :=
  List.Sorted.insertionSort_eq h

/-- `sorted` only depends on the multiset of the data. -/
theorem sortedOf_perm {l₁ l₂ : List α} (h : l₁ ~ l₂) : sortedOf l₁ = sortedOf l₂ :=
  List.eq_of_perm_of_sorted
    ((perm_sortedOf l₁).trans (h.trans (perm_sortedOf l₂).symm))
    (sorted_sortedOf _) (sorted_sortedOf _)

/-- Two positions of a sorted list are ordered like their indices. -/
theorem sorted_getElem_le_getElem {s : List α} (hs : Sorted (· ≤ ·) s) {i j : Nat}
    (hi : i < s.length) (hj : j < s.length) (hij : i ≤ j) :
    s.get ⟨i, hi⟩ ≤ s.get ⟨j, hj⟩ :=
  hs.rel_get_of_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij

/-- Every element of the prefix `s.take (i+1)` is `≤ s[i]` when `s` is sorted. -/
theorem le_getElem_of_mem_take {s : List α} {i : Nat} (hi : i < s.length)
    (hs : Sorted (· ≤ ·) s) : ∀ x ∈ s.take (i + 1), x ≤ s.get ⟨i, hi⟩ := by
  induction s generalizing i with
  | nil => exact absurd hi (by simp)
  | cons a t ih =>
    cases i with
    | zero =>
      intro x hx
      have hxa : x = a := by simpa using hx
      rw [hxa]
      exact le_rfl
    | succ j =>
      have hj : j < t.length := by simpa using hi
      have hat : ∀ b ∈ t, a ≤ b := (sorted_cons.mp hs).1
      rw [take_succ_cons]
      intro x hx
      rw [mem_cons] at hx
      rcases hx with rfl | hx
      · exact hat _ (getElem_mem hj)
      · exact ih hj hs.tail x hx

/-- Every element of the suffix `s.drop i` is `≥ s[i]` when `s` is sorted. -/
theorem getElem_le_of_mem_drop {s : List α} {i : Nat} (hi : i < s.length)
    (hs : Sorted (· ≤ ·) s) : ∀ x ∈ s.drop i, s.get ⟨i, hi⟩ ≤ x := by
  induction s generalizing i with
  | nil => exact absurd hi (by simp)
  | cons a t ih =>
    cases i with
    | zero =>
      intro x hx
      simp only [drop_zero] at hx
      rw [mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_rfl
      · exact (sorted_cons.mp hs).1 x hx
    | succ j =>
      have hj : j < t.length := by simpa using hi
      rw [drop_succ_cons]
      exact ih hj hs.tail

theorem head?_drop_get {l : List α} {i : Nat} (h : i < l.length) :
    (l.drop i).head? = some (l.get ⟨i, h⟩) := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih (by simpa using h)

theorem head?_drop_none {l : List α} {i : Nat} (h : l.length ≤ i) :
    (l.drop i).head? = (none : Option α) := by
  induction l generalizing i with
  | nil => simp
  | cons x t ih =>
    cases i with
    | zero => exact absurd h (by simp)
    | succ j => exact ih (by simpa using h)

theorem head?_map {β : Type*} (f : α → β) (l : List α) :
    (l.head?).map f = (l.map f).head? := by cases l <;> rfl

theorem drop_map {β : Type*} (f : α → β) (i : Nat) (l : List α) :
    (l.map f).drop i = (l.drop i).map f := by
  induction l generalizing i with
  | nil => simp
  | cons x t ih =>
    cases i with
    | zero => simp
    | succ j =>
      show (map f t).drop j = (t.drop j).map f
      exact ih j

/-- The low median of `data`.

`none` is returned exactly for empty data, mirroring the `StatisticsError` raised by
Python's `median_low`. -/
def medianLow (data : List α) : Option α :=
  ((sortedOf data).drop (medianIdx data.length)).head?

/-- The low-median index of non-empty data, as a `Fin` into the sorted data. -/
def medianFin (data : List α) (hn : data.length ≠ 0) : Fin (sortedOf data).length :=
  ⟨medianIdx data.length, by rw [length_sortedOf]; exact medianIdx_lt _ hn⟩

theorem medianIdx_lt_sortedOf {data : List α} (hn : data.length ≠ 0) :
    medianIdx data.length < (sortedOf data).length := by
  rw [length_sortedOf]; exact medianIdx_lt _ hn

theorem medianLow_nil : medianLow ([] : List α) = none := by
  simp [medianLow, sortedOf, medianIdx]

theorem medianLow_eq_some {data : List α} (hn : data.length ≠ 0) :
    medianLow data = some ((sortedOf data).get (medianFin data hn)) := by
  have hi : medianIdx data.length < (sortedOf data).length := medianIdx_lt_sortedOf hn
  show ((sortedOf data).drop (medianIdx data.length)).head? = _
  rw [head?_drop_get hi]
  congr 1

theorem medianLow_eq_none {data : List α} : medianLow data = none ↔ data = [] := by
  constructor
  · intro h
    by_contra hn
    have hl : data.length ≠ 0 := fun hz => hn (List.length_eq_zero_iff.mp hz)
    rw [medianLow_eq_some hl] at h
    exact Option.noConfusion h
  · rintro rfl
    exact medianLow_nil

theorem medianLow_isSome {data : List α} : (medianLow data).isSome ↔ data ≠ [] := by
  constructor
  · intro h hn
    rw [hn, medianLow_nil] at h
    simp at h
  · intro hn
    have hl : data.length ≠ 0 := fun h => hn (List.length_eq_zero_iff.mp h)
    rw [medianLow_eq_some hl]
    simp

theorem medianLow_some_iff {data : List α} {m : α} :
    medianLow data = some m ↔
      ∃ hn : data.length ≠ 0, (sortedOf data).get (medianFin data hn) = m := by
  constructor
  · intro h
    have hn : data.length ≠ 0 := by
      intro hz
      have h2 : data = [] := List.length_eq_zero_iff.mp hz
      rw [h2, medianLow_nil] at h
      exact Option.noConfusion h
    have h2 : some ((sortedOf data).get (medianFin data hn)) = some m := by
      rw [← medianLow_eq_some hn, h]
    exact ⟨hn, Option.some.inj h2⟩
  · rintro ⟨hn, e⟩
    rw [medianLow_eq_some hn, e]

/-- Accessing a list at two `Fin` indices with the same value gives the same element. -/
theorem get_fin_eq {l : List α} {i j : Fin l.length} (h : i.val = j.val) : l.get i = l.get j := by
  cases i with | mk iv ip =>
  cases j with | mk jv jp =>
  dsimp at h
  subst h
  rfl

theorem medianLow_getElem {data : List α} (hn : data.length ≠ 0) {i : Nat}
    (heq : medianIdx data.length = i) :
    medianLow data =
      some ((sortedOf data).get ⟨i, by rw [← heq]; exact medianIdx_lt_sortedOf hn⟩) := by
  rw [medianLow_eq_some hn]
  congr 1
  exact get_fin_eq (by show medianIdx data.length = i; exact heq)

/-! ### Properties of the functional implementation -/

/-- The low median is always an element of the data (it is not an average). -/
theorem medianLow_mem {data : List α} {m : α} (h : medianLow data = some m) : m ∈ data := by
  obtain ⟨hn, e⟩ := medianLow_some_iff.mp h
  rw [← e]
  exact (perm_sortedOf data).mem_iff.mp (getElem_mem (medianFin data hn).isLt)

/-- The low median only depends on the multiset of the data, not on its order. -/
theorem medianLow_perm {d₁ d₂ : List α} (h : d₁ ~ d₂) : medianLow d₁ = medianLow d₂ := by
  have hl : d₁.length = d₂.length := h.length_eq
  have hso : sortedOf d₁ = sortedOf d₂ := sortedOf_perm h
  simp only [medianLow, hso, hl]

/-- A single data point is its own low median. -/
theorem medianLow_singleton (a : α) : medianLow [a] = some a := by
  have hs : sortedOf [a] = [a] := sortedOf_eq_self (List.sorted_singleton a)
  simp [medianLow, hs, medianIdx]

/-- For two data points the low median is the smaller one. -/
theorem medianLow_pair (a b : α) : medianLow [a, b] = some (min a b) := by
  have hs : sortedOf [a, b] = if a ≤ b then [a, b] else [b, a] := by
    simp [sortedOf, List.insertionSort, List.orderedInsert]
  rw [medianLow, hs]
  have h1 : ((if a ≤ b then [a, b] else [b, a]).drop (medianIdx [a, b].length)).head? =
      (if a ≤ b then [a, b] else [b, a]).head? := by simp [medianIdx]
  rw [h1]
  split_ifs with h <;> simp [h, min_def]

/-- Constant data has that constant as its low median. -/
theorem medianLow_replicate (n : Nat) (a : α) :
    medianLow (List.replicate (n + 1) a) = some a := by
  have hs : sortedOf (List.replicate (n + 1) a) = List.replicate (n + 1) a :=
    sortedOf_eq_self (List.sorted_le_replicate _ _)
  have hlen : (List.replicate (n + 1) a).length = n + 1 := length_replicate
  have hi : medianIdx (List.replicate (n + 1) a).length < (List.replicate (n + 1) a).length := by
    rw [hlen]; exact medianIdx_lt _ (by omega)
  rw [medianLow, hs, head?_drop_get hi]
  exact congrArg some (getElem_replicate hi)

/-- On already sorted data the low median is the element at index `(n-1)/2`. -/
theorem medianLow_sorted {data : List α} (hs : Sorted (· ≤ ·) data) (hn : data.length ≠ 0) :
    medianLow data = some (data.get ⟨medianIdx data.length, medianIdx_lt _ hn⟩) := by
  rw [medianLow, sortedOf_eq_self hs, head?_drop_get (medianIdx_lt _ hn)]

/-- Odd length: the middle element of the sorted data (`data[n // 2]` in Python). -/
theorem medianLow_odd {data : List α} {k : Nat} (h : data.length = 2 * k + 1) :
    medianLow data = some ((sortedOf data).get ⟨k, by rw [length_sortedOf, h]; omega⟩) :=
  medianLow_getElem (by omega) (by rw [h]; exact medianIdx_odd k)

/-- Even length: the element at index `n // 2 - 1` of the sorted data. -/
theorem medianLow_even {data : List α} {k : Nat} (h : data.length = 2 * k + 2) :
    medianLow data = some ((sortedOf data).get ⟨k, by rw [length_sortedOf, h]; omega⟩) :=
  medianLow_getElem (by omega) (by rw [h]; exact medianIdx_even k)

/-- Even length: the returned value is the *smaller* of the two middle values. -/
theorem medianLow_even_le {data : List α} {k : Nat} (h : data.length = 2 * k + 2) :
    (sortedOf data).get ⟨k, by rw [length_sortedOf, h]; omega⟩ ≤
      (sortedOf data).get ⟨k + 1, by rw [length_sortedOf, h]; omega⟩ :=
  sorted_getElem_le_getElem (sorted_sortedOf data)
    (by rw [length_sortedOf, h]; omega) (by rw [length_sortedOf, h]; omega) (by omega)

/-- Exactly the shape of the Python source:
`if n % 2 == 1: data[n//2] else: data[n//2-1]`. -/
theorem medianLow_python {data : List α} (hn : 0 < data.length) :
    medianLow data =
      if data.length % 2 = 1
      then some ((sortedOf data).get ⟨data.length / 2, by rw [length_sortedOf]; omega⟩)
      else some ((sortedOf data).get ⟨data.length / 2 - 1, by rw [length_sortedOf]; omega⟩) := by
  have hn' : data.length ≠ 0 := Nat.ne_of_gt hn
  by_cases hodd : data.length % 2 = 1
  · rw [if_pos hodd]
    exact medianLow_getElem hn' (by rw [medianIdx_python data.length hn, if_pos hodd])
  · rw [if_neg hodd]
    exact medianLow_getElem hn' (by rw [medianIdx_python data.length hn, if_neg hodd])

/-- The defining property of a median: at least half of the data is `≤ m` and at least
half of the data is `≥ m` (with the low median the two halves are
`(n + 1) / 2` and `n / 2 + 1`). -/
theorem medianLow_halving {data : List α} {m : α} (hn : data.length ≠ 0)
    (hm : medianLow data = some m) :
    (data.length + 1) / 2 ≤ (data.filter (· ≤ m)).length ∧
      data.length / 2 + 1 ≤ (data.filter (· ≥ m)).length := by
  set s := sortedOf data with hs_def
  set i := medianIdx data.length with hi_def
  have hlen : s.length = data.length := length_sortedOf data
  have hpos : 0 < data.length := Nat.pos_of_ne_zero hn
  have hi : i < s.length := by rw [hlen]; exact medianIdx_lt _ hn
  have hsort : Sorted (· ≤ ·) s := sorted_sortedOf data
  obtain ⟨hn2, e⟩ := medianLow_some_iff.mp hm
  have hm' : m = s.get ⟨i, hi⟩ := by
    rw [← e]
    exact (get_fin_eq (by show (medianFin data hn2).val = i; rfl)).symm
  have htake : ∀ x ∈ s.take (i + 1), x ≤ m := by
    intro x hx
    have := le_getElem_of_mem_take hi hsort x hx
    rwa [hm']
  have hdrop : ∀ x ∈ s.drop i, m ≤ x := by
    intro x hx
    have := getElem_le_of_mem_drop hi hsort x hx
    rwa [hm']
  have hA : i + 1 ≤ (s.filter (· ≤ m)).length := by
    have h2 : ((s.take (i + 1)).filter (· ≤ m)).length = (s.take (i + 1)).length := by
      rw [filter_eq_self.mpr (fun x hx => by simp [htake x hx])]
    have h5 : (s.take (i + 1)).length = i + 1 := by rw [length_take]; omega
    have h6 : (s.filter (· ≤ m)).length =
        ((s.take (i + 1)).filter (· ≤ m)).length + ((s.drop (i + 1)).filter (· ≤ m)).length := by
      have h6' := congrArg List.length
        (filter_append (p := (· ≤ m)) (s.take (i + 1)) (s.drop (i + 1)))
      rw [take_append_drop] at h6'
      rw [h6', length_append]
    omega
  have hB : s.length - i ≤ (s.filter (· ≥ m)).length := by
    have h4 : ((s.drop i).filter (· ≥ m)).length = (s.drop i).length := by
      rw [filter_eq_self.mpr (fun x hx => by simp [hdrop x hx])]
    have h7 : (s.drop i).length = s.length - i := length_drop
    have h8 : (s.filter (· ≥ m)).length =
        ((s.take i).filter (· ≥ m)).length + ((s.drop i).filter (· ≥ m)).length := by
      have h8' := congrArg List.length (filter_append (p := (· ≥ m)) (s.take i) (s.drop i))
      rw [take_append_drop] at h8'
      rw [h8', length_append]
    omega
  have h9 : (data.filter (· ≤ m)).length = (s.filter (· ≤ m)).length :=
    (Perm.filter (· ≤ m) (perm_sortedOf data)).length_eq.symm
  have h10 : (data.filter (· ≥ m)).length = (s.filter (· ≥ m)).length :=
    (Perm.filter (· ≥ m) (perm_sortedOf data)).length_eq.symm
  have h11 := medianIdx_halves data.length hpos
  have h12 : i = medianIdx data.length := rfl
  constructor <;> omega

/-- The low median lies between the minimum and the maximum of the data. -/
theorem medianLow_bounds {data : List α} {m : α} (h : medianLow data = some m) :
    data.minimum ≤ (m : WithTop α) ∧ (m : WithBot α) ≤ data.maximum :=
  ⟨List.minimum_le_of_mem' (medianLow_mem h), List.le_maximum_of_mem' (medianLow_mem h)⟩

end Generic

/-! ## 5. Unit tests (the assertions of the Python `check` function)

The Python unit tests use integer data, so the executable layer of the formalization is
`List Int`; every theorem of the generic section above instantiates to it. -/

section IntLayer

/-- Lean counterpart of Python's `StatisticsError`. -/
inductive StatisticsError where
  /-- `median_low` was called on empty data. -/
  | noMedianForEmptyData : StatisticsError
  /-- `benchmark_median_low`'s pre-condition failed. -/
  | preconditionFailed : StatisticsError
  deriving DecidableEq, Repr

-- 1. odd number of elements (returns the middle value)
example : medianLow ([1, 3, 5] : List Int) = some 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6, 9] : List Int) = some 4 := by native_decide

-- 2. even number of elements (returns the smaller of the two middle values)
example : medianLow ([1, 3, 5, 7] : List Int) = some 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6] : List Int) = some 3 := by native_decide

-- 3. single value
example : medianLow ([42] : List Int) = some 42 := by native_decide

-- 4. two values
example : medianLow ([10, 20] : List Int) = some 10 := by native_decide

-- 5. unsorted input
example : medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) = some 4 := by native_decide

-- 6. negative values
example : medianLow ([-5, -1, 0, 3, 7] : List Int) = some 0 := by native_decide
example : medianLow ([-10, -5, 5, 10] : List Int) = some (-5) := by native_decide

-- 7. error case: empty data raises `StatisticsError`, modelled by `none`
example : medianLow ([] : List Int) = none := by native_decide

-- duplicates, constant data and longer inputs
example : medianLow ([3, 3, 3, 3] : List Int) = some 3 := by native_decide
example : medianLow ([5, 5, 1, 1, 3] : List Int) = some 3 := by native_decide
example : medianLow (List.range 101) = some 50 := by native_decide
example : medianLow (List.range 100) = some 49 := by native_decide
example : medianLow (List.range 101 |>.reverse) = some 50 := by native_decide

#eval medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int)
#eval medianLow ([-10, -5, 5, 10] : List Int)
#eval medianLow ([] : List Int)
#eval sortedOf ([9, 1, 6, 2, 5, 4, 3] : List Int)

/-- The whole Python `check(benchmark_median_low)` suite as a single executable Boolean. -/
def pythonCheck : Bool :=
  (medianLow ([1, 3, 5] : List Int) == some 3) &&
    (medianLow ([1, 2, 3, 4, 5, 6, 9] : List Int) == some 4) &&
    (medianLow ([1, 3, 5, 7] : List Int) == some 3) &&
    (medianLow ([1, 2, 3, 4, 5, 6] : List Int) == some 3) &&
    (medianLow ([42] : List Int) == some 42) &&
    (medianLow ([10, 20] : List Int) == some 10) &&
    (medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) == some 4) &&
    (medianLow ([-5, -1, 0, 3, 7] : List Int) == some 0) &&
    (medianLow ([-10, -5, 5, 10] : List Int) == some (-5)) &&
    (medianLow ([] : List Int) == none)

example : pythonCheck = true := by native_decide

#eval pythonCheck

/-! ## 6. Pre-condition and the `benchmark_median_low` wrapper -/

/-- Python's `pre(data)`: `data` is a non-empty list/tuple of numbers.

"is a list of numbers" is expressed by the type `List Int` itself in the typed model, so the
only remaining obligation is non-emptiness. -/
def Pre (data : List Int) : Prop := data ≠ []

instance (data : List Int) : Decidable (Pre data) :=
  decidable_of_iff (data ≠ []) Iff.rfl

theorem Pre_iff_length {data : List Int} : Pre data ↔ 0 < data.length := by
  simp [Pre, List.length_pos_iff]

/-- Decidable equality for the benchmark's result type (needed by the `native_decide`
tests below). -/
instance : DecidableEq (Except StatisticsError Int) :=
  fun a b => match a, b with
    | .ok x, .ok y =>
      if h : x = y then .isTrue (by rw [h])
      else .isFalse (fun h2 => h (Except.ok.inj h2))
    | .error e, .error f =>
      if h : e = f then .isTrue (by rw [h])
      else .isFalse (fun h2 => h (Except.error.inj h2))
    | .ok _, .error _ => .isFalse (fun h => Except.noConfusion h)
    | .error _, .ok _ => .isFalse (fun h => Except.noConfusion h)

/-- Python's `benchmark_median_low`: check the pre-condition, then return the low median. -/
def benchmarkMedianLow (data : List Int) : Except StatisticsError Int :=
  if Pre data then
    match medianLow data with
    | some m => .ok m
    | none => throw StatisticsError.noMedianForEmptyData
  else throw StatisticsError.preconditionFailed

theorem benchmarkMedianLow_eq {data : List Int} (h : Pre data) :
    ∃ m, benchmarkMedianLow data = .ok m ∧ medianLow data = some m := by
  have hl : data.length ≠ 0 := by
    intro hz; exact h (List.length_eq_zero_iff.mp hz)
  refine ⟨(sortedOf data).get (medianFin data hl), ?_, medianLow_eq_some hl⟩
  simp [benchmarkMedianLow, h, medianLow_eq_some hl]

theorem benchmarkMedianLow_empty :
    benchmarkMedianLow [] = .error StatisticsError.preconditionFailed := rfl

-- unit tests for the wrapper (including the `StatisticsError` case of the Python `check`)
example : benchmarkMedianLow [1, 3, 5] = .ok 3 := by native_decide
example : benchmarkMedianLow [1, 2, 3, 4, 5, 6, 9] = .ok 4 := by native_decide
example : benchmarkMedianLow [1, 3, 5, 7] = .ok 3 := by native_decide
example : benchmarkMedianLow [1, 2, 3, 4, 5, 6] = .ok 3 := by native_decide
example : benchmarkMedianLow [42] = .ok 42 := by native_decide
example : benchmarkMedianLow [10, 20] = .ok 10 := by native_decide
example : benchmarkMedianLow [9, 1, 6, 2, 5, 4, 3] = .ok 4 := by native_decide
example : benchmarkMedianLow [-5, -1, 0, 3, 7] = .ok 0 := by native_decide
example : benchmarkMedianLow [-10, -5, 5, 10] = .ok (-5) := by native_decide
example : benchmarkMedianLow [] = .error StatisticsError.preconditionFailed := by native_decide

#eval benchmarkMedianLow [1, 3, 5, 7]
#eval benchmarkMedianLow []

/-! ## 7. Property propositions and their proofs (Int layer) -/

/-- `nthOpt xs i` is the `i`-th element of `xs`, or `none` if out of range.
This is the executable form of Python's `xs[i]`. -/
def nthOpt (xs : List Int) (i : Nat) : Option Int := (xs.drop i).head?

/-- Empty data raises `StatisticsError` (modelled by `none` / `.error`). -/
def empty_error_prop : Prop :=
  medianLow ([] : List Int) = none ∧
    benchmarkMedianLow [] = .error StatisticsError.preconditionFailed

theorem empty_error_thm : empty_error_prop :=
  ⟨medianLow_nil, benchmarkMedianLow_empty⟩

/-- A single data point is its own low median. -/
def singleton_prop : Prop := ∀ a : Int, medianLow [a] = some a

theorem singleton_thm : singleton_prop := fun _ => medianLow_singleton _

/-- For two data points the low median is the smaller one. -/
def pair_prop : Prop := ∀ a b : Int, medianLow [a, b] = some (min a b)

theorem pair_thm : pair_prop := fun _ _ => medianLow_pair _ _

/-- Odd length `2k+1`: the middle element `data[n // 2]` of the sorted data is returned. -/
def odd_middle_prop : Prop :=
  ∀ (data : List Int) (k : Nat), data.length = 2 * k + 1 →
    medianLow data = nthOpt (sortedOf data) k

theorem odd_middle_thm : odd_middle_prop := by
  intro data k hk
  have hkl : k < (sortedOf data).length := by rw [length_sortedOf, hk]; omega
  have e : nthOpt (sortedOf data) k = some ((sortedOf data).get ⟨k, hkl⟩) := head?_drop_get hkl
  rw [e, medianLow_odd hk]

/-- Even length `2k+2`: the *smaller* of the two middle elements, `data[n // 2 - 1]`,
is returned. -/
def even_lower_prop : Prop :=
  ∀ (data : List Int) (k : Nat), data.length = 2 * k + 2 →
    medianLow data = nthOpt (sortedOf data) k ∧
      nthOpt (sortedOf data) k ≤ nthOpt (sortedOf data) (k + 1)

theorem even_lower_thm : even_lower_prop := by
  intro data k hk
  have hkl : k < (sortedOf data).length := by rw [length_sortedOf, hk]; omega
  have hkl' : k + 1 < (sortedOf data).length := by rw [length_sortedOf, hk]; omega
  have e : nthOpt (sortedOf data) k = some ((sortedOf data).get ⟨k, hkl⟩) := head?_drop_get hkl
  have e' : nthOpt (sortedOf data) (k + 1) =
      some ((sortedOf data).get ⟨k + 1, hkl'⟩) := head?_drop_get hkl'
  refine ⟨by rw [e, medianLow_even hk], ?_⟩
  rw [e, e']
  exact medianLow_even_le hk

/-- The exact branch structure of the Python source:
`if n % 2 == 1: data[n // 2] else: data[n // 2 - 1]`. -/
def python_branch_prop : Prop :=
  ∀ data : List Int, Pre data →
    medianLow data =
      if data.length % 2 = 1 then nthOpt (sortedOf data) (data.length / 2)
      else nthOpt (sortedOf data) (data.length / 2 - 1)

theorem python_branch_thm : python_branch_prop := by
  intro data hd
  have hn : 0 < data.length := Pre_iff_length.mp hd
  have h1 : data.length / 2 < (sortedOf data).length := by rw [length_sortedOf]; omega
  have h2 : data.length / 2 - 1 < (sortedOf data).length := by rw [length_sortedOf]; omega
  have e1 : nthOpt (sortedOf data) (data.length / 2) =
      some ((sortedOf data).get ⟨data.length / 2, h1⟩) := head?_drop_get h1
  have e2 : nthOpt (sortedOf data) (data.length / 2 - 1) =
      some ((sortedOf data).get ⟨data.length / 2 - 1, h2⟩) := head?_drop_get h2
  rw [e1, e2, medianLow_python hn]

/-- The result is always an element of the data (the low median is not an average). -/
def member_prop : Prop :=
  ∀ (data : List Int) (m : Int), medianLow data = some m → m ∈ data

theorem member_thm : member_prop := fun _ _ => medianLow_mem

/-- The result does not depend on the order of the data. -/
def perm_invariant_prop : Prop :=
  ∀ d₁ d₂ : List Int, d₁ ~ d₂ → medianLow d₁ = medianLow d₂

theorem perm_invariant_thm : perm_invariant_prop := fun _ _ => medianLow_perm

/-- On already sorted data no re-sorting happens: the element at index `(n-1)/2` is returned. -/
def sorted_input_prop : Prop :=
  ∀ data : List Int, Sorted (· ≤ ·) data → Pre data →
    medianLow data = nthOpt data (medianIdx data.length)

theorem sorted_input_thm : sorted_input_prop := by
  intro data hs hd
  have hn : data.length ≠ 0 := by
    intro h; exact hd (List.length_eq_zero_iff.mp h)
  have e : nthOpt data (medianIdx data.length) =
      some (data.get ⟨medianIdx data.length, medianIdx_lt _ hn⟩) :=
    head?_drop_get (medianIdx_lt _ hn)
  rw [e, medianLow_sorted hs hn]

/-- Constant data returns that constant. -/
def constant_prop : Prop :=
  ∀ (n : Nat) (a : Int), medianLow (List.replicate (n + 1) a) = some a

theorem constant_thm : constant_prop := fun _ _ => medianLow_replicate _ _

/-- The median property: at least half of the points are `≤ m` and at least half are `≥ m`.
For the *low* median the two bounds are `(n+1)/2` and `n/2 + 1`. -/
def halving_prop : Prop :=
  ∀ (data : List Int) (m : Int), Pre data → medianLow data = some m →
    (data.length + 1) / 2 ≤ (data.filter (· ≤ m)).length ∧
      data.length / 2 + 1 ≤ (data.filter (· ≥ m)).length

theorem halving_thm : halving_prop := by
  intro data m hd hm
  have hn : data.length ≠ 0 := by
    intro h; exact hd (List.length_eq_zero_iff.mp h)
  exact medianLow_halving hn hm

/-- The low median lies between the minimum and the maximum of the data. -/
def bounds_prop : Prop :=
  ∀ (data : List Int) (m : Int), medianLow data = some m →
    data.minimum ≤ (m : WithTop Int) ∧ (m : WithBot Int) ≤ data.maximum

theorem bounds_thm : bounds_prop := fun _ _ => medianLow_bounds

/-- The low median is a fixed point: re-running it on the single returned value gives the
same value back. -/
def fixed_point_prop : Prop :=
  ∀ (data : List Int) (m : Int), medianLow data = some m → medianLow [m] = some m

theorem fixed_point_thm : fixed_point_prop := fun _ _ _ => medianLow_singleton _

/-- Translating all data by `c` translates the low median by `c`
(exact arithmetic, no rounding: this is the `Rat`/`Real`-style intent of the task). -/
def translation_prop : Prop :=
  ∀ (data : List Int) (c : Int), medianLow (data.map (· + c)) = (medianLow data).map (· + c)

theorem sortedOf_map_add (data : List Int) (c : Int) :
    sortedOf (data.map (· + c)) = (sortedOf data).map (· + c) := by
  have h := List.map_insertionSort (· ≤ ·) (· ≤ ·) (fun x => x + c) data
    (fun a _ b _ => (add_le_add_iff_right c).symm)
  simpa [sortedOf] using h.symm

theorem translation_thm : translation_prop := by
  intro data c
  rw [medianLow, sortedOf_map_add, length_map, drop_map, ← head?_map, ← medianLow]

/-- Scaling all data by a positive constant scales the low median by the same constant
(exact arithmetic: no rounding is involved). -/
def scaling_prop : Prop :=
  ∀ (data : List Int) (c : Int), 0 < c →
    medianLow (data.map (· * c)) = (medianLow data).map (· * c)

theorem sortedOf_map_mul (data : List Int) (c : Int) (hc : 0 < c) :
    sortedOf (data.map (· * c)) = (sortedOf data).map (· * c) := by
  have h := List.map_insertionSort (· ≤ ·) (· ≤ ·) (fun x => x * c) data
    (fun a _ b _ => (mul_le_mul_iff_of_pos_right hc).symm)
  simpa [sortedOf] using h.symm

theorem scaling_thm : scaling_prop := by
  intro data c hc
  rw [medianLow, sortedOf_map_mul data c hc, length_map, drop_map, ← head?_map, ← medianLow]

/-! ## 8. Post-condition -/

/-- The post-condition of `medianLow`, as a conjunction of the properties proved above.

`res` is the `Option Int` produced by the implementation: `none` models Python's
`StatisticsError`, `some m` models a returned low median. -/
def Post_prop (data : List Int) (res : Option Int) : Prop :=
  -- empty data yields the error value (`StatisticsError`)
  (data = [] → res = none) ∧
  -- admissible data yields a value
  (Pre data → ∃ m, res = some m) ∧
  -- the returned value is one of the data points
  (∀ m, res = some m → m ∈ data) ∧
  -- odd length: the middle element of the sorted data, `data[n // 2]`
  (∀ m, res = some m → data.length % 2 = 1 →
    some m = nthOpt (sortedOf data) (data.length / 2)) ∧
  -- even length: the *lower* middle element `data[n // 2 - 1]`, and it is `≤` the upper one
  (∀ m, res = some m → data.length % 2 = 0 →
    some m = nthOpt (sortedOf data) (data.length / 2 - 1) ∧
      nthOpt (sortedOf data) (data.length / 2 - 1) ≤ nthOpt (sortedOf data) (data.length / 2)) ∧
  -- at least half of the data is `≤ m` and at least half is `≥ m`
  (∀ m, res = some m →
    (data.length + 1) / 2 ≤ (data.filter (· ≤ m)).length ∧
      data.length / 2 + 1 ≤ (data.filter (· ≥ m)).length) ∧
  -- `m` lies between the minimum and the maximum of the data
  (∀ m, res = some m →
    data.minimum ≤ (m : WithTop Int) ∧ (m : WithBot Int) ≤ data.maximum)

/-- Post-condition of the Python `benchmark_median_low` wrapper: the pre-condition is
enforced by raising `StatisticsError`, otherwise a value satisfying `Post_prop` is returned. -/
def Benchmark_Post_prop (data : List Int) (res : Except StatisticsError Int) : Prop :=
  (¬ Pre data → res = .error StatisticsError.preconditionFailed) ∧
    (Pre data → ∃ m, res = .ok m ∧ Post_prop data (some m))

/-! ## 9. Property-based tests

Every executable property stated above (each `_prop` and the post-condition) is checked on
many inputs: exhaustively on a bounded family of data sets (`native_decide`) and randomly
with `Plausible` (which fails the compilation if it finds a counterexample). -/

/-- A bounded family of test data sets: all lengths `0 .. 13` of pseudo-random integers,
plus the exact inputs of the Python `check` function. -/
def pbData : List (List Int) :=
  (List.range 14).map (fun n => (List.range n).map (fun i : Nat => (((i : Int) * 7 + 3) % 11) - 5)) ++
    [[], [0], [1, 2], [2, 1], [-3, -3, -3], [5, 1, 4, 2, 3], [-10, -5, 5, 10],
     [1, 3, 5], [1, 3, 5, 7], [42], [10, 20], [9, 1, 6, 2, 5, 4, 3], [-5, -1, 0, 3, 7],
     [1, 2, 3, 4, 5, 6, 9], [1, 2, 3, 4, 5, 6]]

def pbShifts : List Int := [-7, -1, 0, 1, 5, 100]

def pbPairs : List (Int × Int) :=
  [(-5, 3), (0, 0), (7, -2), (10, 20), (1, 1000), (-3, -3), (-1, -1)]

/-- Boolean order test on `Option Int` (`Option` has no decidable `≤` instance). -/
def oleOpt (a b : Option Int) : Bool :=
  match a, b with
  | some x, some y => decide (x ≤ y)
  | none, _ => true
  | some _, none => false

/-- Executable Boolean mirror of `Post_prop` (needed because `Post_prop` quantifies over all
integers `m`, which `decide` cannot handle). -/
def postCheckVal (data : List Int) (m : Int) : Bool :=
  decide (m ∈ data) &&
    decide ((data.length + 1) / 2 ≤ (data.filter (· ≤ m)).length) &&
    decide (data.length / 2 + 1 ≤ (data.filter (· ≥ m)).length) &&
    decide (data.minimum.getD m ≤ m) &&
    decide (m ≤ data.maximum.getD m) &&
    decide (if data.length % 2 = 1
      then some m = nthOpt (sortedOf data) (data.length / 2)
      else some m = nthOpt (sortedOf data) (data.length / 2 - 1) ∧
        oleOpt (nthOpt (sortedOf data) (data.length / 2 - 1))
          (nthOpt (sortedOf data) (data.length / 2)) = true)

def postCheck (data : List Int) (res : Option Int) : Bool :=
  match res with
  | none => decide (data = [])
  | some m => decide (data ≠ []) && postCheckVal data m

-- PBT for `empty_error_prop`
example : (decide (medianLow ([] : List Int) = none) &&
    decide (benchmarkMedianLow [] = .error StatisticsError.preconditionFailed)) = true :=
  by native_decide

-- PBT for `singleton_prop`
example : ((List.range 21).map (fun i => i - 10)).all
    (fun a => decide (medianLow [a] = some a)) = true := by native_decide
#eval Plausible.Testable.check (∀ a : Int, medianLow [a] = some a)

-- PBT for `pair_prop`
example : pbPairs.all (fun p => decide (medianLow [p.1, p.2] = some (min p.1 p.2))) = true :=
  by native_decide
#eval Plausible.Testable.check (∀ a b : Int, medianLow [a, b] = some (min a b))

-- PBT for `member_prop`
example : pbData.all (fun xs =>
    ((medianLow xs).map (fun m => decide (m ∈ xs))).getD true) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  ((medianLow xs).map (fun m => decide (m ∈ xs))).getD true)

-- PBT for `perm_invariant_prop` (`reverse` and `sortedOf` are permutations of the data)
example : pbData.all (fun xs =>
    decide (medianLow xs.reverse = medianLow xs ∧ medianLow (sortedOf xs) = medianLow xs)) = true :=
  by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, medianLow xs.reverse = medianLow xs)
#eval Plausible.Testable.check (∀ xs : List Int, medianLow (sortedOf xs) = medianLow xs)

-- PBT for `odd_middle_prop`, `even_lower_prop` and `python_branch_prop`
example : pbData.all (fun xs => decide (
    if xs.length % 2 = 1 then medianLow xs = nthOpt (sortedOf xs) (xs.length / 2)
    else medianLow xs = nthOpt (sortedOf xs) (xs.length / 2 - 1))) = true := by native_decide
example : pbData.all (fun xs => decide (xs.length % 2 = 0 →
    oleOpt (nthOpt (sortedOf xs) (medianIdx xs.length))
      (nthOpt (sortedOf xs) (medianIdx xs.length + 1)) = true)) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  medianLow xs = if xs.length % 2 = 1 then nthOpt (sortedOf xs) (xs.length / 2)
    else nthOpt (sortedOf xs) (xs.length / 2 - 1))

-- PBT for `sorted_input_prop`
example : pbData.all (fun xs =>
    decide (medianLow (sortedOf xs) = nthOpt (sortedOf xs) (medianIdx (sortedOf xs).length))) =
  true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  medianLow (sortedOf xs) = nthOpt (sortedOf xs) (medianIdx (sortedOf xs).length))

-- PBT for `constant_prop`
example : (List.range 8).all (fun n => (List.range 7).all
    (fun i => decide (medianLow (List.replicate (n + 1) (i - 3)) = some (i - 3)))) = true :=
  by native_decide
#eval Plausible.Testable.check (∀ a : Int, medianLow (List.replicate 5 a) = some a)

-- PBT for `halving_prop`
example : pbData.all (fun xs => ((medianLow xs).map (fun m => decide (
      (xs.length + 1) / 2 ≤ (xs.filter (· ≤ m)).length ∧
        xs.length / 2 + 1 ≤ (xs.filter (· ≥ m)).length))).getD true) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, ((medianLow xs).map (fun m => decide (
      (xs.length + 1) / 2 ≤ (xs.filter (· ≤ m)).length ∧
        xs.length / 2 + 1 ≤ (xs.filter (· ≥ m)).length))).getD true)

-- PBT for `bounds_prop` (executable form: `minimum`/`maximum` default to `m` on empty data,
-- which cannot happen here because `medianLow xs = some m` implies `xs ≠ []`)
example : pbData.all (fun xs => ((medianLow xs).map (fun m =>
    decide (xs.minimum.getD m ≤ m ∧ m ≤ xs.maximum.getD m))).getD true) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, ((medianLow xs).map (fun m =>
    decide (xs.minimum.getD m ≤ m ∧ m ≤ xs.maximum.getD m))).getD true)

-- PBT for `fixed_point_prop`
example : pbData.all (fun xs =>
    ((medianLow xs).map (fun m => decide (medianLow [m] = some m))).getD true) = true :=
  by native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  ((medianLow xs).map (fun m => decide (medianLow [m] = some m))).getD true)

-- PBT for `translation_prop`
example : pbData.all (fun xs => pbShifts.all (fun c =>
    decide (medianLow (xs.map (· + c)) = (medianLow xs).map (· + c)))) = true := by native_decide
#eval Plausible.Testable.check (∀ (xs : List Int) (c : Int),
  medianLow (xs.map (· + c)) = (medianLow xs).map (· + c))

-- PBT for `scaling_prop`
example : pbData.all (fun xs => (List.range 5).all (fun c =>
    decide (medianLow (xs.map (· * ((c : Int) + 1))) =
      (medianLow xs).map (· * ((c : Int) + 1))))) = true := by native_decide
#eval Plausible.Testable.check (∀ (xs : List Int) (c : Nat),
  medianLow (xs.map (· * (c + 1 : Int))) = (medianLow xs).map (· * (c + 1 : Int)))

-- PBT for the post-condition `Post_prop` (via its executable mirror `postCheck`)
example : pbData.all (fun xs => postCheck xs (medianLow xs)) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs (medianLow xs))

-- PBT for `Benchmark_Post_prop`
example : pbData.all (fun xs =>
    decide (benchmarkMedianLow xs = (medianLow xs).elim
      (.error StatisticsError.preconditionFailed) (.ok))) = true := by native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  benchmarkMedianLow xs = (medianLow xs).elim
    (.error StatisticsError.preconditionFailed) (.ok))

/-- `oleOpt` really tests `≤` on `Option Int`. -/
theorem oleOpt_true {a b : Option Int} (h : oleOpt a b = true) : a ≤ b := by
  cases a with
  | none => simp
  | some x =>
    cases b with
    | none => simp [oleOpt] at h
    | some y =>
      simp [oleOpt] at h
      exact h

/-- Soundness of the executable mirror, `res = none` case. -/
theorem postCheck_sound_none (data : List Int) (h : postCheck data none = true) :
    Post_prop data none := by
  have e : postCheck data none = decide (data = []) := rfl
  rw [e] at h
  have hd : data = [] := of_decide_eq_true h
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hpre
    exact absurd hd hpre
  · intro m hm
    exact Option.noConfusion hm
  · intro m hm _
    exact Option.noConfusion hm
  · intro m hm _
    exact Option.noConfusion hm
  · intro m hm
    exact Option.noConfusion hm
  · intro m hm
    exact Option.noConfusion hm

/-- Soundness of the executable mirror, `res = some m0` case. -/
theorem postCheck_sound_some (data : List Int) (m0 : Int)
    (h : postCheck data (some m0) = true) : Post_prop data (some m0) := by
  have e1 : postCheck data (some m0) = (decide (data ≠ []) && postCheckVal data m0) := by
    simp [postCheck]
  rw [e1, Bool.and_eq_true] at h
  obtain ⟨hne, hv⟩ := h
  have hne' : data ≠ [] := of_decide_eq_true hne
  have e4 : postCheckVal data m0 =
      (decide (m0 ∈ data) &&
        decide ((data.length + 1) / 2 ≤ (data.filter (· ≤ m0)).length) &&
        decide (data.length / 2 + 1 ≤ (data.filter (· ≥ m0)).length) &&
        decide (data.minimum.getD m0 ≤ m0) &&
        decide (m0 ≤ data.maximum.getD m0) &&
        decide (if data.length % 2 = 1
          then some m0 = nthOpt (sortedOf data) (data.length / 2)
          else some m0 = nthOpt (sortedOf data) (data.length / 2 - 1) ∧
            oleOpt (nthOpt (sortedOf data) (data.length / 2 - 1))
              (nthOpt (sortedOf data) (data.length / 2)) = true)) := by
    simp [postCheckVal]
  rw [e4] at hv
  -- `&&` associates to the left, so the components are peeled off from the right
  rw [Bool.and_eq_true] at hv
  have c6 := of_decide_eq_true hv.2
  have hv1 := hv.1
  rw [Bool.and_eq_true] at hv1
  have hv2 := hv1.1
  rw [Bool.and_eq_true] at hv2
  have hv3 := hv2.1
  rw [Bool.and_eq_true] at hv3
  have c3 : data.length / 2 + 1 ≤ (data.filter (· ≥ m0)).length := of_decide_eq_true hv3.2
  have hv4 := hv3.1
  rw [Bool.and_eq_true] at hv4
  have c1 : m0 ∈ data := of_decide_eq_true hv4.1
  have c2 : (data.length + 1) / 2 ≤ (data.filter (· ≤ m0)).length := of_decide_eq_true hv4.2
  refine ⟨fun h0 => absurd h0 hne', fun _ => ⟨m0, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    injection hm with e
    rw [← e]
    exact c1
  · intro m hm hodd
    injection hm with e
    rw [if_pos hodd] at c6
    rw [← e]
    exact c6
  · intro m hm heven
    injection hm with e
    have hnot : ¬(data.length % 2 = 1) := by omega
    rw [if_neg hnot] at c6
    exact ⟨by rw [← e]; exact c6.1, oleOpt_true c6.2⟩
  · intro m hm
    injection hm with e
    rw [← e]
    exact ⟨c2, c3⟩
  · intro m hm
    injection hm with e
    rw [← e]
    exact ⟨List.minimum_le_of_mem' c1, List.le_maximum_of_mem' c1⟩

/-- The executable mirror is sound: whenever `postCheck` accepts, `Post_prop` holds.  This is
what makes the bounded and randomized post-condition PBTs above tests of `Post_prop`. -/
theorem postCheck_sound (data : List Int) (res : Option Int) (h : postCheck data res = true) :
    Post_prop data res := by
  cases res with
  | none => exact postCheck_sound_none data h
  | some m0 => exact postCheck_sound_some data m0 h

/-! ## 10. Correctness: `Pre → Post` -/

theorem correctness_thm (data : List Int) (h : Pre data) :
    Post_prop data (medianLow data) := by
  have hl : 0 < data.length := Pre_iff_length.mp h
  have hn : data.length ≠ 0 := Nat.ne_of_gt hl
  refine ⟨fun h0 => by rw [h0]; exact medianLow_nil,
    fun _ => ⟨_, medianLow_eq_some hn⟩,
    fun _ hm => medianLow_mem hm,
    ?_, ?_,
    fun _ hm => medianLow_halving hn hm,
    fun _ hm => medianLow_bounds hm⟩
  · intro m hm hodd
    have hk : data.length = 2 * (data.length / 2) + 1 := by omega
    have e := odd_middle_thm data (data.length / 2) hk
    rw [hm] at e
    exact e
  · intro m hm heven
    have hk : data.length = 2 * (data.length / 2 - 1) + 2 := by omega
    obtain ⟨e1, e2⟩ := even_lower_thm data (data.length / 2 - 1) hk
    rw [hm] at e1
    have hk' : data.length / 2 - 1 + 1 = data.length / 2 := by omega
    exact ⟨e1, by rw [← hk']; exact e2⟩

/-- Correctness of the Python `benchmark_median_low` wrapper: it enforces the pre-condition
and otherwise returns a value satisfying the post-condition. -/
theorem benchmark_correctness_thm (data : List Int) :
    Benchmark_Post_prop data (benchmarkMedianLow data) := by
  constructor
  · intro hn
    simp [benchmarkMedianLow, hn]
    rfl
  · intro hd
    have hn : data.length ≠ 0 := by
      intro hz; exact hd (List.length_eq_zero_iff.mp hz)
    refine ⟨(sortedOf data).get (medianFin data hn), ?_, ?_⟩
    · simp [benchmarkMedianLow, hd, medianLow_eq_some hn]
    · have hpost := correctness_thm data hd
      rw [medianLow_eq_some hn] at hpost
      exact hpost

/-! ## 11. Imperative implementation (`Id.run do` with mutable state) -/

/-- The inner step of the imperative insertion sort: insert `x` into the already sorted
accumulator `acc`, keeping it sorted.  This is the mutable-buffer counterpart of Python's
`sorted(data)`. -/
def sortedInsert (x : Int) (acc : List Int) : List Int := List.orderedInsert (· ≤ ·) x acc

/-- Imperative insertion sort: a mutable accumulator that is updated inside a `for` loop
walking over the data. -/
def sortImp (data : List Int) : List Int :=
  Id.run do
    let mut acc : List Int := []
    for x in data.reverse do
      acc := sortedInsert x acc
    return acc

/-- Imperative low median: sort with a mutable accumulator, compute the index in mutable
variables and read the element off the sorted buffer.  `none` models `StatisticsError`. -/
def medianLowImp (data : List Int) : Option Int :=
  Id.run do
    let mut acc : List Int := []
    for x in data.reverse do
      acc := sortedInsert x acc
    let mut n := data.length
    let mut idx := medianIdx n
    return (acc.drop idx).head?

/-- Imperative counterpart of Python's `benchmark_median_low`: check the pre-condition first
and raise `StatisticsError` otherwise. -/
def benchmarkMedianLowImp (data : List Int) : Except StatisticsError Int :=
  Id.run do
    let mut n := data.length
    if n = 0 then
      return .error StatisticsError.preconditionFailed
    match medianLowImp data with
    | some m => return .ok m
    | none => return .error StatisticsError.noMedianForEmptyData

/-! ## 12. Imperative tests -/

example : sortImp [9, 1, 6, 2, 5, 4, 3] = [1, 2, 3, 4, 5, 6, 9] := by native_decide
example : medianLowImp [1, 3, 5] = some 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6, 9] = some 4 := by native_decide
example : medianLowImp [1, 3, 5, 7] = some 3 := by native_decide
example : medianLowImp [1, 2, 3, 4, 5, 6] = some 3 := by native_decide
example : medianLowImp [42] = some 42 := by native_decide
example : medianLowImp [10, 20] = some 10 := by native_decide
example : medianLowImp [9, 1, 6, 2, 5, 4, 3] = some 4 := by native_decide
example : medianLowImp [-5, -1, 0, 3, 7] = some 0 := by native_decide
example : medianLowImp [-10, -5, 5, 10] = some (-5) := by native_decide
example : medianLowImp [] = (none : Option Int) := by native_decide
example : benchmarkMedianLowImp [1, 3, 5] = .ok 3 := by native_decide
example : benchmarkMedianLowImp [1, 3, 5, 7] = .ok 3 := by native_decide
example : benchmarkMedianLowImp [-10, -5, 5, 10] = .ok (-5) := by native_decide
example : benchmarkMedianLowImp [] = .error StatisticsError.preconditionFailed := by native_decide

-- bounded property-based test of the equivalence on the whole test family
example : pbData.all (fun xs =>
    decide (medianLowImp xs = medianLow xs ∧
      benchmarkMedianLowImp xs = benchmarkMedianLow xs)) = true := by native_decide

#eval sortImp [9, 1, 6, 2, 5, 4, 3]
#eval medianLowImp [9, 1, 6, 2, 5, 4, 3]
#eval medianLowImp ([] : List Int)
#eval benchmarkMedianLowImp [1, 2, 3, 4, 5, 6]
#eval benchmarkMedianLowImp ([] : List Int)

/-! ## 13. Equivalence theorem: functional = imperative -/

theorem sortImp_foldl (data : List Int) :
    sortImp data = data.reverse.foldl (fun acc x => sortedInsert x acc) [] := by
  simp [sortImp]

theorem medianLowImp_foldl (data : List Int) :
    medianLowImp data =
      ((data.reverse.foldl (fun acc x => sortedInsert x acc) []).drop
        (medianIdx data.length)).head? := by
  simp [medianLowImp]

/-- Walking the reversed list from the left with `sortedInsert` is the same as folding from
the right, i.e. exactly `List.insertionSort`. -/
theorem foldl_sortedInsert_reverse (l acc : List Int) :
    (l.reverse).foldl (fun s x => sortedInsert x s) acc =
      List.foldr (fun x s => sortedInsert x s) acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, List.foldl_concat, List.foldr_cons]
    show sortedInsert a (t.reverse.foldl (fun s x => sortedInsert x s) acc) =
      sortedInsert a (List.foldr (fun x s => sortedInsert x s) acc t)
    rw [ih acc]

theorem foldr_sortedInsert (l : List Int) :
    List.foldr (fun x s => sortedInsert x s) [] l = List.insertionSort (· ≤ ·) l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show sortedInsert a (List.foldr (fun x s => sortedInsert x s) [] t) =
      List.insertionSort (· ≤ ·) (a :: t)
    rw [ih, List.insertionSort, sortedInsert]

theorem sortImp_eq_sortedOf (data : List Int) : sortImp data = sortedOf data := by
  rw [sortImp_foldl, foldl_sortedInsert_reverse, foldr_sortedInsert]
  rfl

theorem foldl_sortedInsert_eq_sortedOf (data : List Int) :
    data.reverse.foldl (fun acc x => sortedInsert x acc) [] = sortedOf data := by
  rw [← sortImp_foldl, sortImp_eq_sortedOf]

theorem medianLowImp_eq (data : List Int) : medianLowImp data = medianLow data := by
  rw [medianLowImp_foldl, foldl_sortedInsert_eq_sortedOf]
  rfl

theorem benchmarkMedianLowImp_eq (data : List Int) :
    benchmarkMedianLowImp data = benchmarkMedianLow data := by
  by_cases h : data = []
  · subst h
    simp [benchmarkMedianLowImp, benchmarkMedianLow, Pre]
    rfl
  · have hn : data.length ≠ 0 := fun hz => h (List.length_eq_zero_iff.mp hz)
    have hsome : medianLow data = some ((sortedOf data).get (medianFin data hn)) :=
      medianLow_eq_some hn
    simp [benchmarkMedianLowImp, benchmarkMedianLow, Pre, hn, h, medianLowImp_eq, hsome]

theorem benchmarkMedianLowImp_correct (data : List Int) :
    Benchmark_Post_prop data (benchmarkMedianLowImp data) := by
  rw [benchmarkMedianLowImp_eq]
  exact benchmark_correctness_thm data


/-! ## Numeric layers

The Python program is generic over `numbers.Number`.  The formalization above is generic over
any `LinearOrder α`, so the very same theorems hold for the exact rational and real models of
the task's numeric intent; the `Int` layer used by the Python unit tests is the executable one.

Primitive `Float` is deliberately *not* used: the specification contains no rounding,
overflow, underflow, NaN or signed-zero behaviour (`median_low` only compares data points and
selects one of them), and Lean has no `LinearOrder Float` instance modelling the IEEE-754
total order.  The `Rat` and `Real` layers below are the exact mathematical models; both are
covered by the same generic theorems, instantiated here. -/

namespace RatLayer

/-- Exact rational model: the generic membership theorem. -/
theorem member_thm (data : List Rat) (m : Rat) (h : medianLow data = some m) : m ∈ data :=
  medianLow_mem h

/-- Exact rational model: the generic halving (median) theorem. -/
theorem halving_thm (data : List Rat) (m : Rat) (hn : 0 < data.length)
    (h : medianLow data = some m) :
    (data.length + 1) / 2 ≤ (data.filter (· ≤ m)).length ∧
      data.length / 2 + 1 ≤ (data.filter (· ≥ m)).length :=
  medianLow_halving (Nat.ne_of_gt hn) h

/-- Exact rational model: the Python branch structure. -/
theorem python_branch_thm (data : List Rat) (hn : 0 < data.length) :
    medianLow data =
      if data.length % 2 = 1
      then some ((sortedOf data).get ⟨data.length / 2, by rw [length_sortedOf]; omega⟩)
      else some ((sortedOf data).get ⟨data.length / 2 - 1, by rw [length_sortedOf]; omega⟩) :=
  medianLow_python hn

example : medianLow ([(1:Rat)/2, (1:Rat)/3, (7:Rat)/5]) = some ((1:Rat)/2) := by native_decide
example : medianLow ([(1:Rat), 3, 5, 7]) = some 3 := by native_decide
example : medianLow ([(3:Rat)/2, -(1:Rat)/2]) = some (-(1:Rat)/2) := by native_decide
example : medianLow ([] : List Rat) = none := by native_decide
example : medianLow ([(1:Rat)/3, (1:Rat)/3, (1:Rat)/3, (1:Rat)/3]) = some ((1:Rat)/3) :=
  by native_decide

#eval medianLow ([(1:Rat)/2, (1:Rat)/3, (7:Rat)/5])

end RatLayer

namespace RealLayer

theorem sorted_135 : Sorted (· ≤ ·) ([(1:Real), 3, 5]) := by
  rw [List.sorted_cons, List.sorted_cons]
  refine ⟨?_, ⟨?_, List.sorted_singleton _⟩⟩
  · intro b hb
    have h : b = 3 ∨ b = 5 := by simpa using hb
    rcases h with rfl | rfl <;> norm_num
  · intro b hb
    have h : b = 5 := by simpa using hb
    rcases h with rfl
    norm_num

theorem sorted_1357 : Sorted (· ≤ ·) ([(1:Real), 3, 5, 7]) := by
  rw [List.sorted_cons, List.sorted_cons, List.sorted_cons]
  refine ⟨?_, ⟨?_, ⟨?_, List.sorted_singleton _⟩⟩⟩
  · intro b hb; simp at hb; rcases hb with rfl | rfl | rfl <;> norm_num
  · intro b hb; simp at hb; rcases hb with rfl | rfl <;> norm_num
  · intro b hb; simp at hb; subst hb; norm_num

theorem sorted_222 : Sorted (· ≤ ·) ([(2:Real), 2, 2]) := by
  rw [List.sorted_cons, List.sorted_cons]
  refine ⟨?_, ⟨?_, List.sorted_singleton _⟩⟩
  · intro b hb; simp at hb; rcases hb with rfl | rfl <;> norm_num
  · intro b hb; simp at hb; subst hb; norm_num

/-- Exact real model: the generic membership theorem. -/
theorem member_thm (data : List Real) (m : Real) (h : medianLow data = some m) : m ∈ data :=
  medianLow_mem h

/-- Exact real model: the generic halving (median) theorem. -/
theorem halving_thm (data : List Real) (m : Real) (hn : 0 < data.length)
    (h : medianLow data = some m) :
    (data.length + 1) / 2 ≤ (data.filter (· ≤ m)).length ∧
      data.length / 2 + 1 ≤ (data.filter (· ≥ m)).length :=
  medianLow_halving (Nat.ne_of_gt hn) h

/-- Exact real model: the generic order-invariance theorem. -/
theorem perm_thm (d₁ d₂ : List Real) (h : d₁ ~ d₂) : medianLow d₁ = medianLow d₂ :=
  medianLow_perm h

/-- Exact real model: the generic bounds theorem. -/
theorem bounds_thm (data : List Real) (m : Real) (h : medianLow data = some m) :
    data.minimum ≤ (m : WithTop Real) ∧ (m : WithBot Real) ≤ data.maximum :=
  medianLow_bounds h

/-- Odd length over the reals: the middle value. -/
example : medianLow ([(1:Real), 3, 5]) = some 3 := by
  have hn : ([(1:Real), 3, 5]).length ≠ 0 := by simp
  rw [medianLow, sortedOf_eq_self sorted_135, head?_drop_get (medianIdx_lt _ hn)]
  rfl

/-- Even length over the reals: the *smaller* of the two middle values. -/
example : medianLow ([(1:Real), 3, 5, 7]) = some 3 := by
  have hn : ([(1:Real), 3, 5, 7]).length ≠ 0 := by simp
  rw [medianLow, sortedOf_eq_self sorted_1357, head?_drop_get (medianIdx_lt _ hn)]
  rfl

/-- Constant real data. -/
example : medianLow ([(2:Real), 2, 2]) = some 2 := by
  have hn : ([(2:Real), 2, 2]).length ≠ 0 := by simp
  rw [medianLow, sortedOf_eq_self sorted_222, head?_drop_get (medianIdx_lt _ hn)]
  rfl

/-- Empty real data yields the error value. -/
example : medianLow ([] : List Real) = none := medianLow_nil

end RealLayer

end IntLayer

end «28_statistics_median_low»

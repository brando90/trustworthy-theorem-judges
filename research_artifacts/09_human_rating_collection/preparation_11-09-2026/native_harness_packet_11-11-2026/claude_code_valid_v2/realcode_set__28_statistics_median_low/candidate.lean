import Mathlib

/-!
# Low median of numeric data (`statistics.median_low`)

Lean 4 formalization of Python's `statistics.median_low` (CPython `Lib/statistics.py`):

```python
def median_low(data):
    data = sorted(data)
    n = len(data)
    if n == 0:
        raise StatisticsError("no median for empty data")
    if n % 2 == 1:
        return data[n // 2]
    else:
        return data[n // 2 - 1]
```

* The data points are modelled as elements of an arbitrary type with a `LinearOrder`
  (`Int`, `Rat`, `Real`, ... — every exact numeric type Python's `numbers.Number` covers
  whose comparison is a total order).  All tests of the Python program use integers, so the
  executable tests below instantiate the generic development at `Int` (and `Rat`).
* `StatisticsError` on empty data is modelled by the result `none`; a successful call returns
  `some m`.
* The pre-condition `Pre` is the Python `pre`: the data is a non-empty list (element types are
  enforced by Lean's type system).
* Besides the index-based specification (`data[n // 2]`, `data[n // 2 - 1]` of the sorted data)
  we prove the order-statistic (rank) characterisation of the low median: it is the unique value
  `m` with fewer than `⌈n/2⌉` data points strictly below it and at least `⌈n/2⌉` points `≤ m`.
* A small `FloatLayer` provides the executable IEEE-754 `Float` version for ground tests.
-/

namespace «28_statistics_median_low»

/-! ## Order-independent part: picking the low-middle element of a (sorted) list -/

section Pick

variable {α : Type}

/-- Given the already sorted data `s`, return the low middle element, mirroring the Python
branching: `n == 0` raises (`none`), odd `n` returns `data[n // 2]`, even `n` returns
`data[n // 2 - 1]`. -/
def pickLow (s : List α) : Option α :=
  if h : s.length = 0 then none
  else if s.length % 2 = 1 then some (s[s.length / 2]'(by omega))
  else some (s[s.length / 2 - 1]'(by omega))

/-- Both Python branches pick index `(n - 1) / 2` of the sorted data. -/
theorem pickLow_eq_getElem? (s : List α) : pickLow s = s[(s.length - 1) / 2]? := by
  unfold pickLow
  split_ifs with h0 hodd
  · rw [eq_comm, List.getElem?_eq_none_iff]; omega
  · rw [List.getElem?_eq_getElem (by omega)]
    congr 2
    omega
  · rw [List.getElem?_eq_getElem (by omega)]
    congr 2
    omega

/-- Counting loop used by the imperative version (`n = len(data)`). -/
theorem foldl_count (s : List α) : s.foldl (fun k _ => k + 1) 0 = s.length := by
  suffices h : ∀ k, s.foldl (fun k _ => k + 1) k = k + s.length by simp [h 0]
  induction s with
  | nil => intro k; simp
  | cons x s ih => intro k; simp only [List.foldl_cons, List.length_cons, ih]; omega

/-- A `for` loop in `Id` that only updates its accumulator is a left fold. -/
theorem idRun_forIn_pure_yield {β γ : Type} (l : List β) (init : γ) (g : β → γ → γ) :
    (forIn (m := Id) l init (fun a b => pure (ForInStep.yield (g a b)))).run
      = l.foldl (fun b a => g a b) init := by
  have h := List.idRun_forIn_yield_eq_foldl l (fun a b => (pure (g a b) : Id γ)) init
  simp only [map_pure, Id.run_pure] at h
  exact h

end Pick

/-! ## Functional implementation -/

variable {α : Type} [LinearOrder α]

/-- Python's `sorted(data)` (ascending, stable insertion sort). -/
def sortData (xs : List α) : List α := xs.insertionSort (· ≤ ·)

theorem sortData_sorted (xs : List α) : (sortData xs).Sorted (· ≤ ·) :=
  List.sorted_insertionSort _ xs

theorem sortData_perm (xs : List α) : List.Perm (sortData xs) xs :=
  List.perm_insertionSort _ xs

@[simp] theorem length_sortData (xs : List α) : (sortData xs).length = xs.length :=
  List.length_insertionSort _ xs

/-- `median_low(data)`: sort the data and pick the low middle element.
`none` models `StatisticsError` (raised exactly for empty data). -/
def medianLow (xs : List α) : Option α := pickLow (sortData xs)

/-- `benchmark_median_low(data)`: identical to `median_low`, since the only failing input of
`median_low`, the empty list, is also the only input rejected by the Python `pre`. -/
def benchmarkMedianLow (xs : List α) : Option α := medianLow xs

/-! ## Unit tests (the Python `check` suite) -/

-- 1. Odd number of elements (returns middle value)
example : medianLow ([1, 3, 5] : List Int) = some 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6, 9] : List Int) = some 4 := by native_decide
-- 2. Even number of elements (returns smaller of two middle values)
example : medianLow ([1, 3, 5, 7] : List Int) = some 3 := by native_decide
example : medianLow ([1, 2, 3, 4, 5, 6] : List Int) = some 3 := by native_decide
-- 3. Single value
example : medianLow ([42] : List Int) = some 42 := by native_decide
-- 4. Two values
example : medianLow ([10, 20] : List Int) = some 10 := by native_decide
-- 5. Unsorted input
example : medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) = some 4 := by native_decide
-- 6. Negative values
example : medianLow ([-5, -1, 0, 3, 7] : List Int) = some 0 := by native_decide
example : medianLow ([-10, -5, 5, 10] : List Int) = some (-5) := by native_decide
-- 7. Error case: empty data raises `StatisticsError`
example : medianLow ([] : List Int) = none := by native_decide
example : benchmarkMedianLow ([] : List Int) = none := by native_decide
example : benchmarkMedianLow ([9, 1, 6, 2, 5, 4, 3] : List Int) = some 4 := by native_decide
-- The same facts checked by the kernel (`decide`) rather than by compiled code.
example : medianLow ([1, 3, 5] : List Int) = some 3 := by decide
example : medianLow ([1, 3, 5, 7] : List Int) = some 3 := by decide
example : medianLow ([] : List Int) = none := rfl
-- Exact rationals (Python `Fraction`) work the same way.
example : medianLow ([1/2, 3, 5/2] : List ℚ) = some (5/2) := by native_decide
example : medianLow ([3/2, 1/2, 7/2, 5/2] : List ℚ) = some (3/2) := by native_decide

#eval medianLow ([1, 3, 5] : List Int)                -- some 3
#eval medianLow ([1, 3, 5, 7] : List Int)             -- some 3
#eval medianLow ([9, 1, 6, 2, 5, 4, 3] : List Int)    -- some 4
#eval medianLow ([-10, -5, 5, 10] : List Int)         -- some (-5)
#eval medianLow ([] : List Int)                       -- none
#eval medianLow ([1/2, 3, 5/2] : List ℚ)              -- some (5/2)

/-! ## Pre-condition -/

/-- Python `pre`: the data is a non-empty list (of numbers; the element type is enforced by
Lean's type system). -/
def Pre (xs : List α) : Prop := xs ≠ []

/-! ## Properties -/

/-- The computation fails (Python raises `StatisticsError`) exactly on empty data. -/
def error_iff_empty_prop (xs : List α) (r : Option α) : Prop := r = none ↔ xs = []

/-- Non-empty data always has a low median (no exception is raised). -/
def succeeds_prop (xs : List α) (r : Option α) : Prop := xs ≠ [] → ∃ m, r = some m

/-- A returned median is one of the data points (it is never an average). -/
def mem_prop (xs : List α) (r : Option α) : Prop := ∀ m, r = some m → m ∈ xs

/-- Odd number of data points: the middle element `data[n // 2]` of the sorted data. -/
def odd_prop (xs : List α) (r : Option α) : Prop :=
  xs.length % 2 = 1 → r = (sortData xs)[xs.length / 2]?

/-- Even (non-zero) number of data points: the smaller of the two middle elements,
`data[n // 2 - 1]` of the sorted data. -/
def even_prop (xs : List α) (r : Option α) : Prop :=
  xs ≠ [] → xs.length % 2 = 0 → r = (sortData xs)[xs.length / 2 - 1]?

/-- Rank (order-statistic) characterisation.  With `n` data points and `k = (n - 1) / 2`
(so `k + 1 = ⌈n / 2⌉`), the low median `m` has at most `k` data points strictly below it and
at least `k + 1` data points `≤ m`: it is the `⌈n/2⌉`-th smallest data point. -/
def rank_prop (xs : List α) (r : Option α) : Prop :=
  ∀ m, r = some m →
    xs.countP (· < m) ≤ (xs.length - 1) / 2 ∧ (xs.length - 1) / 2 < xs.countP (· ≤ m)

/-- The rank conditions determine the low median uniquely: any value `v` (not necessarily a
data point) satisfying them is the result. -/
def unique_prop (xs : List α) (r : Option α) : Prop :=
  xs ≠ [] → ∀ v : α,
    xs.countP (· < v) ≤ (xs.length - 1) / 2 → (xs.length - 1) / 2 < xs.countP (· ≤ v) →
    r = some v

/-- Median property: at least half of the data points are `≤ m` and at least half are `≥ m`. -/
def half_prop (xs : List α) (r : Option α) : Prop :=
  ∀ m, r = some m →
    xs.length ≤ 2 * xs.countP (· ≤ m) ∧ xs.length ≤ 2 * xs.countP (m ≤ ·)

/-- The result only depends on the multiset of data points, not on their order. -/
def perm_invariant_prop (xs ys : List α) : Prop :=
  List.Perm xs ys → medianLow xs = medianLow ys

/-! ### Auxiliary lemmas -/

/-- `median_low` returns element `(n - 1) / 2` of the sorted data (if it exists). -/
theorem medianLow_eq_getElem? (xs : List α) :
    medianLow xs = (sortData xs)[(xs.length - 1) / 2]? := by
  rw [medianLow, pickLow_eq_getElem?, length_sortData]

theorem sorted_getElem_le {s : List α} (hs : s.Sorted (· ≤ ·)) {i j : ℕ} (hij : i ≤ j)
    (hj : j < s.length) : s[i]'(lt_of_le_of_lt hij hj) ≤ s[j] := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact List.pairwise_iff_getElem.1 hs i j _ hj h
  · subst h; exact le_rfl

/-- In a sorted list, the first `k + 1` elements are all `≤ s[k]`. -/
theorem countP_le_of_sorted {s : List α} (hs : s.Sorted (· ≤ ·)) {k : ℕ} (hk : k < s.length) :
    k + 1 ≤ s.countP (fun x => decide (x ≤ s[k])) := by
  have htake : ∀ a ∈ s.take (k + 1), decide (a ≤ s[k]) = true := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    rw [List.getElem_take]
    have hi' : i ≤ k := by simp at hi; omega
    exact decide_eq_true (sorted_getElem_le hs hi' hk)
  calc k + 1 = (s.take (k + 1)).length := by simp; omega
    _ = (s.take (k + 1)).countP (fun x => decide (x ≤ s[k])) :=
        (List.countP_eq_length.2 htake).symm
    _ ≤ (s.take (k + 1)).countP (fun x => decide (x ≤ s[k]))
          + (s.drop (k + 1)).countP (fun x => decide (x ≤ s[k])) := Nat.le_add_right _ _
    _ = s.countP (fun x => decide (x ≤ s[k])) := by
        rw [← List.countP_append, List.take_append_drop]

/-- In a sorted list, only elements before position `k` can be `< s[k]`. -/
theorem countP_lt_of_sorted {s : List α} (hs : s.Sorted (· ≤ ·)) {k : ℕ} (hk : k < s.length) :
    s.countP (fun x => decide (x < s[k])) ≤ k := by
  have hdrop : ∀ a ∈ s.drop k, ¬ (decide (a < s[k]) = true) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
    rw [List.getElem_drop]
    have hkj : k + j < s.length := by simp at hj; omega
    have := sorted_getElem_le hs (Nat.le_add_right k j) hkj
    simp only [decide_eq_true_eq, not_lt]
    exact this
  calc s.countP (fun x => decide (x < s[k]))
      = (s.take k).countP (fun x => decide (x < s[k]))
          + (s.drop k).countP (fun x => decide (x < s[k])) := by
          rw [← List.countP_append, List.take_append_drop]
    _ = (s.take k).countP (fun x => decide (x < s[k])) + 0 := by
          rw [List.countP_eq_zero.2 hdrop]
    _ ≤ (s.take k).length := by rw [Nat.add_zero]; exact List.countP_le_length
    _ ≤ k := by simp

/-! ### Property theorems -/

theorem error_iff_empty_thm (xs : List α) : error_iff_empty_prop xs (medianLow xs) := by
  unfold error_iff_empty_prop
  rw [medianLow_eq_getElem?, List.getElem?_eq_none_iff, length_sortData,
    ← List.length_eq_zero_iff]
  omega

theorem succeeds_thm (xs : List α) : succeeds_prop xs (medianLow xs) := by
  intro hne
  exact Option.ne_none_iff_exists'.1 (fun h => hne ((error_iff_empty_thm xs).1 h))

theorem mem_thm (xs : List α) : mem_prop xs (medianLow xs) := by
  intro m h
  rw [medianLow_eq_getElem?] at h
  exact (sortData_perm xs).mem_iff.1 (List.mem_of_getElem? h)

theorem odd_thm (xs : List α) : odd_prop xs (medianLow xs) := by
  intro h
  rw [medianLow_eq_getElem?]
  congr 1
  omega

theorem even_thm (xs : List α) : even_prop xs (medianLow xs) := by
  intro hne h
  have := List.length_pos_iff.2 hne
  rw [medianLow_eq_getElem?]
  congr 1
  omega

theorem rank_thm (xs : List α) : rank_prop xs (medianLow xs) := by
  intro m h
  rw [medianLow_eq_getElem?, List.getElem?_eq_some_iff] at h
  obtain ⟨hk, rfl⟩ := h
  constructor
  · rw [← (sortData_perm xs).countP_eq (fun x => decide (x < (sortData xs)[(xs.length - 1) / 2]))]
    exact countP_lt_of_sorted (sortData_sorted xs) hk
  · rw [← (sortData_perm xs).countP_eq (fun x => decide (x ≤ (sortData xs)[(xs.length - 1) / 2]))]
    exact countP_le_of_sorted (sortData_sorted xs) hk

theorem unique_thm (xs : List α) : unique_prop xs (medianLow xs) := by
  intro hne v hlt hle
  obtain ⟨m, hm⟩ := succeeds_thm xs hne
  have hr := rank_thm xs m hm
  rcases lt_trichotomy v m with hvm | rfl | hmv
  · exfalso
    have : xs.countP (fun x => decide (x ≤ v)) ≤ xs.countP (fun x => decide (x < m)) :=
      List.countP_mono_left (fun x _ hx => by
        simp only [decide_eq_true_eq] at hx ⊢; exact lt_of_le_of_lt hx hvm)
    omega
  · exact hm
  · exfalso
    have : xs.countP (fun x => decide (x ≤ m)) ≤ xs.countP (fun x => decide (x < v)) :=
      List.countP_mono_left (fun x _ hx => by
        simp only [decide_eq_true_eq] at hx ⊢; exact lt_of_le_of_lt hx hmv)
    omega

theorem half_thm (xs : List α) : half_prop xs (medianLow xs) := by
  intro m h
  have hr := rank_thm xs m h
  have hsplit := List.length_eq_countP_add_countP (fun x => decide (x < m)) (l := xs)
  have hcompl : xs.countP (fun x => decide ¬(decide (x < m) = true))
      = xs.countP (fun x => decide (m ≤ x)) :=
    List.countP_congr (fun x _ => by simp [not_lt])
  rw [hcompl] at hsplit
  constructor <;> omega

theorem perm_invariant_thm (xs ys : List α) : perm_invariant_prop xs ys := by
  intro h
  have hsort : sortData xs = sortData ys :=
    List.eq_of_perm_of_sorted (((sortData_perm xs).trans h).trans (sortData_perm ys).symm)
      (sortData_sorted xs) (sortData_sorted ys)
  rw [medianLow, medianLow, hsort]

/-! ## Post-condition -/

/-- Post-condition of `median_low` on input `xs` with result `r`. -/
def Post_prop (xs : List α) (r : Option α) : Prop :=
  error_iff_empty_prop xs r ∧ succeeds_prop xs r ∧ mem_prop xs r ∧ odd_prop xs r ∧
  even_prop xs r ∧ rank_prop xs r ∧ unique_prop xs r ∧ half_prop xs r

/-! ## Property-based tests

Executable Boolean forms of the properties, checked on random (`Plausible`) and on bounded
exhaustive / pseudo-random inputs at `Int`. -/

section PBT

/-- Executable rank conditions for a candidate value `v`. -/
def rankCheck (xs : List Int) (v : Int) : Bool :=
  xs.countP (· < v) ≤ (xs.length - 1) / 2 && (xs.length - 1) / 2 < xs.countP (· ≤ v)

/-- Executable form of `Post_prop xs r` (uniqueness tested for all data points `v ∈ xs`). -/
def postCheck (xs : List Int) (r : Option Int) : Bool :=
  (r.isNone == xs.isEmpty) &&
  (xs.isEmpty || r.isSome) &&
  r.all (fun m => decide (m ∈ xs)) &&
  (xs.length % 2 != 1 || r == (sortData xs)[xs.length / 2]?) &&
  (xs.isEmpty || xs.length % 2 != 0 || r == (sortData xs)[xs.length / 2 - 1]?) &&
  r.all (fun m => rankCheck xs m) &&
  (xs.isEmpty || xs.all (fun v => !(rankCheck xs v) || r == some v)) &&
  r.all (fun m => decide (xs.length ≤ 2 * xs.countP (· ≤ m) ∧ xs.length ≤ 2 * xs.countP (m ≤ ·)))

-- error_iff_empty_prop
#eval Plausible.Testable.check (∀ xs : List Int, (medianLow xs = none ↔ xs = []))
-- succeeds_prop (non-empty lists are generated as `x :: xs`)
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int), (medianLow (x :: xs)).isSome = true)
-- mem_prop
#eval Plausible.Testable.check
  (∀ xs : List Int, (medianLow xs).all (fun m => decide (m ∈ xs)) = true)
-- odd_prop (Boolean implication, so no samples are discarded)
#eval Plausible.Testable.check
  (∀ xs : List Int,
    (xs.length % 2 != 1 || medianLow xs == (sortData xs)[xs.length / 2]?) = true)
-- even_prop
#eval Plausible.Testable.check
  (∀ xs : List Int,
    (xs.isEmpty || xs.length % 2 != 0 || medianLow xs == (sortData xs)[xs.length / 2 - 1]?)
      = true)
-- rank_prop
#eval Plausible.Testable.check
  (∀ xs : List Int, (medianLow xs).all (fun m => rankCheck xs m) = true)
-- unique_prop (candidates: all data points, and all values of a window around the data)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (x :: xs).all (fun v => !(rankCheck (x :: xs) v) || medianLow (x :: xs) == some v) = true)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int),
    (List.range 25).all (fun i => let v : Int := (i : Int) - 12
      !(rankCheck (x :: xs) v) || medianLow (x :: xs) == some v) = true)
-- half_prop
#eval Plausible.Testable.check
  (∀ xs : List Int, (medianLow xs).all (fun m =>
    decide (xs.length ≤ 2 * xs.countP (· ≤ m) ∧ xs.length ≤ 2 * xs.countP (m ≤ ·))) = true)
-- perm_invariant_prop (instances: reversal, rotation / swapping two blocks)
#eval Plausible.Testable.check (∀ xs : List Int, medianLow xs.reverse = medianLow xs)
#eval Plausible.Testable.check (∀ xs ys : List Int, medianLow (xs ++ ys) = medianLow (ys ++ xs))
-- Post_prop (under Pre: non-empty lists `x :: xs`)
#eval Plausible.Testable.check
  (∀ (x : Int) (xs : List Int), postCheck (x :: xs) (medianLow (x :: xs)) = true)
-- Post_prop also holds for the empty list (where only the error clauses are informative)
example : postCheck [] (medianLow ([] : List Int)) = true := by native_decide

/-- All lists of length `≤ k` over the given alphabet. -/
def allLists (alphabet : List Int) : ℕ → List (List Int)
  | 0 => [[]]
  | k + 1 => [] :: (allLists alphabet k).flatMap (fun l => alphabet.map (· :: l))

/-- Pseudo-random lists of lengths `1 … 40`. -/
def pseudoRandomLists : List (List Int) :=
  (List.range 40).map (fun n =>
    (List.range (n + 1)).map (fun i => ((i * 37 + 11 * n + 5) % 23 : Int) - 11))

/-- Bounded test corpus: exhaustive over small lists plus pseudo-random longer ones. -/
def testLists : List (List Int) := allLists [-1, 0, 1, 2] 5 ++ pseudoRandomLists

#eval testLists.length   -- 1365 + 40

-- Bounded PBT: Post_prop (executable form) on every test list, both empty and non-empty.
example : testLists.all (fun xs => postCheck xs (medianLow xs)) = true := by native_decide
-- Bounded PBT: uniqueness for every candidate value in a window (not only data points).
example : testLists.all (fun xs => xs.isEmpty ||
    (List.range 31).all (fun i => let v : Int := (i : Int) - 15
      !(rankCheck xs v) || medianLow xs == some v)) = true := by native_decide
-- Bounded PBT: permutation invariance under reversal and rotations.
example : testLists.all (fun xs => medianLow xs.reverse == medianLow xs &&
    (List.range xs.length).all (fun i => medianLow xs == medianLow (xs.rotate i))) = true := by
  native_decide
-- Bounded PBT: odd / even index formulas.
example : testLists.all (fun xs =>
    (xs.length % 2 != 1 || medianLow xs == (sortData xs)[xs.length / 2]?) &&
    (xs.isEmpty || xs.length % 2 != 0 || medianLow xs == (sortData xs)[xs.length / 2 - 1]?))
    = true := by native_decide

end PBT

/-! ## Correctness theorem: `Pre → Post` -/

theorem medianLow_correct_thm (xs : List α) (_hpre : Pre xs) : Post_prop xs (medianLow xs) :=
  ⟨error_iff_empty_thm xs, succeeds_thm xs, mem_thm xs, odd_thm xs, even_thm xs, rank_thm xs,
    unique_thm xs, half_thm xs⟩

/-- Under the pre-condition the result is a data point satisfying the rank conditions. -/
theorem medianLow_spec_thm (xs : List α) (hpre : Pre xs) :
    ∃ m, medianLow xs = some m ∧ m ∈ xs ∧
      xs.countP (· < m) ≤ (xs.length - 1) / 2 ∧ (xs.length - 1) / 2 < xs.countP (· ≤ m) := by
  obtain ⟨m, hm⟩ := succeeds_thm xs hpre
  exact ⟨m, hm, mem_thm xs m hm, rank_thm xs m hm⟩

/-- `benchmark_median_low` and `median_low` agree, and the benchmark fails exactly when the
Python `pre` rejects the input. -/
theorem benchmarkMedianLow_thm (xs : List α) :
    benchmarkMedianLow xs = medianLow xs ∧ (benchmarkMedianLow xs = none ↔ ¬ Pre xs) := by
  refine ⟨rfl, ?_⟩
  unfold benchmarkMedianLow Pre
  rw [not_not]
  exact error_iff_empty_thm xs

/-- The generic development applies verbatim to real-valued data (`LinearOrder ℝ` is
noncomputable, so there are no `#eval` tests at `ℝ`, but all theorems hold there). -/
example (xs : List ℝ) (h : Pre xs) : ∃ m, medianLow xs = some m ∧ m ∈ xs ∧
    xs.length ≤ 2 * xs.countP (· ≤ m) ∧ xs.length ≤ 2 * xs.countP (m ≤ ·) := by
  obtain ⟨m, hm⟩ := succeeds_thm xs h
  exact ⟨m, hm, mem_thm xs m hm, half_thm xs m hm⟩

/-! ## Imperative implementation -/

/-- Imperative `median_low`: build the sorted data with a loop (insertion sort into a mutable
accumulator), count its length with a loop, then branch exactly like the Python code. -/
def medianLowImp (xs : List α) : Option α := Id.run do
  -- data = sorted(data)
  let mut sorted : List α := []
  for x in xs do
    sorted := sorted.orderedInsert (· ≤ ·) x
  -- n = len(data)
  let mut n : ℕ := 0
  for _y in sorted do
    n := n + 1
  if n = 0 then
    return none                    -- raise StatisticsError("no median for empty data")
  if n % 2 = 1 then
    return sorted[n / 2]?          -- return data[n // 2]
  else
    return sorted[n / 2 - 1]?      -- return data[n // 2 - 1]

/-! ## Imperative tests -/

example : medianLowImp ([1, 3, 5] : List Int) = some 3 := by native_decide
example : medianLowImp ([1, 2, 3, 4, 5, 6, 9] : List Int) = some 4 := by native_decide
example : medianLowImp ([1, 3, 5, 7] : List Int) = some 3 := by native_decide
example : medianLowImp ([1, 2, 3, 4, 5, 6] : List Int) = some 3 := by native_decide
example : medianLowImp ([42] : List Int) = some 42 := by native_decide
example : medianLowImp ([10, 20] : List Int) = some 10 := by native_decide
example : medianLowImp ([9, 1, 6, 2, 5, 4, 3] : List Int) = some 4 := by native_decide
example : medianLowImp ([-5, -1, 0, 3, 7] : List Int) = some 0 := by native_decide
example : medianLowImp ([-10, -5, 5, 10] : List Int) = some (-5) := by native_decide
example : medianLowImp ([] : List Int) = none := by native_decide
example : medianLowImp ([1/2, 3, 5/2] : List ℚ) = some (5/2) := by native_decide

#eval medianLowImp ([9, 1, 6, 2, 5, 4, 3] : List Int)   -- some 4
#eval medianLowImp ([1, 3, 5, 7] : List Int)            -- some 3
#eval medianLowImp ([] : List Int)                      -- none

-- PBT: functional and imperative versions agree.
#eval Plausible.Testable.check (∀ xs : List Int, medianLow xs = medianLowImp xs)
example : testLists.all (fun xs => medianLow xs == medianLowImp xs) = true := by native_decide

/-! ## Equivalence theorem -/

theorem foldl_orderedInsert_sorted (xs acc : List α) (hacc : acc.Sorted (· ≤ ·)) :
    (xs.foldl (fun acc x => acc.orderedInsert (· ≤ ·) x) acc).Sorted (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih => exact ih _ (List.Sorted.orderedInsert x acc hacc)

theorem foldl_orderedInsert_perm (xs acc : List α) :
    List.Perm (xs.foldl (fun acc x => acc.orderedInsert (· ≤ ·) x) acc) (xs ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.cons_append]
    exact (ih _).trans
      ((List.Perm.append_left xs (List.perm_orderedInsert _ x acc)).trans List.perm_middle)

/-- The imperative sorting loop computes `sorted(data)`. -/
theorem foldl_orderedInsert_eq_sortData (xs : List α) :
    xs.foldl (fun acc x => acc.orderedInsert (· ≤ ·) x) [] = sortData xs :=
  List.eq_of_perm_of_sorted
    ((foldl_orderedInsert_perm xs []).trans (by simpa using (sortData_perm xs).symm))
    (foldl_orderedInsert_sorted xs [] List.sorted_nil) (sortData_sorted xs)

/-- The `do`-block, unfolded to its functional meaning. -/
theorem medianLowImp_unfold (xs : List α) :
    medianLowImp xs =
      if xs.length = 0 then none
      else if xs.length % 2 = 1 then (sortData xs)[xs.length / 2]?
      else (sortData xs)[xs.length / 2 - 1]? := by
  simp only [medianLowImp, Id.run_bind, pure_bind, idRun_forIn_pure_yield,
    foldl_orderedInsert_eq_sortData, foldl_count, length_sortData]
  split_ifs <;> rfl

/-- Functional and imperative implementations agree on every input. -/
theorem medianLow_eq_medianLowImp_thm (xs : List α) : medianLow xs = medianLowImp xs := by
  rw [medianLowImp_unfold, medianLow_eq_getElem?]
  split_ifs with h0 hodd
  · rw [List.getElem?_eq_none_iff, length_sortData]; omega
  · congr 1; omega
  · congr 1; omega

/-- Consequently the imperative version satisfies the post-condition as well. -/
theorem medianLowImp_correct_thm (xs : List α) (hpre : Pre xs) : Post_prop xs (medianLowImp xs) :=
  medianLow_eq_medianLowImp_thm xs ▸ medianLow_correct_thm xs hpre

/-! ## Float layer

Executable IEEE-754 `Float` version for Python `float` inputs.  `Float` is not a `LinearOrder`
in Lean (NaN breaks totality), so the order-theoretic theorems above are stated for the exact
`LinearOrder` model; for NaN-free data the two agree.  The structural error behaviour is still
provable here. -/

namespace FloatLayer

/-- `median_low` on floats: `sorted(data)` is a merge sort by `≤`, then the Python branching. -/
def medianLow (xs : List Float) : Option Float :=
  pickLow (xs.mergeSort (fun a b => a ≤ b))

/-- Empty data raises, non-empty data returns a value (also for `Float`). -/
theorem medianLow_none_iff_thm (xs : List Float) : medianLow xs = none ↔ xs = [] := by
  rw [medianLow, pickLow_eq_getElem?, List.getElem?_eq_none_iff, List.length_mergeSort,
    ← List.length_eq_zero_iff]
  omega

#eval medianLow [1.0, 3.0, 5.0]           -- some 3.000000
#eval medianLow [1.0, 3.0, 5.0, 7.0]      -- some 3.000000
#eval medianLow [9.5, 1.5, 6.5, 2.5, 5.5] -- some 5.500000
#eval medianLow [-10.0, -5.0, 5.0, 10.0]  -- some (-5.000000)
#eval medianLow []                        -- none
example : (medianLow [1.0, 3.0, 5.0]).isSome = true := by native_decide
example : (medianLow []).isNone = true := by native_decide
-- PBT: not executable beyond `Float` equality tests (`Float` has no decidable `LinearOrder`);
-- the error behaviour is checked here on all small lists of a few float values.
example : ((List.range 6).all (fun n =>
    (medianLow ((List.range n).map (fun i => (i.toFloat - 2.5) * 1.5))).isNone == (n == 0)))
    = true := by native_decide

end FloatLayer

end «28_statistics_median_low»

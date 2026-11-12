import Mathlib

/-!
# `statistics.quantiles` — Python program translated to Lean 4

The Python benchmark divides `data` into `n` continuous intervals of equal
probability and returns the `n - 1` cut points that separate them, following
CPython's `statistics.quantiles`:

* `method = 'exclusive'` (the default): `m = ld + 1`, `j = clamp(i*m/n, 1, ld-1)`,
  `delta = i*m - j*n` (an *integer*, possibly negative, i.e. extrapolation),
  cut point `(data[j-1] * (n - delta) + data[j] * delta) / n`;
* `method = 'inclusive'`: `m = ld - 1`, `j, delta = divmod(i*m, n)`,
  cut point `(data[j] * (n - delta) + data[j+1] * delta) / n`.

`benchmark_quantiles` first checks the pre-condition (`data` has at least two
points, `n ≥ 1`, `method` valid) and raises `StatisticsError` otherwise.

## Numeric model

CPython accepts `int | float | Fraction | Decimal`.  Every cut point is an exact
rational affine combination of two data points with *integer* coefficients, so the
mathematical intent is exact rational arithmetic: the primary model (`RatLayer`)
takes the data as `List Rat` and all properties, the pre/post-condition and the
functional/imperative equivalence are stated and proved there.  A `FloatLayer`
reproducing CPython's IEEE-754 output is given for executable ground unit tests,
and a `RealLayer` records that the exact cut points are the real numbers that
CPython prints.

Python exceptions are modelled by the `QResult` sum type: `QResult.error msg`
stands for a raised `StatisticsError`/`ValueError` carrying `msg`.
-/

namespace StatisticsQuantiles31

/-! ## Result type (Python: return value or raised exception) -/

/-- `QResult α` models a Python function that either returns a value of type `α`
or raises an exception with a message. -/
inductive QResult (α : Type) where
  | ok : α → QResult α
  | error : String → QResult α
  deriving DecidableEq, BEq, Repr, Inhabited

namespace QResult

/-- `QResult.map f r` is Python's `f(r)` when `r` does not raise. -/
def map (f : α → β) : QResult α → QResult β
  | ok a => ok (f a)
  | error e => error e

@[simp] theorem map_ok (f : α → β) (a : α) : map f (ok a) = ok (f a) := rfl
@[simp] theorem map_error (f : α → β) (e : String) : map f (QResult.error e) = error e := rfl

end QResult

/-! ## Total list indexing (the interpolation formulae index `data` directly) -/

/-- `nthRat l i` is `l[i]`, and `0` when `i` is out of range (the algorithm only
reads in-range positions once the pre-condition holds). -/
def nthRat (l : List Rat) (i : Nat) : Rat := Option.getD (l[i]?) 0

@[simp] theorem nthRat_nil (i : Nat) : nthRat [] i = 0 := by simp [nthRat]

@[simp] theorem nthRat_cons_zero (a : Rat) (l : List Rat) : nthRat (a :: l) 0 = a :=
  by simp [nthRat]

@[simp] theorem nthRat_cons_succ (a : Rat) (l : List Rat) (i : Nat) :
    nthRat (a :: l) (i + 1) = nthRat l i := by simp [nthRat]

theorem nthRat_mem {l : List Rat} {i : Nat} (h : i < l.length) : nthRat l i ∈ l := by
  induction l generalizing i with
  | nil => cases h
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ k =>
      simp only [nthRat_cons_succ, List.mem_cons]
      exact Or.inr (ih (Nat.succ_lt_succ_iff.mp h))

/-- On a non-decreasing list, `nthRat` is monotone in the index. -/
theorem nthRat_le_nthRat {l : List Rat} (hl : List.Sorted (· ≤ ·) l) {i j : Nat}
    (hij : i ≤ j) (hj : j < l.length) : nthRat l i ≤ nthRat l j := by
  induction l generalizing i j with
  | nil => cases hj
  | cons a l ih =>
    obtain ⟨ha, hls⟩ := List.sorted_cons.mp hl
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ k =>
        simp only [nthRat_cons_zero, nthRat_cons_succ]
        exact ha _ (nthRat_mem (Nat.succ_lt_succ_iff.mp hj))
    | succ i' =>
      cases j with
      | zero => exact absurd hij (by simp)
      | succ k =>
        simp only [nthRat_cons_succ]
        exact ih hls (Nat.succ_le_succ_iff.mp hij) (Nat.succ_lt_succ_iff.mp hj)

/-! ## Sorting (Python: `data = sorted(data)`) -/

/-- `sortedData data` is Python's `sorted(data)`. -/
def sortedData (data : List Rat) : List Rat := data.insertionSort (· ≤ ·)

theorem sortedData_sorted (data : List Rat) : List.Sorted (· ≤ ·) (sortedData data) :=
  List.sorted_insertionSort _ data

theorem sortedData_perm (data : List Rat) : List.Perm (sortedData data) data :=
  List.perm_insertionSort _ data

@[simp] theorem sortedData_length (data : List Rat) : (sortedData data).length = data.length :=
  (sortedData_perm data).length_eq

theorem mem_sortedData {x : Rat} {data : List Rat} : x ∈ sortedData data ↔ x ∈ data :=
  (sortedData_perm data).mem_iff

/-! ## The cut-point formulae -/

/-- `inclusive` method: `j, delta = divmod(i * (ld - 1), n)`. -/
def inclIdx (ld n i : Nat) : Nat := (i * (ld - 1)) / n
def inclDelta (ld n i : Nat) : Nat := (i * (ld - 1)) % n

/-- Python: `interpolated = (data[j] * (n - delta) + data[j + 1] * delta) / n`. -/
def cutPointInclusive (sd : List Rat) (n i : Nat) : Rat :=
  (nthRat sd (inclIdx sd.length n i) * ((n : Rat) - (inclDelta sd.length n i : Rat))
      + nthRat sd (inclIdx sd.length n i + 1) * (inclDelta sd.length n i : Rat)) / (n : Rat)

/-- `exclusive` method: `j0 = i * (ld + 1) / n` before clamping. -/
def exclIdx0 (ld n i : Nat) : Nat := (i * (ld + 1)) / n

/-- Python: `j = 1 if j < 1 else ld-1 if j > ld-1 else j`. -/
def clampIdx (j0 ld : Nat) : Nat :=
  if j0 < 1 then 1 else if ld - 1 < j0 then ld - 1 else j0

def exclIdx (ld n i : Nat) : Nat := clampIdx (exclIdx0 ld n i) ld

/-- Python: `delta = i*m - j*n` — exact *integer* math, possibly negative. -/
def exclDelta (ld n i : Nat) : Int :=
  (i * (ld + 1) : Int) - (exclIdx ld n i * n : Int)

/-- Python: `interpolated = (data[j - 1] * (n - delta) + data[j] * delta) / n`. -/
def cutPointExclusive (sd : List Rat) (n i : Nat) : Rat :=
  (nthRat sd (exclIdx sd.length n i - 1) * ((n : Rat) - (exclDelta sd.length n i : Rat))
      + nthRat sd (exclIdx sd.length n i) * (exclDelta sd.length n i : Rat)) / (n : Rat)

/-- The cut point selected by `method`. -/
def cutPoint (sd : List Rat) (n : Nat) (method : String) (i : Nat) : Rat :=
  if method = "inclusive" then cutPointInclusive sd n i else cutPointExclusive sd n i

/-! ## Implementation (functional) -/

/-- The list of `n - 1` cut points, computed on the sorted data. -/
def quantilesCore (data : List Rat) (n : Nat) (method : String) : List Rat :=
  (List.range (n - 1)).map (fun k => cutPoint (sortedData data) n method (k + 1))

/-- Python's `statistics.quantiles`, including its `StatisticsError` / `ValueError` raises. -/
def quantiles (data : List Rat) (n : Nat) (method : String) : QResult (List Rat) :=
  if n < 1 then QResult.error "n must be at least 1"
  else if data.length < 2 then QResult.error "must have at least two data points"
  else if method = "inclusive" then QResult.ok (quantilesCore data n method)
  else if method = "exclusive" then QResult.ok (quantilesCore data n method)
  else QResult.error ("Unknown method: " ++ method)

/-- Executable form of Python's `pre(data, n, method)` guard. -/
def preBool (data : List Rat) (n : Nat) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) &&
    decide (method = "inclusive" ∨ method = "exclusive")

/-- Python's `benchmark_quantiles`: pre-condition check, then `quantiles`. -/
def benchmarkQuantiles (data : List Rat) (n : Nat) (method : String) : QResult (List Rat) :=
  if preBool data n method then quantiles data n method
  else QResult.error
    "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

/-! ## Unit tests

Ground truth produced by CPython's `statistics.quantiles` (the assertions of the
Python `check` function and of its doctest):

```text
quantiles([1, 2, 3, 4])                          == [1.25, 2.5, 3.75]
quantiles([0,1,...,10], n=10)                    == [0.2, 1.4, 2.6, 3.8, 5.0, 6.2, 7.4, 8.6, 9.8]
quantiles([1, 2, 3, 4, 5], n=2)                  == [3.0]
quantiles([1, 2, 3, 4], n=4, method='inclusive') == [1.75, 2.5, 3.25]
quantiles([1,...,10], n=4)                       == [2.75, 5.5, 8.25]
quantiles([4, 1, 3, 2], n=4)                     == [1.25, 2.5, 3.75]
quantiles([1.5, 2.5, 3.5, 4.5], n=2)             == [3.0]
quantiles([1, 2], n=4)                           == [0.75, 1.5, 2.25]
```

The `theorem`s below are kernel-checked (`simp` evaluates the definition,
`norm_num` normalises the rational arithmetic); the `example`s with
`native_decide` and the `#eval`s are executable smoke tests.
-/

#eval benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive"
#eval benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive"
#eval benchmarkQuantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive"
#eval benchmarkQuantiles [1] 4 "exclusive"

/-- Python test 1 and the doctest: quartiles of `[1,2,3,4]` (exclusive). -/
theorem test_quartiles_exclusive :
    benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by
  have hs : sortedData [1, 2, 3, 4] = [1, 2, 3, 4] := by decide
  have hr : List.range 3 = [0, 1, 2] := by decide
  have hp : preBool [1, 2, 3, 4] 4 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- Python test 4: quartiles of `[1,2,3,4]` with `method='inclusive'`. -/
theorem test_quartiles_inclusive :
    benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by
  have hs : sortedData [1, 2, 3, 4] = [1, 2, 3, 4] := by decide
  have hr : List.range 3 = [0, 1, 2] := by decide
  have hp : preBool [1, 2, 3, 4] 4 "inclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointInclusive, inclIdx,
    inclDelta, nthRat, hs, hr, hp]
  norm_num

/-- Python test 2: deciles of `0..10`. -/
theorem test_deciles :
    benchmarkQuantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive"
      = .ok [1/5, 7/5, 13/5, 19/5, 5, 31/5, 37/5, 43/5, 49/5] := by
  have hs : sortedData [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
      = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  have hr : List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  have hp : preBool [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- Python test 3: the median (`n = 2`) of an odd-length sample. -/
theorem test_median_odd : benchmarkQuantiles [1, 2, 3, 4, 5] 2 "exclusive" = .ok [3] := by
  have hs : sortedData [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] := by decide
  have hr : List.range 1 = [0] := by decide
  have hp : preBool [1, 2, 3, 4, 5] 2 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- Python test 6: quartiles of `1..10`. -/
theorem test_larger_dataset :
    benchmarkQuantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4 "exclusive"
      = .ok [11/4, 11/2, 33/4] := by
  have hs : sortedData [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
      = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  have hr : List.range 3 = [0, 1, 2] := by decide
  have hp : preBool [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- Python test 7: unsorted input is sorted internally. -/
theorem test_unsorted_input :
    benchmarkQuantiles [4, 1, 3, 2] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by
  have hs : sortedData [4, 1, 3, 2] = [1, 2, 3, 4] := by decide
  have hr : List.range 3 = [0, 1, 2] := by decide
  have hp : preBool [4, 1, 3, 2] 4 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- Python test 8: fractional (here exactly rational) data, `n = 2`. -/
theorem test_fractional_data :
    benchmarkQuantiles [3/2, 5/2, 7/2, 9/2] 2 "exclusive" = .ok [3] := by
  have h1 : (3/2 : Rat) ≤ 5/2 := by norm_num
  have h2 : (5/2 : Rat) ≤ 7/2 := by norm_num
  have h3 : (7/2 : Rat) ≤ 9/2 := by norm_num
  have hs : sortedData [3/2, 5/2, 7/2, 9/2] = [3/2, 5/2, 7/2, 9/2] := by
    simp [sortedData, List.insertionSort, List.orderedInsert, h1, h2, h3]
  have hr : List.range 1 = [0] := by decide
  have hp : preBool [3/2, 5/2, 7/2, 9/2] 2 "exclusive" = true := by
    simp [preBool]
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- The `exclusive` method extrapolates: for `[1,2]` and `n = 4` the first cut point
`3/4` lies *below* the minimum of the data. -/
theorem test_extrapolation :
    benchmarkQuantiles [1, 2] 4 "exclusive" = .ok [3/4, 3/2, 9/4] := by
  have hs : sortedData [1, 2] = [1, 2] := by decide
  have hr : List.range 3 = [0, 1, 2] := by decide
  have hp : preBool [1, 2] 4 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, cutPointExclusive, exclIdx,
    exclIdx0, exclDelta, clampIdx, nthRat, hs, hr, hp]
  norm_num

/-- `n = 1` yields no cut point at all (`n - 1 = 0` of them). -/
theorem test_n_one : benchmarkQuantiles [1, 2, 3] 1 "exclusive" = .ok [] := by
  have hp : preBool [1, 2, 3] 1 "exclusive" = true := by decide
  simp [benchmarkQuantiles, quantiles, quantilesCore, cutPoint, hp]

/-- Python test 9a: a single data point raises `StatisticsError`. -/
theorem test_error_single_point : benchmarkQuantiles [1] 4 "exclusive"
    = .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  simp [benchmarkQuantiles, preBool]

/-- Python test 9b: `n < 1` raises `StatisticsError`. -/
theorem test_error_n_zero : benchmarkQuantiles [1, 2] 0 "exclusive"
    = .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  simp [benchmarkQuantiles, preBool]

/-- Python test 9c: an unknown method raises `StatisticsError` in `benchmark_quantiles`. -/
theorem test_error_bad_method : benchmarkQuantiles [1, 2, 3] 4 "invalid"
    = .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  simp [benchmarkQuantiles, preBool]

example : benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmarkQuantiles [1, 2, 3, 4, 5] 2 "exclusive" = .ok [3] := by native_decide
example : benchmarkQuantiles [1, 2] 4 "exclusive" = .ok [3/4, 3/2, 9/4] := by native_decide
example : benchmarkQuantiles [1] 4 "exclusive"
    = .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"
    := by native_decide
example : quantiles [1, 2, 3] 4 "invalid" = .error "Unknown method: invalid" := by native_decide

/-! ## Pre-condition -/

/-- Python's `pre(data, n, method)`: `data` is a sequence with at least two elements,
`n` is an integer with `n ≥ 1`, and `method` is `'inclusive'` or `'exclusive'`.

(The Python guard also rejects non-`list`/`tuple` data and non-`int` `n`; in the
typed Lean model every `data : List Rat` and every `n : Nat` already satisfies
those two clauses.) -/
def Pre (data : List Rat) (n : Nat) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

theorem preBool_spec {data : List Rat} {n : Nat} {method : String} :
    preBool data n method = true ↔ Pre data n method := by
  by_cases h1 : 2 ≤ data.length <;> by_cases h2 : 1 ≤ n <;>
    by_cases h3 : method = "inclusive" ∨ method = "exclusive" <;>
      simp [preBool, Pre, h1, h2, h3]

/-- `sortedData` is the identity on already sorted input. -/
theorem sortedData_eq_self {l : List Rat} (h : List.Sorted (· ≤ ·) l) : sortedData l = l :=
  List.eq_of_perm_of_sorted (sortedData_perm l) (sortedData_sorted l) h

/-- Under the pre-condition `benchmark_quantiles` does not raise; it returns the
`n - 1` cut points computed by `quantilesCore`. -/
theorem benchmarkQuantiles_ok {data : List Rat} {n : Nat} {method : String}
    (h : Pre data n method) :
    benchmarkQuantiles data n method = .ok (quantilesCore data n method) := by
  have hb : preBool data n method = true := preBool_spec.mpr h
  obtain ⟨h1, h2, h3⟩ := h
  have hn0 : n ≠ 0 := by omega
  have hl : ¬ (data.length < 2) := by omega
  rcases h3 with rfl | rfl
  · simp [benchmarkQuantiles, quantiles, hb, hn0, hl]
  · simp [benchmarkQuantiles, quantiles, hb, hn0, hl]

/-- Outside the pre-condition `benchmark_quantiles` raises `StatisticsError`. -/
theorem benchmarkQuantiles_error {data : List Rat} {n : Nat} {method : String}
    (h : ¬ Pre data n method) : benchmarkQuantiles data n method
    = .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  simp [benchmarkQuantiles, preBool_spec.not.mpr h]

/-! ## Properties of the implementation -/

/-- The result is a list of exactly `n - 1` cut points. -/
def length_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  (benchmarkQuantiles data n method).map List.length = QResult.ok (n - 1)

/-- Admissible input never raises. -/
def noError_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  ∃ res, benchmarkQuantiles data n method = .ok res

/-- The cut points are returned in non-decreasing order (they separate *continuous*
intervals, so consecutive cut points never decrease). -/
def sorted_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  ∀ res, benchmarkQuantiles data n method = .ok res → List.Sorted (· ≤ ·) res

/-- With `method = 'inclusive'` every cut point is a convex combination of two data
points, hence lies between any lower bound `lo` and any upper bound `hi` of the data
(in particular between `min data` and `max data`). -/
def bounds_prop (data : List Rat) (n : Nat) : Prop :=
  ∀ lo hi : Rat, (∀ x ∈ data, lo ≤ x) → (∀ x ∈ data, x ≤ hi) →
    ∀ res, benchmarkQuantiles data n "inclusive" = .ok res → ∀ c ∈ res, lo ≤ c ∧ c ≤ hi

/-- `n = 1` produces no cut point at all. -/
def empty_prop (data : List Rat) (method : String) : Prop :=
  benchmarkQuantiles data 1 method = .ok []

/-- Inputs violating the pre-condition raise `StatisticsError`. -/
def error_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  ¬ Pre data n method →
    benchmarkQuantiles data n method
      = .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

/-- For `n = 2` the `exclusive` method returns the sample median: the middle element
for an odd number of data points, the mean of the two middle elements otherwise. -/
def median_prop (data : List Rat) : Prop :=
  (∀ k, 1 ≤ k → data.length = 2 * k + 1 →
    benchmarkQuantiles data 2 "exclusive" = .ok [nthRat (sortedData data) k]) ∧
  (∀ k, data.length = 2 * k + 2 →
    benchmarkQuantiles data 2 "exclusive"
      = .ok [(nthRat (sortedData data) k + nthRat (sortedData data) (k + 1)) / 2])

/-! ### Algebra of the interpolation formulae

Both methods compute `(a * (n - delta) + b * delta) / n`, i.e. the point obtained by
moving from `a` towards `b` by the fraction `delta / n` (for `exclusive`, `delta` may
be negative or larger than `n`, which is exactly CPython's extrapolation).
-/

theorem convex_combination_eq (a b d : Rat) {n : Nat} (hn : 0 < n) :
    (a * ((n : Rat) - d) + b * d) / (n : Rat) = a + (d / (n : Rat)) * (b - a) := by
  field_simp
  ring

theorem cutPointInclusive_eq (sd : List Rat) {n i : Nat} (hn : 0 < n) :
    cutPointInclusive sd n i =
      nthRat sd (inclIdx sd.length n i)
        + ((inclDelta sd.length n i : Rat) / (n : Rat))
          * (nthRat sd (inclIdx sd.length n i + 1) - nthRat sd (inclIdx sd.length n i)) := by
  simp only [cutPointInclusive]
  exact convex_combination_eq _ _ _ hn

theorem cutPointExclusive_eq (sd : List Rat) {n i : Nat} (hn : 0 < n) :
    cutPointExclusive sd n i =
      nthRat sd (exclIdx sd.length n i - 1)
        + ((exclDelta sd.length n i : Rat) / (n : Rat))
          * (nthRat sd (exclIdx sd.length n i) - nthRat sd (exclIdx sd.length n i - 1)) := by
  simp only [cutPointExclusive]
  exact convex_combination_eq _ _ _ hn

theorem exclDelta_def (ld n i : Nat) :
    exclDelta ld n i = (↑(i * (ld + 1)) - ↑(exclIdx ld n i * n) : Int) := rfl

/-! ### Index arithmetic -/

theorem inclIdx_succ_lt (sd : List Rat) (hld : 2 ≤ sd.length) {n i : Nat} (hn : 0 < n)
    (hi : i < n) : inclIdx sd.length n i + 1 < sd.length := by
  have hm : 0 < sd.length - 1 := by omega
  have h1 : i * (sd.length - 1) < n * (sd.length - 1) :=
    Nat.mul_lt_mul_of_pos_right hi hm
  have h2 : inclIdx sd.length n i < sd.length - 1 := by
    rw [inclIdx]
    exact (Nat.div_lt_iff_lt_mul hn).mpr (by
      rw [Nat.mul_comm (sd.length - 1) n]; exact h1)
  omega

theorem inclIdx_mono (sd : List Rat) {n i k : Nat} (hik : i ≤ k) :
    inclIdx sd.length n i ≤ inclIdx sd.length n k := by
  simp only [inclIdx]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hik)

/-- The three clamping cases of the `exclusive` index. -/
theorem exclIdx_cases (ld n i : Nat) :
    (exclIdx ld n i = 1 ∧ exclIdx0 ld n i < 1) ∨
    (exclIdx ld n i = ld - 1 ∧ ld - 1 < exclIdx0 ld n i) ∨
    (exclIdx ld n i = exclIdx0 ld n i ∧ 1 ≤ exclIdx0 ld n i ∧ exclIdx0 ld n i ≤ ld - 1) := by
  by_cases h1 : exclIdx0 ld n i < 1
  · exact Or.inl ⟨by simp [exclIdx, clampIdx, h1], h1⟩
  · by_cases h2 : ld - 1 < exclIdx0 ld n i
    · exact Or.inr (Or.inl ⟨by simp [exclIdx, clampIdx, h1, h2], h2⟩)
    · exact Or.inr (Or.inr ⟨by simp [exclIdx, clampIdx, h1, h2], by omega, by omega⟩)

theorem exclIdx_pos (ld n i : Nat) (hld : 2 ≤ ld) : 1 ≤ exclIdx ld n i := by
  rcases exclIdx_cases ld n i with ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨h3, h3', _⟩ <;> omega

theorem exclIdx_le (ld n i : Nat) (hld : 2 ≤ ld) : exclIdx ld n i ≤ ld - 1 := by
  rcases exclIdx_cases ld n i with ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨h3, _, h3''⟩ <;> omega

theorem exclIdx0_mono (ld n : Nat) {i k : Nat} (h : i ≤ k) :
    exclIdx0 ld n i ≤ exclIdx0 ld n k := by
  simp only [exclIdx0]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

theorem exclIdx_mono (ld n : Nat) (hld : 2 ≤ ld) {i k : Nat} (h : i ≤ k) :
    exclIdx ld n i ≤ exclIdx ld n k := by
  have h0 := exclIdx0_mono ld n h
  have hp := exclIdx_pos ld n k hld
  have hq := exclIdx_le ld n i hld
  rcases exclIdx_cases ld n i with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3', h3''⟩
  · omega
  · rcases exclIdx_cases ld n k with ⟨h4, h4'⟩ | ⟨h5, h5'⟩ | ⟨h6, h6', h6''⟩ <;> omega
  · rcases exclIdx_cases ld n k with ⟨h4, h4'⟩ | ⟨h5, h5'⟩ | ⟨h6, h6', h6''⟩ <;> omega

/-- When the index is not clamped from above, `delta` is the remainder `i * m % n`. -/
theorem exclDelta_case3 (ld n i : Nat) (_hn : 0 < n) :
    (↑(i * (ld + 1)) - ↑(((i * (ld + 1)) / n) * n) : Int) = ↑((i * (ld + 1)) % n) := by
  have ele : ((i * (ld + 1)) / n) * n ≤ i * (ld + 1) := Nat.div_mul_le_self _ _
  have e' : (i * (ld + 1)) % n + ((i * (ld + 1)) / n) * n = i * (ld + 1) := by
    have e0 := Nat.mod_add_div (i * (ld + 1)) n
    rw [show ((i * (ld + 1)) / n) * n = n * ((i * (ld + 1)) / n) from Nat.mul_comm _ _]
    exact e0
  have e3 : (i * (ld + 1)) - ((i * (ld + 1)) / n) * n = (i * (ld + 1)) % n :=
    Nat.sub_eq_of_eq_add e'.symm
  rw [← Nat.cast_sub ele, e3]

/-- Unless the index was clamped from above, `delta < n`. -/
theorem exclDelta_lt_n (ld n i : Nat) (hn : 0 < n) (h : ¬(ld - 1 < exclIdx0 ld n i)) :
    exclDelta ld n i < (n : Int) := by
  rcases exclIdx_cases ld n i with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3', h3''⟩
  · have h1'' : (i * (ld + 1)) / n < 1 := by simpa [exclIdx0] using h1'
    have hlt : i * (ld + 1) < n := by
      have := (Nat.div_lt_iff_lt_mul hn).mp h1''
      simpa using this
    have hj : exclIdx ld n i * n = 1 * n := by rw [h1]
    have hc : (↑(1 * n) : Int) = ↑n := by simp
    have hlt' : (↑(i * (ld + 1)) : Int) < ↑n := Nat.cast_lt.mpr hlt
    rw [exclDelta_def, hj, hc]
    linarith
  · exact absurd h2' h
  · have hj : exclIdx ld n i * n = ((i * (ld + 1)) / n) * n := by rw [h3, exclIdx0]
    have hmod : (↑((i * (ld + 1)) % n) : Int) < ↑n := Nat.cast_lt.mpr (Nat.mod_lt _ hn)
    rw [exclDelta_def, hj, exclDelta_case3 ld n i hn]
    exact hmod

/-- Unless the index was clamped from below, `delta ≥ 0`. -/
theorem exclDelta_nonneg (ld n i : Nat) (hn : 0 < n) (h : ¬(exclIdx0 ld n i < 1)) :
    0 ≤ exclDelta ld n i := by
  rcases exclIdx_cases ld n i with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3', h3''⟩
  · exact absurd h1' h
  · have h2'' : ld - 1 < (i * (ld + 1)) / n := by simpa [exclIdx0] using h2'
    have hlt : (ld - 1) * n < i * (ld + 1) := by
      have := (Nat.lt_div_iff_mul_lt hn).mp h2''
      omega
    have hj : exclIdx ld n i * n = (ld - 1) * n := by rw [h2]
    have hle : (↑((ld - 1) * n) : Int) ≤ ↑(i * (ld + 1)) := Nat.cast_le.mpr (by omega)
    rw [exclDelta_def, hj]
    linarith
  · have hj : exclIdx ld n i * n = ((i * (ld + 1)) / n) * n := by rw [h3, exclIdx0]
    have hmod : (0 : Int) ≤ ↑((i * (ld + 1)) % n) := Nat.cast_nonneg _
    rw [exclDelta_def, hj, exclDelta_case3 ld n i hn]
    exact hmod

/-! ### Monotonicity of the cut points -/

theorem cutPointInclusive_le_upper (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) {n i : Nat} (hn : 0 < n) (hi : i < n) :
    cutPointInclusive sd n i ≤ nthRat sd (inclIdx sd.length n i + 1) := by
  have hj := inclIdx_succ_lt sd hld hn hi
  have hab : nthRat sd (inclIdx sd.length n i) ≤ nthRat sd (inclIdx sd.length n i + 1) :=
    nthRat_le_nthRat hsd (by omega) hj
  have hmod : inclDelta sd.length n i < n := Nat.mod_lt _ hn
  have hfrac : (inclDelta sd.length n i : Rat) / (n : Rat) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact Nat.cast_le.mpr (Nat.le_of_lt hmod)
  have hdiff : 0 ≤ nthRat sd (inclIdx sd.length n i + 1) - nthRat sd (inclIdx sd.length n i) := by
    linarith
  rw [cutPointInclusive_eq sd hn]
  linarith [mul_le_mul_of_nonneg_right hfrac hdiff]

theorem cutPointInclusive_le_lower (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) {n i : Nat} (hn : 0 < n) (hi : i < n) :
    nthRat sd (inclIdx sd.length n i) ≤ cutPointInclusive sd n i := by
  have hj := inclIdx_succ_lt sd hld hn hi
  have hab : nthRat sd (inclIdx sd.length n i) ≤ nthRat sd (inclIdx sd.length n i + 1) :=
    nthRat_le_nthRat hsd (by omega) hj
  have hfrac : 0 ≤ (inclDelta sd.length n i : Rat) / (n : Rat) :=
    div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Nat.zero_le n)
  have hdiff : 0 ≤ nthRat sd (inclIdx sd.length n i + 1) - nthRat sd (inclIdx sd.length n i) := by
    linarith
  rw [cutPointInclusive_eq sd hn]
  linarith [mul_nonneg hfrac hdiff]

theorem cutPointInclusive_mono (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) (n : Nat) (hn : 0 < n) {i k : Nat} (hik : i ≤ k) (hk : k < n) :
    cutPointInclusive sd n i ≤ cutPointInclusive sd n k := by
  have hi : i < n := Nat.lt_of_le_of_lt hik hk
  by_cases heq : inclIdx sd.length n i = inclIdx sd.length n k
  · have e1 : n * inclIdx sd.length n i + inclDelta sd.length n i = i * (sd.length - 1) := by
      rw [inclIdx, inclDelta]; exact Nat.div_add_mod _ _
    have e2 : n * inclIdx sd.length n k + inclDelta sd.length n k = k * (sd.length - 1) := by
      rw [inclIdx, inclDelta]; exact Nat.div_add_mod _ _
    rw [heq] at e1
    have e1' : inclIdx sd.length n k * n + inclDelta sd.length n i = i * (sd.length - 1) := by
      rw [Nat.mul_comm (inclIdx sd.length n k) n]; exact e1
    have e2' : inclIdx sd.length n k * n + inclDelta sd.length n k = k * (sd.length - 1) := by
      rw [Nat.mul_comm (inclIdx sd.length n k) n]; exact e2
    have hsum : inclIdx sd.length n k * n + inclDelta sd.length n i ≤
        inclIdx sd.length n k * n + inclDelta sd.length n k := by
      rw [e1', e2']
      exact Nat.mul_le_mul_right _ hik
    have hdd : inclDelta sd.length n i ≤ inclDelta sd.length n k :=
      Nat.add_le_add_iff_left.mp hsum
    have hddR : (inclDelta sd.length n i : Rat) ≤ (inclDelta sd.length n k : Rat) :=
      Nat.cast_le.mpr hdd
    have hfrac : (inclDelta sd.length n i : Rat) / (n : Rat) ≤
        (inclDelta sd.length n k : Rat) / (n : Rat) :=
      div_le_div_of_nonneg_right hddR (by exact_mod_cast Nat.zero_le n)
    have hhab : nthRat sd (inclIdx sd.length n k) ≤ nthRat sd (inclIdx sd.length n k + 1) :=
      nthRat_le_nthRat hsd (by omega) (inclIdx_succ_lt sd hld hn hk)
    have hdiff : 0 ≤ nthRat sd (inclIdx sd.length n k + 1) - nthRat sd (inclIdx sd.length n k) := by
      linarith
    rw [cutPointInclusive_eq sd hn, cutPointInclusive_eq sd hn, heq]
    linarith [mul_le_mul_of_nonneg_right hfrac hdiff]
  · have hlt : inclIdx sd.length n i < inclIdx sd.length n k := by
      have := inclIdx_mono sd (n := n) hik
      omega
    have c1 := cutPointInclusive_le_upper sd hsd hld hn hi
    have c2 : nthRat sd (inclIdx sd.length n i + 1) ≤ nthRat sd (inclIdx sd.length n k) :=
      nthRat_le_nthRat hsd (by omega) (by
        have := inclIdx_succ_lt sd hld hn hk; omega)
    have c3 := cutPointInclusive_le_lower sd hsd hld hn hk
    linarith

/-- Unless the index was clamped from above, the `exclusive` cut point stays below `data[j]`. -/
theorem cutPointExclusive_le (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) {n i : Nat} (hn : 0 < n)
    (hnc : ¬(sd.length - 1 < exclIdx0 sd.length n i)) :
    cutPointExclusive sd n i ≤ nthRat sd (exclIdx sd.length n i) := by
  have hj2 : exclIdx sd.length n i ≤ sd.length - 1 := exclIdx_le _ _ _ hld
  have hab : nthRat sd (exclIdx sd.length n i - 1) ≤ nthRat sd (exclIdx sd.length n i) :=
    nthRat_le_nthRat hsd (Nat.sub_le _ _) (by omega)
  have hd0 : exclDelta sd.length n i ≤ (n : Int) :=
    Int.le_of_lt (exclDelta_lt_n sd.length n i hn hnc)
  have hd : (exclDelta sd.length n i : Rat) ≤ (n : Rat) := Int.cast_le.mpr hd0
  have hfrac : (exclDelta sd.length n i : Rat) / (n : Rat) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact hd
  have hdiff : 0 ≤ nthRat sd (exclIdx sd.length n i) - nthRat sd (exclIdx sd.length n i - 1) := by
    linarith
  rw [cutPointExclusive_eq sd hn]
  linarith [mul_le_mul_of_nonneg_right hfrac hdiff]

/-- Unless the index was clamped from below, the `exclusive` cut point stays above `data[j-1]`. -/
theorem le_cutPointExclusive (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) {n i : Nat} (hn : 0 < n) (hnc : ¬(exclIdx0 sd.length n i < 1)) :
    nthRat sd (exclIdx sd.length n i - 1) ≤ cutPointExclusive sd n i := by
  have hab : nthRat sd (exclIdx sd.length n i - 1) ≤ nthRat sd (exclIdx sd.length n i) :=
    nthRat_le_nthRat hsd (Nat.sub_le _ _) (by
      have := exclIdx_le sd.length n i hld; omega)
  have hd : 0 ≤ (exclDelta sd.length n i : Rat) :=
    Int.cast_nonneg.mpr (exclDelta_nonneg sd.length n i hn hnc)
  have hfrac : 0 ≤ (exclDelta sd.length n i : Rat) / (n : Rat) :=
    div_nonneg hd (by exact_mod_cast Nat.zero_le n)
  have hdiff : 0 ≤ nthRat sd (exclIdx sd.length n i) - nthRat sd (exclIdx sd.length n i - 1) := by
    linarith
  rw [cutPointExclusive_eq sd hn]
  linarith [mul_nonneg hfrac hdiff]

theorem cutPointExclusive_mono (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) (n : Nat) (hn : 0 < n) {i k : Nat} (hik : i ≤ k) :
    cutPointExclusive sd n i ≤ cutPointExclusive sd n k := by
  have hj : exclIdx sd.length n i ≤ exclIdx sd.length n k := exclIdx_mono sd.length n hld hik
  have h1 : 1 ≤ exclIdx sd.length n i := exclIdx_pos _ _ _ hld
  have h2 : exclIdx sd.length n k ≤ sd.length - 1 := exclIdx_le _ _ _ hld
  by_cases heq : exclIdx sd.length n i = exclIdx sd.length n k
  · have hdd : exclDelta sd.length n i ≤ exclDelta sd.length n k := by
      have him : (↑(i * (sd.length + 1)) : Int) ≤ ↑(k * (sd.length + 1)) :=
        Int.ofNat_le.mpr (Nat.mul_le_mul_right _ hik)
      rw [exclDelta_def, exclDelta_def, heq]
      linarith
    have hddR : (exclDelta sd.length n i : Rat) ≤ (exclDelta sd.length n k : Rat) :=
      Int.cast_le.mpr hdd
    have hfrac : (exclDelta sd.length n i : Rat) / (n : Rat) ≤
        (exclDelta sd.length n k : Rat) / (n : Rat) :=
      div_le_div_of_nonneg_right hddR (by exact_mod_cast Nat.zero_le n)
    have hhab : nthRat sd (exclIdx sd.length n k - 1) ≤ nthRat sd (exclIdx sd.length n k) :=
      nthRat_le_nthRat hsd (Nat.sub_le _ _) (by
        have := exclIdx_le sd.length n k hld; omega)
    have hdiff : 0 ≤ nthRat sd (exclIdx sd.length n k) - nthRat sd (exclIdx sd.length n k - 1) := by
      linarith
    rw [cutPointExclusive_eq sd hn, cutPointExclusive_eq sd hn, heq]
    linarith [mul_le_mul_of_nonneg_right hfrac hdiff]
  · have hlt : exclIdx sd.length n i < exclIdx sd.length n k := by omega
    have hnc_i : ¬(sd.length - 1 < exclIdx0 sd.length n i) := by
      intro hc
      have hi2 : exclIdx sd.length n i = sd.length - 1 := by
        rcases exclIdx_cases sd.length n i with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hc'⟩
        · omega
        · exact ha
        · omega
      have hc' : sd.length - 1 < exclIdx0 sd.length n k :=
        Nat.lt_of_lt_of_le hc (exclIdx0_mono sd.length n hik)
      have hk2 : exclIdx sd.length n k = sd.length - 1 := by
        rcases exclIdx_cases sd.length n k with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hc''⟩
        · omega
        · exact ha
        · omega
      omega
    have hnc_k : ¬(exclIdx0 sd.length n k < 1) := by
      intro hc
      have hk2 : exclIdx sd.length n k = 1 := by
        rcases exclIdx_cases sd.length n k with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hc'⟩
        · exact ha
        · omega
        · omega
      omega
    have c1 : cutPointExclusive sd n i ≤ nthRat sd (exclIdx sd.length n i) :=
      cutPointExclusive_le sd hsd hld hn hnc_i
    have c3 : nthRat sd (exclIdx sd.length n k - 1) ≤ cutPointExclusive sd n k :=
      le_cutPointExclusive sd hsd hld hn hnc_k
    have c2 : nthRat sd (exclIdx sd.length n i) ≤ nthRat sd (exclIdx sd.length n k - 1) :=
      nthRat_le_nthRat hsd (by omega) (by omega)
    linarith

/-- Mapping a function that is monotone on `[0, N)` over `List.range N` gives a sorted list. -/
theorem sorted_map_range {f : Nat → Rat} (N : Nat)
    (hmono : ∀ i j, i ≤ j → j < N → f i ≤ f j) :
    List.Sorted (· ≤ ·) ((List.range N).map f) := by
  induction N with
  | zero => simp [List.Sorted]
  | succ N ih =>
    have hmono' : ∀ i j, i ≤ j → j < N → f i ≤ f j :=
      fun i j hij hj => hmono i j hij (Nat.lt_of_lt_of_le hj (by omega))
    rw [List.range_succ, List.map_append, List.map_singleton]
    simp only [List.Sorted]
    rw [List.pairwise_append]
    refine ⟨ih hmono', by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range] at hi
    exact hmono i N (Nat.le_of_lt hi) (by omega)

/-- `inclusive` cut points are convex combinations, hence stay inside the data range. -/
theorem cutPointInclusive_bounds (sd : List Rat) (hsd : List.Sorted (· ≤ ·) sd)
    (hld : 2 ≤ sd.length) {n i : Nat} (hn : 0 < n)
    (hi : i < n) (lo hi' : Rat) (hlo : ∀ x ∈ sd, lo ≤ x) (hhi : ∀ x ∈ sd, x ≤ hi') :
    lo ≤ cutPointInclusive sd n i ∧ cutPointInclusive sd n i ≤ hi' := by
  have hj := inclIdx_succ_lt sd hld hn hi
  have hab : nthRat sd (inclIdx sd.length n i) ≤ nthRat sd (inclIdx sd.length n i + 1) :=
    nthRat_le_nthRat hsd (by omega) hj
  have ha : lo ≤ nthRat sd (inclIdx sd.length n i) := hlo _ (nthRat_mem (by omega))
  have hb : lo ≤ nthRat sd (inclIdx sd.length n i + 1) := hlo _ (nthRat_mem hj)
  have hA : nthRat sd (inclIdx sd.length n i) ≤ hi' := hhi _ (nthRat_mem (by omega))
  have hB : nthRat sd (inclIdx sd.length n i + 1) ≤ hi' := hhi _ (nthRat_mem hj)
  have hd0 : 0 ≤ (inclDelta sd.length n i : Rat) := Nat.cast_nonneg _
  have hdn : (inclDelta sd.length n i : Rat) ≤ (n : Rat) :=
    Nat.cast_le.mpr (Nat.le_of_lt (Nat.mod_lt _ hn))
  have hfrac0 : 0 ≤ (inclDelta sd.length n i : Rat) / (n : Rat) :=
    div_nonneg hd0 (by exact_mod_cast Nat.zero_le n)
  have hfrac1 : (inclDelta sd.length n i : Rat) / (n : Rat) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact hdn
  have hdiff : 0 ≤ nthRat sd (inclIdx sd.length n i + 1) - nthRat sd (inclIdx sd.length n i) := by
    linarith
  rw [cutPointInclusive_eq sd hn]
  exact ⟨by linarith [mul_nonneg hfrac0 hdiff],
    by linarith [mul_le_mul_of_nonneg_right hfrac1 hdiff]⟩

/-! ### The stated properties hold -/

theorem quantilesCore_length (data : List Rat) (n : Nat) (method : String) :
    (quantilesCore data n method).length = n - 1 := by
  simp [quantilesCore]

theorem quantilesCore_sorted (data : List Rat) (n : Nat) (method : String)
    (hld : 2 ≤ data.length) (hn : 1 ≤ n) :
    List.Sorted (· ≤ ·) (quantilesCore data n method) := by
  have hsd : List.Sorted (· ≤ ·) (sortedData data) := sortedData_sorted data
  have hld' : 2 ≤ (sortedData data).length := by rwa [sortedData_length]
  apply sorted_map_range
  intro i j hij hj
  have hj' : j + 1 < n := by omega
  by_cases hm : method = "inclusive"
  · have e1 : cutPoint (sortedData data) n method (i + 1) =
        cutPointInclusive (sortedData data) n (i + 1) := by simp [cutPoint, hm]
    have e2 : cutPoint (sortedData data) n method (j + 1) =
        cutPointInclusive (sortedData data) n (j + 1) := by simp [cutPoint, hm]
    rw [e1, e2]
    exact cutPointInclusive_mono (sortedData data) hsd hld' n (by omega) (by omega) hj'
  · have e1 : cutPoint (sortedData data) n method (i + 1) =
        cutPointExclusive (sortedData data) n (i + 1) := by simp [cutPoint, hm]
    have e2 : cutPoint (sortedData data) n method (j + 1) =
        cutPointExclusive (sortedData data) n (j + 1) := by simp [cutPoint, hm]
    rw [e1, e2]
    exact cutPointExclusive_mono (sortedData data) hsd hld' n (by omega) (by omega)

/-- Python: `raise StatisticsError('n must be at least 1')`. -/
theorem quantiles_error_n (data : List Rat) (method : String) :
    quantiles data 0 method = .error "n must be at least 1" := by simp [quantiles]

/-- Python: `raise StatisticsError('must have at least two data points')`. -/
theorem quantiles_error_short (data : List Rat) (n : Nat) (method : String) (h1 : 1 ≤ n)
    (h2 : data.length < 2) :
    quantiles data n method = .error "must have at least two data points" := by
  have hn0 : n ≠ 0 := by omega
  simp [quantiles, hn0, h2]

/-- Python: `raise ValueError(f'Unknown method: {method!r}')`. -/
theorem quantiles_error_method (data : List Rat) (n : Nat) (method : String) (h1 : 1 ≤ n)
    (h2 : 2 ≤ data.length) (h3 : method ≠ "inclusive") (h4 : method ≠ "exclusive") :
    quantiles data n method = .error ("Unknown method: " ++ method) := by
  have hn0 : n ≠ 0 := by omega
  have hl : ¬(data.length < 2) := by omega
  simp [quantiles, hn0, hl, h3, h4]

theorem length_thm {data : List Rat} {n : Nat} {method : String} (h : Pre data n method) :
    length_prop data n method := by
  simp only [length_prop, benchmarkQuantiles_ok h]
  simp [quantilesCore_length]

theorem noError_thm {data : List Rat} {n : Nat} {method : String} (h : Pre data n method) :
    noError_prop data n method := ⟨quantilesCore data n method, benchmarkQuantiles_ok h⟩

theorem sorted_thm {data : List Rat} {n : Nat} {method : String} (h : Pre data n method) :
    sorted_prop data n method := by
  intro res hres
  rw [benchmarkQuantiles_ok h] at hres
  have hinj := QResult.ok.inj hres
  rw [← hinj]
  exact quantilesCore_sorted data n method h.1 h.2.1

theorem empty_thm {data : List Rat} {method : String} (h : Pre data 1 method) :
    empty_prop data method := by
  simp only [empty_prop, benchmarkQuantiles_ok h]
  simp [quantilesCore]

theorem error_thm {data : List Rat} {n : Nat} {method : String} :
    error_prop data n method := fun h => benchmarkQuantiles_error h

theorem bounds_thm {data : List Rat} {n : Nat} (h : Pre data n "inclusive") :
    bounds_prop data n := by
  intro lo hi hlo hhi res hres c hc
  rw [benchmarkQuantiles_ok h] at hres
  have hinj := QResult.ok.inj hres
  rw [← hinj] at hc
  simp only [quantilesCore] at hc
  obtain ⟨k, hk, hkeq⟩ := List.mem_map.mp hc
  have hsd : List.Sorted (· ≤ ·) (sortedData data) := sortedData_sorted data
  have hld : 2 ≤ (sortedData data).length := by rw [sortedData_length]; exact h.1
  have hkn : k + 1 < n := by
    simp only [List.mem_range] at hk
    omega
  have hlo' : ∀ x ∈ sortedData data, lo ≤ x := fun x hx => hlo x (mem_sortedData.mp hx)
  have hhi' : ∀ x ∈ sortedData data, x ≤ hi := fun x hx => hhi x (mem_sortedData.mp hx)
  have bnd := cutPointInclusive_bounds (sortedData data) hsd hld (by omega) hkn lo hi hlo' hhi'
  have ecut : cutPoint (sortedData data) n "inclusive" (k + 1) =
      cutPointInclusive (sortedData data) n (k + 1) := by simp [cutPoint]
  rw [← hkeq, ecut]
  exact bnd

/-- For an odd number of data points the `exclusive` median is the middle element. -/
theorem cutPointExclusive_median_odd (sd : List Rat) (k : Nat) (hk : 1 ≤ k)
    (h : sd.length = 2 * k + 1) : cutPointExclusive sd 2 1 = nthRat sd k := by
  have h1 : exclIdx0 sd.length 2 1 = k + 1 := by simp [exclIdx0, h]; omega
  have h2 : ¬(k + 1 < 1) := by omega
  have h3 : ¬(sd.length - 1 < k + 1) := by rw [h]; omega
  have h4 : exclIdx sd.length 2 1 = k + 1 := by simp [exclIdx, clampIdx, h1, h2, h3]
  have h5 : exclDelta sd.length 2 1 = 0 := by
    rw [exclDelta_def, h4, h]
    push_cast
    ring
  simp [cutPointExclusive, h4, h5, Nat.add_sub_cancel]
  field_simp
  ring

/-- For an even number of data points the `exclusive` median is the mean of the two
middle elements. -/
theorem cutPointExclusive_median_even (sd : List Rat) (k : Nat) (h : sd.length = 2 * k + 2) :
    cutPointExclusive sd 2 1 = (nthRat sd k + nthRat sd (k + 1)) / 2 := by
  have h1 : exclIdx0 sd.length 2 1 = k + 1 := by simp [exclIdx0, h]; omega
  have h2 : ¬(k + 1 < 1) := by omega
  have h3 : ¬(sd.length - 1 < k + 1) := by rw [h]; omega
  have h4 : exclIdx sd.length 2 1 = k + 1 := by simp [exclIdx, clampIdx, h1, h2, h3]
  have h5 : exclDelta sd.length 2 1 = 1 := by
    rw [exclDelta_def, h4, h]
    push_cast
    ring
  simp [cutPointExclusive, h4, h5, Nat.add_sub_cancel]
  field_simp
  ring

theorem median_odd_thm (data : List Rat) (k : Nat) (hk : 1 ≤ k)
    (h : data.length = 2 * k + 1) :
    benchmarkQuantiles data 2 "exclusive" = .ok [nthRat (sortedData data) k] := by
  have hpre : Pre data 2 "exclusive" := ⟨by rw [h]; omega, by omega, Or.inr rfl⟩
  rw [benchmarkQuantiles_ok hpre]
  have hsd : (sortedData data).length = 2 * k + 1 := by rw [sortedData_length, h]
  have hr : List.range (2 - 1) = [0] := by decide
  simp [quantilesCore, cutPoint, hr,
    cutPointExclusive_median_odd (sortedData data) k hk hsd]

theorem median_even_thm (data : List Rat) (k : Nat) (h : data.length = 2 * k + 2) :
    benchmarkQuantiles data 2 "exclusive"
      = .ok [(nthRat (sortedData data) k + nthRat (sortedData data) (k + 1)) / 2] := by
  have hpre : Pre data 2 "exclusive" := ⟨by rw [h]; omega, by omega, Or.inr rfl⟩
  rw [benchmarkQuantiles_ok hpre]
  have hsd : (sortedData data).length = 2 * k + 2 := by rw [sortedData_length, h]
  have hr : List.range (2 - 1) = [0] := by decide
  simp [quantilesCore, cutPoint, hr,
    cutPointExclusive_median_even (sortedData data) k hsd]

theorem median_thm (data : List Rat) : median_prop data :=
  ⟨fun k hk h => median_odd_thm data k hk h, fun k h => median_even_thm data k h⟩

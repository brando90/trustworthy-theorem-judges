import Mathlib

/-!
# `statistics.quantiles` — divide data into `n` continuous intervals with equal probability

A Lean 4 formalization of the Python function `benchmark_quantiles`, which is a
re-implementation of `statistics.quantiles` from Python's standard library.

The function divides sorted `data` into `n` continuous intervals with equal
probability and returns the list of `n - 1` cut points separating those
intervals.  Cut points are linearly interpolated between data points using
*exact* integer arithmetic for the interpolation weights.

* `method = "inclusive"`: the data is treated as population data, the minimum is
  the 0th percentile and the maximum the 100th percentile.
* `method = "exclusive"` (the default): the data is treated as a sample; the
  rescaled index is clamped to `1 .. ld - 1`, so the interpolation weight
  `delta` may become negative (linear extrapolation beyond the observed range).

Numbers are modelled by `ℚ` (Python's `Fraction`), so that all the arithmetic is
exact and every stated property is decidable on concrete inputs.  Python
exceptions are modelled by the `Except String` error monad: `StatisticsError` /
`ValueError` become `Except.error`.

The file contains a purely functional implementation, an imperative
implementation written with `Id.run do` and mutable state, unit tests for both,
the pre/post-conditions, the correctness theorem and the equivalence theorem.
-/

namespace StatisticsQuantiles

/-- Decidable equality on the result type, so that the unit tests below can be
discharged by `native_decide`. -/
instance instDecEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by simp)
  | .error _, .ok _ => isFalse (by simp)

/-! ## Functional implementation -/

/-- `sorted(data)`: sort the data in non-decreasing order. -/
def sortData (data : List ℚ) : List ℚ := data.mergeSort (fun a b => decide (a ≤ b))

/-- One cut point of the `inclusive` method:
`j, delta = divmod(i * m, n)` with `m = ld - 1`, then
`(data[j] * (n - delta) + data[j+1] * delta) / n`. -/
def cutInclusive (s : List ℚ) (n i : ℕ) : ℚ :=
  let m := s.length - 1
  let j := i * m / n
  let delta := i * m % n
  (s.getD j 0 * ((n : ℚ) - (delta : ℚ)) + s.getD (j + 1) 0 * (delta : ℚ)) / (n : ℚ)

/-- The clamped rescaled index `j` of the `exclusive` method:
`j = i * m // n`, clamped to `1 .. ld - 1` (where `m = ld + 1`). -/
def exclusiveIndex (ld n i : ℕ) : ℕ :=
  let j := i * (ld + 1) / n
  if j < 1 then 1 else if j > ld - 1 then ld - 1 else j

/-- One cut point of the `exclusive` method.  Note that
`delta = i * m - j * n` is computed in `ℤ` because clamping `j` can make it
negative (the Python code relies on exact integer math here). -/
def cutExclusive (s : List ℚ) (n i : ℕ) : ℚ :=
  let ld := s.length
  let j := exclusiveIndex ld n i
  let delta : ℤ := (i * (ld + 1) : ℤ) - (j : ℤ) * (n : ℤ)
  (s.getD (j - 1) 0 * ((n : ℚ) - (delta : ℚ)) + s.getD j 0 * (delta : ℚ)) / (n : ℚ)

/-- `quantiles(data, n, method)`.  `n < 1` and `len(data) < 2` raise a
`StatisticsError`, an unknown method raises a `ValueError`. -/
def quantiles (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    Except String (List ℚ) :=
  if n < 1 then
    .error "n must be at least 1"
  else if (sortData data).length < 2 then
    .error "must have at least two data points"
  else if method = "inclusive" then
    .ok ((List.range' 1 (n - 1)).map (cutInclusive (sortData data) n))
  else if method = "exclusive" then
    .ok ((List.range' 1 (n - 1)).map (cutExclusive (sortData data) n))
  else
    .error ("Unknown method: " ++ method)

/-- Boolean version of the Python pre-condition `pre`. -/
def preB (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  2 ≤ data.length && 1 ≤ n && (method = "inclusive" || method = "exclusive")

/-- `benchmark_quantiles`: check the pre-condition first, then run `quantiles`. -/
def benchmarkQuantiles (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    Except String (List ℚ) :=
  if preB data n method then
    quantiles data n method
  else
    .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1. Basic quartiles (default arguments)
example : benchmarkQuantiles [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide

-- 2. Deciles: 9 cut points
example : (benchmarkQuantiles [0,1,2,3,4,5,6,7,8,9,10] 10).map List.length = .ok 9 := by
  native_decide

-- 3. Median (n = 2)
example : benchmarkQuantiles [1, 2, 3, 4, 5] 2 = .ok [3] := by native_decide

-- 4. Inclusive method
example : benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by
  native_decide

-- 5. Exclusive method (explicit default)
example : benchmarkQuantiles [1, 2, 3, 4] 4 "exclusive" = .ok [5/4, 5/2, 15/4] := by
  native_decide

-- 6. Larger dataset
example : (benchmarkQuantiles [1,2,3,4,5,6,7,8,9,10] 4).map List.length = .ok 3 := by
  native_decide

-- 7. Unsorted input is sorted internally
example : benchmarkQuantiles [4, 1, 3, 2] 4 = benchmarkQuantiles [1, 2, 3, 4] 4 := by
  native_decide

-- 8. Non-integral data
example : benchmarkQuantiles [3/2, 5/2, 7/2, 9/2] 2 = .ok [3] := by native_decide

-- 9. Error cases
example : benchmarkQuantiles [1] 4 = .error
    "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  native_decide

example : benchmarkQuantiles [1, 2] 0 = .error
    "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  native_decide

example : benchmarkQuantiles [1, 2, 3] 4 "invalid" = .error
    "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  native_decide

#eval benchmarkQuantiles [1, 2, 3, 4]
#eval benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive"
#eval benchmarkQuantiles [0,1,2,3,4,5,6,7,8,9,10] 10

/-! ## Pre-condition -/

/-- The Python pre-condition `pre(data, n, method)`: the data has at least two
elements, `n ≥ 1` and the method is one of the two supported ones. -/
def Pre (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

theorem preB_iff (data : List ℚ) (n : ℕ) (method : String) :
    preB data n method = true ↔ Pre data n method := by
  simp [preB, Pre, and_assoc]

/-! ## Properties -/

/-- Sorting does not change the length of the data. -/
theorem length_sortData (data : List ℚ) : (sortData data).length = data.length :=
  (List.mergeSort_perm data _).length_eq

theorem sorted_sortData (data : List ℚ) :
    (sortData data).Sorted (· ≤ ·) := by
  have := List.sorted_mergeSort (le := fun a b => decide ((a : ℚ) ≤ b))
    (by intro a b c hab hbc; simp_all; exact le_trans hab hbc)
    (by intro a b; simp; exact le_total a b) data
  simpa [sortData, List.Sorted] using this

/-- **Property 1 (length).**  Under the pre-condition the call succeeds and
returns exactly `n - 1` cut points. -/
def length_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∃ r, benchmarkQuantiles data n method = .ok r ∧ r.length = n - 1

/-- **Property 2 (errors).**  If the pre-condition fails the call raises an
error (`StatisticsError` in Python). -/
def error_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ¬ Pre data n method → ∃ e, benchmarkQuantiles data n method = .error e

/-- **Property 3 (specification of the cut points).**  Every returned cut point
is the value produced by the exact-integer interpolation formula of the Python
source, evaluated on the *sorted* data. -/
def spec_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∀ r, benchmarkQuantiles data n method = .ok r →
    ∀ k (hk : k < r.length),
      r[k] = if method = "inclusive" then cutInclusive (sortData data) n (k + 1)
             else cutExclusive (sortData data) n (k + 1)

/-- **Property 4 (order invariance).**  The result only depends on the
multiset of data values: the implementation sorts its input. -/
def perm_prop (data data' : List ℚ) (n : ℕ) (method : String) : Prop :=
  data.Perm data' → benchmarkQuantiles data n method = benchmarkQuantiles data' n method

/-- **Property 5 (interpolation).**  For the `inclusive` method every cut point
lies between two actual data points, i.e. inside the range of the data. -/
def inclusive_range_prop (data : List ℚ) (n : ℕ) : Prop :=
  ∀ r, benchmarkQuantiles data n "inclusive" = .ok r →
    ∀ v ∈ r, ∃ a ∈ data, ∃ b ∈ data, a ≤ v ∧ v ≤ b

/-! ### Proofs of the properties -/

/-- The normal form of a successful call: under the pre-condition the result is
the list of the `n - 1` interpolated cut points of the sorted data. -/
theorem benchmarkQuantiles_eq (data : List ℚ) (n : ℕ) (method : String)
    (h : Pre data n method) :
    benchmarkQuantiles data n method =
      .ok ((List.range' 1 (n - 1)).map
        (fun i => if method = "inclusive" then cutInclusive (sortData data) n i
                  else cutExclusive (sortData data) n i)) := by
  obtain ⟨hlen, hn, hm⟩ := h
  have hpre : preB data n method = true := (preB_iff data n method).2 ⟨hlen, hn, hm⟩
  have hs : ¬ (sortData data).length < 2 := by rw [length_sortData]; omega
  rcases hm with rfl | rfl <;>
    simp [benchmarkQuantiles, hpre, quantiles, hs, Nat.not_lt.2 hn]

theorem length_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    length_prop data n method :=
  ⟨_, benchmarkQuantiles_eq data n method h, by simp⟩

theorem error_thm (data : List ℚ) (n : ℕ) (method : String) :
    error_prop data n method := by
  intro h
  have hf : preB data n method = false := by
    by_contra hc
    exact h ((preB_iff data n method).1 (by simpa using hc))
  exact ⟨"benchmark_quantiles requires at least 2 data points, n >= 1, and valid method",
    by simp [benchmarkQuantiles, hf]⟩

/-- A successful call implies the pre-condition. -/
theorem pre_of_ok (data : List ℚ) (n : ℕ) (method : String) (r : List ℚ)
    (h : benchmarkQuantiles data n method = .ok r) : Pre data n method := by
  by_contra hc
  obtain ⟨e, he⟩ := error_thm data n method hc
  rw [he] at h
  exact absurd h (by simp)

theorem spec_thm (data : List ℚ) (n : ℕ) (method : String) :
    spec_prop data n method := by
  intro r hr k hk
  have hpre := pre_of_ok data n method r hr
  rw [benchmarkQuantiles_eq data n method hpre] at hr
  have hr' : r = (List.range' 1 (n - 1)).map
      (fun i => if method = "inclusive" then cutInclusive (sortData data) n i
                else cutExclusive (sortData data) n i) := by
    simpa using hr.symm
  subst hr'
  simp [List.getElem_map, List.getElem_range', Nat.add_comm]

theorem perm_thm (data data' : List ℚ) (n : ℕ) (method : String) :
    perm_prop data data' n method := by
  intro hp
  have hsort : sortData data = sortData data' := by
    refine List.eq_of_perm_of_sorted (r := (· ≤ ·)) ?_ (sorted_sortData data) (sorted_sortData data')
    exact ((List.mergeSort_perm data _).trans hp).trans (List.mergeSort_perm data' _).symm
  have hlen : data.length = data'.length := hp.length_eq
  simp only [benchmarkQuantiles, quantiles, preB, hsort, hlen]

/-- Elements of a sorted list are monotone in their index. -/
theorem sorted_getD_le (s : List ℚ) (hs : s.Sorted (· ≤ ·)) {i j : ℕ}
    (hij : i ≤ j) (hj : j < s.length) : s.getD i 0 ≤ s.getD j 0 := by
  have hi : i < s.length := lt_of_le_of_lt hij hj
  rw [List.getD_eq_getElem s 0 hi, List.getD_eq_getElem s 0 hj]
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.1 hs) i j hi hj hlt

theorem inclusive_range_thm (data : List ℚ) (n : ℕ) : inclusive_range_prop data n := by
  intro r hr v hv
  obtain ⟨hlen, hn, -⟩ := pre_of_ok data n "inclusive" r hr
  rw [benchmarkQuantiles_eq data n "inclusive" ⟨hlen, hn, Or.inl rfl⟩] at hr
  have hr' : r = (List.range' 1 (n - 1)).map (cutInclusive (sortData data) n) := by
    simpa using hr.symm
  subst hr'
  simp only [List.mem_map] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have hi' : 1 ≤ i ∧ i < n := by
    have := List.mem_range'_1.1 (by simpa using hi)
    omega
  obtain ⟨hi1, hin⟩ := hi'
  have hld2 : 2 ≤ (sortData data).length := by rw [length_sortData]; exact hlen
  set s := sortData data with hsdef
  set ld := s.length with hld
  set m := ld - 1 with hmdef
  set j := i * m / n with hjdef
  set delta := i * m % n with hdelta
  have hnpos : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hjm : j < m := Nat.div_lt_of_lt_mul ((Nat.mul_lt_mul_right hm0).mpr hin)
  have hj1 : j + 1 < ld := by omega
  have hjlt : j < ld := by omega
  -- the two neighbouring data points
  have hmem : ∀ k, k < ld → s.getD k 0 ∈ data := by
    intro k hk
    have : s.getD k 0 ∈ s := by
      rw [List.getD_eq_getElem s 0 hk]; exact List.getElem_mem hk
    exact (List.mergeSort_perm data _).mem_iff.1 this
  refine ⟨s.getD j 0, hmem j hjlt, s.getD (j + 1) 0, hmem (j + 1) hj1, ?_, ?_⟩
  · -- s[j] ≤ cut
    have hab : s.getD j 0 ≤ s.getD (j + 1) 0 := sorted_getD_le s (sorted_sortData data) (by omega) hj1
    have hd : (delta : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast le_of_lt (Nat.mod_lt _ hnpos)
    have hd0 : (0 : ℚ) ≤ (delta : ℚ) := by positivity
    have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    rw [cutInclusive, le_div_iff₀ hnq]
    nlinarith [hab, hd, hd0]
  · have hab : s.getD j 0 ≤ s.getD (j + 1) 0 := sorted_getD_le s (sorted_sortData data) (by omega) hj1
    have hd : (delta : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast le_of_lt (Nat.mod_lt _ hnpos)
    have hd0 : (0 : ℚ) ≤ (delta : ℚ) := by positivity
    have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    rw [cutInclusive, div_le_iff₀ hnq]
    nlinarith [hab, hd, hd0]

/-- **Property 6 (median).**  With `n = 2` and the `inclusive` method on an odd
number of data points, the single cut point is the middle order statistic, i.e.
the median of the data. -/
def median_prop (data : List ℚ) (k : ℕ) : Prop :=
  data.length = 2 * k + 1 → 1 ≤ k →
    benchmarkQuantiles data 2 "inclusive" = .ok [(sortData data).getD k 0]

theorem median_thm (data : List ℚ) (k : ℕ) : median_prop data k := by
  intro hlen hk
  have hpre : Pre data 2 "inclusive" := ⟨by omega, by omega, Or.inl rfl⟩
  rw [benchmarkQuantiles_eq data 2 "inclusive" hpre]
  have hslen : (sortData data).length = 2 * k + 1 := by rw [length_sortData, hlen]
  have hj : ((sortData data).length - 1) / 2 = k := by rw [hslen]; omega
  have hd : ((sortData data).length - 1) % 2 = 0 := by rw [hslen]; omega
  simp [cutInclusive, hj, hd]

/-! ## Post-condition and correctness -/

/-- The post-condition: the conjunction of all the properties above. -/
def Post_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  length_prop data n method ∧
  error_prop data n method ∧
  spec_prop data n method ∧
  (∀ data', perm_prop data data' n method) ∧
  (method = "inclusive" → inclusive_range_prop data n) ∧
  (∀ k, median_prop data k)

/-- **Correctness**: the pre-condition implies the post-condition. -/
theorem correctness (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    Post_prop data n method :=
  ⟨length_thm data n method h, error_thm data n method, spec_thm data n method,
    fun data' => perm_thm data data' n method, fun _ => inclusive_range_thm data n,
    fun k => median_thm data k⟩

/-! ## Imperative implementation -/

/-- The imperative version of `benchmark_quantiles`: it mirrors the Python code
line by line, using `Id.run do` with a mutable `result` accumulator. -/
def benchmarkQuantilesImp (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    Except String (List ℚ) := Id.run do
  if !(preB data n method) then
    return .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"
  if n < 1 then
    return .error "n must be at least 1"
  let s := sortData data
  let ld := s.length
  if ld < 2 then
    return .error "must have at least two data points"
  if method = "inclusive" then
    let m := ld - 1
    let mut result : Array ℚ := #[]
    for i in List.range' 1 (n - 1) do
      let j := i * m / n
      let delta := i * m % n
      result := result.push
        ((s.getD j 0 * ((n : ℚ) - (delta : ℚ)) + s.getD (j + 1) 0 * (delta : ℚ)) / (n : ℚ))
    return .ok result.toList
  if method = "exclusive" then
    let m := ld + 1
    let mut result : Array ℚ := #[]
    for i in List.range' 1 (n - 1) do
      let j0 := i * m / n
      let j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
      let delta : ℤ := (i * m : ℤ) - (j : ℤ) * (n : ℤ)
      result := result.push
        ((s.getD (j - 1) 0 * ((n : ℚ) - (delta : ℚ)) + s.getD j 0 * (delta : ℚ)) / (n : ℚ))
    return .ok result.toList
  return .error ("Unknown method: " ++ method)

/-! ## Imperative unit tests -/

example : benchmarkQuantilesImp [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantilesImp [1, 2, 3, 4] 4 "inclusive" = .ok [7/4, 5/2, 13/4] := by
  native_decide
example : benchmarkQuantilesImp [1, 2, 3, 4, 5] 2 = .ok [3] := by native_decide
example : benchmarkQuantilesImp [4, 1, 3, 2] 4 = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantilesImp [1] 4 = .error
    "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method" := by
  native_decide

#eval benchmarkQuantilesImp [1, 2, 3, 4]
#eval benchmarkQuantilesImp [0,1,2,3,4,5,6,7,8,9,10] 10

/-! ## Equivalence of the functional and the imperative implementation -/

/-- The `push`-loop over a list computes exactly the `map` of the loop body. -/
theorem push_loop (f : ℕ → ℚ) (l : List ℕ) :
    (Id.run (do
      let mut result : Array ℚ := #[]
      for i in l do
        result := result.push (f i)
      return result)).toList = l.map f := by
  simp

theorem equivalence (data : List ℚ) (n : ℕ) (method : String) :
    benchmarkQuantiles data n method = benchmarkQuantilesImp data n method := by
  by_cases hpre : preB data n method = true
  · obtain ⟨hlen, hn, hm⟩ := (preB_iff ..).1 hpre
    have hs2 : ¬ ((sortData data).length < 2) := by rw [length_sortData]; omega
    rw [benchmarkQuantiles_eq data n method ⟨hlen, hn, hm⟩]
    rcases hm with rfl | rfl
    · simp [benchmarkQuantilesImp, hpre, Nat.not_lt.2 hn, hs2, Id.run, cutInclusive]
      rfl
    · simp [benchmarkQuantilesImp, hpre, Nat.not_lt.2 hn, hs2, Id.run, cutExclusive,
        exclusiveIndex]
      rfl
  · have hf : preB data n method = false := by simpa using hpre
    simp only [benchmarkQuantiles, benchmarkQuantilesImp, hf, Bool.false_eq_true, if_false,
      Bool.not_false, if_true, Id.run]
    rfl

end StatisticsQuantiles

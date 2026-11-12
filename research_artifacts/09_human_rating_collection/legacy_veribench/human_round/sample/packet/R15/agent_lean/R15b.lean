import Mathlib

/-!
# Exact quantiles

This file formalizes the inclusive and exclusive interpolation algorithms used by
Python's `statistics.quantiles`.  Python accepts several numeric classes; the Lean
model uses `ℚ`, which represents all integer and fractional test inputs exactly.
Errors are represented with `Except String`.
-/

namespace StatisticsQuantiles

private def inclusiveCut (sorted : List ℚ) (n i : ℕ) : ℚ :=
  let m := sorted.length - 1
  let j := i * m / n
  let delta := i * m % n
  (sorted.getD j 0 * (n - delta) + sorted.getD (j + 1) 0 * delta) / n

private def exclusiveCut (sorted : List ℚ) (n i : ℕ) : ℚ :=
  let m := sorted.length + 1
  let raw := i * m / n
  let j := max 1 (min raw (sorted.length - 1))
  let delta : ℤ := Int.ofNat (i * m) - Int.ofNat (j * n)
  let n' : ℚ := n
  let delta' : ℚ := delta
  (sorted.getD (j - 1) 0 * (n' - delta') + sorted.getD j 0 * delta') / n'

private def expectedCuts (data : List ℚ) (n : ℕ) (method : String) : List ℚ :=
  let sorted := data.mergeSort
  let indices := (List.range (n - 1)).map (· + 1)
  if method = "inclusive" then
    indices.map (inclusiveCut sorted n)
  else
    indices.map (exclusiveCut sorted n)

/-- Functional translation of `statistics.quantiles`. -/
def quantiles (data : List ℚ) (n : ℕ := 4)
    (method : String := "exclusive") : Except String (List ℚ) :=
  if n < 1 then
    .error "n must be at least 1"
  else if data.length < 2 then
    .error "must have at least two data points"
  else
    let sorted := data.mergeSort
    let indices := (List.range (n - 1)).map (· + 1)
    if method = "inclusive" then
      .ok (indices.map (inclusiveCut sorted n))
    else if method = "exclusive" then
      .ok (indices.map (exclusiveCut sorted n))
    else
      .error s!"Unknown method: {method}"

/-- The checked entry point corresponding to Python's `benchmark_quantiles`. -/
def benchmarkQuantiles (data : List ℚ) (n : ℕ := 4)
    (method : String := "exclusive") : Except String (List ℚ) :=
  if data.length < 2 then
    .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"
  else if n < 1 then
    .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"
  else if method ≠ "inclusive" ∧ method ≠ "exclusive" then
    .error "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"
  else
    quantiles data n method

example : (benchmarkQuantiles [1, 2, 3, 4]).toOption = some [5 / 4, 5 / 2, 15 / 4] := by
  native_decide

example : (benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive").toOption =
    some [7 / 4, 5 / 2, 13 / 4] := by
  native_decide

example : (benchmarkQuantiles [1, 2, 3, 4, 5] 2).toOption = some [3] := by
  native_decide

example : (benchmarkQuantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10).toOption.map List.length =
    some 9 := by
  native_decide

example : (benchmarkQuantiles [1] 4).toOption = none := by
  native_decide

#eval benchmarkQuantiles [4, 1, 3, 2]
#eval benchmarkQuantiles [1, 2, 3, 4] 4 "inclusive"
#eval benchmarkQuantiles [1, 2] 0

/-- The dynamically checked Python precondition, specialized to rational lists. -/
def Pre (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

/-- Valid inputs produce a successful result. -/
def validResult_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∃ cuts, benchmarkQuantiles data n method = .ok cuts

/-- Every successful result has exactly `n - 1` cut points. -/
def cutCount_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∀ cuts, benchmarkQuantiles data n method = .ok cuts → cuts.length = n - 1

/-- The result is precisely the appropriate interpolation formula on sorted data. -/
def interpolation_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  benchmarkQuantiles data n method = .ok (expectedCuts data n method)

private theorem expectedCuts_length (data : List ℚ) (n : ℕ) (method : String) :
    (expectedCuts data n method).length = n - 1 := by
  unfold expectedCuts
  split <;> simp

theorem interpolation_thm (data : List ℚ) (n : ℕ) (method : String)
    (h : Pre data n method) : interpolation_prop data n method := by
  rcases h with ⟨hdata, hn, hmethod⟩
  have hdata' : ¬data.length < 2 := Nat.not_lt.mpr hdata
  have hn' : ¬n < 1 := Nat.not_lt.mpr hn
  rcases hmethod with rfl | rfl <;>
    simp [interpolation_prop, benchmarkQuantiles, quantiles, expectedCuts, hdata', hn']

theorem validResult_thm (data : List ℚ) (n : ℕ) (method : String)
    (h : Pre data n method) : validResult_prop data n method := by
  refine ⟨expectedCuts data n method, ?_⟩
  exact interpolation_thm data n method h

theorem cutCount_thm (data : List ℚ) (n : ℕ) (method : String)
    (h : Pre data n method) : cutCount_prop data n method := by
  intro cuts hcuts
  have hinterp := interpolation_thm data n method h
  rw [interpolation_prop, hcuts] at hinterp
  cases hinterp
  exact expectedCuts_length data n method

/-- The complete postcondition records success, output size, and exact interpolation. -/
def Post_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  validResult_prop data n method ∧
    cutCount_prop data n method ∧ interpolation_prop data n method

theorem benchmarkQuantiles_correct (data : List ℚ) (n : ℕ) (method : String) :
    Pre data n method → Post_prop data n method := by
  intro h
  exact ⟨validResult_thm data n method h, cutCount_thm data n method h,
    interpolation_thm data n method h⟩

private def reverseMapImperative (f : α → β) (xs : List α) : List β := Id.run do
  let mut result : List β := []
  for x in xs do
    result := f x :: result
  return result.reverse

private theorem reverseMapImperative_eq (f : α → β) (xs : List α) :
    reverseMapImperative f xs = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reverseMapImperative]

private def cutsImperative (data : List ℚ) (n : ℕ) (method : String) : List ℚ :=
  let sorted := data.mergeSort
  let indices := (List.range (n - 1)).map (· + 1)
  let cut := if method = "inclusive" then inclusiveCut sorted n
    else exclusiveCut sorted n
  reverseMapImperative cut indices

/-- Imperative checked entry point, with a mutable accumulator for the cuts. -/
def benchmarkQuantilesImperative (data : List ℚ) (n : ℕ := 4)
    (method : String := "exclusive") : Except String (List ℚ) := Id.run do
  let message :=
    "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"
  let mut result : Except String (List ℚ) := .error message
  if data.length < 2 then
    result := .error message
  else if n < 1 then
    result := .error message
  else if method ≠ "inclusive" ∧ method ≠ "exclusive" then
    result := .error message
  else
    result := .ok (cutsImperative data n method)
  return result

example : (benchmarkQuantilesImperative [1, 2, 3, 4]).toOption =
    some [5 / 4, 5 / 2, 15 / 4] := by
  native_decide

example : (benchmarkQuantilesImperative [1, 2, 3, 4] 4 "inclusive").toOption =
    some [7 / 4, 5 / 2, 13 / 4] := by
  native_decide

#eval benchmarkQuantilesImperative [1, 2, 3, 4, 5] 2
#eval benchmarkQuantilesImperative [1, 2, 3] 4 "invalid"

private theorem cutsImperative_eq (data : List ℚ) (n : ℕ) (method : String) :
    cutsImperative data n method = expectedCuts data n method := by
  unfold cutsImperative expectedCuts
  rw [reverseMapImperative_eq]
  split <;> rfl

theorem functional_imperative_equiv (data : List ℚ) (n : ℕ) (method : String) :
    benchmarkQuantiles data n method = benchmarkQuantilesImperative data n method := by
  simp only [benchmarkQuantiles, benchmarkQuantilesImperative, Id.run]
  split <;> rename_i hdata
  · rfl
  split <;> rename_i hn
  · rfl
  split <;> rename_i hmethod
  · rfl
  · change quantiles data n method = .ok (cutsImperative data n method)
    rcases not_and_or.mp hmethod with hinc | hexc
    · have hinc' : method = "inclusive" := Classical.not_not.mp hinc
      subst method
      simp [quantiles, expectedCuts, cutsImperative_eq, hdata, hn]
    · have hexc' : method = "exclusive" := Classical.not_not.mp hexc
      subst method
      simp [quantiles, expectedCuts, cutsImperative_eq, hdata, hn]

end StatisticsQuantiles

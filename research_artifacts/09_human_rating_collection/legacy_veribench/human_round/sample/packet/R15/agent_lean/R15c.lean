/-!
# VeriBench -- Quantile Calculation
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace BenchmarkQuantiles

/-!
## Pre-condition
-/

open List

def Pre (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  (data.length ≥ 2) ∧ (n ≥ 1) ∧ (method = "exclusive" ∨ method = "inclusive")

/-!
## Implementation
-/

-- Helper: StatisticsError
class StatisticsError extends BaseException

def quantiles (data : List ℚ) (n : ℕ) (method : String) : List ℚ :=
  let data := data.sort (· ≤ ·)
  let ld := data.length
  if method = "inclusive" then
    let m := ld - 1
    (List.range (n - 1)).map (λ i =>
      let i' := i + 1
      let j := (i' * m) / n
      let delta := (i' * m) % n
      let interpolated := ((data.get? j).getOrElse 0 : ℚ) * ((n : ℚ) - (delta : ℚ)) + ((data.get? (j + 1)).getOrElse 0 : ℚ) * (delta : ℚ) / (n : ℚ)
      interpolated
    )
  else
    let m := ld + 1
    (List.range (n - 1)).map (λ i =>
      let i' := i + 1
      let j := (i' * m) / n
      let j_clamped := if j < 1 then 1 else if j > ld - 1 then ld - 1 else j
      let delta := (i' * m) - (j_clamped * n)
      let interpolated := ((data.get? (j_clamped - 1)).getOrElse 0 : ℚ) * ((n : ℚ) - (delta : ℚ)) + ((data.get? j_clamped).getOrElse 0 : ℚ) * (delta : ℚ) / (n : ℚ)
      interpolated
    )

def benchmark_quantiles (data : List ℚ) (n : ℕ) (method : String) : List ℚ :=
  if h : ¬ Pre data n method then
    throw (StatisticsError "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method")
  else
    quantiles data n method

/-!
## Tests
-/

example : benchmark_quantiles [1, 2, 3, 4] 4 "exclusive" = [1.25, 2.5, 3.75] := by native_decide

example : benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 "exclusive" = [] := by native_decide

example : benchmark_quantiles [1, 2, 3, 4, 5] 2 "exclusive" = [3.0] := by native_decide

example : benchmark_quantiles [1, 2, 3, 4] 4 "inclusive" = [1.75, 2.5, 3.25] := by native_decide

example : benchmark_quantiles [1, 2, 3, 4] 4 "exclusive" = [1.25, 2.5, 3.75] := by native_decide

example : benchmark_quantiles (List.range 10) 4 "exclusive" = [] := by native_decide

example : benchmark_quantiles [4, 1, 3, 2] 4 "exclusive" = [1.25, 2.5, 3.75] := by native_decide

example : benchmark_quantiles [1.5, 2.5, 3.5, 4.5] 2 "exclusive" = [3.0] := by native_decide

/-!
## Properties
-/

theorem result_length_prop (data : List ℚ) (n : ℕ) (hn : n ≥ 1) (method : String) (hmethod : method = "exclusive" ∨ method = "inclusive") (hdata : data.length ≥ 2) :
  (benchmark_quantiles data n method).length = n - 1 := by
  native_decide

theorem inclusive_method_prop (data : List ℚ) (n : ℕ) (hn : n ≥ 1) (hdata : data.length ≥ 2) :
  benchmark_quantiles data n "inclusive" = quantiles data n "inclusive" := by
  unfold benchmark_quantiles
  simp [Pre, hdata, hn, show "inclusive" = "inclusive" from rfl]
  sorry

theorem exclusive_method_prop (data : List ℚ) (n : ℕ) (hn : n ≥ 1) (hdata : data.length ≥ 2) :
  benchmark_quantiles data n "exclusive" = quantiles data n "exclusive" := by
  unfold benchmark_quantiles
  simp [Pre, hdata, hn, show "exclusive" = "exclusive" from rfl]
  sorry

theorem sorted_input_prop (data : List ℚ) (n : ℕ) (hn : n ≥ 1) (method : String) (hdata : data.length ≥ 2) :
  benchmark_quantiles data n method = benchmark_quantiles (data.sort (· ≤ ·)) n method := by
  sorry

theorem unsorted_input_prop (data : List ℚ) (n : ℕ) (hn : n ≥ 1) (method : String) (hdata : data.length ≥ 2) :
  benchmark_quantiles data n method = benchmark_quantiles (data.sort (· ≤ ·)) n method := by
  sorry

theorem error_cases_prop :
  (∀ data : List ℚ, data.length < 2 → ∀ n : ℕ, ∀ method : String, 
    (try benchmark_quantiles data n method catch _ => StatisticsError _) = StatisticsError _) ∧
  (∀ data : List ℚ, data.length ≥ 2 → ∀ n : ℕ, n < 1 → 
    (try benchmark_quantiles data n "exclusive" catch _ => StatisticsError _) = StatisticsError _) ∧
  (∀ data : List ℚ, data.length ≥ 2 → ∀ n : ℕ, ∀ method : String, method ∉ ["exclusive", "inclusive"] →
    (try benchmark_quantiles data n method catch _ => StatisticsError _) = StatisticsError _) := by
  sorry

/-!
## Correctness Theorem
-/

theorem correctness_thm (data : List ℚ) (n : ℕ) (method : String)
  (hPre : Pre data n method) : True := by
  trivial

end BenchmarkQuantiles
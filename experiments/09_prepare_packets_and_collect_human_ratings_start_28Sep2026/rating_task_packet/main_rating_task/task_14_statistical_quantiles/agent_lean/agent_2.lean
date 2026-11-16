import Mathlib

/-!
# Formalization of `statistics.quantiles` (Task 31)

This module formalizes Python's `statistics.quantiles` and `benchmark_quantiles`
functions, which divide a dataset into `n` continuous intervals with equal probability
and return the `n - 1` cut points separating the intervals, supporting both the
`"exclusive"` (default) and `"inclusive"` methods.

## Structure
1. Functional implementation (`pre`, `quantiles`, `benchmark_quantiles`, `benchmark_quantiles?`,
   plus `Float` executable counterparts)
2. Unit tests (`by native_decide` and `#eval`)
3. Pre-condition predicate (`Pre`)
4. Property propositions (`<name>_prop`) and proven theorems (`<name>_thm`)
5. Post-condition predicate (`Post_prop`)
6. Property-based tests (`Plausible.Testable.check` and bounded `native_decide` checks)
7. Total correctness theorem (`Pre → Post_prop`)
8. Imperative implementation using `Id.run do` with mutable state
9. Imperative unit tests
10. Functional-imperative equivalence theorems
-/

namespace «31_statistics_quantiles»

/-! ## 1. Implementation (Functional Definition) -/

/-- Clamp a natural number `j` to the closed interval `[low, high]`. -/
def clampNat (j low high : Nat) : Nat :=
  if j < low then low else if j > high then high else j

/-- Boolean pre-condition matching Python's `pre(data, n=4, method='exclusive')`:-
    `data` has at least 2 elements, `n ≥ 1`, and `method` is `"inclusive"` or `"exclusive"`. -/
def pre {α : Type} (data : List α) (n : Nat := 4) (method : String := "exclusive") : Bool :=
  decide (data.length ≥ 2) && decide (n ≥ 1) && (method == "inclusive" || method == "exclusive")

/-- Linear interpolation step for the `"inclusive"` quantile method on a sorted list `s`.
    Computes `(s[j] * (n - delta) + s[j + 1] * delta) / n` where `(j, delta) = divmod(i * (ld - 1), n)`. -/
def inclusiveStep (s : List Rat) (n i : Nat) : Rat :=
  let ld := s.length
  let m := ld - 1
  let j := (i * m) / n
  let delta := (i * m) % n
  (s.getD j 0 * ((n - delta : Nat) : Rat) + s.getD (j + 1) 0 * (delta : Rat)) / (n : Rat)

/-- Linear interpolation step for the `"exclusive"` quantile method on a sorted list `s`.
    Computes `(s[j - 1] * (n - delta) + s[j] * delta) / n` where `j = clamp((i * (ld + 1)) // n, 1, ld - 1)`
    and `delta = i * (ld + 1) - j * n`. -/
def exclusiveStep (s : List Rat) (n i : Nat) : Rat :=
  let ld := s.length
  let m := ld + 1
  let j0 := (i * m) / n
  let j := clampNat j0 1 (ld - 1)
  let delta : Int := (i : Int) * (m : Int) - (j : Int) * (n : Int)
  (s.getD (j - 1) 0 * ((n : Int) - delta : Rat) + s.getD j 0 * (delta : Rat)) / (n : Rat)

/-- Functional implementation of Python's `quantiles(data, n=4, method='exclusive')` over `Rat`.
    Returns the `n - 1` cut points separating `data` into `n` intervals, or `[]` on invalid input. -/
def quantiles (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : List Rat :=
  if n < 1 then []
  else
    let s := data.mergeSort
    let ld := s.length
    if ld < 2 then []
    else if method == "inclusive" then
      (List.range (n - 1)).map (fun k => inclusiveStep s n (k + 1))
    else if method == "exclusive" then
      (List.range (n - 1)).map (fun k => exclusiveStep s n (k + 1))
    else []

/-- Main function to be verified (`benchmark_quantiles`), returning `List Rat`. -/
def benchmark_quantiles (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : List Rat :=
  if !pre data n method then []
  else quantiles data n method

/-- Option-returning variant of `benchmark_quantiles` that explicitly models raising
    `StatisticsError` / `ValueError` as `none` when `pre` fails and `some result` when `pre` holds. -/
def benchmark_quantiles? (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : Option (List Rat) :=
  if !pre data n method then none
  else some (quantiles data n method)

/-- Floating-point step for `"inclusive"` method. -/
def inclusiveStepFloat (s : List Float) (n i : Nat) : Float :=
  let ld := s.length
  let m := ld - 1
  let j := (i * m) / n
  let delta := (i * m) % n
  (s.getD j 0.0 * Float.ofNat (n - delta) + s.getD (j + 1) 0.0 * Float.ofNat delta) / Float.ofNat n

/-- Floating-point step for `"exclusive"` method. -/
def exclusiveStepFloat (s : List Float) (n i : Nat) : Float :=
  let ld := s.length
  let m := ld + 1
  let j0 := (i * m) / n
  let j := clampNat j0 1 (ld - 1)
  let delta : Int := (i : Int) * (m : Int) - (j : Int) * (n : Int)
  (s.getD (j - 1) 0.0 * Float.ofInt ((n : Int) - delta) + s.getD j 0.0 * Float.ofInt delta) / Float.ofNat n

/-- Executable `Float` implementation of `quantiles`. -/
def quantilesFloat (data : List Float) (n : Nat := 4) (method : String := "exclusive") : List Float :=
  if n < 1 then []
  else
    let s := data.mergeSort (fun a b => decide (a ≤ b))
    let ld := s.length
    if ld < 2 then []
    else if method == "inclusive" then
      (List.range (n - 1)).map (fun k => inclusiveStepFloat s n (k + 1))
    else if method == "exclusive" then
      (List.range (n - 1)).map (fun k => exclusiveStepFloat s n (k + 1))
    else []

/-- Executable `Float` implementation of `benchmark_quantiles?`. -/
def benchmark_quantiles_float? (data : List Float) (n : Nat := 4) (method : String := "exclusive") : Option (List Float) :=
  if !pre data n method then none
  else some (quantilesFloat data n method)

/-! ## 2. Unit Tests -/

-- 1. Basic quartiles (default)
example : benchmark_quantiles [1, 2, 3, 4] = [1.25, 2.5, 3.75] := by native_decide
example : (benchmark_quantiles [1, 2, 3, 4]).length = 3 := by native_decide
example : benchmark_quantiles? [1, 2, 3, 4] = some [1.25, 2.5, 3.75] := by native_decide

-- 2. Deciles (n = 10)
example : (benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10).length = 9 := by native_decide
example : benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 =
  [0.2, 1.4, 2.6, 3.8, 5, 6.2, 7.4, 8.6, 9.8] := by native_decide

-- 3. Median (n = 2)
example : benchmark_quantiles [1, 2, 3, 4, 5] 2 = [3] := by native_decide
example : (benchmark_quantiles [1, 2, 3, 4, 5] 2).length = 1 := by native_decide

-- 4. Inclusive method
example : benchmark_quantiles [1, 2, 3, 4] 4 "inclusive" = [1.75, 2.5, 3.25] := by native_decide
example : (benchmark_quantiles [1, 2, 3, 4] 4 "inclusive").length = 3 := by native_decide

-- 5. Exclusive method (explicit)
example : benchmark_quantiles [1, 2, 3, 4] 4 "exclusive" = [1.25, 2.5, 3.75] := by native_decide
example : (benchmark_quantiles [1, 2, 3, 4] 4 "exclusive").length = 3 := by native_decide

-- 6. Larger dataset (1..10, n = 4)
example : benchmark_quantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4 = [2.75, 5.5, 8.25] := by native_decide
example : (benchmark_quantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4).length = 3 := by native_decide

-- 7. Unsorted input (sorted internally)
example : benchmark_quantiles [4, 1, 3, 2] 4 = [1.25, 2.5, 3.75] := by native_decide
example : (benchmark_quantiles [4, 1, 3, 2] 4).length = 3 := by native_decide

-- 8. Fractional / Float data
example : benchmark_quantiles [1.5, 2.5, 3.5, 4.5] 2 = [3.0] := by native_decide
example : ((quantilesFloat [1.5, 2.5, 3.5, 4.5] 2).getD 0 0.0 - 3.0).abs < 1e-9 := by native_decide
example : (quantilesFloat [1.0, 2.0, 3.0, 4.0] 4 "inclusive").length = 3 := by native_decide

-- 9. Error cases (single data point, n = 0, invalid method)
example : benchmark_quantiles? [1] 4 = none := by native_decide
example : benchmark_quantiles? [1, 2] 0 = none := by native_decide
example : benchmark_quantiles? [1, 2, 3] 4 "invalid" = none := by native_decide
example : benchmark_quantiles [1] 4 = [] := by native_decide
example : benchmark_quantiles [1, 2] 0 = [] := by native_decide
example : benchmark_quantiles [1, 2, 3] 4 "invalid" = [] := by native_decide
example : (benchmark_quantiles_float? [1.0] 4).isNone = true := by native_decide
example : (benchmark_quantiles_float? [1.0, 2.0] 0).isNone = true := by native_decide
example : (benchmark_quantiles_float? [1.0, 2.0, 3.0] 4 "invalid").isNone = true := by native_decide

#eval benchmark_quantiles [1, 2, 3, 4]
#eval benchmark_quantiles [1, 2, 3, 4] 4 "inclusive"
#eval benchmark_quantiles [4, 1, 3, 2] 4
#eval benchmark_quantiles [1.5, 2.5, 3.5, 4.5] 2
#eval benchmark_quantiles? [1] 4
#eval quantilesFloat [1.0, 2.0, 3.0, 4.0] 4 "exclusive"

/-! ## 3. Pre-condition Predicate (`Pre`) -/

/-- Pre-condition proposition: `data` has at least 2 elements, `n ≥ 1`,
    and `method` is either `"inclusive"` or `"exclusive"`. -/
def Pre {α : Type} (data : List α) (n : Nat := 4) (method : String := "exclusive") : Prop :=
  data.length ≥ 2 ∧ n ≥ 1 ∧ (method = "inclusive" ∨ method = "exclusive")

instance {α : Type} (data : List α) (n : Nat) (method : String) : Decidable (Pre data n method) :=
  inferInstanceAs (Decidable (data.length ≥ 2 ∧ n ≥ 1 ∧ (method = "inclusive" ∨ method = "exclusive")))

/-! ## 4. Property Propositions and Theorems -/

/-- Helper theorem: boolean `pre` is true if and only if proposition `Pre` holds. -/
theorem pre_iff_Pre {α : Type} (data : List α) (n : Nat) (method : String) :
    pre data n method = true ↔ Pre data n method := by
  simp [pre, Pre, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc]

/-- Helper theorem: boolean `pre` is false if and only if `¬ Pre` holds. -/
theorem pre_eq_false_iff_not_Pre {α : Type} (data : List α) (n : Nat) (method : String) :
    pre data n method = false ↔ ¬ Pre data n method := by
  rw [← Bool.not_eq_true, pre_iff_Pre]

/-- Property 1: Under `Pre`, `benchmark_quantiles` agrees with `quantiles` and
    `benchmark_quantiles?` returns `some (quantiles data n method)`. -/
def valid_input_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  Pre data n method →
    benchmark_quantiles data n method = quantiles data n method ∧
    benchmark_quantiles? data n method = some (quantiles data n method)

theorem valid_input_thm (data : List Rat) (n : Nat) (method : String) :
    valid_input_prop data n method := by
  intro hPre
  have hpre : pre data n method = true := (pre_iff_Pre data n method).mpr hPre
  simp [benchmark_quantiles, benchmark_quantiles?, hpre]

/-- Property 2: When `¬ Pre`, `benchmark_quantiles` returns `[]` and
    `benchmark_quantiles?` returns `none` (corresponding to raising `StatisticsError`). -/
def invalid_input_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  ¬ Pre data n method →
    benchmark_quantiles data n method = [] ∧
    benchmark_quantiles? data n method = none

theorem invalid_input_thm (data : List Rat) (n : Nat) (method : String) :
    invalid_input_prop data n method := by
  intro hNotPre
  have hpre : pre data n method = false := (pre_eq_false_iff_not_Pre data n method).mpr hNotPre
  simp [benchmark_quantiles, benchmark_quantiles?, hpre]

/-- Property 3: When `Pre data n method` holds, the returned list of cut points has length `n - 1`. -/
def length_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  Pre data n method → (benchmark_quantiles data n method).length = n - 1

theorem length_thm (data : List Rat) (n : Nat) (method : String) :
    length_prop data n method := by
  intro hPre
  have hvalid := (valid_input_thm data n method hPre).1
  rw [hvalid]
  rcases hPre with ⟨hld, hn, hmethod⟩
  have hn_not_lt : ¬ (n < 1) := by omega
  have hld_not_lt : ¬ (data.length < 2) := by omega
  unfold quantiles
  rcases hmethod with rfl | rfl <;> simp [hn_not_lt, hld_not_lt]

/-- Property 4: When `n = 1` and `Pre data 1 method` holds, there are 0 cut points (`[]`). -/
def n_eq_one_prop (data : List Rat) (method : String) : Prop :=
  Pre data 1 method → benchmark_quantiles data 1 method = []

theorem n_eq_one_thm (data : List Rat) (method : String) :
    n_eq_one_prop data method := by
  intro hPre
  have hlen := length_thm data 1 method hPre
  exact List.eq_nil_of_length_eq_zero hlen

/-- Helper lemma: `data.mergeSort` is sorted (`List.Pairwise (· ≤ ·)`). -/
theorem pairwise_le_mergeSort (data : List Rat) :
    List.Pairwise (· ≤ ·) data.mergeSort :=
  List.sorted_mergeSort' (· ≤ ·) data

/-- Helper lemma: permutations have identical `mergeSort` results. -/
theorem perm_mergeSort_eq {data₁ data₂ : List Rat} (h : List.Perm data₁ data₂) :
    data₁.mergeSort = data₂.mergeSort :=
  List.eq_of_perm_of_sorted
    ((List.mergeSort_perm data₁ _).trans (h.trans (List.mergeSort_perm data₂ _).symm))
    (pairwise_le_mergeSort data₁)
    (pairwise_le_mergeSort data₂)

/-- Property 5: Permutation invariance — any permutation of `data` yields the exact same quantiles. -/
def perm_invariant_prop (data₁ data₂ : List Rat) (n : Nat) (method : String) : Prop :=
  List.Perm data₁ data₂ →
    benchmark_quantiles data₁ n method = benchmark_quantiles data₂ n method ∧
    benchmark_quantiles? data₁ n method = benchmark_quantiles? data₂ n method

theorem perm_invariant_thm (data₁ data₂ : List Rat) (n : Nat) (method : String) :
    perm_invariant_prop data₁ data₂ n method := by
  intro hperm
  have hlen : data₁.length = data₂.length := hperm.length_eq
  have hsort : data₁.mergeSort = data₂.mergeSort := perm_mergeSort_eq hperm
  have hpre : pre data₁ n method = pre data₂ n method := by simp [pre, hlen]
  have hq : quantiles data₁ n method = quantiles data₂ n method := by simp [quantiles, hsort]
  simp [benchmark_quantiles, benchmark_quantiles?, hpre, hq]

/-- Property 6: Sorting idempotence — sorting `data` beforehand does not change the quantiles. -/
def sort_idempotent_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  benchmark_quantiles data.mergeSort n method = benchmark_quantiles data n method

theorem sort_idempotent_thm (data : List Rat) (n : Nat) (method : String) :
    sort_idempotent_prop data n method := by
  unfold sort_idempotent_prop
  exact (perm_invariant_thm data.mergeSort data n method (List.mergeSort_perm data _)).1

/-- Property 7: Exact element-wise formula for the `"inclusive"` method. -/
def inclusive_formula_prop (data : List Rat) (n : Nat) : Prop :=
  Pre data n "inclusive" →
    ∀ (k : Nat) (hk : k < (benchmark_quantiles data n "inclusive").length),
      (benchmark_quantiles data n "inclusive")[k] = inclusiveStep data.mergeSort n (k + 1)

theorem inclusive_formula_thm (data : List Rat) (n : Nat) :
    inclusive_formula_prop data n := by
  intro hPre k hk
  have hvalid := (valid_input_thm data n "inclusive" hPre).1
  rcases hPre with ⟨hld, hn, _⟩
  have hn_not_lt : ¬ (n < 1) := by omega
  have hld_not_lt : ¬ (data.length < 2) := by omega
  have hq : benchmark_quantiles data n "inclusive" =
      (List.range (n - 1)).map (fun k => inclusiveStep data.mergeSort n (k + 1)) := by
    rw [hvalid]; unfold quantiles; simp [hn_not_lt, hld_not_lt]
  simp [hq] at hk ⊢

/-- Property 8: Exact element-wise formula for the `"exclusive"` method. -/
def exclusive_formula_prop (data : List Rat) (n : Nat) : Prop :=
  Pre data n "exclusive" →
    ∀ (k : Nat) (hk : k < (benchmark_quantiles data n "exclusive").length),
      (benchmark_quantiles data n "exclusive")[k] = exclusiveStep data.mergeSort n (k + 1)

theorem exclusive_formula_thm (data : List Rat) (n : Nat) :
    exclusive_formula_prop data n := by
  intro hPre k hk
  have hvalid := (valid_input_thm data n "exclusive" hPre).1
  rcases hPre with ⟨hld, hn, _⟩
  have hn_not_lt : ¬ (n < 1) := by omega
  have hld_not_lt : ¬ (data.length < 2) := by omega
  have hq : benchmark_quantiles data n "exclusive" =
      (List.range (n - 1)).map (fun k => exclusiveStep data.mergeSort n (k + 1)) := by
    rw [hvalid]; unfold quantiles; simp [hn_not_lt, hld_not_lt]
  simp [hq] at hk ⊢

/-- Helper lemma: indexing with `getD` into a sorted list is monotone. -/
theorem sorted_getD_le {s : List Rat} (hs : List.Pairwise (· ≤ ·) s)
    {a b : Nat} (hab : a ≤ b) (hb : b < s.length) :
    s.getD a 0 ≤ s.getD b 0 := by
  have ha : a < s.length := Nat.lt_of_le_of_lt hab hb
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some]
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp hs) a b ha hb hlt

/-- Helper lemma: index bound `(i * (ld - 1)) / n + 1 < ld` for `1 ≤ i < n` and `ld ≥ 2`. -/
theorem inclusive_div_lt {ld n i : Nat} (hld : ld ≥ 2) (hi : i < n) :
    (i * (ld - 1)) / n + 1 < ld := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have hm : 0 < ld - 1 := by omega
  have hmul : i * (ld - 1) < (ld - 1) * n := by
    calc i * (ld - 1) ≤ (n - 1) * (ld - 1) := Nat.mul_le_mul_right (ld - 1) (by omega)
    _ < n * (ld - 1) := Nat.mul_lt_mul_of_pos_right (by omega) hm
    _ = (ld - 1) * n := Nat.mul_comm _ _
  have hdiv : (i * (ld - 1)) / n < ld - 1 := (Nat.div_lt_iff_lt_mul hn).mpr hmul
  omega

/-- Helper lemma: convex combination bounds over `Rat`. -/
theorem convex_bounds {lo a b hi w d n : Rat}
    (hn : 0 < n) (hw : 0 ≤ w) (hd : 0 ≤ d) (hsum : w + d = n)
    (h1 : lo ≤ a) (h2 : a ≤ b) (h3 : b ≤ hi) :
    lo ≤ (a * w + b * d) / n ∧ (a * w + b * d) / n ≤ hi := by
  constructor
  · rw [le_div_iff₀ hn]
    have h_eq : lo * n = lo * w + lo * d := by rw [← hsum]; ring
    have h_w : lo * w ≤ a * w := mul_le_mul_of_nonneg_right h1 hw
    have h_d : lo * d ≤ b * d := mul_le_mul_of_nonneg_right (le_trans h1 h2) hd
    linarith
  · rw [div_le_iff₀ hn]
    have h_eq : hi * n = hi * w + hi * d := by rw [← hsum]; ring
    have h_w : a * w ≤ hi * w := mul_le_mul_of_nonneg_right (le_trans h2 h3) hw
    have h_d : b * d ≤ hi * d := mul_le_mul_of_nonneg_right h3 hd
    linarith

/-- Helper lemma: monotonicity of linear interpolation with identical endpoints. -/
theorem interp_mono_same {a b w₁ d₁ w₂ d₂ n : Rat}
    (hn : 0 < n) (hsum₁ : w₁ + d₁ = n) (hsum₂ : w₂ + d₂ = n)
    (hab : a ≤ b) (hd : d₁ ≤ d₂) :
    (a * w₁ + b * d₁) / n ≤ (a * w₂ + b * d₂) / n := by
  rw [div_le_div_iff_of_pos_right hn]
  have h : 0 ≤ (b - a) * (d₂ - d₁) := mul_nonneg (by linarith) (by linarith)
  linear_combination h + a * hsum₁ - a * hsum₂

/-- Helper lemma: monotonicity of linear interpolation across adjacent intervals. -/
theorem interp_mono_diff {a₁ b₁ a₂ b₂ w₁ d₁ w₂ d₂ n : Rat}
    (hn : 0 < n) (hsum₁ : w₁ + d₁ = n) (hsum₂ : w₂ + d₂ = n)
    (hw₁ : 0 ≤ w₁) (hd₂ : 0 ≤ d₂)
    (hab₁ : a₁ ≤ b₁) (hmid : b₁ ≤ a₂) (hab₂ : a₂ ≤ b₂) :
    (a₁ * w₁ + b₁ * d₁) / n ≤ (a₂ * w₂ + b₂ * d₂) / n := by
  rw [div_le_div_iff_of_pos_right hn]
  have h1 : 0 ≤ (b₁ - a₁) * w₁ := mul_nonneg (by linarith) hw₁
  have h2 : 0 ≤ (a₂ - b₁) * n := mul_nonneg (by linarith) (le_of_lt hn)
  have h3 : 0 ≤ (b₂ - a₂) * d₂ := mul_nonneg (by linarith) hd₂
  linear_combination h1 + h2 + h3 + b₁ * hsum₁ - a₂ * hsum₂

/-- Helper lemma: remainder monotonicity when quotients are equal. -/
theorem nat_mod_le_of_div_eq {x₁ x₂ n : Nat} (hx : x₁ ≤ x₂) (hj : x₁ / n = x₂ / n) :
    x₁ % n ≤ x₂ % n := by
  have h1 := Nat.div_add_mod x₁ n
  have h2 := Nat.div_add_mod x₂ n
  rw [hj] at h1
  omega

/-- Helper lemma: `((n - d : Nat) : Rat) + ((d : Nat) : Rat) = (n : Rat)` for `d < n`. -/
theorem nat_sub_add_cancel_rat {n d : Nat} (hd : d < n) :
    ((n - d : Nat) : Rat) + ((d : Nat) : Rat) = (n : Rat) := by
  exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hd)

/-- Helper lemma: `inclusiveStep` is monotone in `i`. -/
theorem inclusiveStep_mono {s : List Rat} {n i₁ i₂ : Nat}
    (hs : List.Pairwise (· ≤ ·) s) (hld : s.length ≥ 2) (hle : i₁ ≤ i₂) (hi₂ : i₂ < n) :
    inclusiveStep s n i₁ ≤ inclusiveStep s n i₂ := by
  unfold inclusiveStep
  dsimp only
  have hn : 0 < n := by omega
  have hn_rat : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hx : i₁ * (s.length - 1) ≤ i₂ * (s.length - 1) := Nat.mul_le_mul_right _ hle
  have hj : (i₁ * (s.length - 1)) / n ≤ (i₂ * (s.length - 1)) / n := Nat.div_le_div_right hx
  have hj₂_lt : (i₂ * (s.length - 1)) / n + 1 < s.length := inclusive_div_lt hld hi₂
  have hj₁_lt : (i₁ * (s.length - 1)) / n + 1 < s.length := by omega
  have hd₁_lt : (i₁ * (s.length - 1)) % n < n := Nat.mod_lt _ hn
  have hd₂_lt : (i₂ * (s.length - 1)) % n < n := Nat.mod_lt _ hn
  have hsum₁ := nat_sub_add_cancel_rat hd₁_lt
  have hsum₂ := nat_sub_add_cancel_rat hd₂_lt
  have hs₁ : s.getD ((i₁ * (s.length - 1)) / n) 0 ≤ s.getD ((i₁ * (s.length - 1)) / n + 1) 0 :=
    sorted_getD_le hs (Nat.le_succ _) hj₁_lt
  have hs₂ : s.getD ((i₂ * (s.length - 1)) / n) 0 ≤ s.getD ((i₂ * (s.length - 1)) / n + 1) 0 :=
    sorted_getD_le hs (Nat.le_succ _) hj₂_lt
  rcases Nat.eq_or_lt_of_le hj with hjeq | hjlt
  · have hd_rat : (((i₁ * (s.length - 1)) % n : Nat) : Rat) ≤ (((i₂ * (s.length - 1)) % n : Nat) : Rat) :=
      Nat.cast_le.mpr (nat_mod_le_of_div_eq hx hjeq)
    rw [hjeq]
    exact interp_mono_same hn_rat hsum₁ hsum₂ hs₂ hd_rat
  · have hs_mid : s.getD ((i₁ * (s.length - 1)) / n + 1) 0 ≤ s.getD ((i₂ * (s.length - 1)) / n) 0 :=
      sorted_getD_le hs hjlt (by omega)
    exact interp_mono_diff hn_rat hsum₁ hsum₂ (by positivity) (by positivity) hs₁ hs_mid hs₂

/-- Helper lemma: `clampNat` bounds. -/
theorem clampNat_bounds {j0 low high : Nat} (h : low ≤ high) :
    low ≤ clampNat j0 low high ∧ clampNat j0 low high ≤ high := by
  unfold clampNat; split_ifs <;> omega

/-- Helper lemma: `clampNat` monotonicity. -/
theorem clampNat_mono {a b low high : Nat} (h : low ≤ high) (hab : a ≤ b) :
    clampNat a low high ≤ clampNat b low high := by
  unfold clampNat; split_ifs <;> omega

/-- Helper lemma: `clampNat` strict inequality implies unclamped bounds. -/
theorem clampNat_le_of_lt {a b low high : Nat} (h : low ≤ high) (hlt : clampNat a low high < clampNat b low high) :
    a ≤ clampNat a low high ∧ clampNat b low high ≤ b := by
  unfold clampNat at hlt ⊢
  split_ifs at hlt ⊢ <;> omega

/-- Helper lemma: `delta` monotonicity in exclusive mode when clamped indices are equal. -/
theorem exclusive_delta_le_of_eq {i₁ i₂ m j₁ j₂ n : Nat}
    (hx : i₁ * m ≤ i₂ * m) (hj : j₁ = j₂) :
    ((i₁ : Int) * (m : Int) - (j₁ : Int) * (n : Int)) ≤
    ((i₂ : Int) * (m : Int) - (j₂ : Int) * (n : Int)) := by
  have hx_int : ((i₁ * m : Nat) : Int) ≤ ((i₂ * m : Nat) : Int) := by exact_mod_cast hx
  push_cast at hx_int
  rw [hj]
  omega

/-- Helper lemma: `delta` bounds in exclusive mode when clamped index strictly increases. -/
theorem exclusive_delta_bounds_of_lt {i₁ i₂ m n high : Nat} (hn : 0 < n)
    (h : 1 ≤ high) (hlt : clampNat ((i₁ * m) / n) 1 high < clampNat ((i₂ * m) / n) 1 high) :
    (i₁ : Int) * (m : Int) - (clampNat ((i₁ * m) / n) 1 high : Int) * (n : Int) ≤ (n : Int) ∧
    (0 : Int) ≤ (i₂ : Int) * (m : Int) - (clampNat ((i₂ * m) / n) 1 high : Int) * (n : Int) := by
  have hcl := clampNat_le_of_lt h hlt
  have hj0₁ : (i₁ * m) / n ≤ clampNat ((i₁ * m) / n) 1 high := hcl.1
  have hj0₂ : clampNat ((i₂ * m) / n) 1 high ≤ (i₂ * m) / n := hcl.2
  have hdiv₁ := Nat.div_add_mod (i₁ * m) n
  have hmod₁ := Nat.mod_lt (i₁ * m) hn
  have hdiv₂ := Nat.div_add_mod (i₂ * m) n
  have hm₁ : n * ((i₁ * m) / n) ≤ n * clampNat ((i₁ * m) / n) 1 high := Nat.mul_le_mul_left n hj0₁
  have hm₂ : n * clampNat ((i₂ * m) / n) 1 high ≤ n * ((i₂ * m) / n) := Nat.mul_le_mul_left n hj0₂
  have hcomm₁ : clampNat ((i₁ * m) / n) 1 high * n = n * clampNat ((i₁ * m) / n) 1 high := Nat.mul_comm _ _
  have hcomm₂ : clampNat ((i₂ * m) / n) 1 high * n = n * clampNat ((i₂ * m) / n) 1 high := Nat.mul_comm _ _
  have hx₁ : ((i₁ * m : Nat) : Int) = (i₁ : Int) * (m : Int) := by push_cast; rfl
  have hx₂ : ((i₂ * m : Nat) : Int) = (i₂ : Int) * (m : Int) := by push_cast; rfl
  omega

/-- Helper lemma: `exclusiveStep` is monotone in `i`. -/
theorem exclusiveStep_mono {s : List Rat} {n i₁ i₂ : Nat}
    (hs : List.Pairwise (· ≤ ·) s) (hld : s.length ≥ 2) (hle : i₁ ≤ i₂) (hi₂ : i₂ < n) :
    exclusiveStep s n i₁ ≤ exclusiveStep s n i₂ := by
  unfold exclusiveStep
  dsimp only
  have hn : 0 < n := by omega
  have hn_rat : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hx : i₁ * (s.length + 1) ≤ i₂ * (s.length + 1) := Nat.mul_le_mul_right _ hle
  have hj0 : (i₁ * (s.length + 1)) / n ≤ (i₂ * (s.length + 1)) / n := Nat.div_le_div_right hx
  have hj_b₁ := clampNat_bounds (j0 := (i₁ * (s.length + 1)) / n) (low := 1) (high := s.length - 1) (by omega)
  have hj_b₂ := clampNat_bounds (j0 := (i₂ * (s.length + 1)) / n) (low := 1) (high := s.length - 1) (by omega)
  have hj : clampNat ((i₁ * (s.length + 1)) / n) 1 (s.length - 1) ≤
            clampNat ((i₂ * (s.length + 1)) / n) 1 (s.length - 1) := clampNat_mono (by omega) hj0
  set j₁ := clampNat ((i₁ * (s.length + 1)) / n) 1 (s.length - 1)
  set j₂ := clampNat ((i₂ * (s.length + 1)) / n) 1 (s.length - 1)
  set d₁ : Int := (i₁ : Int) * ((s.length + 1 : Nat) : Int) - (j₁ : Int) * (n : Int)
  set d₂ : Int := (i₂ : Int) * ((s.length + 1 : Nat) : Int) - (j₂ : Int) * (n : Int)
  have hs₁ : s.getD (j₁ - 1) 0 ≤ s.getD j₁ 0 := sorted_getD_le hs (by omega) (by omega)
  have hs₂ : s.getD (j₂ - 1) 0 ≤ s.getD j₂ 0 := sorted_getD_le hs (by omega) (by omega)
  have hsum₁ : ((n : Int) - d₁ : Rat) + (d₁ : Rat) = (n : Rat) := by push_cast; ring
  have hsum₂ : ((n : Int) - d₂ : Rat) + (d₂ : Rat) = (n : Rat) := by push_cast; ring
  rcases Nat.eq_or_lt_of_le hj with hjeq | hjlt
  · have hd_le : d₁ ≤ d₂ := exclusive_delta_le_of_eq hx hjeq
    have hd_rat : (d₁ : Rat) ≤ (d₂ : Rat) := Int.cast_le.mpr hd_le
    rw [hjeq]
    exact interp_mono_same hn_rat hsum₁ hsum₂ hs₂ hd_rat
  · have hdb := exclusive_delta_bounds_of_lt hn (by omega) hjlt
    have hw₁_rat : (0 : Rat) ≤ ((n : Int) - d₁ : Rat) := sub_nonneg.mpr (Int.cast_le.mpr hdb.1)
    have hd₂_rat : (0 : Rat) ≤ (d₂ : Rat) := Int.cast_nonneg.mpr hdb.2
    have hs_mid : s.getD j₁ 0 ≤ s.getD (j₂ - 1) 0 := sorted_getD_le hs (by omega) (by omega)
    exact interp_mono_diff hn_rat hsum₁ hsum₂ hw₁_rat hd₂_rat hs₁ hs_mid hs₂

/-- Helper lemma: mapping a monotone function over `List.range m` produces a sorted list. -/
theorem pairwise_map_range (m : Nat) (f : Nat → Rat)
    (hf : ∀ a b, a ≤ b → b < m → f a ≤ f b) :
    List.Pairwise (· ≤ ·) ((List.range m).map f) := by
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  simp only [List.length_map, List.length_range] at ha hb
  simp only [List.getElem_map, List.getElem_range]
  exact hf a b (Nat.le_of_lt hab) hb

/-- Property 9: Output monotonicity / sortedness — for both `"inclusive"` and `"exclusive"` methods,
    the returned list of quantile cut points is sorted in non-decreasing order. -/
def output_sorted_prop (data : List Rat) (n : Nat) (method : String) : Prop :=
  Pre data n method → List.Pairwise (· ≤ ·) (benchmark_quantiles data n method)

theorem output_sorted_thm (data : List Rat) (n : Nat) (method : String) :
    output_sorted_prop data n method := by
  intro hPre
  have hvalid := (valid_input_thm data n method hPre).1
  rw [hvalid]
  rcases hPre with ⟨hld, hn, hmethod⟩
  have hn_not_lt : ¬ (n < 1) := by omega
  have hld_sort : (data.mergeSort).length ≥ 2 := by rw [List.length_mergeSort]; exact hld
  have hld_not_lt : ¬ ((data.mergeSort).length < 2) := by omega
  have hsort : List.Pairwise (· ≤ ·) data.mergeSort := pairwise_le_mergeSort data
  unfold quantiles
  rcases hmethod with rfl | rfl
  · simp only [hn_not_lt, ↓reduceIte, hld_not_lt, beq_self_eq_true]
    apply pairwise_map_range
    intro a b hab hb
    exact inclusiveStep_mono hsort hld_sort (by omega) (by omega)
  · have hne : ("exclusive" == "inclusive") = false := rfl
    simp only [hn_not_lt, ↓reduceIte, hld_not_lt, hne, Bool.false_eq_true, beq_self_eq_true]
    apply pairwise_map_range
    intro a b hab hb
    exact exclusiveStep_mono hsort hld_sort (by omega) (by omega)

/-- Helper lemma: bounds on `inclusiveStep`. -/
theorem inclusiveStep_bounds {s : List Rat} {n i : Nat}
    (hs : List.Pairwise (· ≤ ·) s) (hld : s.length ≥ 2) (hin : i < n) :
    s.getD 0 0 ≤ inclusiveStep s n i ∧ inclusiveStep s n i ≤ s.getD (s.length - 1) 0 := by
  unfold inclusiveStep
  dsimp only
  have hn : 0 < n := by omega
  have hn_rat : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hj_lt : (i * (s.length - 1)) / n + 1 < s.length := inclusive_div_lt hld hin
  have hdel_lt : (i * (s.length - 1)) % n < n := Nat.mod_lt _ hn
  have hsum := nat_sub_add_cancel_rat hdel_lt
  exact convex_bounds hn_rat (by positivity) (by positivity) hsum
    (sorted_getD_le hs (Nat.zero_le _) (by omega))
    (sorted_getD_le hs (Nat.le_succ _) hj_lt)
    (sorted_getD_le hs (by omega) (by omega))

/-- Property 10: Inclusive bounds — when `method = "inclusive"`, every cut point lies
    between the minimum (`data.mergeSort[0]`) and maximum (`data.mergeSort[ld - 1]`) of `data`. -/
def inclusive_bounds_prop (data : List Rat) (n : Nat) : Prop :=
  Pre data n "inclusive" →
    ∀ q ∈ benchmark_quantiles data n "inclusive",
      data.mergeSort.getD 0 0 ≤ q ∧ q ≤ data.mergeSort.getD (data.length - 1) 0

theorem inclusive_bounds_thm (data : List Rat) (n : Nat) :
    inclusive_bounds_prop data n := by
  intro hPre q hq
  have hvalid := (valid_input_thm data n "inclusive" hPre).1
  rcases hPre with ⟨hld, hn, _⟩
  have hn_not_lt : ¬ (n < 1) := by omega
  have hld_eq : data.mergeSort.length = data.length := List.length_mergeSort data
  have hld_sort : data.mergeSort.length ≥ 2 := by omega
  have hld_not_lt : ¬ (data.mergeSort.length < 2) := by omega
  have hsort : List.Pairwise (· ≤ ·) data.mergeSort := pairwise_le_mergeSort data
  rw [hvalid] at hq
  unfold quantiles at hq
  simp only [hn_not_lt, ↓reduceIte, hld_not_lt, beq_self_eq_true, List.mem_map, List.mem_range] at hq
  rcases hq with ⟨k, hk, rfl⟩
  rw [← hld_eq]
  exact inclusiveStep_bounds hsort hld_sort (by omega)

/-- Helper lemma: when `n ≤ ld + 1` and `1 ≤ i < n`, the exclusive delta lies in `[0, n]`. -/
theorem exclusive_delta_bounds_when_n_le {ld n i : Nat}
    (hld : ld ≥ 2) (hn_le : n ≤ ld + 1) (hi1 : 1 ≤ i) (hin : i < n) :
    let j := clampNat ((i * (ld + 1)) / n) 1 (ld - 1)
    (i : Int) * ((ld + 1 : Nat) : Int) - (j : Int) * (n : Int) ≤ (n : Int) ∧
    (0 : Int) ≤ (i : Int) * ((ld + 1 : Nat) : Int) - (j : Int) * (n : Int) := by
  dsimp only
  have hn : 0 < n := by omega
  have hge : 1 * n ≤ i * (ld + 1) := by
    calc 1 * n ≤ i * n := Nat.mul_le_mul_right n hi1
    _ ≤ i * (ld + 1) := Nat.mul_le_mul_left i hn_le
  have hj0_ge : 1 ≤ (i * (ld + 1)) / n := (Nat.le_div_iff_mul_le hn).mpr hge
  have hj_le_j0 : clampNat ((i * (ld + 1)) / n) 1 (ld - 1) ≤ (i * (ld + 1)) / n := by
    unfold clampNat; split_ifs <;> omega
  have hdiv := Nat.div_add_mod (i * (ld + 1)) n
  have hmod := Nat.mod_lt (i * (ld + 1)) hn
  have hm_lo : n * clampNat ((i * (ld + 1)) / n) 1 (ld - 1) ≤ n * ((i * (ld + 1)) / n) :=
    Nat.mul_le_mul_left n hj_le_j0
  have hcomm : clampNat ((i * (ld + 1)) / n) 1 (ld - 1) * n = n * clampNat ((i * (ld + 1)) / n) 1 (ld - 1) :=
    Nat.mul_comm _ _
  have hx : ((i * (ld + 1) : Nat) : Int) = (i : Int) * ((ld + 1 : Nat) : Int) := by push_cast; rfl
  have h_upper : i * (ld + 1) ≤ clampNat ((i * (ld + 1)) / n) 1 (ld - 1) * n + n := by
    by_cases hhi : (i * (ld + 1)) / n > ld - 1
    · have hcl : clampNat ((i * (ld + 1)) / n) 1 (ld - 1) = ld - 1 := by
        unfold clampNat; split_ifs <;> omega
      rw [hcl]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, ld = l + 2 := ⟨ld - 2, by omega⟩
      have h1 : i * (l + 2 + 1) ≤ k * (l + 2 + 1) := Nat.mul_le_mul_right _ (by omega)
      have h2 : k * (l + 2 + 1) = k * l + 3 * k := by ring
      have h3 : (l + 2 - 1) * (k + 1) + (k + 1) = k * l + 2 * k + l + 2 := by
        change (l + 1) * (k + 1) + (k + 1) = k * l + 2 * k + l + 2; ring
      omega
    · have hcl : clampNat ((i * (ld + 1)) / n) 1 (ld - 1) = (i * (ld + 1)) / n := by
        unfold clampNat; split_ifs <;> omega
      rw [hcomm, hcl]
      omega
  omega

/-- Helper lemma: bounds on `exclusiveStep` when `n ≤ s.length + 1`. -/
theorem exclusiveStep_bounds {s : List Rat} {n i : Nat}
    (hs : List.Pairwise (· ≤ ·) s) (hld : s.length ≥ 2) (hn_le : n ≤ s.length + 1)
    (hi1 : 1 ≤ i) (hin : i < n) :
    s.getD 0 0 ≤ exclusiveStep s n i ∧ exclusiveStep s n i ≤ s.getD (s.length - 1) 0 := by
  unfold exclusiveStep
  dsimp only
  have hn : 0 < n := by omega
  have hn_rat : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hj_b := clampNat_bounds (j0 := (i * (s.length + 1)) / n) (low := 1) (high := s.length - 1) (by omega)
  set j := clampNat ((i * (s.length + 1)) / n) 1 (s.length - 1)
  set d : Int := (i : Int) * ((s.length + 1 : Nat) : Int) - (j : Int) * (n : Int)
  have hdb := exclusive_delta_bounds_when_n_le hld hn_le hi1 hin
  have hw_rat : (0 : Rat) ≤ ((n : Int) - d : Rat) := sub_nonneg.mpr (Int.cast_le.mpr hdb.1)
  have hd_rat : (0 : Rat) ≤ (d : Rat) := Int.cast_nonneg.mpr hdb.2
  have hsum : ((n : Int) - d : Rat) + (d : Rat) = (n : Rat) := by push_cast; ring
  exact convex_bounds hn_rat hw_rat hd_rat hsum
    (sorted_getD_le hs (by omega) (by omega))
    (sorted_getD_le hs (by omega) (by omega))
    (sorted_getD_le hs (by omega) (by omega))

/-- Property 11: Exclusive bounds — when `method = "exclusive"` and `n ≤ data.length + 1`,
    every cut point lies between the minimum and maximum of `data`. -/
def exclusive_bounds_prop (data : List Rat) (n : Nat) : Prop :=
  Pre data n "exclusive" → n ≤ data.length + 1 →
    ∀ q ∈ benchmark_quantiles data n "exclusive",
      data.mergeSort.getD 0 0 ≤ q ∧ q ≤ data.mergeSort.getD (data.length - 1) 0

theorem exclusive_bounds_thm (data : List Rat) (n : Nat) :
    exclusive_bounds_prop data n := by
  intro hPre hn_le q hq
  have hvalid := (valid_input_thm data n "exclusive" hPre).1
  rcases hPre with ⟨hld, hn, _⟩
  have hn_not_lt : ¬ (n < 1) := by omega
  have hld_eq : data.mergeSort.length = data.length := List.length_mergeSort data
  have hld_sort : data.mergeSort.length ≥ 2 := by omega
  have hld_not_lt : ¬ (data.mergeSort.length < 2) := by omega
  have hsort : List.Pairwise (· ≤ ·) data.mergeSort := pairwise_le_mergeSort data
  have hne : ("exclusive" == "inclusive") = false := rfl
  rw [hvalid] at hq
  unfold quantiles at hq
  simp only [hn_not_lt, ↓reduceIte, hld_not_lt, hne, Bool.false_eq_true, beq_self_eq_true,
    List.mem_map, List.mem_range] at hq
  rcases hq with ⟨k, hk, rfl⟩
  rw [← hld_eq] at hn_le ⊢
  exact exclusiveStep_bounds hsort hld_sort hn_le (by omega) (by omega)

/-- Helper lemma: sorting a replicated list `List.replicate ld c` returns `List.replicate ld c`. -/
theorem mergeSort_replicate (ld : Nat) (c : Rat) :
    (List.replicate ld c).mergeSort = List.replicate ld c := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun x hx => ?_⟩
  exact List.eq_of_mem_replicate ((List.mergeSort_perm (List.replicate ld c) _).subset hx)

/-- Helper lemma: interpolating between equal values `c` and `c` yields `c`. -/
theorem interp_const {c w d n : Rat} (hn : n ≠ 0) (hsum : w + d = n) :
    (c * w + c * d) / n = c := by
  have h : c * w + c * d = c * n := by linear_combination c * hsum
  rw [h, mul_div_cancel_right₀ c hn]

/-- Property 12: Constant dataset — if all `ld ≥ 2` elements of `data` equal `c`,
    every cut point in `benchmark_quantiles` equals `c`. -/
def constant_data_prop (ld : Nat) (c : Rat) (n : Nat) (method : String) : Prop :=
  Pre (List.replicate ld c) n method →
    benchmark_quantiles (List.replicate ld c) n method = List.replicate (n - 1) c

theorem constant_data_thm (ld : Nat) (c : Rat) (n : Nat) (method : String) :
    constant_data_prop ld c n method := by
  intro hPre
  have hvalid := (valid_input_thm (List.replicate ld c) n method hPre).1
  rw [hvalid]
  rcases hPre with ⟨hld, hn, hmethod⟩
  simp only [List.length_replicate] at hld
  have hn_not_lt : ¬ (n < 1) := by omega
  have hn_pos : (n : Rat) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hrep : (List.replicate ld c).mergeSort = List.replicate ld c := mergeSort_replicate ld c
  have hld_not_lt : ¬ ((List.replicate ld c).mergeSort.length < 2) := by simp [hrep]; omega
  unfold quantiles
  rcases hmethod with rfl | rfl
  · simp only [hn_not_lt, ↓reduceIte, hld_not_lt, beq_self_eq_true]
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun q hq => ?_⟩
    rw [List.mem_map] at hq
    rcases hq with ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    rw [hrep]
    unfold inclusiveStep
    dsimp only
    simp only [List.length_replicate]
    have hj_lt : ((k + 1) * (ld - 1)) / n + 1 < ld := inclusive_div_lt hld (by omega)
    have hj0_lt : ((k + 1) * (ld - 1)) / n < ld := by omega
    have hdel_lt : ((k + 1) * (ld - 1)) % n < n := Nat.mod_lt _ (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj0_lt, hj_lt, ↓reduceIte, Option.getD_some]
    exact interp_const hn_pos (nat_sub_add_cancel_rat hdel_lt)
  · have hne : ("exclusive" == "inclusive") = false := rfl
    simp only [hn_not_lt, ↓reduceIte, hld_not_lt, hne, Bool.false_eq_true, beq_self_eq_true]
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun q hq => ?_⟩
    rw [List.mem_map] at hq
    rcases hq with ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    rw [hrep]
    unfold exclusiveStep
    dsimp only
    simp only [List.length_replicate]
    have hj_bounds := clampNat_bounds (j0 := ((k + 1) * (ld + 1)) / n) (low := 1) (high := ld - 1) (by omega)
    set j := clampNat (((k + 1) * (ld + 1)) / n) 1 (ld - 1)
    have hj1_lt : j - 1 < ld := by omega
    have hj_lt : j < ld := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj1_lt, hj_lt, ↓reduceIte, Option.getD_some]
    exact interp_const hn_pos (by push_cast; ring)

/-- Helper lemma: `inclusiveStep` for `n = 2`, `i = 1` on odd-length list `2 * k + 1`. -/
theorem odd_median_inc (s : List Rat) (k : Nat) (hld : s.length = 2 * k + 1) :
    inclusiveStep s 2 1 = s.getD k 0 := by
  unfold inclusiveStep
  dsimp only
  rw [hld]
  have h1 : (1 * (2 * k + 1 - 1)) / 2 = k := by omega
  have h2 : (1 * (2 * k + 1 - 1)) % 2 = 0 := by omega
  rw [h1, h2]
  norm_num

/-- Helper lemma: `exclusiveStep` for `n = 2`, `i = 1` on odd-length list `2 * k + 1` (`k ≥ 1`). -/
theorem odd_median_exc (s : List Rat) (k : Nat) (hk : k ≥ 1) (hld : s.length = 2 * k + 1) :
    exclusiveStep s 2 1 = s.getD k 0 := by
  unfold exclusiveStep
  dsimp only
  rw [hld]
  have h1 : (1 * (2 * k + 1 + 1)) / 2 = k + 1 := by omega
  have h2 : clampNat ((1 * (2 * k + 1 + 1)) / 2) 1 (2 * k + 1 - 1) = k + 1 := by
    rw [h1]; unfold clampNat; split_ifs <;> omega
  have h3 : ((1 : Nat) : Int) * ((2 * k + 1 + 1 : Nat) : Int) -
    ((clampNat ((1 * (2 * k + 1 + 1)) / 2) 1 (2 * k + 1 - 1) : Nat) : Int) * ((2 : Nat) : Int) = 0 := by
    rw [h2]; omega
  rw [h3, h2]
  simp

/-- Property 13: Odd-length median (`n = 2`) — when `data` has odd length `2 * k + 1` (`k ≥ 1`),
    both `"inclusive"` and `"exclusive"` methods return the exact middle element `[data.mergeSort[k]]`. -/
def odd_median_prop (data : List Rat) (k : Nat) (method : String) : Prop :=
  k ≥ 1 → data.length = 2 * k + 1 → Pre data 2 method →
    benchmark_quantiles data 2 method = [data.mergeSort.getD k 0]

theorem odd_median_thm (data : List Rat) (k : Nat) (method : String) :
    odd_median_prop data k method := by
  intro hk hlen hPre
  have hvalid := (valid_input_thm data 2 method hPre).1
  rw [hvalid]
  rcases hPre with ⟨_, _, hmethod⟩
  have hld_sort : data.mergeSort.length = 2 * k + 1 := by rw [List.length_mergeSort, hlen]
  have hld_not_lt : ¬ (data.mergeSort.length < 2) := by omega
  have hn_not_lt : ¬ (2 < 1) := by decide
  unfold quantiles
  rcases hmethod with rfl | rfl
  · simp only [hn_not_lt, ↓reduceIte, hld_not_lt, beq_self_eq_true]
    exact congrArg (· :: []) (odd_median_inc data.mergeSort k hld_sort)
  · have hne : ("exclusive" == "inclusive") = false := rfl
    simp only [hn_not_lt, ↓reduceIte, hld_not_lt, hne, Bool.false_eq_true, beq_self_eq_true]
    exact congrArg (· :: []) (odd_median_exc data.mergeSort k hk hld_sort)

/-! ## 5. Post-condition (`Post_prop`) -/

/-- Post-condition combining all core specification properties of `benchmark_quantiles`. -/
def Post_prop (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : Prop :=
  benchmark_quantiles data n method = quantiles data n method ∧
  benchmark_quantiles? data n method = some (quantiles data n method) ∧
  (benchmark_quantiles data n method).length = n - 1 ∧
  List.Pairwise (· ≤ ·) (benchmark_quantiles data n method) ∧
  benchmark_quantiles data.mergeSort n method = benchmark_quantiles data n method ∧
  (method = "inclusive" →
    (∀ (k : Nat) (hk : k < (benchmark_quantiles data n "inclusive").length),
      (benchmark_quantiles data n "inclusive")[k] = inclusiveStep data.mergeSort n (k + 1)) ∧
    (∀ q ∈ benchmark_quantiles data n "inclusive",
      data.mergeSort.getD 0 0 ≤ q ∧ q ≤ data.mergeSort.getD (data.length - 1) 0)) ∧
  (method = "exclusive" →
    (∀ (k : Nat) (hk : k < (benchmark_quantiles data n "exclusive").length),
      (benchmark_quantiles data n "exclusive")[k] = exclusiveStep data.mergeSort n (k + 1)) ∧
    (n ≤ data.length + 1 →
      ∀ q ∈ benchmark_quantiles data n "exclusive",
        data.mergeSort.getD 0 0 ≤ q ∧ q ≤ data.mergeSort.getD (data.length - 1) 0))

instance (data : List Rat) (n : Nat) (method : String) : Decidable (valid_input_prop data n method) := by
  unfold valid_input_prop; exact inferInstance

instance (data : List Rat) (n : Nat) (method : String) : Decidable (invalid_input_prop data n method) := by
  unfold invalid_input_prop; exact inferInstance

instance (data : List Rat) (n : Nat) (method : String) : Decidable (length_prop data n method) := by
  unfold length_prop; exact inferInstance

instance (data : List Rat) (method : String) : Decidable (n_eq_one_prop data method) := by
  unfold n_eq_one_prop; exact inferInstance

instance (data : List Rat) (n : Nat) (method : String) : Decidable (sort_idempotent_prop data n method) := by
  unfold sort_idempotent_prop; exact inferInstance

instance (data : List Rat) (n : Nat) : Decidable (inclusive_formula_prop data n) := by
  unfold inclusive_formula_prop; exact inferInstance

instance (data : List Rat) (n : Nat) : Decidable (exclusive_formula_prop data n) := by
  unfold exclusive_formula_prop; exact inferInstance

instance (data : List Rat) (n : Nat) (method : String) : Decidable (output_sorted_prop data n method) := by
  unfold output_sorted_prop; exact inferInstance

instance (data : List Rat) (n : Nat) : Decidable (inclusive_bounds_prop data n) := by
  unfold inclusive_bounds_prop; exact inferInstance

instance (data : List Rat) (n : Nat) : Decidable (exclusive_bounds_prop data n) := by
  unfold exclusive_bounds_prop; exact inferInstance

instance (ld : Nat) (c : Rat) (n : Nat) (method : String) : Decidable (constant_data_prop ld c n method) := by
  unfold constant_data_prop; exact inferInstance

instance (data : List Rat) (k : Nat) (method : String) : Decidable (odd_median_prop data k method) := by
  unfold odd_median_prop; exact inferInstance

instance (data : List Rat) (n : Nat) (method : String) : Decidable (Post_prop data n method) := by
  unfold Post_prop; exact inferInstance

/-! ## 6. Property-Based Tests (PBTs) -/

-- Randomized PBTs using Plausible for every `_prop` and `Post_prop`
#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  valid_input_prop (x :: y :: rest) ((n % 10) + 1) "exclusive" ∧
  valid_input_prop (x :: y :: rest) ((n % 10) + 1) "inclusive")

#eval Plausible.Testable.check (∀ (x : Rat) (n : Nat),
  invalid_input_prop [x] n "exclusive" ∧ invalid_input_prop [x, x] 0 "exclusive" ∧
  invalid_input_prop [x, x] (n + 1) "invalid")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  length_prop (x :: y :: rest) ((n % 12) + 1) "exclusive" ∧
  length_prop (x :: y :: rest) ((n % 12) + 1) "inclusive")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat),
  n_eq_one_prop (x :: y :: rest) "exclusive" ∧ n_eq_one_prop (x :: y :: rest) "inclusive")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  benchmark_quantiles (x :: y :: rest).reverse ((n % 8) + 1) "exclusive" =
    benchmark_quantiles (x :: y :: rest) ((n % 8) + 1) "exclusive" ∧
  benchmark_quantiles (x :: y :: rest).reverse ((n % 8) + 1) "inclusive" =
    benchmark_quantiles (x :: y :: rest) ((n % 8) + 1) "inclusive")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  sort_idempotent_prop (x :: y :: rest) ((n % 8) + 1) "exclusive" ∧
  sort_idempotent_prop (x :: y :: rest) ((n % 8) + 1) "inclusive")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  inclusive_formula_prop (x :: y :: rest) ((n % 8) + 1) ∧
  exclusive_formula_prop (x :: y :: rest) ((n % 8) + 1))

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  output_sorted_prop (x :: y :: rest) ((n % 8) + 1) "exclusive" ∧
  output_sorted_prop (x :: y :: rest) ((n % 8) + 1) "inclusive")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  inclusive_bounds_prop (x :: y :: rest) ((n % 8) + 1) ∧
  exclusive_bounds_prop (x :: y :: rest) ((n % 8) + 1))

#eval Plausible.Testable.check (∀ (c : Rat) (ld n : Nat),
  constant_data_prop ((ld % 8) + 2) c ((n % 8) + 1) "exclusive" ∧
  constant_data_prop ((ld % 8) + 2) c ((n % 8) + 1) "inclusive")

#eval Plausible.Testable.check (∀ (x y z : Rat),
  odd_median_prop [x, y, z] 1 "exclusive" ∧ odd_median_prop [x, y, z] 1 "inclusive")

#eval Plausible.Testable.check (∀ (x y : Rat) (rest : List Rat) (n : Nat),
  Post_prop (x :: y :: rest) ((n % 8) + 1) "exclusive" ∧
  Post_prop (x :: y :: rest) ((n % 8) + 1) "inclusive")

-- Bounded exhaustive PBTs using `native_decide`
example : (List.range 10).all (fun n =>
  let n' := n + 1
  let data : List Rat := [4, 1, 7, 2, 9, 3]
  decide (Post_prop data n' "exclusive") && decide (Post_prop data n' "inclusive")
) = true := by native_decide

example : (List.range 8).all (fun n =>
  let n' := n + 1
  let data : List Rat := [-3, 10, 0, 5, 2, 8]
  let qInc := benchmark_quantiles data n' "inclusive"
  let qExc := benchmark_quantiles data n' "exclusive"
  qInc.all (fun q => decide (-3 ≤ q ∧ q ≤ 10)) &&
  (if n' ≤ data.length + 1 then qExc.all (fun q => decide (-3 ≤ q ∧ q ≤ 10)) else true)
) = true := by native_decide

example : (List.range 8).all (fun n =>
  let n' := n + 1
  let data : List Rat := [1, 4, 2, 9, 5]
  let qInc := benchmark_quantiles data n' "inclusive"
  let qExc := benchmark_quantiles data n' "exclusive"
  (List.range (n' - 1)).all (fun k =>
    qInc.getD k 0 == inclusiveStep data.mergeSort n' (k + 1) &&
    qExc.getD k 0 == exclusiveStep data.mergeSort n' (k + 1))
) = true := by native_decide

/-! ## 7. Correctness Theorem (`Pre → Post_prop`) -/

/-- Main correctness theorem: whenever `Pre data n method` holds, `Post_prop data n method` holds. -/
theorem benchmark_quantiles_correct (data : List Rat) (n : Nat := 4) (method : String := "exclusive") :
    Pre data n method → Post_prop data n method := by
  intro hPre
  refine ⟨(valid_input_thm data n method hPre).1,
          (valid_input_thm data n method hPre).2,
          length_thm data n method hPre,
          output_sorted_thm data n method hPre,
          sort_idempotent_thm data n method,
          ?_, ?_⟩
  · intro hInc
    subst hInc
    exact ⟨inclusive_formula_thm data n hPre, inclusive_bounds_thm data n hPre⟩
  · intro hExc
    subst hExc
    exact ⟨exclusive_formula_thm data n hPre, exclusive_bounds_thm data n hPre⟩

/-! ## 8. Imperative Implementation (`Id.run do`) -/

/-- Imperative implementation of `quantiles` using `Id.run do` and mutable `result`,
    translating the Python loop structure directly. -/
def quantiles_imp (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : List Rat := Id.run do
  if n < 1 then
    return []
  else
    let s := data.mergeSort
    let ld := s.length
    if ld < 2 then
      return []
    else if method == "inclusive" then
      let m := ld - 1
      let mut result : List Rat := []
      for k in List.range (n - 1) do
        let i := k + 1
        let j := (i * m) / n
        let delta := (i * m) % n
        let interpolated := (s.getD j 0 * ((n - delta : Nat) : Rat) + s.getD (j + 1) 0 * (delta : Rat)) / (n : Rat)
        result := result ++ [interpolated]
      return result
    else if method == "exclusive" then
      let m := ld + 1
      let mut result : List Rat := []
      for k in List.range (n - 1) do
        let i := k + 1
        let j0 := (i * m) / n
        let j := clampNat j0 1 (ld - 1)
        let delta : Int := (i : Int) * (m : Int) - (j : Int) * (n : Int)
        let interpolated := (s.getD (j - 1) 0 * ((n : Int) - delta : Rat) + s.getD j 0 * (delta : Rat)) / (n : Rat)
        result := result ++ [interpolated]
      return result
    else
      return []

/-- Imperative implementation of `benchmark_quantiles`. -/
def benchmark_quantiles_imp (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : List Rat := Id.run do
  if !pre data n method then
    return []
  else
    return quantiles_imp data n method

/-- Imperative implementation of `benchmark_quantiles?`. -/
def benchmark_quantiles?_imp (data : List Rat) (n : Nat := 4) (method : String := "exclusive") : Option (List Rat) := Id.run do
  if !pre data n method then
    return none
  else
    return some (quantiles_imp data n method)

/-- Imperative `Float` implementation of `quantilesFloat`. -/
def quantilesFloat_imp (data : List Float) (n : Nat := 4) (method : String := "exclusive") : List Float := Id.run do
  if n < 1 then
    return []
  else
    let s := data.mergeSort (fun a b => decide (a ≤ b))
    let ld := s.length
    if ld < 2 then
      return []
    else if method == "inclusive" then
      let mut result : List Float := []
      for k in List.range (n - 1) do
        result := result ++ [inclusiveStepFloat s n (k + 1)]
      return result
    else if method == "exclusive" then
      let mut result : List Float := []
      for k in List.range (n - 1) do
        result := result ++ [exclusiveStepFloat s n (k + 1)]
      return result
    else
      return []

/-! ## 9. Imperative Tests -/

example : benchmark_quantiles_imp [1, 2, 3, 4] = [1.25, 2.5, 3.75] := by native_decide
example : (benchmark_quantiles_imp [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10).length = 9 := by native_decide
example : benchmark_quantiles_imp [1, 2, 3, 4, 5] 2 = [3] := by native_decide
example : benchmark_quantiles_imp [1, 2, 3, 4] 4 "inclusive" = [1.75, 2.5, 3.25] := by native_decide
example : benchmark_quantiles_imp [1, 2, 3, 4] 4 "exclusive" = [1.25, 2.5, 3.75] := by native_decide
example : benchmark_quantiles_imp [4, 1, 3, 2] 4 = [1.25, 2.5, 3.75] := by native_decide
example : benchmark_quantiles_imp [1.5, 2.5, 3.5, 4.5] 2 = [3.0] := by native_decide
example : benchmark_quantiles?_imp [1] 4 = none := by native_decide
example : benchmark_quantiles?_imp [1, 2] 0 = none := by native_decide
example : benchmark_quantiles?_imp [1, 2, 3] 4 "invalid" = none := by native_decide

#eval benchmark_quantiles_imp [1, 2, 3, 4]
#eval benchmark_quantiles_imp [1, 2, 3, 4] 4 "inclusive"
#eval benchmark_quantiles?_imp [1] 4
#eval quantilesFloat_imp [1.0, 2.0, 3.0, 4.0] 4 "exclusive"

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

/-- Helper lemma: flattening a mapped list of singletons equals `List.map`. -/
theorem flatten_map_singleton {α β : Type} (xs : List α) (f : α → β) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Equivalence between `quantiles_imp` and `quantiles`. -/
theorem quantiles_imp_eq_quantiles (data : List Rat) (n : Nat) (method : String) :
    quantiles_imp data n method = quantiles data n method := by
  unfold quantiles_imp quantiles inclusiveStep exclusiveStep
  dsimp only
  split_ifs <;> simp [flatten_map_singleton]

/-- Equivalence between `benchmark_quantiles_imp` and `benchmark_quantiles`. -/
theorem benchmark_quantiles_imp_eq (data : List Rat) (n : Nat := 4) (method : String := "exclusive") :
    benchmark_quantiles_imp data n method = benchmark_quantiles data n method := by
  unfold benchmark_quantiles_imp benchmark_quantiles
  rw [quantiles_imp_eq_quantiles]
  split_ifs <;> rfl

/-- Equivalence between `benchmark_quantiles?_imp` and `benchmark_quantiles?`. -/
theorem benchmark_quantiles?_imp_eq (data : List Rat) (n : Nat := 4) (method : String := "exclusive") :
    benchmark_quantiles?_imp data n method = benchmark_quantiles? data n method := by
  unfold benchmark_quantiles?_imp benchmark_quantiles?
  rw [quantiles_imp_eq_quantiles]
  split_ifs <;> rfl

/-- Equivalence between `quantilesFloat_imp` and `quantilesFloat`. -/
theorem quantilesFloat_imp_eq (data : List Float) (n : Nat := 4) (method : String := "exclusive") :
    quantilesFloat_imp data n method = quantilesFloat data n method := by
  unfold quantilesFloat_imp quantilesFloat
  dsimp only
  split_ifs <;> simp [flatten_map_singleton]

end «31_statistics_quantiles»

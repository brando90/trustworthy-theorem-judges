import Mathlib

/-!
# Statistics Quantiles (`31_statistics_quantiles`)

Formalization of Python's `statistics.quantiles` (`benchmark_quantiles`):
dividing a sample or population dataset into `n` continuous intervals with equal probability,
returning the list of `n - 1` linearly interpolated cut points separating the intervals.

Both `"exclusive"` (default, sample data) and `"inclusive"` (population data) methods are
formalized across:
- Exact rational arithmetic (`ℚ` / `Rat`), serving as both an executable layer and exact
  mathematical model for linear interpolation over rational/integer/decimal/float inputs;
- Executable IEEE-754 floating-point (`Float`) for floating-point execution and unit/property tests;
- Real arithmetic (`ℝ` / `Real`) with proven cast correspondence to the `ℚ` model.
-/

namespace «31_statistics_quantiles»

/-!
## 4. Implementation (Functional Definitions)
-/

/-- Executable boolean precondition check matching Python's `pre(data, n, method)`. -/
def pre {α : Type*} (data : List α) (n : ℕ := 4) (method : String := "exclusive") : Bool :=
  decide (data.length ≥ 2) && decide (n ≥ 1) && (method == "inclusive" || method == "exclusive")

/-- Clamp raw index `j_raw` to the closed interval `[1, ld - 1]` for the exclusive method. -/
def exclusiveClamp (ld j_raw : ℕ) : ℕ :=
  if j_raw < 1 then 1 else if j_raw > ld - 1 then ld - 1 else j_raw

/-- Single cut-point interpolation for `"inclusive"` method on a sorted list `s` at step `i`. -/
def inclusiveInterp {α : Type*} [Field α] (s : List α) (n i : ℕ) : α :=
  let ld := s.length
  let m := ld - 1
  let j := (i * m) / n
  let delta := (i * m) % n
  (s.getD j 0 * ((n : α) - (delta : α)) + s.getD (j + 1) 0 * (delta : α)) / (n : α)

/-- Single cut-point interpolation for `"exclusive"` method on a sorted list `s` at step `i`. -/
def exclusiveInterp {α : Type*} [Field α] (s : List α) (n i : ℕ) : α :=
  let ld := s.length
  let m := ld + 1
  let j_raw := (i * m) / n
  let j := exclusiveClamp ld j_raw
  let delta : ℤ := (i * m : ℤ) - (j * n : ℤ)
  (s.getD (j - 1) 0 * ((n : α) - (delta : α)) + s.getD j 0 * (delta : α)) / (n : α)

/-- Core functional implementation of `quantiles` over any ordered field (such as `ℚ` or `ℝ`).
Returns `none` when `n < 1`, `data.length < 2`, or `method` is not `"inclusive"` / `"exclusive"`
(corresponding to raising `StatisticsError` / `ValueError` in Python). -/
def quantilesGeneric {α : Type*} [Field α] [LE α] [DecidableRel (· ≤ · : α → α → Prop)]
    (data : List α) (n : ℕ := 4) (method : String := "exclusive") : Option (List α) :=
  if n < 1 then
    none
  else
    let sortedData := List.insertionSort (· ≤ ·) data
    let ld := sortedData.length
    if ld < 2 then
      none
    else if method == "inclusive" then
      some ((List.range' 1 (n - 1)).map (inclusiveInterp sortedData n))
    else if method == "exclusive" then
      some ((List.range' 1 (n - 1)).map (exclusiveInterp sortedData n))
    else
      none

/-- Functional implementation of `quantiles` over `ℚ`. -/
def quantiles (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") : Option (List ℚ) :=
  quantilesGeneric data n method

/-- Main verified function `benchmark_quantiles` over `ℚ`. -/
def benchmark_quantiles (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") : Option (List ℚ) :=
  if !(pre data n method) then
    none
  else
    quantiles data n method

/-- Mathematical `Real` layer implementation of `quantiles`. -/
noncomputable def quantilesReal (data : List ℝ) (n : ℕ := 4) (method : String := "exclusive") : Option (List ℝ) :=
  letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
  quantilesGeneric data n method

/-- Mathematical `Real` layer implementation of `benchmark_quantiles`. -/
noncomputable def benchmark_quantilesReal (data : List ℝ) (n : ℕ := 4) (method : String := "exclusive") : Option (List ℝ) :=
  if !(pre data n method) then
    none
  else
    quantilesReal data n method

/-- Single cut-point interpolation for `"inclusive"` method over `Float`. -/
def inclusiveInterpFloat (s : List Float) (n i : ℕ) : Float :=
  let ld := s.length
  let m := ld - 1
  let j := (i * m) / n
  let delta := (i * m) % n
  (s.getD j 0.0 * (Float.ofNat n - Float.ofNat delta) + s.getD (j + 1) 0.0 * Float.ofNat delta) / Float.ofNat n

/-- Single cut-point interpolation for `"exclusive"` method over `Float`. -/
def exclusiveInterpFloat (s : List Float) (n i : ℕ) : Float :=
  let ld := s.length
  let m := ld + 1
  let j_raw := (i * m) / n
  let j := exclusiveClamp ld j_raw
  let delta : ℤ := (i * m : ℤ) - (j * n : ℤ)
  (s.getD (j - 1) 0.0 * (Float.ofInt (n : ℤ) - Float.ofInt delta) + s.getD j 0.0 * Float.ofInt delta) / Float.ofNat n

/-- Executable `Float` implementation of `quantiles`. -/
def quantilesFloat (data : List Float) (n : ℕ := 4) (method : String := "exclusive") : Option (List Float) :=
  if n < 1 then
    none
  else
    let sortedData := List.insertionSort (· ≤ ·) data
    let ld := sortedData.length
    if ld < 2 then
      none
    else if method == "inclusive" then
      some ((List.range' 1 (n - 1)).map (inclusiveInterpFloat sortedData n))
    else if method == "exclusive" then
      some ((List.range' 1 (n - 1)).map (exclusiveInterpFloat sortedData n))
    else
      none

/-- Executable `Float` implementation of `benchmark_quantiles`. -/
def benchmark_quantilesFloat (data : List Float) (n : ℕ := 4) (method : String := "exclusive") : Option (List Float) :=
  if !(pre data n method) then
    none
  else
    quantilesFloat data n method

/-- Helper for approximate equality of `Float` lists in unit tests (tolerance `1e-9`). -/
def floatListApprox (actual expected : List Float) (tol : Float := 1e-9) : Bool :=
  actual.length == expected.length &&
    (List.zip actual expected).all (fun (a, b) => Float.abs (a - b) < tol)

/-!
## 5. Unit Tests
-/

-- 1. Basic quartiles (default: n = 4, method = "exclusive")
#eval benchmark_quantiles [1, 2, 3, 4]
#eval benchmark_quantilesFloat [1.0, 2.0, 3.0, 4.0]
example : benchmark_quantiles [1, 2, 3, 4] = some [5/4, 5/2, 15/4] := by native_decide
example : (match benchmark_quantilesFloat [1.0, 2.0, 3.0, 4.0] with
  | some res => res.length == 3 && floatListApprox res [1.25, 2.5, 3.75]
  | none => false) = true := by native_decide

-- 2. Deciles (n = 10)
#eval benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10
example : (benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10).map List.length = some 9 := by native_decide
example : (benchmark_quantilesFloat [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0] 10).map List.length = some 9 := by native_decide

-- 3. Median (n = 2)
#eval benchmark_quantiles [1, 2, 3, 4, 5] 2
example : benchmark_quantiles [1, 2, 3, 4, 5] 2 = some [3] := by native_decide
example : (match benchmark_quantilesFloat [1.0, 2.0, 3.0, 4.0, 5.0] 2 with
  | some res => res.length == 1 && floatListApprox res [3.0]
  | none => false) = true := by native_decide

-- 4. Inclusive method
#eval benchmark_quantiles [1, 2, 3, 4] 4 "inclusive"
#eval benchmark_quantilesFloat [1.0, 2.0, 3.0, 4.0] 4 "inclusive"
example : benchmark_quantiles [1, 2, 3, 4] 4 "inclusive" = some [7/4, 5/2, 13/4] := by native_decide
example : (match benchmark_quantilesFloat [1.0, 2.0, 3.0, 4.0] 4 "inclusive" with
  | some res => res.length == 3 && floatListApprox res [1.75, 2.5, 3.25]
  | none => false) = true := by native_decide

-- 5. Exclusive method (explicit)
#eval benchmark_quantiles [1, 2, 3, 4] 4 "exclusive"
example : benchmark_quantiles [1, 2, 3, 4] 4 "exclusive" = some [5/4, 5/2, 15/4] := by native_decide

-- 6. Larger dataset (1..10, n = 4)
#eval benchmark_quantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4
example : benchmark_quantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4 = some [11/4, 11/2, 33/4] := by native_decide

-- 7. Unsorted input (sorted internally)
#eval benchmark_quantiles [4, 1, 3, 2] 4
example : benchmark_quantiles [4, 1, 3, 2] 4 = some [5/4, 5/2, 15/4] := by native_decide
example : benchmark_quantiles [4, 1, 3, 2] 4 = benchmark_quantiles [1, 2, 3, 4] 4 := by native_decide

-- 8. Fractional / Float data
#eval benchmark_quantiles [3/2, 5/2, 7/2, 9/2] 2
example : benchmark_quantiles [3/2, 5/2, 7/2, 9/2] 2 = some [3] := by native_decide
example : (match benchmark_quantilesFloat [1.5, 2.5, 3.5, 4.5] 2 with
  | some res => res.length == 1 && floatListApprox res [3.0]
  | none => false) = true := by native_decide

-- 9. Error cases (returns `none`, corresponding to raising StatisticsError / ValueError)
#eval benchmark_quantiles [1] 4
#eval benchmark_quantiles [1, 2] 0
#eval benchmark_quantiles [1, 2, 3] 4 "invalid"
example : benchmark_quantiles [1] 4 = none := by native_decide
example : benchmark_quantiles [1, 2] 0 = none := by native_decide
example : benchmark_quantiles [1, 2, 3] 4 "invalid" = none := by native_decide
example : (benchmark_quantilesFloat [1.0] 4).isNone = true := by native_decide
example : (benchmark_quantilesFloat [1.0, 2.0] 0).isNone = true := by native_decide
example : (benchmark_quantilesFloat [1.0, 2.0, 3.0] 4 "invalid").isNone = true := by native_decide

/-!
## 6. Pre-condition Predicate (`Pre`)
-/

/-- Pre-condition for `quantiles` / `benchmark_quantiles`:
`data` has at least 2 elements, `n ≥ 1`, and `method` is `"inclusive"` or `"exclusive"`. -/
def Pre {α : Type*} (data : List α) (n : ℕ := 4) (method : String := "exclusive") : Prop :=
  data.length ≥ 2 ∧ n ≥ 1 ∧ (method = "inclusive" ∨ method = "exclusive")

instance instDecidablePre {α : Type*} (data : List α) (n : ℕ) (method : String) :
    Decidable (Pre data n method) := by
  unfold Pre
  infer_instance

theorem pre_eq_true_iff {α : Type*} (data : List α) (n : ℕ) (method : String) :
    pre data n method = true ↔ Pre data n method := by
  simp only [pre, Pre, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
  exact and_assoc

/-!
## 7. Property Propositions and Theorems
-/

/-! ### Helper Lemmas -/

lemma getD_mono_of_pairwise {α : Type*} [Field α] [LinearOrder α]
    {s : List α} (hs : List.Pairwise (· ≤ ·) s)
    {a b : ℕ} (ha : a < s.length) (hb : b < s.length) (hab : a ≤ b) :
    s.getD a 0 ≤ s.getD b 0 := by
  rw [List.getD_eq_getElem s 0 ha, List.getD_eq_getElem s 0 hb]
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp hs) a b ha hb hlt

lemma getD_eq_of_forall_eq {α : Type*} (s : List α) (c d : α) (h : ∀ x ∈ s, x = c)
    {k : ℕ} (hk : k < s.length) : s.getD k d = c := by
  rw [List.getD_eq_getElem s d hk]
  exact h s[k] (List.getElem_mem hk)

lemma getD_map_of_lt {α β : Type*} (s : List α) (f : α → β) (d₁ : β) (d₂ : α)
    {k : ℕ} (hk : k < s.length) :
    (s.map f).getD k d₁ = f (s.getD k d₂) := by
  rw [List.getD_eq_getElem _ d₁ (by simp [hk]), List.getD_eq_getElem _ d₂ hk, List.getElem_map]

lemma inclusive_j_lt {ld n i : ℕ} (hld : 2 ≤ ld) (hn : 1 ≤ n) (hi : i < n) :
    (i * (ld - 1)) / n + 1 < ld := by
  have hmul : i * (ld - 1) < n * (ld - 1) := Nat.mul_lt_mul_of_pos_right hi (by omega)
  have hdiv : (i * (ld - 1)) / n < ld - 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    linarith
  omega

lemma exclusiveClamp_bounds {ld q : ℕ} (hld : 2 ≤ ld) :
    1 ≤ exclusiveClamp ld q ∧ exclusiveClamp ld q ≤ ld - 1 := by
  unfold exclusiveClamp
  split_ifs <;> omega

lemma exclusiveClamp_mono {ld q₁ q₂ : ℕ} (hld : 2 ≤ ld) (hq : q₁ ≤ q₂) :
    exclusiveClamp ld q₁ ≤ exclusiveClamp ld q₂ := by
  unfold exclusiveClamp
  split_ifs <;> omega

lemma exclusiveClamp_ge_of_lt {ld q : ℕ} (h : exclusiveClamp ld q < ld - 1) :
    q ≤ exclusiveClamp ld q := by
  unfold exclusiveClamp at *
  split_ifs at * <;> omega

lemma exclusiveClamp_le_of_gt {ld q : ℕ} (h : 1 < exclusiveClamp ld q) :
    exclusiveClamp ld q ≤ q := by
  unfold exclusiveClamp at *
  split_ifs at * <;> omega

lemma inclusiveInterp_bounds {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {s : List α} {n i : ℕ}
    (hs : List.Pairwise (· ≤ ·) s) (hld : 2 ≤ s.length) (hn : 1 ≤ n) (hi : i < n) :
    s.getD ((i * (s.length - 1)) / n) 0 ≤ inclusiveInterp s n i ∧
    inclusiveInterp s n i ≤ s.getD ((i * (s.length - 1)) / n + 1) 0 := by
  unfold inclusiveInterp
  dsimp only
  set m := s.length - 1
  set j := (i * m) / n
  set d := (i * m) % n
  have hj1 : j + 1 < s.length := inclusive_j_lt hld hn hi
  have hj : j < s.length := by omega
  have hle : s.getD j 0 ≤ s.getD (j + 1) 0 := getD_mono_of_pairwise hs hj hj1 (by omega)
  have hmod : d < n := Nat.mod_lt _ (by omega)
  have hn_pos : (0 : α) < (n : α) := by positivity
  have hd_nonneg : (0 : α) ≤ (d : α) := Nat.cast_nonneg d
  have hd_le : (d : α) ≤ (n : α) := by exact_mod_cast le_of_lt hmod
  constructor
  · rw [le_div_iff₀ hn_pos]
    nlinarith
  · rw [div_le_iff₀ hn_pos]
    nlinarith

lemma inclusiveInterp_mono {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {s : List α} {n i₁ i₂ : ℕ}
    (hs : List.Pairwise (· ≤ ·) s) (hld : 2 ≤ s.length) (hn : 1 ≤ n)
    (hi₁ : i₁ < n) (hi₂ : i₂ < n) (hle : i₁ ≤ i₂) :
    inclusiveInterp s n i₁ ≤ inclusiveInterp s n i₂ := by
  have hm_le : i₁ * (s.length - 1) ≤ i₂ * (s.length - 1) := Nat.mul_le_mul_right _ hle
  set j₁ := (i₁ * (s.length - 1)) / n
  set j₂ := (i₂ * (s.length - 1)) / n
  have hj_le : j₁ ≤ j₂ := Nat.div_le_div_right hm_le
  rcases Nat.eq_or_lt_of_le hj_le with hjeq | hjlt
  · unfold inclusiveInterp
    dsimp only
    change (s.getD j₁ 0 * ((n : α) - (((i₁ * (s.length - 1)) % n : ℕ) : α)) +
              s.getD (j₁ + 1) 0 * (((i₁ * (s.length - 1)) % n : ℕ) : α)) / (n : α) ≤
           (s.getD j₂ 0 * ((n : α) - (((i₂ * (s.length - 1)) % n : ℕ) : α)) +
              s.getD (j₂ + 1) 0 * (((i₂ * (s.length - 1)) % n : ℕ) : α)) / (n : α)
    rw [← hjeq]
    set d₁ : ℕ := (i₁ * (s.length - 1)) % n
    set d₂ : ℕ := (i₂ * (s.length - 1)) % n
    have hdiv1 : n * j₁ + d₁ = i₁ * (s.length - 1) := Nat.div_add_mod (i₁ * (s.length - 1)) n
    have hdiv2 : n * j₁ + d₂ = i₂ * (s.length - 1) := by
      rw [hjeq]
      exact Nat.div_add_mod (i₂ * (s.length - 1)) n
    have hd_le : d₁ ≤ d₂ := by omega
    have hd_le_q : (d₁ : α) ≤ (d₂ : α) := by exact_mod_cast hd_le
    have hj1 : j₁ + 1 < s.length := inclusive_j_lt hld hn hi₁
    have hs_le : s.getD j₁ 0 ≤ s.getD (j₁ + 1) 0 := getD_mono_of_pairwise hs (by omega) hj1 (by omega)
    have hn_pos : (0 : α) < (n : α) := by positivity
    rw [div_le_div_iff_of_pos_right hn_pos]
    nlinarith
  · have hb1 := (inclusiveInterp_bounds hs hld hn hi₁).2
    have hb2 := (inclusiveInterp_bounds hs hld hn hi₂).1
    have hj1 : j₁ + 1 < s.length := inclusive_j_lt hld hn hi₁
    have hj2 : j₂ < s.length := by
      have h := inclusive_j_lt hld hn hi₂
      change j₂ + 1 < s.length at h
      omega
    have hs_mid : s.getD (j₁ + 1) 0 ≤ s.getD j₂ 0 := getD_mono_of_pairwise hs hj1 hj2 (by omega)
    linarith

lemma exclusiveInterp_mono {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {s : List α} {n i₁ i₂ : ℕ}
    (hs : List.Pairwise (· ≤ ·) s) (hld : 2 ≤ s.length) (hn : 1 ≤ n)
    (hle : i₁ ≤ i₂) :
    exclusiveInterp s n i₁ ≤ exclusiveInterp s n i₂ := by
  unfold exclusiveInterp
  dsimp only
  set ld := s.length
  set m := ld + 1
  have hm_le : i₁ * m ≤ i₂ * m := Nat.mul_le_mul_right m hle
  set q₁ := (i₁ * m) / n
  set q₂ := (i₂ * m) / n
  have hq_le : q₁ ≤ q₂ := Nat.div_le_div_right hm_le
  set j₁ := exclusiveClamp ld q₁
  set j₂ := exclusiveClamp ld q₂
  have hj_le : j₁ ≤ j₂ := exclusiveClamp_mono hld hq_le
  have hb₁ := exclusiveClamp_bounds (q := q₁) hld
  have hb₂ := exclusiveClamp_bounds (q := q₂) hld
  have hn_pos : (0 : α) < (n : α) := by positivity
  rcases Nat.eq_or_lt_of_le hj_le with hjeq | hjlt
  · rw [← hjeq]
    set d₁ : ℤ := (i₁ * m : ℤ) - (j₁ * n : ℤ)
    set d₂ : ℤ := (i₂ * m : ℤ) - (j₁ * n : ℤ)
    have hd_le : d₁ ≤ d₂ := by omega
    have hd_le_q : (d₁ : α) ≤ (d₂ : α) := by exact_mod_cast hd_le
    have hs_le : s.getD (j₁ - 1) 0 ≤ s.getD j₁ 0 :=
      getD_mono_of_pairwise hs (by omega) (by omega) (by omega)
    rw [div_le_div_iff_of_pos_right hn_pos]
    nlinarith
  · have hq₁_le : q₁ ≤ j₁ := exclusiveClamp_ge_of_lt (by omega)
    have hdiv₁ : n * q₁ + (i₁ * m) % n = i₁ * m := Nat.div_add_mod (i₁ * m) n
    have hmod₁ : (i₁ * m) % n < n := Nat.mod_lt _ (by omega)
    have hmul_le₁ : j₁ * n ≥ n * q₁ := by
      rw [Nat.mul_comm j₁ n]
      exact Nat.mul_le_mul_left n hq₁_le
    have him₁_lt : i₁ * m < j₁ * n + n := by omega
    set d₁ : ℤ := (i₁ * m : ℤ) - (j₁ * n : ℤ)
    have hd₁_le : d₁ ≤ (n : ℤ) := by omega
    have hd₁_le_q : (d₁ : α) ≤ (n : α) := by exact_mod_cast hd₁_le
    have hj₂_le_q₂ : j₂ ≤ q₂ := exclusiveClamp_le_of_gt (by omega)
    have hdiv₂ : n * q₂ + (i₂ * m) % n = i₂ * m := Nat.div_add_mod (i₂ * m) n
    have hmul_le₂ : j₂ * n ≤ n * q₂ := by
      rw [Nat.mul_comm j₂ n]
      exact Nat.mul_le_mul_left n hj₂_le_q₂
    have him₂_ge : j₂ * n ≤ i₂ * m := by omega
    set d₂ : ℤ := (i₂ * m : ℤ) - (j₂ * n : ℤ)
    have hd₂_ge : (0 : ℤ) ≤ d₂ := by omega
    have hd₂_ge_q : (0 : α) ≤ (d₂ : α) := by exact_mod_cast hd₂_ge
    have hs₁ : s.getD (j₁ - 1) 0 ≤ s.getD j₁ 0 :=
      getD_mono_of_pairwise hs (by omega) (by omega) (by omega)
    have hs₂ : s.getD (j₂ - 1) 0 ≤ s.getD j₂ 0 :=
      getD_mono_of_pairwise hs (by omega) (by omega) (by omega)
    have hs_mid : s.getD j₁ 0 ≤ s.getD (j₂ - 1) 0 :=
      getD_mono_of_pairwise hs (by omega) (by omega) (by omega)
    have hleft : (s.getD (j₁ - 1) 0 * ((n : α) - (d₁ : α)) + s.getD j₁ 0 * (d₁ : α)) / (n : α) ≤ s.getD j₁ 0 := by
      rw [div_le_iff₀ hn_pos]
      nlinarith
    have hright : s.getD (j₂ - 1) 0 ≤ (s.getD (j₂ - 1) 0 * ((n : α) - (d₂ : α)) + s.getD j₂ 0 * (d₂ : α)) / (n : α) := by
      rw [le_div_iff₀ hn_pos]
      nlinarith
    linarith

lemma pairwise_map_range' {α : Type*} [Preorder α] (f : ℕ → α) (n : ℕ)
    (hf : ∀ i₁ i₂, i₁ < n → i₂ < n → i₁ ≤ i₂ → f i₁ ≤ f i₂) :
    List.Pairwise (· ≤ ·) ((List.range' 1 (n - 1)).map f) := by
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  rw [List.length_map, List.length_range'] at ha hb
  rw [List.getElem_map, List.getElem_map, List.getElem_range', List.getElem_range']
  apply hf <;> omega

lemma quantilesGeneric_eq_benchmark {α : Type*} [Field α] [LE α] [DecidableRel (· ≤ · : α → α → Prop)]
    (data : List α) (n : ℕ) (method : String) :
    (if !(pre data n method) then none else quantilesGeneric data n method) =
    quantilesGeneric data n method := by
  unfold pre quantilesGeneric
  by_cases hn : n < 1
  · have hn' : ¬ (n ≥ 1) := by omega
    simp [hn, hn']
  · have hn' : n ≥ 1 := by omega
    by_cases hld : data.length < 2
    · have hld' : ¬ (data.length ≥ 2) := by omega
      simp [hn, hn', hld, hld']
    · have hld' : data.length ≥ 2 := by omega
      by_cases hm1 : method == "inclusive"
      · simp [hn, hn', hld, hld', hm1]
      · by_cases hm2 : method == "exclusive"
        · simp [hn, hn', hld, hld', hm1, hm2]
        · simp [hn, hn', hld, hld', hm1, hm2]

lemma quantilesGeneric_inclusive_of_pre {α : Type*} [Field α] [LE α] [DecidableRel (· ≤ · : α → α → Prop)]
    (data : List α) (n : ℕ) (hld : 2 ≤ data.length) (hn : 1 ≤ n) :
    quantilesGeneric data n "inclusive" =
      some ((List.range' 1 (n - 1)).map (inclusiveInterp (List.insertionSort (· ≤ ·) data) n)) := by
  unfold quantilesGeneric
  have hn' : ¬ (n < 1) := by omega
  have hld' : ¬ (data.length < 2) := by omega
  simp [hn', hld']

lemma quantilesGeneric_exclusive_of_pre {α : Type*} [Field α] [LE α] [DecidableRel (· ≤ · : α → α → Prop)]
    (data : List α) (n : ℕ) (hld : 2 ≤ data.length) (hn : 1 ≤ n) :
    quantilesGeneric data n "exclusive" =
      some ((List.range' 1 (n - 1)).map (exclusiveInterp (List.insertionSort (· ≤ ·) data) n)) := by
  unfold quantilesGeneric
  have hn' : ¬ (n < 1) := by omega
  have hld' : ¬ (data.length < 2) := by omega
  have hne : ("exclusive" == "inclusive") = false := by decide
  simp [hn', hld', hne]

theorem benchmark_quantiles_eq_quantiles (data : List ℚ) (n : ℕ) (method : String) :
    benchmark_quantiles data n method = quantiles data n method :=
  quantilesGeneric_eq_benchmark data n method

theorem benchmark_quantilesReal_eq_quantilesReal (data : List ℝ) (n : ℕ) (method : String) :
    benchmark_quantilesReal data n method = quantilesReal data n method := by
  letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
  exact quantilesGeneric_eq_benchmark data n method

theorem benchmark_quantilesFloat_eq_quantilesFloat (data : List Float) (n : ℕ) (method : String) :
    benchmark_quantilesFloat data n method = quantilesFloat data n method := by
  unfold benchmark_quantilesFloat pre quantilesFloat
  by_cases hn : n < 1
  · have hn' : ¬ (n ≥ 1) := by omega
    simp [hn, hn']
  · have hn' : n ≥ 1 := by omega
    by_cases hld : data.length < 2
    · have hld' : ¬ (data.length ≥ 2) := by omega
      simp [hn, hn', hld, hld']
    · have hld' : data.length ≥ 2 := by omega
      by_cases hm1 : method == "inclusive"
      · simp [hn, hn', hld, hld', hm1]
      · by_cases hm2 : method == "exclusive"
        · simp [hn, hn', hld, hld', hm1, hm2]
        · simp [hn, hn', hld, hld', hm1, hm2]

/-! ### Property 1: Validity / Error Characterization (`valid_iff_pre_prop`) -/

/-- Property 1: `benchmark_quantiles` succeeds (`isSome`) iff `Pre` holds, and returns `none` otherwise. -/
def valid_iff_pre_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  (benchmark_quantiles data n method).isSome = true ↔ Pre data n method

theorem valid_iff_pre_thm (data : List ℚ) (n : ℕ) (method : String) :
    valid_iff_pre_prop data n method := by
  unfold valid_iff_pre_prop
  rw [benchmark_quantiles_eq_quantiles]
  unfold quantiles quantilesGeneric Pre
  by_cases hn : n < 1
  · simp [hn]
  · by_cases hld : data.length < 2
    · simp [hn, hld]
    · by_cases hm1 : method = "inclusive"
      · subst hm1; simp [hn, hld]; omega
      · by_cases hm2 : method = "exclusive"
        · subst hm2; simp [hn, hld]; omega
        · have hm1' : (method == "inclusive") = false := beq_false_of_ne hm1
          have hm2' : (method == "exclusive") = false := beq_false_of_ne hm2
          simp [hn, hld, hm1, hm2, hm1', hm2']

theorem error_iff_not_pre_thm (data : List ℚ) (n : ℕ) (method : String) :
    benchmark_quantiles data n method = none ↔ ¬ Pre data n method := by
  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, ← Bool.not_eq_true]
  exact not_iff_not.mpr (valid_iff_pre_thm data n method)

/-! ### Property 2: Output Length (`length_prop`) -/

/-- Property 2: Under `Pre data n method`, `benchmark_quantiles` returns a list of length `n - 1`. -/
def length_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∃ res, benchmark_quantiles data n method = some res ∧ res.length = n - 1

theorem length_thm (data : List ℚ) (n : ℕ) (method : String) (hpre : Pre data n method) :
    length_prop data n method := by
  unfold length_prop
  rw [benchmark_quantiles_eq_quantiles]
  unfold quantiles
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    rw [quantilesGeneric_inclusive_of_pre data n hld hn]
    exact ⟨_, rfl, by simp [List.length_map, List.length_range']⟩
  · subst hm
    rw [quantilesGeneric_exclusive_of_pre data n hld hn]
    exact ⟨_, rfl, by simp [List.length_map, List.length_range']⟩

/-! ### Property 3: Permutation and Sorting Invariance (`perm_invariant_thm` / `sorted_idempotent_prop`) -/

/-- Property 3: Sorting `data` before calling `benchmark_quantiles` leaves the output unchanged. -/
def sorted_idempotent_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  benchmark_quantiles (List.insertionSort (· ≤ ·) data) n method = benchmark_quantiles data n method

theorem perm_invariant_thm {data₁ data₂ : List ℚ} (hperm : List.Perm data₁ data₂) (n : ℕ) (method : String) :
    benchmark_quantiles data₁ n method = benchmark_quantiles data₂ n method := by
  rw [benchmark_quantiles_eq_quantiles, benchmark_quantiles_eq_quantiles]
  unfold quantiles quantilesGeneric
  have hsort_eq : List.insertionSort (· ≤ ·) data₁ = List.insertionSort (· ≤ ·) data₂ := by
    apply List.Perm.eq_of_sorted (fun a b _ _ hab hba => le_antisymm hab hba)
    · exact List.sorted_insertionSort (· ≤ ·) data₁
    · exact List.sorted_insertionSort (· ≤ ·) data₂
    · exact (List.perm_insertionSort (· ≤ ·) data₁).trans (hperm.trans (List.perm_insertionSort (· ≤ ·) data₂).symm)
  simp [hsort_eq]

theorem sorted_idempotent_thm (data : List ℚ) (n : ℕ) (method : String) :
    sorted_idempotent_prop data n method :=
  perm_invariant_thm (List.perm_insertionSort (· ≤ ·) data) n method

/-! ### Property 4: Monotonicity / Sortedness of Cut Points (`monotone_prop`) -/

/-- Property 4: Under `Pre data n method`, the returned cut points are sorted in non-decreasing order. -/
def monotone_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∃ res, benchmark_quantiles data n method = some res ∧ List.Pairwise (· ≤ ·) res

theorem monotone_thm (data : List ℚ) (n : ℕ) (method : String) (hpre : Pre data n method) :
    monotone_prop data n method := by
  unfold monotone_prop
  rw [benchmark_quantiles_eq_quantiles]
  unfold quantiles
  set s := List.insertionSort (· ≤ ·) data
  have hs_sort : List.Pairwise (· ≤ ·) s := List.sorted_insertionSort (· ≤ ·) data
  have hs_len : s.length = data.length := List.length_insertionSort (· ≤ ·) data
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    rw [quantilesGeneric_inclusive_of_pre data n hld hn]
    refine ⟨_, rfl, ?_⟩
    apply pairwise_map_range' (inclusiveInterp s n) n
    intro i₁ i₂ hi₁ hi₂ hle
    exact inclusiveInterp_mono hs_sort (by omega) hn hi₁ hi₂ hle
  · subst hm
    rw [quantilesGeneric_exclusive_of_pre data n hld hn]
    refine ⟨_, rfl, ?_⟩
    apply pairwise_map_range' (exclusiveInterp s n) n
    intro i₁ i₂ _ _ hle
    exact exclusiveInterp_mono hs_sort (by omega) hn hle

/-! ### Property 5: Population Bounds for Inclusive Method (`inclusive_bounds_prop`) -/

/-- Property 5: For the `"inclusive"` method, every cut point lies between the minimum and maximum
of the sorted dataset (`s[0] ≤ q ≤ s[ld - 1]`). -/
def inclusive_bounds_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  method = "inclusive" →
    ∃ res, benchmark_quantiles data n method = some res ∧
      let s := List.insertionSort (· ≤ ·) data
      ∀ q ∈ res, s.getD 0 0 ≤ q ∧ q ≤ s.getD (s.length - 1) 0

theorem inclusive_bounds_thm (data : List ℚ) (n : ℕ) (method : String) (hpre : Pre data n method) :
    inclusive_bounds_prop data n method := by
  intro hm
  subst hm
  rw [benchmark_quantiles_eq_quantiles]
  unfold quantiles
  rcases hpre with ⟨hld, hn, _⟩
  rw [quantilesGeneric_inclusive_of_pre data n hld hn]
  set s := List.insertionSort (· ≤ ·) data
  have hs_sort : List.Pairwise (· ≤ ·) s := List.sorted_insertionSort (· ≤ ·) data
  have hs_len : s.length = data.length := List.length_insertionSort (· ≤ ·) data
  refine ⟨_, rfl, ?_⟩
  dsimp only
  intro q hq
  rw [List.mem_map] at hq
  rcases hq with ⟨i, hi_mem, rfl⟩
  rw [List.mem_range'] at hi_mem
  rcases hi_mem with ⟨k, hk, rfl⟩
  have hi_lt : 1 + 1 * k < n := by omega
  have hb := inclusiveInterp_bounds hs_sort (by omega) hn hi_lt
  set j := ((1 + 1 * k) * (s.length - 1)) / n
  have hj1 : j + 1 < s.length := inclusive_j_lt (by omega) hn hi_lt
  have hj : j < s.length := Nat.lt_of_succ_lt hj1
  have hmin : s.getD 0 0 ≤ s.getD j 0 :=
    getD_mono_of_pairwise hs_sort (by omega) hj (Nat.zero_le j)
  have hmax : s.getD (j + 1) 0 ≤ s.getD (s.length - 1) 0 :=
    getD_mono_of_pairwise hs_sort hj1 (by omega) (Nat.le_sub_one_of_lt hj1)
  exact ⟨le_trans hmin hb.1, le_trans hb.2 hmax⟩

/-! ### Property 6: Pointwise Cut-Point Specification (`pointwise_prop`) -/

/-- Property 6: Under `Pre data n method`, every cut point at index `k < n - 1` (for interval `i = k + 1`)
equals `inclusiveInterp` when `method = "inclusive"` and `exclusiveInterp` when `method = "exclusive"`. -/
def pointwise_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∃ res, benchmark_quantiles data n method = some res ∧
    res.length = n - 1 ∧
    let s := List.insertionSort (· ≤ ·) data
    ∀ (k : ℕ) (hk : k < res.length),
      res[k] = if method = "inclusive" then inclusiveInterp s n (k + 1) else exclusiveInterp s n (k + 1)

theorem pointwise_thm (data : List ℚ) (n : ℕ) (method : String) (hpre : Pre data n method) :
    pointwise_prop data n method := by
  unfold pointwise_prop
  rw [benchmark_quantiles_eq_quantiles]
  unfold quantiles
  set s := List.insertionSort (· ≤ ·) data
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    rw [quantilesGeneric_inclusive_of_pre data n hld hn]
    refine ⟨_, rfl, by simp [List.length_map, List.length_range'], ?_⟩
    dsimp only
    intro k hk
    simp only [↓reduceIte, List.getElem_map, List.getElem_range']
    congr 1
    omega
  · subst hm
    rw [quantilesGeneric_exclusive_of_pre data n hld hn]
    refine ⟨_, rfl, by simp [List.length_map, List.length_range'], ?_⟩
    dsimp only
    intro k hk
    have hne : ("exclusive" = "inclusive") ↔ False := by decide
    simp only [hne, ↓reduceIte, List.getElem_map, List.getElem_range']
    congr 1
    omega

/-! ### Property 7: Constant Dataset Preservation (`constant_data_prop`) -/

lemma inclusiveInterp_const (s : List ℚ) (c : ℚ) (n i : ℕ)
    (hs : ∀ x ∈ s, x = c) (hld : 2 ≤ s.length) (hn : 1 ≤ n) (hi : i < n) :
    inclusiveInterp s n i = c := by
  unfold inclusiveInterp
  dsimp only
  have hj1 : (i * (s.length - 1)) / n + 1 < s.length := inclusive_j_lt hld hn hi
  have hj : (i * (s.length - 1)) / n < s.length := by omega
  rw [getD_eq_of_forall_eq s c 0 hs hj, getD_eq_of_forall_eq s c 0 hs hj1]
  have hn_ne : (n : ℚ) ≠ 0 := by positivity
  field_simp [hn_ne]
  ring

lemma exclusiveInterp_const (s : List ℚ) (c : ℚ) (n i : ℕ)
    (hs : ∀ x ∈ s, x = c) (hld : 2 ≤ s.length) (hn : 1 ≤ n) :
    exclusiveInterp s n i = c := by
  unfold exclusiveInterp
  dsimp only
  have hb := exclusiveClamp_bounds (q := (i * (s.length + 1)) / n) hld
  have hj_prev : exclusiveClamp s.length ((i * (s.length + 1)) / n) - 1 < s.length := by omega
  have hj_curr : exclusiveClamp s.length ((i * (s.length + 1)) / n) < s.length := by omega
  rw [getD_eq_of_forall_eq s c 0 hs hj_prev, getD_eq_of_forall_eq s c 0 hs hj_curr]
  have hn_ne : (n : ℚ) ≠ 0 := by positivity
  field_simp [hn_ne]
  ring

/-- Property 7: If all elements in `data` equal `c`, every quantile cut point equals `c`. -/
def constant_data_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∀ c : ℚ, (∀ x ∈ data, x = c) →
    benchmark_quantiles data n method = some (List.replicate (n - 1) c)

theorem constant_data_thm (data : List ℚ) (n : ℕ) (method : String) (hpre : Pre data n method) :
    constant_data_prop data n method := by
  intro c hc
  rw [benchmark_quantiles_eq_quantiles]
  unfold quantiles
  set s := List.insertionSort (· ≤ ·) data
  have hs_len : s.length = data.length := List.length_insertionSort (· ≤ ·) data
  have hs_all : ∀ x ∈ s, x = c := by
    intro x hx
    exact hc x ((List.perm_insertionSort (· ≤ ·) data).subset hx)
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    rw [quantilesGeneric_inclusive_of_pre data n hld hn, Option.some.injEq]
    apply List.ext_getElem
    · simp [List.length_map, List.length_range', List.length_replicate]
    · intro k hk1 hk2
      rw [List.getElem_map, List.getElem_range', List.getElem_replicate]
      rw [List.length_map, List.length_range'] at hk1
      exact inclusiveInterp_const s c n (1 + 1 * k) hs_all (by omega) hn (by omega)
  · subst hm
    rw [quantilesGeneric_exclusive_of_pre data n hld hn, Option.some.injEq]
    apply List.ext_getElem
    · simp [List.length_map, List.length_range', List.length_replicate]
    · intro k hk1 hk2
      rw [List.getElem_map, List.getElem_range', List.getElem_replicate]
      exact exclusiveInterp_const s c n (1 + 1 * k) hs_all (by omega) hn

/-! ### Property 8: Translation / Shift Equivariance (`shift_equivariant_prop`) -/

lemma orderedInsert_map_add (c x : ℚ) (l : List ℚ) :
    List.orderedInsert (· ≤ ·) (x + c) (l.map (· + c)) =
    (List.orderedInsert (· ≤ ·) x l).map (· + c) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.orderedInsert]
    have hiff : (x + c ≤ y + c) ↔ (x ≤ y) := add_le_add_iff_right c
    by_cases hxy : x ≤ y
    · have hxyc : x + c ≤ y + c := hiff.mpr hxy
      simp [hxy, hxyc]
    · have hxyc : ¬ (x + c ≤ y + c) := mt hiff.mp hxy
      simp [hxy, hxyc, ih]

lemma insertionSort_map_add (c : ℚ) (l : List ℚ) :
    List.insertionSort (· ≤ ·) (l.map (· + c)) =
    (List.insertionSort (· ≤ ·) l).map (· + c) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.insertionSort, ih, orderedInsert_map_add]

lemma inclusiveInterp_map_add (s : List ℚ) (c : ℚ) (n i : ℕ)
    (hld : 2 ≤ s.length) (hn : 1 ≤ n) (hi : i < n) :
    inclusiveInterp (s.map (· + c)) n i = inclusiveInterp s n i + c := by
  unfold inclusiveInterp
  simp only [List.length_map]
  have hj1 : (i * (s.length - 1)) / n + 1 < s.length := inclusive_j_lt hld hn hi
  have hj : (i * (s.length - 1)) / n < s.length := by omega
  rw [getD_map_of_lt s (· + c) 0 0 hj, getD_map_of_lt s (· + c) 0 0 hj1]
  have hn_ne : (n : ℚ) ≠ 0 := by positivity
  field_simp [hn_ne]
  ring

lemma exclusiveInterp_map_add (s : List ℚ) (c : ℚ) (n i : ℕ)
    (hld : 2 ≤ s.length) (hn : 1 ≤ n) :
    exclusiveInterp (s.map (· + c)) n i = exclusiveInterp s n i + c := by
  unfold exclusiveInterp
  simp only [List.length_map]
  have hb := exclusiveClamp_bounds (q := (i * (s.length + 1)) / n) hld
  have hj_prev : exclusiveClamp s.length ((i * (s.length + 1)) / n) - 1 < s.length := by omega
  have hj_curr : exclusiveClamp s.length ((i * (s.length + 1)) / n) < s.length := by omega
  rw [getD_map_of_lt s (· + c) 0 0 hj_prev, getD_map_of_lt s (· + c) 0 0 hj_curr]
  have hn_ne : (n : ℚ) ≠ 0 := by positivity
  field_simp [hn_ne]
  ring

/-- Property 8: Shifting every data point by `+ c` shifts every output quantile cut point by `+ c`. -/
def shift_equivariant_prop (data : List ℚ) (n : ℕ) (method : String) (c : ℚ) : Prop :=
  benchmark_quantiles (data.map (· + c)) n method =
    (benchmark_quantiles data n method).map (List.map (· + c))

theorem shift_equivariant_thm (data : List ℚ) (n : ℕ) (method : String) (c : ℚ) (hpre : Pre data n method) :
    shift_equivariant_prop data n method c := by
  unfold shift_equivariant_prop
  rw [benchmark_quantiles_eq_quantiles, benchmark_quantiles_eq_quantiles]
  unfold quantiles
  set s := List.insertionSort (· ≤ ·) data
  have hs_len : s.length = data.length := List.length_insertionSort (· ≤ ·) data
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    have hlen_map : 2 ≤ (data.map (· + c)).length := by simp; omega
    rw [quantilesGeneric_inclusive_of_pre (data.map (· + c)) n hlen_map hn,
        quantilesGeneric_inclusive_of_pre data n hld hn,
        insertionSort_map_add, Option.map_some, Option.some.injEq, List.map_map]
    apply List.ext_getElem
    · simp [List.length_map, List.length_range']
    · intro k hk1 hk2
      rw [List.getElem_map, List.getElem_map, List.getElem_range']
      rw [List.length_map, List.length_range'] at hk1
      dsimp only [Function.comp_apply]
      exact inclusiveInterp_map_add s c n (1 + 1 * k) (by omega) hn (by omega)
  · subst hm
    have hlen_map : 2 ≤ (data.map (· + c)).length := by simp; omega
    rw [quantilesGeneric_exclusive_of_pre (data.map (· + c)) n hlen_map hn,
        quantilesGeneric_exclusive_of_pre data n hld hn,
        insertionSort_map_add, Option.map_some, Option.some.injEq, List.map_map]
    apply List.ext_getElem
    · simp [List.length_map, List.length_range']
    · intro k hk1 hk2
      rw [List.getElem_map, List.getElem_map, List.getElem_range']
      dsimp only [Function.comp_apply]
      exact exclusiveInterp_map_add s c n (1 + 1 * k) (by omega) hn

/-! ### Correspondence with `Real` and `Float` Layers -/

lemma orderedInsert_map_ratCast (x : ℚ) (l : List ℚ) :
    letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
    List.orderedInsert (· ≤ ·) (x : ℝ) (l.map (Rat.cast : ℚ → ℝ)) =
    (List.orderedInsert (· ≤ ·) x l).map (Rat.cast : ℚ → ℝ) := by
  letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.orderedInsert]
    by_cases hxy : x ≤ y
    · have hxyr : (x : ℝ) ≤ (y : ℝ) := Rat.cast_le.mpr hxy
      simp [hxy, hxyr]
    · have hxyr : ¬ ((x : ℝ) ≤ (y : ℝ)) := mt Rat.cast_le.mp hxy
      simp [hxy, hxyr, ih]

lemma insertionSort_map_ratCast (l : List ℚ) :
    letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
    List.insertionSort (· ≤ ·) (l.map (Rat.cast : ℚ → ℝ)) =
    (List.insertionSort (· ≤ ·) l).map (Rat.cast : ℚ → ℝ) := by
  letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.insertionSort, ih, orderedInsert_map_ratCast]

lemma inclusiveInterp_map_ratCast (s : List ℚ) (n i : ℕ)
    (hld : 2 ≤ s.length) (hn : 1 ≤ n) (hi : i < n) :
    inclusiveInterp (s.map (Rat.cast : ℚ → ℝ)) n i = Rat.cast (inclusiveInterp s n i) := by
  unfold inclusiveInterp
  simp only [List.length_map]
  have hj1 : (i * (s.length - 1)) / n + 1 < s.length := inclusive_j_lt hld hn hi
  have hj : (i * (s.length - 1)) / n < s.length := by omega
  rw [getD_map_of_lt s (Rat.cast : ℚ → ℝ) 0 0 hj, getD_map_of_lt s (Rat.cast : ℚ → ℝ) 0 0 hj1]
  push_cast
  rfl

lemma exclusiveInterp_map_ratCast (s : List ℚ) (n i : ℕ)
    (hld : 2 ≤ s.length) :
    exclusiveInterp (s.map (Rat.cast : ℚ → ℝ)) n i = Rat.cast (exclusiveInterp s n i) := by
  unfold exclusiveInterp
  simp only [List.length_map]
  have hb := exclusiveClamp_bounds (q := (i * (s.length + 1)) / n) hld
  have hj_prev : exclusiveClamp s.length ((i * (s.length + 1)) / n) - 1 < s.length := by omega
  have hj_curr : exclusiveClamp s.length ((i * (s.length + 1)) / n) < s.length := by omega
  rw [getD_map_of_lt s (Rat.cast : ℚ → ℝ) 0 0 hj_prev, getD_map_of_lt s (Rat.cast : ℚ → ℝ) 0 0 hj_curr]
  push_cast
  rfl

/-- Exact correspondence theorem between the `ℚ` (`Rat`) layer and the `ℝ` (`Real`) layer. -/
theorem benchmark_quantilesReal_ratCast_thm (data : List ℚ) (n : ℕ) (method : String) :
    benchmark_quantilesReal (data.map (Rat.cast : ℚ → ℝ)) n method =
      (benchmark_quantiles data n method).map (List.map (Rat.cast : ℚ → ℝ)) := by
  letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
  rw [benchmark_quantilesReal_eq_quantilesReal, benchmark_quantiles_eq_quantiles]
  unfold quantilesReal quantiles quantilesGeneric
  rw [insertionSort_map_ratCast]
  set s := List.insertionSort (· ≤ ·) data
  have hs_len : s.length = data.length := List.length_insertionSort (· ≤ ·) data
  by_cases hn : n < 1
  · simp [hn]
  · by_cases hld : data.length < 2
    · simp [s, hn, hld]
    · by_cases hm1 : method == "inclusive"
      · simp only [s, List.length_map, List.length_insertionSort, hn, ↓reduceIte, hld, hm1,
          Option.map_some, Option.some.injEq, List.map_map]
        apply List.ext_getElem
        · simp [List.length_map, List.length_range']
        · intro k hk1 hk2
          rw [List.getElem_map, List.getElem_map, List.getElem_range']
          rw [List.length_map, List.length_range'] at hk1
          dsimp only [Function.comp_apply]
          exact inclusiveInterp_map_ratCast s n (1 + 1 * k) (by omega) (by omega) (by omega)
      · by_cases hm2 : method == "exclusive"
        · simp only [s, List.length_map, List.length_insertionSort, hn, ↓reduceIte, hld, hm1,
            Bool.false_eq_true, hm2, Option.map_some, Option.some.injEq, List.map_map]
          apply List.ext_getElem
          · simp [List.length_map, List.length_range']
          · intro k hk1 hk2
            rw [List.getElem_map, List.getElem_map, List.getElem_range']
            dsimp only [Function.comp_apply]
            exact exclusiveInterp_map_ratCast s n (1 + 1 * k) (by omega)
        · simp [s, hn, hld, hm1, hm2]

/-- Real layer monotonicity and length theorem. -/
theorem benchmark_quantilesReal_spec_thm (data : List ℝ) (n : ℕ) (method : String) (hpre : Pre data n method) :
    ∃ res, benchmark_quantilesReal data n method = some res ∧
      res.length = n - 1 ∧ List.Pairwise (· ≤ ·) res := by
  letI : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := Classical.decRel _
  rw [benchmark_quantilesReal_eq_quantilesReal]
  unfold quantilesReal
  set s := List.insertionSort (· ≤ ·) data
  have hs_sort : List.Pairwise (· ≤ ·) s := List.sorted_insertionSort (· ≤ ·) data
  have hs_len : s.length = data.length := List.length_insertionSort (· ≤ ·) data
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    rw [quantilesGeneric_inclusive_of_pre data n hld hn]
    refine ⟨_, rfl, by simp [List.length_map, List.length_range'], ?_⟩
    apply pairwise_map_range' (inclusiveInterp s n) n
    intro i₁ i₂ hi₁ hi₂ hle
    exact inclusiveInterp_mono hs_sort (by omega) hn hi₁ hi₂ hle
  · subst hm
    rw [quantilesGeneric_exclusive_of_pre data n hld hn]
    refine ⟨_, rfl, by simp [List.length_map, List.length_range'], ?_⟩
    apply pairwise_map_range' (exclusiveInterp s n) n
    intro i₁ i₂ _ _ hle
    exact exclusiveInterp_mono hs_sort (by omega) hn hle

/-- Float layer structural theorem: validity and output length. -/
def float_length_prop (data : List Float) (n : ℕ) (method : String) : Prop :=
  ∃ res, benchmark_quantilesFloat data n method = some res ∧ res.length = n - 1

theorem float_length_thm (data : List Float) (n : ℕ) (method : String) (hpre : Pre data n method) :
    float_length_prop data n method := by
  unfold float_length_prop
  rw [benchmark_quantilesFloat_eq_quantilesFloat]
  unfold quantilesFloat
  rcases hpre with ⟨hld, hn, hm | hm⟩
  · subst hm
    have hn' : ¬ (n < 1) := by omega
    have hld' : ¬ (data.length < 2) := by omega
    refine ⟨(List.range' 1 (n - 1)).map (inclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n), ?_, ?_⟩
    · simp [hn', hld']
    · simp [List.length_map, List.length_range']
  · subst hm
    have hn' : ¬ (n < 1) := by omega
    have hld' : ¬ (data.length < 2) := by omega
    have hne : ("exclusive" == "inclusive") = false := by decide
    refine ⟨(List.range' 1 (n - 1)).map (exclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n), ?_, ?_⟩
    · simp [hn', hld', hne]
    · simp [List.length_map, List.length_range']

/-!
## 8. Post-condition (`Post_prop`)
-/

/-- Post-condition conjunction of all verified properties for `benchmark_quantiles`. -/
def Post_prop (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") : Prop :=
  valid_iff_pre_prop data n method ∧
  length_prop data n method ∧
  sorted_idempotent_prop data n method ∧
  monotone_prop data n method ∧
  inclusive_bounds_prop data n method ∧
  pointwise_prop data n method ∧
  constant_data_prop data n method

/-!
## 9. Property-Based Tests (PBTs)
-/

/-- Executable boolean checker for `valid_iff_pre_prop`. -/
def check_valid_iff_pre (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  (benchmark_quantiles data n method).isSome == pre data n method

/-- Executable boolean checker for `length_prop`. -/
def check_length (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  match benchmark_quantiles data n method with
  | some res => res.length == n - 1
  | none => false

/-- Executable boolean checker for `sorted_idempotent_prop`. -/
def check_sorted_idempotent (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  benchmark_quantiles (List.insertionSort (· ≤ ·) data) n method == benchmark_quantiles data n method

/-- Executable boolean helper checking if a list of `ℚ` is non-decreasing. -/
def isSortedRat : List ℚ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && isSortedRat (b :: rest)

/-- Executable boolean checker for `monotone_prop`. -/
def check_monotone (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  match benchmark_quantiles data n method with
  | some res => isSortedRat res
  | none => false

/-- Executable boolean checker for `inclusive_bounds_prop`. -/
def check_inclusive_bounds (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  if method == "inclusive" then
    match benchmark_quantiles data n method with
    | some res =>
      let s := List.insertionSort (· ≤ ·) data
      res.all (fun q => decide (s.getD 0 0 ≤ q ∧ q ≤ s.getD (s.length - 1) 0))
    | none => false
  else
    true

/-- Executable boolean checker for `pointwise_prop`. -/
def check_pointwise (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  match benchmark_quantiles data n method with
  | some res =>
    let s := List.insertionSort (· ≤ ·) data
    res.length == n - 1 &&
      (List.range res.length).all (fun k =>
        let expected := if method == "inclusive" then inclusiveInterp s n (k + 1) else exclusiveInterp s n (k + 1)
        res.getD k 0 == expected)
  | none => false

/-- Executable boolean checker for `constant_data_prop` on constant lists. -/
def check_constant_data (c : ℚ) (len : ℕ) (n : ℕ) (method : String) : Bool :=
  let data := List.replicate len c
  if pre data n method then
    benchmark_quantiles data n method == some (List.replicate (n - 1) c)
  else
    true

/-- Executable boolean checker for `shift_equivariant_prop`. -/
def check_shift_equivariant (data : List ℚ) (n : ℕ) (method : String) (c : ℚ) : Bool :=
  benchmark_quantiles (data.map (· + c)) n method ==
    (benchmark_quantiles data n method).map (List.map (· + c))

/-- Executable boolean checker for `float_length_prop`. -/
def check_float_length (data : List Float) (n : ℕ) (method : String) : Bool :=
  match benchmark_quantilesFloat data n method with
  | some res => res.length == n - 1
  | none => false

/-- Executable boolean checker for the full post-condition `Post_prop`. -/
def check_post (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  check_valid_iff_pre data n method &&
  check_length data n method &&
  check_sorted_idempotent data n method &&
  check_monotone data n method &&
  check_inclusive_bounds data n method &&
  check_pointwise data n method

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ (data : List ℚ) (n : ℕ) (b : Bool),
  let method := if b then "inclusive" else "exclusive"
  check_valid_iff_pre data n method = true)

#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  let data := x :: y :: rest
  let n := k % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_length data n method = true)

#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  let data := x :: y :: rest
  let n := k % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_sorted_idempotent data n method = true)

#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  let data := x :: y :: rest
  let n := k % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_monotone data n method = true)

#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ),
  let data := x :: y :: rest
  let n := k % 12 + 1
  check_inclusive_bounds data n "inclusive" = true)

#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  let data := x :: y :: rest
  let n := k % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_pointwise data n method = true)

#eval Plausible.Testable.check (∀ (c : ℚ) (k1 k2 : ℕ) (b : Bool),
  let len := k1 % 10 + 2
  let n := k2 % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_constant_data c len n method = true)

#eval Plausible.Testable.check (∀ (x y c : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  let data := x :: y :: rest
  let n := k % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_shift_equivariant data n method c = true)

#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  let data := x :: y :: rest
  let n := k % 12 + 1
  let method := if b then "inclusive" else "exclusive"
  check_post data n method = true)

-- Bounded exhaustive PBTs via `native_decide`
def sampleDatasets : List (List ℚ) :=
  [ [1, 2], [2, 1], [1, 2, 3, 4], [4, 1, 3, 2],
    [-5, 0, 5, 10, 15], [3/2, 5/2, 7/2, 9/2],
    [10, 10, 10, 10], [-3, -1, -1, 0, 2, 8, 20] ]

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_valid_iff_pre d n m)))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_length d n m)))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_sorted_idempotent d n m)))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_monotone d n m)))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n => check_inclusive_bounds d n "inclusive"))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_pointwise d n m)))) = true := by native_decide

example : ((List.range' 2 5).all (fun len =>
  (List.range' 1 6).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_constant_data (7/3) len n m)))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 6).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_shift_equivariant d n m (5/2))))) = true := by native_decide

example : ((List.range' 1 8).all (fun n =>
  ["exclusive", "inclusive"].all (fun m =>
    check_float_length [1.0, 2.0, 3.0, 4.0, 5.0] n m))) = true := by native_decide

example : (sampleDatasets.all (fun d =>
  (List.range' 1 8).all (fun n =>
    ["exclusive", "inclusive"].all (fun m => check_post d n m)))) = true := by native_decide

-- Note: `benchmark_quantilesReal_spec_thm` and `benchmark_quantilesReal_ratCast_thm` are stated over `ℝ` (`Real`),
-- whose comparisons are noncomputable; their executable counterparts are tested above via `check_post` over `ℚ` and `check_float_length` over `Float`.

/-!
## 10. Correctness Theorem (`Pre -> Post`)
-/

/-- Main correctness theorem: whenever `Pre data n method` holds, `Post_prop data n method` holds. -/
theorem benchmark_quantiles_correct (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive")
    (hpre : Pre data n method) :
    Post_prop data n method :=
  ⟨valid_iff_pre_thm data n method,
   length_thm data n method hpre,
   sorted_idempotent_thm data n method,
   monotone_thm data n method hpre,
   inclusive_bounds_thm data n method hpre,
   pointwise_thm data n method hpre,
   constant_data_thm data n method hpre⟩

/-!
## 11. Imperative Implementation
-/

/-- Imperative implementation of `quantiles` over `ℚ` using `Id.run do` and mutable accumulator `result`. -/
def quantiles_imp (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") : Option (List ℚ) := Id.run do
  if n < 1 then
    return none
  let sortedData := List.insertionSort (· ≤ ·) data
  let ld := sortedData.length
  if ld < 2 then
    return none
  if method == "inclusive" then
    let m := ld - 1
    let mut result : List ℚ := []
    for i in List.range' 1 (n - 1) do
      let j := (i * m) / n
      let delta := (i * m) % n
      let interpolated := (sortedData.getD j 0 * ((n : ℚ) - (delta : ℚ)) + sortedData.getD (j + 1) 0 * (delta : ℚ)) / (n : ℚ)
      result := result ++ [interpolated]
    return some result
  else if method == "exclusive" then
    let m := ld + 1
    let mut result : List ℚ := []
    for i in List.range' 1 (n - 1) do
      let j_raw := (i * m) / n
      let j := exclusiveClamp ld j_raw
      let delta : ℤ := (i * m : ℤ) - (j * n : ℤ)
      let interpolated := (sortedData.getD (j - 1) 0 * ((n : ℚ) - (delta : ℚ)) + sortedData.getD j 0 * (delta : ℚ)) / (n : ℚ)
      result := result ++ [interpolated]
    return some result
  else
    return none

/-- Imperative implementation of `benchmark_quantiles` over `ℚ`. -/
def benchmark_quantiles_imp (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") : Option (List ℚ) := Id.run do
  if !(pre data n method) then
    return none
  return (quantiles_imp data n method)

/-- Imperative implementation of `quantilesFloat` over `Float` using `Id.run do` and mutable state. -/
def quantilesFloat_imp (data : List Float) (n : ℕ := 4) (method : String := "exclusive") : Option (List Float) := Id.run do
  if n < 1 then
    return none
  let sortedData := List.insertionSort (· ≤ ·) data
  let ld := sortedData.length
  if ld < 2 then
    return none
  if method == "inclusive" then
    let m := ld - 1
    let mut result : List Float := []
    for i in List.range' 1 (n - 1) do
      let j := (i * m) / n
      let delta := (i * m) % n
      let interpolated := (sortedData.getD j 0.0 * (Float.ofNat n - Float.ofNat delta) + sortedData.getD (j + 1) 0.0 * Float.ofNat delta) / Float.ofNat n
      result := result ++ [interpolated]
    return some result
  else if method == "exclusive" then
    let m := ld + 1
    let mut result : List Float := []
    for i in List.range' 1 (n - 1) do
      let j_raw := (i * m) / n
      let j := exclusiveClamp ld j_raw
      let delta : ℤ := (i * m : ℤ) - (j * n : ℤ)
      let interpolated := (sortedData.getD (j - 1) 0.0 * (Float.ofInt (n : ℤ) - Float.ofInt delta) + sortedData.getD j 0.0 * Float.ofInt delta) / Float.ofNat n
      result := result ++ [interpolated]
    return some result
  else
    return none

/-- Imperative implementation of `benchmark_quantilesFloat` over `Float`. -/
def benchmark_quantilesFloat_imp (data : List Float) (n : ℕ := 4) (method : String := "exclusive") : Option (List Float) := Id.run do
  if !(pre data n method) then
    return none
  return (quantilesFloat_imp data n method)

/-!
## 12. Imperative Tests
-/

#eval benchmark_quantiles_imp [1, 2, 3, 4]
#eval benchmark_quantiles_imp [1, 2, 3, 4] 4 "inclusive"
#eval benchmark_quantilesFloat_imp [1.0, 2.0, 3.0, 4.0]
example : benchmark_quantiles_imp [1, 2, 3, 4] = some [5/4, 5/2, 15/4] := by native_decide
example : benchmark_quantiles_imp [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 =
  benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 := by native_decide
example : benchmark_quantiles_imp [1, 2, 3, 4, 5] 2 = some [3] := by native_decide
example : benchmark_quantiles_imp [1, 2, 3, 4] 4 "inclusive" = some [7/4, 5/2, 13/4] := by native_decide
example : benchmark_quantiles_imp [4, 1, 3, 2] 4 = some [5/4, 5/2, 15/4] := by native_decide
example : benchmark_quantiles_imp [3/2, 5/2, 7/2, 9/2] 2 = some [3] := by native_decide
example : benchmark_quantiles_imp [1] 4 = none := by native_decide
example : benchmark_quantiles_imp [1, 2] 0 = none := by native_decide
example : benchmark_quantiles_imp [1, 2, 3] 4 "invalid" = none := by native_decide
example : (match benchmark_quantilesFloat_imp [1.0, 2.0, 3.0, 4.0] 4 "exclusive" with
  | some res => res.length == 3 && floatListApprox res [1.25, 2.5, 3.75]
  | none => false) = true := by native_decide

/-!
## 13. Equivalence Theorem (Functional = Imperative)
-/

lemma forIn_append_map {α β : Type*} (xs : List α) (f : α → β) (acc : List β) :
    (ForIn.forIn xs acc (fun x r => pure (ForInStep.yield (r ++ [f x]))) : Id (List β)) =
    pure (acc ++ xs.map f) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.forIn_cons, pure_bind, ih, List.map_cons, List.append_assoc, List.singleton_append]

/-- Equivalence theorem between functional `quantiles` and imperative `quantiles_imp`. -/
theorem quantiles_equiv (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    quantiles data n method = quantiles_imp data n method := by
  unfold quantiles quantilesGeneric quantiles_imp
  by_cases hn : n < 1
  · simp only [hn, ↓reduceIte]; rfl
  · by_cases hld : (List.insertionSort (· ≤ ·) data).length < 2
    · simp only [hn, ↓reduceIte, hld]; rfl
    · by_cases hm1 : method == "inclusive"
      · simp only [hn, ↓reduceIte, hld, hm1]
        have hloop := forIn_append_map (List.range' 1 (n - 1))
          (inclusiveInterp (List.insertionSort (· ≤ ·) data) n) []
        change some (List.map (inclusiveInterp (List.insertionSort (· ≤ ·) data) n) (List.range' 1 (n - 1))) =
          ((ForIn.forIn (List.range' 1 (n - 1)) [] (fun i r =>
            pure (ForInStep.yield (r ++ [inclusiveInterp (List.insertionSort (· ≤ ·) data) n i]))) : Id (List ℚ)) >>=
            fun result => pure (some result))
        rw [hloop, List.nil_append]
        rfl
      · by_cases hm2 : method == "exclusive"
        · simp only [hn, ↓reduceIte, hld, hm1, Bool.false_eq_true, hm2]
          have hloop := forIn_append_map (List.range' 1 (n - 1))
            (exclusiveInterp (List.insertionSort (· ≤ ·) data) n) []
          change some (List.map (exclusiveInterp (List.insertionSort (· ≤ ·) data) n) (List.range' 1 (n - 1))) =
            ((ForIn.forIn (List.range' 1 (n - 1)) [] (fun i r =>
              pure (ForInStep.yield (r ++ [exclusiveInterp (List.insertionSort (· ≤ ·) data) n i]))) : Id (List ℚ)) >>=
              fun result => pure (some result))
          rw [hloop, List.nil_append]
          rfl
        · simp only [hn, ↓reduceIte, hld, hm1, hm2, Bool.false_eq_true]; rfl

/-- Equivalence theorem between functional `benchmark_quantiles` and imperative `benchmark_quantiles_imp`. -/
theorem benchmark_quantiles_equiv (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    benchmark_quantiles data n method = benchmark_quantiles_imp data n method := by
  unfold benchmark_quantiles benchmark_quantiles_imp
  by_cases hp : pre data n method
  · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, quantiles_equiv]; rfl
  · simp only [hp, Bool.not_false, ↓reduceIte]; rfl

/-- Equivalence theorem between functional `quantilesFloat` and imperative `quantilesFloat_imp`. -/
theorem quantilesFloat_equiv (data : List Float) (n : ℕ := 4) (method : String := "exclusive") :
    quantilesFloat data n method = quantilesFloat_imp data n method := by
  unfold quantilesFloat quantilesFloat_imp
  by_cases hn : n < 1
  · simp only [hn, ↓reduceIte]; rfl
  · by_cases hld : (List.insertionSort (· ≤ ·) data).length < 2
    · simp only [hn, ↓reduceIte, hld]; rfl
    · by_cases hm1 : method == "inclusive"
      · simp only [hn, ↓reduceIte, hld, hm1]
        have hloop := forIn_append_map (List.range' 1 (n - 1))
          (inclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n) []
        change some (List.map (inclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n) (List.range' 1 (n - 1))) =
          ((ForIn.forIn (List.range' 1 (n - 1)) [] (fun i r =>
            pure (ForInStep.yield (r ++ [inclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n i]))) : Id (List Float)) >>=
            fun result => pure (some result))
        rw [hloop, List.nil_append]
        rfl
      · by_cases hm2 : method == "exclusive"
        · simp only [hn, ↓reduceIte, hld, hm1, Bool.false_eq_true, hm2]
          have hloop := forIn_append_map (List.range' 1 (n - 1))
            (exclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n) []
          change some (List.map (exclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n) (List.range' 1 (n - 1))) =
            ((ForIn.forIn (List.range' 1 (n - 1)) [] (fun i r =>
              pure (ForInStep.yield (r ++ [exclusiveInterpFloat (List.insertionSort (· ≤ ·) data) n i]))) : Id (List Float)) >>=
              fun result => pure (some result))
          rw [hloop, List.nil_append]
          rfl
        · simp only [hn, ↓reduceIte, hld, hm1, hm2, Bool.false_eq_true]; rfl

/-- Equivalence theorem between functional `benchmark_quantilesFloat` and imperative `benchmark_quantilesFloat_imp`. -/
theorem benchmark_quantilesFloat_equiv (data : List Float) (n : ℕ := 4) (method : String := "exclusive") :
    benchmark_quantilesFloat data n method = benchmark_quantilesFloat_imp data n method := by
  unfold benchmark_quantilesFloat benchmark_quantilesFloat_imp
  by_cases hp : pre data n method
  · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, quantilesFloat_equiv]; rfl
  · simp only [hp, Bool.not_false, ↓reduceIte]; rfl

end «31_statistics_quantiles»

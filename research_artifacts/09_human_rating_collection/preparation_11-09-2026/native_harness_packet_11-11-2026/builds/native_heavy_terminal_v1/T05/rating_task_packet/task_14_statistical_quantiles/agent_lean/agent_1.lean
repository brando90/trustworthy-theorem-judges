import Mathlib

/-!
# Quantiles (translation of Python `statistics.quantiles`)

Divide data into `n` continuous intervals with equal probability and return the
`n - 1` cut points separating them (`n = 4` for quartiles, `10` for deciles,
`100` for percentiles).  Two methods are supported, exactly as in CPython:

* `"exclusive"` (default): `m = ld + 1`, `j = clamp (i*m/n) 1 (ld-1)`,
  `delta = i*m - j*n`, cut point `(data[j-1]*(n-delta) + data[j]*delta)/n`.
* `"inclusive"`: `m = ld - 1`, `(j, delta) = divmod (i*m) n`,
  cut point `(data[j]*(n-delta) + data[j+1]*delta)/n`.

The data is sorted first.  Errors (`StatisticsError`/`ValueError`) are modelled
by `none`.

## Numeric modelling

* `RatLayer`: the exact model.  Python's `int`, `float`, `Fraction` and `Decimal`
  inputs are all rational numbers, and the algorithm only uses `+ - * /`, so
  `ℚ` represents the mathematical intent exactly.  All properties, the
  correctness theorem and the functional/imperative equivalence are stated and
  proved here.
* `FloatLayer`: the same algorithm over primitive `Float`, used for executable
  ground tests that mirror the Python test-suite (`1.25`, `2.5`, …) together
  with the structural theorems that can be proved about it.

The integer index bookkeeping (`clamp`, `jIncl`, `deltaIncl`, `jExcl`,
`deltaExcl`) is shared by both layers.
-/

namespace «31_statistics_quantiles»

/-! ## Shared integer index computations -/

/-- `clamp x lo hi`: the Python expression `lo if x < lo else hi if x > hi else x`. -/
def clamp (x lo hi : ℕ) : ℕ :=
  if x < lo then lo else if hi < x then hi else x

/-- Inclusive method: `j = (i * m) / n` with `m = ld - 1`. -/
def jIncl (ld n i : ℕ) : ℕ := (i * (ld - 1)) / n

/-- Inclusive method: `delta = (i * m) % n` with `m = ld - 1` (`divmod`). -/
def deltaIncl (ld n i : ℕ) : ℕ := (i * (ld - 1)) % n

/-- Exclusive method: `j = i * m // n` clamped to `1 .. ld - 1`, with `m = ld + 1`. -/
def jExcl (ld n i : ℕ) : ℕ := clamp ((i * (ld + 1)) / n) 1 (ld - 1)

/-- Exclusive method: `delta = i*m - j*n` in exact integer arithmetic
(it may be negative or exceed `n`, which yields extrapolation). -/
def deltaExcl (ld n i : ℕ) : ℤ := ((i * (ld + 1) : ℕ) : ℤ) - (jExcl ld n i : ℤ) * (n : ℤ)

/-- Validity of the `method` string. -/
def validMethod (method : String) : Bool :=
  method == "inclusive" || method == "exclusive"

/-! ## RatLayer: exact functional implementation -/

section RatLayer

/-- `sorted(data)` -/
def sortData (data : List ℚ) : List ℚ :=
  data.mergeSort (fun a b => decide (a ≤ b))

/-- Cut point `i` of the inclusive method on the sorted list `s`. -/
def cutIncl (s : List ℚ) (n i : ℕ) : ℚ :=
  let j := jIncl s.length n i
  let δ := deltaIncl s.length n i
  (s.getD j 0 * ((n : ℚ) - (δ : ℚ)) + s.getD (j + 1) 0 * (δ : ℚ)) / (n : ℚ)

/-- Cut point `i` of the exclusive method on the sorted list `s`. -/
def cutExcl (s : List ℚ) (n i : ℕ) : ℚ :=
  let j := jExcl s.length n i
  let δ := deltaExcl s.length n i
  (s.getD (j - 1) 0 * ((n : ℚ) - (δ : ℚ)) + s.getD j 0 * (δ : ℚ)) / (n : ℚ)

/-- Cut point `i` (for `1 ≤ i ≤ n - 1`) of the given method on the sorted list `s`. -/
def cutPoint (s : List ℚ) (n : ℕ) (method : String) (i : ℕ) : ℚ :=
  if method = "inclusive" then cutIncl s n i else cutExcl s n i

/-- Python `quantiles(data, n, method)`; `none` models the raised exceptions. -/
def quantiles (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    Option (List ℚ) :=
  if n < 1 then none
  else
    let s := sortData data
    if s.length < 2 then none
    else if validMethod method then
      some ((List.range' 1 (n - 1)).map (cutPoint s n method))
    else none

/-- Python `pre(data, n, method)`. -/
def pre (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) && validMethod method

/-- Python `benchmark_quantiles(data, n, method)`: the function under verification. -/
def benchmark_quantiles (data : List ℚ) (n : ℕ := 4) (method : String := "exclusive") :
    Option (List ℚ) :=
  if pre data n method then quantiles data n method else none

end RatLayer

/-! ## Unit tests (RatLayer, mirroring the Python `check`) -/

-- 1. Basic quartiles (default): [1.25, 2.5, 3.75]
example : benchmark_quantiles [1, 2, 3, 4] = some [5/4, 5/2, 15/4] := by native_decide
-- 2. Deciles
example : (benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10).map List.length = some 9 := by
  native_decide
example : benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 =
    some [1/5, 7/5, 13/5, 19/5, 5, 31/5, 37/5, 43/5, 49/5] := by native_decide
-- 3. Median (n = 2)
example : benchmark_quantiles [1, 2, 3, 4, 5] 2 = some [3] := by native_decide
-- 4. Inclusive method: [1.75, 2.5, 3.25]
example : benchmark_quantiles [1, 2, 3, 4] 4 "inclusive" = some [7/4, 5/2, 13/4] := by native_decide
-- 5. Exclusive method (explicit)
example : benchmark_quantiles [1, 2, 3, 4] 4 "exclusive" = some [5/4, 5/2, 15/4] := by native_decide
-- 6. Larger dataset: range(1, 11)
example : benchmark_quantiles [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 4 = some [11/4, 11/2, 33/4] := by
  native_decide
-- 7. Unsorted input is sorted internally
example : benchmark_quantiles [4, 1, 3, 2] 4 = some [5/4, 5/2, 15/4] := by native_decide
-- 8. Float data [1.5, 2.5, 3.5, 4.5], n = 2
example : benchmark_quantiles [3/2, 5/2, 7/2, 9/2] 2 = some [3] := by native_decide
-- 9. Error cases
example : benchmark_quantiles [1] 4 = none := by native_decide
example : benchmark_quantiles [1, 2] 0 = none := by native_decide
example : benchmark_quantiles [1, 2, 3] 4 "invalid" = none := by native_decide
-- Extrapolation of the exclusive method (CPython: quantiles([1, 2], n=4) == [0.75, 1.5, 2.25])
example : benchmark_quantiles [1, 2] 4 = some [3/4, 3/2, 9/4] := by native_decide
-- n = 1 gives no cut points
example : benchmark_quantiles [1, 2, 3] 1 = some [] := by native_decide
-- Further cases cross-checked against CPython 3
example : benchmark_quantiles [1, 2, 3, 4, 5, 6] 5 = some [7/5, 14/5, 21/5, 28/5] := by native_decide
example : benchmark_quantiles [1, 2, 3, 4, 5, 6] 5 "inclusive" = some [2, 3, 4, 5] := by native_decide
example : benchmark_quantiles [1, 2, 3] 7 = some [4/7, 8/7, 12/7, 16/7, 20/7, 24/7] := by native_decide
example : benchmark_quantiles [5, 1] 3 "inclusive" = some [7/3, 11/3] := by native_decide

#eval benchmark_quantiles [1, 2, 3, 4]
#eval benchmark_quantiles [1, 2, 3, 4] 4 "inclusive"
#eval benchmark_quantiles [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10
#eval benchmark_quantiles [1, 2] 4
#eval benchmark_quantiles [1, 2, 3] 4 "invalid"

/-! ## Pre-condition -/

/-- Pre-condition (Python `pre`): at least two data points, `n ≥ 1`, and a valid method. -/
def Pre (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

/-! ## Helper lemmas -/

theorem validMethod_iff (method : String) :
    validMethod method = true ↔ (method = "inclusive" ∨ method = "exclusive") := by
  simp [validMethod]

theorem pre_iff (data : List ℚ) (n : ℕ) (method : String) :
    pre data n method = true ↔ Pre data n method := by
  simp [pre, Pre, validMethod_iff, and_assoc]

theorem sortData_perm (data : List ℚ) : (sortData data).Perm data :=
  List.mergeSort_perm data _

theorem sortData_length (data : List ℚ) : (sortData data).length = data.length :=
  List.length_mergeSort data

theorem sortData_sorted (data : List ℚ) : (sortData data).Pairwise (· ≤ ·) :=
  List.sorted_mergeSort' (· ≤ ·) data

theorem sortData_eq_of_perm {data data' : List ℚ} (h : data'.Perm data) :
    sortData data' = sortData data :=
  List.eq_of_perm_of_sorted ((sortData_perm data').trans (h.trans (sortData_perm data).symm))
    (sortData_sorted data') (sortData_sorted data)

/-- Elements of a sorted list are monotone in the index (`getD` form). -/
theorem getD_le_getD_of_sorted {s : List ℚ} (hs : s.Pairwise (· ≤ ·)) {a b : ℕ}
    (hab : a ≤ b) (hb : b < s.length) : s.getD a 0 ≤ s.getD b 0 := by
  rw [List.getD_eq_getElem s 0 (lt_of_le_of_lt hab hb), List.getD_eq_getElem s 0 hb]
  rcases Nat.lt_or_eq_of_le hab with h | h
  · exact (List.pairwise_iff_getElem.mp hs) a b _ hb h
  · subst h; exact le_rfl

theorem getD_mem {s : List ℚ} {a : ℕ} (ha : a < s.length) : s.getD a 0 ∈ s := by
  rw [List.getD_eq_getElem s 0 ha]; exact List.getElem_mem ha

/-- Under the pre-condition, `benchmark_quantiles` succeeds and returns the interpolation
formula evaluated on the sorted data. -/
theorem benchmark_quantiles_eq (data : List ℚ) (n : ℕ) (method : String)
    (h : Pre data n method) :
    benchmark_quantiles data n method =
      some ((List.range' 1 (n - 1)).map (cutPoint (sortData data) n method)) := by
  obtain ⟨hlen, hn, hm⟩ := h
  have hpre : pre data n method = true := (pre_iff data n method).mpr ⟨hlen, hn, hm⟩
  have hvm : validMethod method = true := (validMethod_iff method).mpr hm
  simp only [benchmark_quantiles, hpre, if_true, quantiles, sortData_length, hvm]
  rw [if_neg (by omega), if_neg (by omega)]

/-- Without the pre-condition, `benchmark_quantiles` fails (Python raises). -/
theorem benchmark_quantiles_eq_none (data : List ℚ) (n : ℕ) (method : String)
    (h : ¬ Pre data n method) : benchmark_quantiles data n method = none := by
  have : pre data n method = false := by
    rw [← Bool.not_eq_true, pre_iff]; exact h
  simp [benchmark_quantiles, this]


/-! ### Clamp lemmas -/

theorem clamp_mono {x y lo hi : ℕ} (hlh : lo ≤ hi) (hxy : x ≤ y) :
    clamp x lo hi ≤ clamp y lo hi := by
  unfold clamp; split_ifs <;> omega

theorem lo_le_clamp {x lo hi : ℕ} (hlh : lo ≤ hi) : lo ≤ clamp x lo hi := by
  unfold clamp; split_ifs <;> omega

theorem clamp_le_hi {x lo hi : ℕ} (hlh : lo ≤ hi) : clamp x lo hi ≤ hi := by
  unfold clamp; split_ifs <;> omega

/-- If the clamp is strictly below the upper bound, it was not clamped from above. -/
theorem le_clamp_of_clamp_lt_hi {x lo hi : ℕ} (h : clamp x lo hi < hi) : x ≤ clamp x lo hi := by
  unfold clamp at *; split_ifs at * <;> omega

/-- If the clamp is strictly above the lower bound, it was not clamped from below. -/
theorem clamp_le_of_lo_lt_clamp {x lo hi : ℕ} (h : lo < clamp x lo hi) : clamp x lo hi ≤ x := by
  unfold clamp at *; split_ifs at * <;> omega

/-! ### Linear interpolation on one segment

`seg a b n δ = a * (n - δ) + b * δ` is `n` times the point at parameter `δ / n` on the
segment from `a` to `b`. -/

/-- `n` times the interpolated value between `a` and `b` at parameter `δ / n`. -/
def seg (a b n δ : ℚ) : ℚ := a * (n - δ) + b * δ

theorem seg_mono_delta {a b n δ δ' : ℚ} (hab : a ≤ b) (hδ : δ ≤ δ') :
    seg a b n δ ≤ seg a b n δ' := by
  unfold seg; nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hδ)]

theorem seg_le_right {a b n δ : ℚ} (hab : a ≤ b) (hδ : δ ≤ n) : seg a b n δ ≤ b * n := by
  unfold seg; nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hδ)]

theorem left_le_seg {a b n δ : ℚ} (hab : a ≤ b) (hδ : 0 ≤ δ) : a * n ≤ seg a b n δ := by
  unfold seg; nlinarith [mul_nonneg (sub_nonneg.mpr hab) hδ]

/-- The exclusive cut point in `seg` form. -/
theorem cutExcl_eq (s : List ℚ) (n i : ℕ) :
    cutExcl s n i =
      seg (s.getD (jExcl s.length n i - 1) 0) (s.getD (jExcl s.length n i) 0) n
        ((i * (s.length + 1) : ℕ) - (jExcl s.length n i : ℚ) * n) / n := by
  simp only [cutExcl, deltaExcl, seg]
  push_cast
  ring

/-- The inclusive cut point in `seg` form. -/
theorem cutIncl_eq (s : List ℚ) (n i : ℕ) :
    cutIncl s n i =
      seg (s.getD (jIncl s.length n i) 0) (s.getD (jIncl s.length n i + 1) 0) n
        ((i * (s.length - 1) : ℕ) - (jIncl s.length n i : ℚ) * n) / n := by
  simp only [cutIncl, deltaIncl, jIncl, seg]
  have h' : ((i * (s.length - 1) % n : ℕ) : ℚ) =
      ((i * (s.length - 1) : ℕ) : ℚ) - ((i * (s.length - 1) / n : ℕ) : ℚ) * (n : ℚ) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div']
  rw [h']


/-! ### Index bounds -/

theorem one_le_jExcl {ld n i : ℕ} (hld : 2 ≤ ld) : 1 ≤ jExcl ld n i :=
  lo_le_clamp (by omega)

theorem jExcl_lt_length {ld n i : ℕ} (hld : 2 ≤ ld) : jExcl ld n i < ld := by
  have := clamp_le_hi (x := i * (ld + 1) / n) (lo := 1) (hi := ld - 1) (by omega)
  unfold jExcl; omega

theorem jIncl_add_one_lt {ld n i : ℕ} (hld : 2 ≤ ld) (hi : i < n) : jIncl ld n i + 1 < ld := by
  unfold jIncl
  have h1 : i * (ld - 1) < (ld - 1) * n := by
    have := Nat.mul_lt_mul_of_pos_right hi (by omega : ld - 1 > 0)
    rwa [Nat.mul_comm n] at this
  have := (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mpr h1
  omega

/-! ### Monotonicity of the cut points in `i` -/

/-- Exclusive cut points are non-decreasing in `i` (for all `i`, thanks to the clamping). -/
theorem cutExcl_mono (s : List ℚ) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length) {n : ℕ}
    (hn : 1 ≤ n) {i i' : ℕ} (hii : i ≤ i') : cutExcl s n i ≤ cutExcl s n i' := by
  rw [cutExcl_eq, cutExcl_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have htt : i * (s.length + 1) ≤ i' * (s.length + 1) := Nat.mul_le_mul_right _ hii
  have hjj : jExcl s.length n i ≤ jExcl s.length n i' :=
    clamp_mono (by omega) (Nat.div_le_div_right htt)
  have hj1 : 1 ≤ jExcl s.length n i := one_le_jExcl hld
  have hj'1 : 1 ≤ jExcl s.length n i' := one_le_jExcl hld
  have hjld : jExcl s.length n i < s.length := jExcl_lt_length hld
  have hj'ld : jExcl s.length n i' < s.length := jExcl_lt_length hld
  have hsj : s.getD (jExcl s.length n i - 1) 0 ≤ s.getD (jExcl s.length n i) 0 :=
    getD_le_getD_of_sorted hs (Nat.sub_le _ 1) hjld
  have hsj' : s.getD (jExcl s.length n i' - 1) 0 ≤ s.getD (jExcl s.length n i') 0 :=
    getD_le_getD_of_sorted hs (Nat.sub_le _ 1) hj'ld
  rcases Nat.lt_or_eq_of_le hjj with hlt | heq
  · -- different segments: `j` was not clamped from above, `j'` not from below
    have h2 : i * (s.length + 1) / n ≤ jExcl s.length n i :=
      le_clamp_of_clamp_lt_hi (by unfold jExcl at *; omega)
    have h3 : i * (s.length + 1) < (jExcl s.length n i + 1) * n :=
      (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_of_le h2)
    have h4 : jExcl s.length n i' ≤ i' * (s.length + 1) / n :=
      clamp_le_of_lo_lt_clamp (by unfold jExcl at *; omega)
    have h5 : jExcl s.length n i' * n ≤ i' * (s.length + 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mp h4
    have h3' : ((i * (s.length + 1) : ℕ) : ℚ) < ((jExcl s.length n i : ℚ) + 1) * n := by
      exact_mod_cast h3
    have h5' : (jExcl s.length n i' : ℚ) * n ≤ ((i' * (s.length + 1) : ℕ) : ℚ) := by
      exact_mod_cast h5
    calc seg _ _ n _ ≤ s.getD (jExcl s.length n i) 0 * n := seg_le_right hsj (by linarith)
      _ ≤ s.getD (jExcl s.length n i' - 1) 0 * n :=
          mul_le_mul_of_nonneg_right (getD_le_getD_of_sorted hs (by omega) (by omega))
            (by positivity)
      _ ≤ _ := left_le_seg hsj' (by linarith)
  · -- same segment
    rw [← heq]
    apply seg_mono_delta hsj
    have : ((i * (s.length + 1) : ℕ) : ℚ) ≤ ((i' * (s.length + 1) : ℕ) : ℚ) := by
      exact_mod_cast htt
    linarith

/-- Inclusive cut points are non-decreasing in `i` (for `i ≤ i' < n`). -/
theorem cutIncl_mono (s : List ℚ) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length) {n : ℕ}
    (hn : 1 ≤ n) {i i' : ℕ} (hii : i ≤ i') (hi' : i' < n) : cutIncl s n i ≤ cutIncl s n i' := by
  rw [cutIncl_eq, cutIncl_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have htt : i * (s.length - 1) ≤ i' * (s.length - 1) := Nat.mul_le_mul_right _ hii
  have hjj : jIncl s.length n i ≤ jIncl s.length n i' := Nat.div_le_div_right htt
  have hj'ld : jIncl s.length n i' + 1 < s.length := jIncl_add_one_lt hld hi'
  have hjld : jIncl s.length n i + 1 < s.length := by omega
  have hsj : s.getD (jIncl s.length n i) 0 ≤ s.getD (jIncl s.length n i + 1) 0 :=
    getD_le_getD_of_sorted hs (Nat.le_succ _) hjld
  have hsj' : s.getD (jIncl s.length n i') 0 ≤ s.getD (jIncl s.length n i' + 1) 0 :=
    getD_le_getD_of_sorted hs (Nat.le_succ _) hj'ld
  have hδ0 : ∀ k, (jIncl s.length n k : ℚ) * n ≤ ((k * (s.length - 1) : ℕ) : ℚ) := fun k => by
    unfold jIncl; exact_mod_cast Nat.div_mul_le_self _ n
  have hδn : ∀ k, ((k * (s.length - 1) : ℕ) : ℚ) < ((jIncl s.length n k : ℚ) + 1) * n := fun k => by
    unfold jIncl
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mp (Nat.lt_succ_self (k * (s.length - 1) / n))
    exact_mod_cast this
  rcases Nat.lt_or_eq_of_le hjj with hlt | heq
  · have h1 := hδn i
    have h2 := hδ0 i'
    calc seg _ _ n _ ≤ s.getD (jIncl s.length n i + 1) 0 * n := seg_le_right hsj (by linarith)
      _ ≤ s.getD (jIncl s.length n i') 0 * n :=
          mul_le_mul_of_nonneg_right (getD_le_getD_of_sorted hs hlt (by omega)) (by positivity)
      _ ≤ _ := left_le_seg hsj' (by linarith)
  · rw [← heq]
    apply seg_mono_delta hsj
    have : ((i * (s.length - 1) : ℕ) : ℚ) ≤ ((i' * (s.length - 1) : ℕ) : ℚ) := by
      exact_mod_cast htt
    linarith

/-! ### Bounds of the inclusive method -/

/-- Inclusive cut points lie between the smallest and the largest data value. -/
theorem cutIncl_bounds (s : List ℚ) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length) {n : ℕ}
    (hn : 1 ≤ n) {i : ℕ} (hi : i < n) :
    s.getD 0 0 ≤ cutIncl s n i ∧ cutIncl s n i ≤ s.getD (s.length - 1) 0 := by
  rw [cutIncl_eq]
  have hjld : jIncl s.length n i + 1 < s.length := jIncl_add_one_lt hld hi
  have hsj : s.getD (jIncl s.length n i) 0 ≤ s.getD (jIncl s.length n i + 1) 0 :=
    getD_le_getD_of_sorted hs (Nat.le_succ _) hjld
  have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
  have hδ0 : (jIncl s.length n i : ℚ) * n ≤ ((i * (s.length - 1) : ℕ) : ℚ) := by
    unfold jIncl; exact_mod_cast Nat.div_mul_le_self _ n
  have hδn : ((i * (s.length - 1) : ℕ) : ℚ) < ((jIncl s.length n i : ℚ) + 1) * n := by
    unfold jIncl
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mp (Nat.lt_succ_self (i * (s.length - 1) / n))
    exact_mod_cast this
  constructor
  · rw [le_div_iff₀ hnpos]
    calc s.getD 0 0 * n ≤ s.getD (jIncl s.length n i) 0 * n :=
          mul_le_mul_of_nonneg_right (getD_le_getD_of_sorted hs (Nat.zero_le _) (by omega)) hnpos.le
      _ ≤ _ := left_le_seg hsj (by linarith)
  · rw [div_le_iff₀ hnpos]
    calc seg _ _ n _ ≤ s.getD (jIncl s.length n i + 1) 0 * n := seg_le_right hsj (by linarith)
      _ ≤ s.getD (s.length - 1) 0 * n :=
          mul_le_mul_of_nonneg_right (getD_le_getD_of_sorted hs (by omega) (by omega)) hnpos.le

/-! ### The median (`n = 2`) -/

/-- Median of a sorted list with at least one element: the middle element for odd length,
the mean of the two middle elements for even length. -/
def median (s : List ℚ) : ℚ :=
  if s.length % 2 = 1 then s.getD (s.length / 2) 0
  else (s.getD (s.length / 2 - 1) 0 + s.getD (s.length / 2) 0) / 2

theorem median_even (s : List ℚ) {k : ℕ} (hk : s.length = 2 * k) (hk1 : 1 ≤ k) :
    median s = (s.getD (k - 1) 0 + s.getD k 0) / 2 := by
  have e1 : s.length / 2 - 1 = k - 1 := by omega
  have e2 : s.length / 2 = k := by omega
  unfold median
  rw [if_neg (by omega), e1, e2]

theorem median_odd (s : List ℚ) {k : ℕ} (hk : s.length = 2 * k + 1) :
    median s = s.getD k 0 := by
  have e2 : s.length / 2 = k := by omega
  unfold median
  rw [if_pos (by omega), e2]

theorem cutExcl_two (s : List ℚ) (hld : 2 ≤ s.length) : cutExcl s 2 1 = median s := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' s.length
  · have hj : jExcl s.length 2 1 = k := by unfold jExcl clamp; split_ifs <;> omega
    have hδ : deltaExcl s.length 2 1 = 1 := by unfold deltaExcl; rw [hj]; omega
    rw [median_even s hk (by omega)]
    simp only [cutExcl, hj, hδ]
    push_cast
    ring
  · have hj : jExcl s.length 2 1 = k + 1 := by unfold jExcl clamp; split_ifs <;> omega
    have hδ : deltaExcl s.length 2 1 = 0 := by unfold deltaExcl; rw [hj]; omega
    rw [median_odd s hk]
    simp only [cutExcl, hj, hδ, Nat.add_sub_cancel]
    push_cast
    ring

theorem cutIncl_two (s : List ℚ) (hld : 2 ≤ s.length) : cutIncl s 2 1 = median s := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' s.length
  · have hj : jIncl s.length 2 1 = k - 1 := by unfold jIncl; omega
    have hδ : deltaIncl s.length 2 1 = 1 := by unfold deltaIncl; omega
    have hk1 : k - 1 + 1 = k := by omega
    rw [median_even s hk (by omega)]
    simp only [cutIncl, hj, hδ, hk1]
    push_cast
    ring
  · have hj : jIncl s.length 2 1 = k := by unfold jIncl; omega
    have hδ : deltaIncl s.length 2 1 = 0 := by unfold deltaIncl; omega
    rw [median_odd s hk]
    simp only [cutIncl, hj, hδ]
    push_cast
    ring


/-! ## Properties -/

/-- The computation succeeds (Python raises no exception). -/
def succeeds_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  (benchmark_quantiles data n method).isSome = true

/-- Specification: the result is the interpolation formula of the chosen method, evaluated on
the *sorted* data for `i = 1, …, n - 1`. -/
def spec_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  benchmark_quantiles data n method =
    some ((List.range' 1 (n - 1)).map (cutPoint (sortData data) n method))

/-- There are exactly `n - 1` cut points. -/
def length_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∀ r, benchmark_quantiles data n method = some r → r.length = n - 1

/-- The cut points are non-decreasing. -/
def sorted_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∀ r, benchmark_quantiles data n method = some r → r.Pairwise (· ≤ ·)

/-- The result depends only on the multiset of data values: the input order is irrelevant
(`data` is sorted internally). -/
def perm_invariant_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ∀ data' : List ℚ, data'.Perm data →
    benchmark_quantiles data' n method = benchmark_quantiles data n method

/-- Inclusive method: every cut point lies between the minimum and the maximum of the data
(the minimum is treated as the 0th and the maximum as the 100th percentile). -/
def inclusive_bounds_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  method = "inclusive" →
    ∀ r, benchmark_quantiles data n method = some r →
      ∀ q ∈ r, (∃ x ∈ data, x ≤ q) ∧ (∃ y ∈ data, q ≤ y)

/-- With `n = 2` the single cut point is the median of the data, for both methods. -/
def median_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  n = 2 → benchmark_quantiles data n method = some [median (sortData data)]

/-- Error behaviour: outside the pre-condition the computation fails
(Python raises `StatisticsError` / `ValueError`). -/
def error_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  ¬ Pre data n method → benchmark_quantiles data n method = none

theorem succeeds_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    succeeds_prop data n method := by
  unfold succeeds_prop
  rw [benchmark_quantiles_eq data n method h]
  rfl

theorem spec_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    spec_prop data n method :=
  benchmark_quantiles_eq data n method h

theorem length_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    length_prop data n method := by
  intro r hr
  rw [benchmark_quantiles_eq data n method h] at hr
  cases hr
  simp

theorem sorted_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    sorted_prop data n method := by
  intro r hr
  rw [benchmark_quantiles_eq data n method h] at hr
  cases hr
  obtain ⟨hlen, hn, _⟩ := h
  have hs := sortData_sorted data
  have hld : 2 ≤ (sortData data).length := by rw [sortData_length]; exact hlen
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range' (s := 1) (n := n - 1) 1)
  intro a b _ hb hab
  rw [List.mem_range'_1] at hb
  unfold cutPoint
  split_ifs
  · exact cutIncl_mono _ hs hld hn hab.le (by omega)
  · exact cutExcl_mono _ hs hld hn hab.le

theorem perm_invariant_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    perm_invariant_prop data n method := by
  intro data' hp
  have h' : Pre data' n method := ⟨by rw [hp.length_eq]; exact h.1, h.2.1, h.2.2⟩
  rw [benchmark_quantiles_eq data n method h, benchmark_quantiles_eq data' n method h',
    sortData_eq_of_perm hp]

theorem inclusive_bounds_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    inclusive_bounds_prop data n method := by
  intro hm r hr q hq
  rw [benchmark_quantiles_eq data n method h] at hr
  cases hr
  rw [List.mem_map] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  rw [List.mem_range'_1] at hi
  have hs := sortData_sorted data
  have hld : 2 ≤ (sortData data).length := by rw [sortData_length]; exact h.1
  have hb := cutIncl_bounds (sortData data) hs hld h.2.1 (i := i) (by omega)
  rw [cutPoint, if_pos hm]
  exact ⟨⟨(sortData data).getD 0 0, (sortData_perm data).mem_iff.mp (getD_mem (by omega)), hb.1⟩,
    ⟨(sortData data).getD ((sortData data).length - 1) 0,
      (sortData_perm data).mem_iff.mp (getD_mem (by omega)), hb.2⟩⟩

theorem median_thm (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    median_prop data n method := by
  intro hn2
  subst hn2
  rw [benchmark_quantiles_eq data 2 method h]
  have hld : 2 ≤ (sortData data).length := by rw [sortData_length]; exact h.1
  have hr : List.range' 1 (2 - 1) = [1] := rfl
  rw [hr, List.map_cons, List.map_nil]
  unfold cutPoint
  split_ifs
  · rw [cutIncl_two _ hld]
  · rw [cutExcl_two _ hld]

theorem error_thm (data : List ℚ) (n : ℕ) (method : String) : error_prop data n method :=
  benchmark_quantiles_eq_none data n method

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties of `benchmark_quantiles`. -/
def Post_prop (data : List ℚ) (n : ℕ) (method : String) : Prop :=
  succeeds_prop data n method ∧ spec_prop data n method ∧ length_prop data n method ∧
    sorted_prop data n method ∧ perm_invariant_prop data n method ∧
    inclusive_bounds_prop data n method ∧ median_prop data n method ∧ error_prop data n method

/-! ## Property-based tests

Executable Boolean forms of every property above, checked on random (Plausible) and
exhaustive small inputs.  `ℚ` is exact, so these test the properties directly. -/

/-- Method string chosen by a Boolean, so Plausible can sample both valid methods. -/
def methodOf (b : Bool) : String := if b then "inclusive" else "exclusive"

-- Admissible inputs are produced directly as `x :: y :: rest` (length ≥ 2) and `k + 1` (n ≥ 1),
-- so no sample is discarded.

-- PBT: succeeds_prop
#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  (benchmark_quantiles (x :: y :: rest) (k + 1) (methodOf b)).isSome = true)
-- PBT: spec_prop
#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  benchmark_quantiles (x :: y :: rest) (k + 1) (methodOf b) =
    some ((List.range' 1 k).map (cutPoint (sortData (x :: y :: rest)) (k + 1) (methodOf b))))
-- PBT: length_prop
#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  ((benchmark_quantiles (x :: y :: rest) (k + 1) (methodOf b)).getD []).length = k)
example : (List.range 12).all (fun n => (List.range 7).all (fun k =>
    ((benchmark_quantiles ((List.range (k + 2)).map (fun x => (x : ℚ) / 3)) n "exclusive").getD []).length
      = n - 1 || n = 0)) = true := by native_decide
-- PBT: sorted_prop
#eval Plausible.Testable.check (∀ (data : List ℚ) (n : ℕ) (b : Bool),
  ((benchmark_quantiles data n (methodOf b)).getD []).Pairwise (· ≤ ·))
example : [[1, 2], [1, 1], [-3, 7, 7, 8], [5, 1, 3, 3, 2, 9, -1]].all (fun data =>
    (List.range 13).all (fun n =>
      ((benchmark_quantiles (data.map (fun x : ℤ => (x : ℚ))) n "exclusive").getD []).Pairwise (· ≤ ·)
        && ((benchmark_quantiles (data.map (fun x : ℤ => (x : ℚ))) n "inclusive").getD []).Pairwise (· ≤ ·)))
    = true := by native_decide
-- PBT: perm_invariant_prop (reversal and rotation are permutations; exhaustive over permutations)
#eval Plausible.Testable.check (∀ (data : List ℚ) (n k : ℕ) (b : Bool),
  benchmark_quantiles data.reverse n (methodOf b) = benchmark_quantiles data n (methodOf b) ∧
  benchmark_quantiles (data.rotate k) n (methodOf b) = benchmark_quantiles data n (methodOf b))
example : ([(1 : ℚ), 2, 3, 4, 5].permutations).all (fun p =>
    benchmark_quantiles p 4 = benchmark_quantiles [1, 2, 3, 4, 5] 4 &&
    benchmark_quantiles p 3 "inclusive" = benchmark_quantiles [1, 2, 3, 4, 5] 3 "inclusive") = true := by
  native_decide
-- PBT: inclusive_bounds_prop
#eval Plausible.Testable.check (∀ (data : List ℚ) (n : ℕ),
  ((benchmark_quantiles data n "inclusive").getD []).all
    (fun q => decide ((∃ x ∈ data, x ≤ q) ∧ (∃ y ∈ data, q ≤ y))) = true)
example : (List.range 9).all (fun n =>
    ((benchmark_quantiles [(7 : ℚ), -2, 5/2, 5/2, 11, 0] n "inclusive").getD []).all
      (fun q => decide ((∃ x ∈ [(7 : ℚ), -2, 5/2, 5/2, 11, 0], x ≤ q) ∧
        (∃ y ∈ [(7 : ℚ), -2, 5/2, 5/2, 11, 0], q ≤ y)))) = true := by native_decide
-- PBT: median_prop
#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (b : Bool),
  benchmark_quantiles (x :: y :: rest) 2 (methodOf b) = some [median (sortData (x :: y :: rest))])
-- PBT: error_prop, as the Boolean `pre ∨ result = none` (random strings are rarely valid methods)
#eval Plausible.Testable.check (∀ (data : List ℚ) (n : ℕ) (method : String),
  (pre data n method || (benchmark_quantiles data n method).isNone) = true)
#eval Plausible.Testable.check (∀ (data : List ℚ) (n : ℕ) (b : Bool),
  (pre data n (methodOf b) || (benchmark_quantiles data n (methodOf b)).isNone) = true)

/-- Executable Boolean form of `Post_prop` (with `perm_invariant_prop` checked on the reversed
input, and the bounds/median clauses guarded by their executable hypotheses). -/
def Post_check (data : List ℚ) (n : ℕ) (method : String) : Bool :=
  let out := benchmark_quantiles data n method
  let r := out.getD []
  out.isSome &&
  (out == some ((List.range' 1 (n - 1)).map (cutPoint (sortData data) n method))) &&
  (r.length == n - 1) &&
  decide (r.Pairwise (· ≤ ·)) &&
  (benchmark_quantiles data.reverse n method == out) &&
  (!(method == "inclusive") ||
    r.all (fun q => decide ((∃ x ∈ data, x ≤ q) ∧ (∃ y ∈ data, q ≤ y)))) &&
  (!(n == 2) || (out == some [median (sortData data)])) &&
  (pre data n method || out.isNone)

-- PBT: Post_prop
#eval Plausible.Testable.check (∀ (x y : ℚ) (rest : List ℚ) (k : ℕ) (b : Bool),
  Post_check (x :: y :: rest) (k + 1) (methodOf b) = true)
example : (List.range' 1 10).all (fun n => (List.range 6).all (fun k =>
    Post_check ((List.range (k + 2)).map (fun x => ((x * x : ℕ) : ℚ) / 7 - 2)) n "exclusive" &&
    Post_check ((List.range (k + 2)).map (fun x => ((x * x : ℕ) : ℚ) / 7 - 2)) n "inclusive")) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness (data : List ℚ) (n : ℕ) (method : String) (h : Pre data n method) :
    Post_prop data n method :=
  ⟨succeeds_thm data n method h, spec_thm data n method h, length_thm data n method h,
    sorted_thm data n method h, perm_invariant_thm data n method h,
    inclusive_bounds_thm data n method h, median_thm data n method h, error_thm data n method⟩

end «31_statistics_quantiles»

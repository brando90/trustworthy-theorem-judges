import Mathlib
import Plausible

/-!
# HumanEval/4: Mean Absolute Deviation

This module formalizes the Python function `mean_absolute_deviation` from HumanEval/4.
For a given non-empty list of input numbers, it calculates the Mean Absolute Deviation (MAD)
around the arithmetic mean of the dataset:

$$\text{MAD}(x_1, \dots, x_n) = \frac{1}{n} \sum_{i=1}^n |x_i - \bar{x}|, \quad \text{where } \bar{x} = \frac{1}{n} \sum_{i=1}^n x_i.$$

We provide:
- Executable `Float` and exact `Rat` (`ℚ`) implementations for ground evaluation and property-based testing.
- Mathematical `Real` (`ℝ`) implementation for formal specification and proof of algebraic/analytic properties.
- Exact correspondence theorems connecting the `Rat` implementation to the `Real` implementation.
- Pre-condition, property propositions and proofs, post-condition, property-based tests, correctness theorem,
  imperative implementations (`Id.run do`), and functional-imperative equivalence theorems.
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## 1. Functional Implementations -/

/-- Arithmetic mean of a list of real numbers. -/
noncomputable def mean (numbers : List ℝ) : ℝ :=
  numbers.sum / (numbers.length : ℝ)

/-- Mean Absolute Deviation around the mean for a list of real numbers. -/
noncomputable def mean_absolute_deviation (numbers : List ℝ) : ℝ :=
  let m := mean numbers
  (numbers.map (fun x => |x - m|)).sum / (numbers.length : ℝ)

/-- Executable `Float` arithmetic mean of a list of floating-point numbers. -/
def mean_float (numbers : List Float) : Float :=
  (numbers.foldl (· + ·) 0.0) / numbers.length.toFloat

/-- Executable `Float` Mean Absolute Deviation around the mean. -/
def mean_absolute_deviation_float (numbers : List Float) : Float :=
  let m := mean_float numbers
  (numbers.foldl (fun acc x => acc + Float.abs (x - m)) 0.0) / numbers.length.toFloat

/-- Executable exact `Rat` (`ℚ`) arithmetic mean of a list of rational numbers. -/
def mean_rat (numbers : List ℚ) : ℚ :=
  numbers.sum / (numbers.length : ℚ)

/-- Executable exact `Rat` (`ℚ`) Mean Absolute Deviation around the mean. -/
def mean_absolute_deviation_rat (numbers : List ℚ) : ℚ :=
  let m := mean_rat numbers
  (numbers.map (fun x => |x - m|)).sum / (numbers.length : ℚ)

/-! ## 2. Unit Tests -/

-- Ground Float unit tests matching Python docstring and `check` function
example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide

example : mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] == 1.0 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide

-- Exact Rat unit tests
example : mean_absolute_deviation_rat [1, 2, 3] = 2 / 3 := by
  native_decide

example : mean_absolute_deviation_rat [1, 2, 3, 4] = 1 := by
  native_decide

example : mean_absolute_deviation_rat [1, 2, 3, 4, 5] = 6 / 5 := by
  native_decide

-- Kernel-checked Real unit tests
theorem test_real_123 : mean_absolute_deviation ([1, 2, 3] : List ℝ) = 2 / 3 := by
  unfold mean_absolute_deviation mean
  dsimp
  norm_num

theorem test_real_1234 : mean_absolute_deviation ([1, 2, 3, 4] : List ℝ) = 1 := by
  unfold mean_absolute_deviation mean
  dsimp
  norm_num [abs_of_pos]

theorem test_real_12345 : mean_absolute_deviation ([1, 2, 3, 4, 5] : List ℝ) = 6 / 5 := by
  unfold mean_absolute_deviation mean
  dsimp
  norm_num

#eval mean_absolute_deviation_float [1.0, 2.0, 3.0]
#eval mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0, 5.0]
#eval mean_absolute_deviation_rat [1, 2, 3]
#eval mean_absolute_deviation_rat [1, 2, 3, 4]
#eval mean_absolute_deviation_rat [1, 2, 3, 4, 5]

/-! ## 3. Pre-condition -/

/-- Pre-condition: the input list of numbers must be non-empty so that the mean and MAD
are well-defined without division by zero. -/
def Pre (numbers : List ℝ) : Prop :=
  numbers ≠ []

/-- Pre-condition for the `Rat` layer. -/
def Pre_rat (numbers : List ℚ) : Prop :=
  numbers ≠ []

/-- Pre-condition for the `Float` layer. -/
def Pre_float (numbers : List Float) : Prop :=
  numbers ≠ []

theorem Pre_iff_length_pos (numbers : List ℝ) : Pre numbers ↔ 0 < numbers.length :=
  List.length_pos_iff.symm

theorem length_cast_pos_of_Pre {numbers : List ℝ} (h : Pre numbers) :
    (0 : ℝ) < (numbers.length : ℝ) :=
  Nat.cast_pos.mpr (List.length_pos_iff.mpr h)

theorem length_cast_ne_zero_of_Pre {numbers : List ℝ} (h : Pre numbers) :
    (numbers.length : ℝ) ≠ 0 :=
  ne_of_gt (length_cast_pos_of_Pre h)

/-! ## 4. Helper Lemmas & Cross-Layer Correspondence -/

/-- Casting a list of rationals to reals commutes with `List.sum`. -/
theorem sum_map_rat_cast (numbers : List ℚ) :
    (numbers.map (fun q : ℚ => (q : ℝ))).sum = ((numbers.sum : ℚ) : ℝ) :=
  (Rat.cast_list_sum numbers).symm

/-- Exact correspondence between `mean_rat` and `mean` via `Rat.cast`. -/
theorem mean_rat_cast (numbers : List ℚ) :
    ((mean_rat numbers : ℚ) : ℝ) = mean (numbers.map (fun q : ℚ => (q : ℝ))) := by
  simp [mean_rat, mean]

/-- Exact correspondence between `mean_absolute_deviation_rat` and `mean_absolute_deviation`
via `Rat.cast`. -/
theorem mean_absolute_deviation_rat_cast (numbers : List ℚ) :
    ((mean_absolute_deviation_rat numbers : ℚ) : ℝ) =
      mean_absolute_deviation (numbers.map (fun q : ℚ => (q : ℝ))) := by
  unfold mean_absolute_deviation_rat mean_absolute_deviation
  dsimp only
  rw [← mean_rat_cast]
  have hmap :
      (numbers.map (fun q : ℚ => (q : ℝ))).map (fun x => |x - (mean_rat numbers : ℝ)|) =
        (numbers.map (fun x => |x - mean_rat numbers|)).map (fun q : ℚ => (q : ℝ)) := by
    rw [List.map_map, List.map_map]
    congr 1
    ext x
    simp [Rat.cast_abs, Rat.cast_sub]
  rw [hmap, ← Rat.cast_list_sum]
  simp

/-- Sum of `x + c` over a list `xs`. -/
theorem sum_map_add_const (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => x + c)).sum = xs.sum + (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.cast_add]
    ring

/-- Sum of `x - c` over a list `xs`. -/
theorem sum_map_sub_const (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => x - c)).sum = xs.sum - (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.cast_add]
    ring

/-- Sum of `k * x` over a list `xs`. -/
theorem sum_map_mul_left (xs : List ℝ) (k : ℝ) :
    (xs.map (fun x => k * x)).sum = k * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih, mul_add]

/-- Mean of a translated list `xs.map (· + c)`. -/
theorem mean_map_add_const {numbers : List ℝ} (h : Pre numbers) (c : ℝ) :
    mean (numbers.map (fun x => x + c)) = mean numbers + c := by
  have hn : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero_of_Pre h
  unfold mean
  rw [List.length_map, sum_map_add_const, add_div, mul_div_cancel_left₀ c hn]

/-- Mean of a scaled list `xs.map (k * ·)`. -/
theorem mean_map_mul_left (numbers : List ℝ) (k : ℝ) :
    mean (numbers.map (fun x => k * x)) = k * mean numbers := by
  unfold mean
  rw [List.length_map, sum_map_mul_left, mul_div_assoc]

/-- Mean of a negated list `xs.map (-·)`. -/
theorem mean_map_neg (numbers : List ℝ) :
    mean (numbers.map (fun x => -x)) = -mean numbers := by
  have h := mean_map_mul_left numbers (-1)
  simpa using h

/-- Mean is invariant under list permutation. -/
theorem mean_perm {numbers₁ numbers₂ : List ℝ} (hp : numbers₁.Perm numbers₂) :
    mean numbers₁ = mean numbers₂ := by
  unfold mean
  rw [hp.sum_eq, hp.length_eq]

/-- If every element of `xs` is `≤ M`, then `xs.sum ≤ xs.length * M`. -/
theorem sum_le_length_mul_of_forall_le (xs : List ℝ) (M : ℝ) (hM : ∀ x ∈ xs, x ≤ M) :
    xs.sum ≤ (xs.length : ℝ) * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ M := hM x List.mem_cons_self
    have hxs : xs.sum ≤ (xs.length : ℝ) * M :=
      ih (fun y hy => hM y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- If every element of `xs` is `≥ m`, then `xs.length * m ≤ xs.sum`. -/
theorem length_mul_le_sum_of_forall_ge (xs : List ℝ) (m : ℝ) (hm : ∀ x ∈ xs, m ≤ x) :
    (xs.length : ℝ) * m ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : m ≤ x := hm x List.mem_cons_self
    have hxs : (xs.length : ℝ) * m ≤ xs.sum :=
      ih (fun y hy => hm y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- In a list of non-negative reals, every member is bounded by the sum of the list. -/
theorem le_sum_of_mem_of_nonneg {xs : List ℝ} (hpos : ∀ y ∈ xs, 0 ≤ y) {x : ℝ} (hx : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · have hys : 0 ≤ ys.sum := List.sum_nonneg (fun z hz => hpos z (List.mem_cons_of_mem x hz))
      linarith
    · have hy : 0 ≤ y := hpos y List.mem_cons_self
      have hle : x ≤ ys.sum := ih (fun z hz => hpos z (List.mem_cons_of_mem y hz)) hmem
      linarith

/-- A list of non-negative reals sums to zero if and only if every element is zero. -/
theorem sum_eq_zero_iff_of_nonneg {xs : List ℝ} (hpos : ∀ y ∈ xs, 0 ≤ y) :
    xs.sum = 0 ↔ ∀ y ∈ xs, y = 0 := by
  constructor
  · intro hsum y hy
    have hle : y ≤ xs.sum := le_sum_of_mem_of_nonneg hpos hy
    have hge : 0 ≤ y := hpos y hy
    linarith
  · exact List.sum_eq_zero

/-- If all elements of a non-empty list equal `c`, its mean is `c`. -/
theorem mean_eq_of_forall_eq {numbers : List ℝ} (h : Pre numbers) {c : ℝ}
    (hc : ∀ x ∈ numbers, x = c) : mean numbers = c := by
  have hn : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero_of_Pre h
  have hsum : numbers.sum = (numbers.length : ℝ) * c := by
    have hle : numbers.sum ≤ (numbers.length : ℝ) * c :=
      sum_le_length_mul_of_forall_le numbers c (fun x hx => le_of_eq (hc x hx))
    have hge : (numbers.length : ℝ) * c ≤ numbers.sum :=
      length_mul_le_sum_of_forall_ge numbers c (fun x hx => ge_of_eq (hc x hx))
    linarith
  unfold mean
  rw [hsum, mul_div_cancel_left₀ c hn]

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1 (Specification Formula): `mean_absolute_deviation` equals the average of absolute
deviations around the arithmetic mean `numbers.sum / numbers.length`. -/
def spec_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers =
    (numbers.map (fun x => |x - numbers.sum / (numbers.length : ℝ)|)).sum / (numbers.length : ℝ)

theorem spec_thm (numbers : List ℝ) (_h : Pre numbers) : spec_prop numbers := by
  rfl

/-- Property 2 (Non-negativity): Mean Absolute Deviation is always non-negative. -/
def nonneg_prop (numbers : List ℝ) : Prop :=
  0 ≤ mean_absolute_deviation numbers

theorem nonneg_thm (numbers : List ℝ) (_h : Pre numbers) : nonneg_prop numbers := by
  unfold nonneg_prop mean_absolute_deviation
  dsimp only
  apply div_nonneg
  · apply List.sum_nonneg
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- Property 3 (Total Absolute Deviation Identity): multiplying MAD by the sample size recovers
the sum of absolute deviations around the mean. -/
def sum_abs_dev_eq_prop (numbers : List ℝ) : Prop :=
  (numbers.length : ℝ) * mean_absolute_deviation numbers =
    (numbers.map (fun x => |x - mean numbers|)).sum

theorem sum_abs_dev_eq_thm (numbers : List ℝ) (h : Pre numbers) :
    sum_abs_dev_eq_prop numbers := by
  unfold sum_abs_dev_eq_prop mean_absolute_deviation
  dsimp only
  exact mul_div_cancel₀ _ (length_cast_ne_zero_of_Pre h)

/-- Property 4 (Zero Sum of Signed Deviations): the signed deviations `x - mean numbers`
around the centerpoint sum to zero. -/
def sum_signed_dev_zero_prop (numbers : List ℝ) : Prop :=
  (numbers.map (fun x => x - mean numbers)).sum = 0

theorem sum_signed_dev_zero_thm (numbers : List ℝ) (h : Pre numbers) :
    sum_signed_dev_zero_prop numbers := by
  unfold sum_signed_dev_zero_prop
  rw [sum_map_sub_const]
  unfold mean
  rw [mul_div_cancel₀ _ (length_cast_ne_zero_of_Pre h), sub_self]

/-- Property 5 (Singleton List): the Mean Absolute Deviation of a single-element list is zero. -/
def singleton_prop (x : ℝ) : Prop :=
  mean_absolute_deviation [x] = 0

theorem singleton_thm (x : ℝ) : singleton_prop x := by
  unfold singleton_prop mean_absolute_deviation mean
  simp

/-- Property 6 (Two-Element List): the Mean Absolute Deviation of `[a, b]` is `|a - b| / 2`. -/
def pair_prop (a b : ℝ) : Prop :=
  mean_absolute_deviation [a, b] = |a - b| / 2

theorem pair_thm (a b : ℝ) : pair_prop a b := by
  unfold pair_prop mean_absolute_deviation mean
  simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.cast_ofNat, List.map_cons, List.map_nil]
  have h1 : a - (a + b) / 2 = (a - b) / 2 := by ring
  have h2 : b - (a + b) / 2 = -((a - b) / 2) := by ring
  have hpos : (0 : ℝ) ≤ 2 := by norm_num
  rw [h1, h2, abs_neg, abs_div, abs_of_nonneg hpos]
  ring

/-- Property 7 (Constant List): if all elements of `numbers` equal `c`, its MAD is zero. -/
def const_zero_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  (∀ x ∈ numbers, x = c) → mean_absolute_deviation numbers = 0

theorem const_zero_thm (numbers : List ℝ) (c : ℝ) (h : Pre numbers) :
    const_zero_prop numbers c := by
  intro hc
  have hm : mean numbers = c := mean_eq_of_forall_eq h hc
  unfold mean_absolute_deviation
  dsimp only
  have hsum : (numbers.map (fun x => |x - mean numbers|)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    rw [hc x hx, hm, sub_self, abs_zero]
  rw [hsum, zero_div]

/-- Property 8 (Zero MAD Characterization): for any non-empty list, MAD equals zero if and only if
every element equals the mean. -/
def eq_zero_iff_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers = 0 ↔ ∀ x ∈ numbers, x = mean numbers

theorem eq_zero_iff_thm (numbers : List ℝ) (h : Pre numbers) : eq_zero_iff_prop numbers := by
  unfold eq_zero_iff_prop mean_absolute_deviation
  dsimp only
  have hn : (numbers.length : ℝ) ≠ 0 := length_cast_ne_zero_of_Pre h
  rw [div_eq_zero_iff, or_iff_left hn]
  have hnonneg : ∀ y ∈ numbers.map (fun x => |x - mean numbers|), 0 ≤ y := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
    exact abs_nonneg _
  rw [sum_eq_zero_iff_of_nonneg hnonneg]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    abs_eq_zero, sub_eq_zero]

/-- Property 9 (Translation / Shift Invariance): adding a constant `c` to every element leaves
the Mean Absolute Deviation unchanged. -/
def translation_invariance_prop (numbers : List ℝ) (c : ℝ) : Prop :=
  mean_absolute_deviation (numbers.map (fun x => x + c)) = mean_absolute_deviation numbers

theorem translation_invariance_thm (numbers : List ℝ) (c : ℝ) (h : Pre numbers) :
    translation_invariance_prop numbers c := by
  unfold translation_invariance_prop mean_absolute_deviation
  dsimp only
  rw [mean_map_add_const h c, List.length_map, List.map_map]
  congr 2
  ext x
  simp [Function.comp, add_sub_add_right_eq_sub]

/-- Property 10 (Scale Equivariance / Absolute Homogeneity): multiplying every element by `k`
scales the Mean Absolute Deviation by `|k|`. -/
def scale_equivariance_prop (numbers : List ℝ) (k : ℝ) : Prop :=
  mean_absolute_deviation (numbers.map (fun x => k * x)) = |k| * mean_absolute_deviation numbers

theorem scale_equivariance_thm (numbers : List ℝ) (k : ℝ) (_h : Pre numbers) :
    scale_equivariance_prop numbers k := by
  unfold scale_equivariance_prop mean_absolute_deviation
  dsimp only
  rw [mean_map_mul_left, List.length_map, List.map_map]
  have hmap :
      List.map ((fun x => |x - k * mean numbers|) ∘ fun x => k * x) numbers =
        (numbers.map (fun x => |x - mean numbers|)).map (fun d => |k| * d) := by
    rw [List.map_map]
    congr 1
    ext x
    simp only [Function.comp_apply, ← mul_sub, abs_mul]
  rw [hmap, sum_map_mul_left, mul_div_assoc]

/-- Property 11 (Negation / Reflection Invariance): negating all elements leaves MAD unchanged. -/
def negation_invariance_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation (numbers.map (fun x => -x)) = mean_absolute_deviation numbers

theorem negation_invariance_thm (numbers : List ℝ) (h : Pre numbers) :
    negation_invariance_prop numbers := by
  unfold negation_invariance_prop
  have hscale := scale_equivariance_thm numbers (-1) h
  simpa [scale_equivariance_prop] using hscale

/-- Property 12 (Permutation Invariance): permuting the input list preserves MAD. -/
def perm_invariance_prop (numbers₁ numbers₂ : List ℝ) : Prop :=
  numbers₁.Perm numbers₂ →
    mean_absolute_deviation numbers₁ = mean_absolute_deviation numbers₂

theorem perm_invariance_thm (numbers₁ numbers₂ : List ℝ) :
    perm_invariance_prop numbers₁ numbers₂ := by
  intro hp
  unfold mean_absolute_deviation
  dsimp only
  rw [mean_perm hp, hp.length_eq, (hp.map (fun x => |x - mean numbers₂|)).sum_eq]

/-- Property 13 (Reversal Invariance): reversing the input list preserves MAD. -/
def reverse_invariance_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers.reverse = mean_absolute_deviation numbers

theorem reverse_invariance_thm (numbers : List ℝ) (_h : Pre numbers) :
    reverse_invariance_prop numbers :=
  perm_invariance_thm numbers.reverse numbers (List.reverse_perm numbers)

/-- Property 14 (Individual Deviation Bound): each element's absolute deviation from the mean
is at most `numbers.length * mean_absolute_deviation numbers`. -/
def single_dev_bound_prop (numbers : List ℝ) : Prop :=
  ∀ x ∈ numbers, |x - mean numbers| ≤ (numbers.length : ℝ) * mean_absolute_deviation numbers

theorem single_dev_bound_thm (numbers : List ℝ) (h : Pre numbers) :
    single_dev_bound_prop numbers := by
  intro x hx
  rw [sum_abs_dev_eq_thm numbers h]
  apply le_sum_of_mem_of_nonneg
  · intro y hy
    rcases List.mem_map.mp hy with ⟨z, _, rfl⟩
    exact abs_nonneg _
  · exact List.mem_map_of_mem hx

/-- Property 15 (Upper Bound by Maximum Deviation): if every element deviates from the mean
by at most `M`, then `mean_absolute_deviation numbers ≤ M`. -/
def upper_bound_prop (numbers : List ℝ) (M : ℝ) : Prop :=
  (∀ x ∈ numbers, |x - mean numbers| ≤ M) → mean_absolute_deviation numbers ≤ M

theorem upper_bound_thm (numbers : List ℝ) (M : ℝ) (h : Pre numbers) :
    upper_bound_prop numbers M := by
  intro hM
  have hn : (0 : ℝ) < (numbers.length : ℝ) := length_cast_pos_of_Pre h
  unfold mean_absolute_deviation
  dsimp only
  rw [div_le_iff₀ hn]
  have hsum :
      (numbers.map (fun x => |x - mean numbers|)).sum ≤ (numbers.length : ℝ) * M := by
    have hlen : (numbers.map (fun x => |x - mean numbers|)).length = numbers.length :=
      List.length_map _
    rw [← hlen]
    apply sum_le_length_mul_of_forall_le
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hM x hx
  linarith

/-- Property 16 (Lower Bound by Minimum Deviation): if every element deviates from the mean
by at least `m`, then `m ≤ mean_absolute_deviation numbers`. -/
def lower_bound_prop (numbers : List ℝ) (m : ℝ) : Prop :=
  (∀ x ∈ numbers, m ≤ |x - mean numbers|) → m ≤ mean_absolute_deviation numbers

theorem lower_bound_thm (numbers : List ℝ) (m : ℝ) (h : Pre numbers) :
    lower_bound_prop numbers m := by
  intro hm
  have hn : (0 : ℝ) < (numbers.length : ℝ) := length_cast_pos_of_Pre h
  unfold mean_absolute_deviation
  dsimp only
  rw [le_div_iff₀ hn]
  have hsum :
      (numbers.length : ℝ) * m ≤ (numbers.map (fun x => |x - mean numbers|)).sum := by
    have hlen : (numbers.map (fun x => |x - mean numbers|)).length = numbers.length :=
      List.length_map _
    rw [← hlen]
    apply length_mul_le_sum_of_forall_ge
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hm x hx
  linarith

/-! ## 6. Post-condition -/

/-- Post-condition combining the exact specification and core mathematical properties of
`mean_absolute_deviation`. -/
def Post_prop (numbers : List ℝ) : Prop :=
  spec_prop numbers ∧
  nonneg_prop numbers ∧
  sum_abs_dev_eq_prop numbers ∧
  sum_signed_dev_zero_prop numbers ∧
  eq_zero_iff_prop numbers ∧
  (∀ c : ℝ, translation_invariance_prop numbers c) ∧
  (∀ k : ℝ, scale_equivariance_prop numbers k) ∧
  negation_invariance_prop numbers ∧
  reverse_invariance_prop numbers ∧
  single_dev_bound_prop numbers ∧
  (∀ M : ℝ, upper_bound_prop numbers M) ∧
  (∀ m : ℝ, lower_bound_prop numbers m)

/-! ## 7. Property-Based Tests (PBTs) -/

/-- Helper to convert a non-empty list of integers `(x :: xs)` into `List ℚ`. -/
def toRatList (x : Int) (xs : List Int) : List ℚ :=
  (x :: xs).map (fun z : Int => (z : ℚ))

/-- Helper to convert a non-empty list of integers `(x :: xs)` into `List Float`. -/
def toFloatList (x : Int) (xs : List Int) : List Float :=
  (x :: xs).map Float.ofInt

-- PBT for `spec_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  mean_absolute_deviation_rat qxs =
    (qxs.map (fun y => |y - qxs.sum / (qxs.length : ℚ)|)).sum / (qxs.length : ℚ))

example : (List.range 20).all (fun n =>
  let fxs := (List.range (n + 1)).map (fun k => Float.ofNat k)
  let expected :=
    (fxs.foldl (fun acc y => acc + Float.abs (y - (fxs.foldl (· + ·) 0.0) / fxs.length.toFloat)) 0.0) /
      fxs.length.toFloat
  mean_absolute_deviation_float fxs == expected) = true := by native_decide

-- PBT for `nonneg_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  0 ≤ mean_absolute_deviation_rat (toRatList x xs))

#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  mean_absolute_deviation_float (toFloatList x xs) ≥ 0.0)

example : (List.range 25).all (fun n =>
  let qxs := (List.range (n + 1)).map (fun k : Nat => (k : ℚ) - 10)
  decide (0 ≤ mean_absolute_deviation_rat qxs)) = true := by native_decide

-- PBT for `sum_abs_dev_eq_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  (qxs.length : ℚ) * mean_absolute_deviation_rat qxs =
    (qxs.map (fun y => |y - mean_rat qxs|)).sum)

example : (List.range 20).all (fun n =>
  let fxs := (List.range (n + 1)).map Float.ofNat
  let lhs := fxs.length.toFloat * mean_absolute_deviation_float fxs
  let rhs := fxs.foldl (fun acc y => acc + Float.abs (y - mean_float fxs)) 0.0
  Float.abs (lhs - rhs) < 1e-6) = true := by native_decide

-- PBT for `sum_signed_dev_zero_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  (qxs.map (fun y => y - mean_rat qxs)).sum = 0)

example : (List.range 20).all (fun n =>
  let fxs := (List.range (n + 1)).map Float.ofNat
  let signed_sum := fxs.foldl (fun acc y => acc + (y - mean_float fxs)) 0.0
  Float.abs signed_sum < 1e-6) = true := by native_decide

-- PBT for `singleton_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ x : Int,
  mean_absolute_deviation_rat [(x : ℚ)] = 0)

#eval Plausible.Testable.check (∀ x : Int,
  mean_absolute_deviation_float [Float.ofInt x] == 0.0)

-- PBT for `pair_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ a b : Int,
  mean_absolute_deviation_rat [(a : ℚ), (b : ℚ)] = |(a : ℚ) - (b : ℚ)| / 2)

#eval Plausible.Testable.check (∀ a b : Int,
  let fa := Float.ofInt a
  let fb := Float.ofInt b
  Float.abs (mean_absolute_deviation_float [fa, fb] - Float.abs (fa - fb) / 2.0) < 1e-6)

-- PBT for `const_zero_prop` and `eq_zero_iff_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (c : Int) (n : Nat),
  let qxs := List.replicate (n % 20 + 1) (c : ℚ)
  mean_absolute_deviation_rat qxs = 0)

#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  (mean_absolute_deviation_rat qxs == 0) = qxs.all (fun y => y == mean_rat qxs))

-- PBT for `translation_invariance_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int) (c : Int),
  let qxs := toRatList x xs
  let qc : ℚ := (c : ℚ)
  mean_absolute_deviation_rat (qxs.map (fun y => y + qc)) = mean_absolute_deviation_rat qxs)

example : (List.range 20).all (fun n =>
  let fxs := (List.range (n + 1)).map Float.ofNat
  let shifted := fxs.map (fun y => y + 7.5)
  Float.abs (mean_absolute_deviation_float shifted - mean_absolute_deviation_float fxs) < 1e-6) = true := by
  native_decide

-- PBT for `scale_equivariance_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int) (k : Int),
  let qxs := toRatList x xs
  let qk : ℚ := (k : ℚ)
  mean_absolute_deviation_rat (qxs.map (fun y => qk * y)) =
    |qk| * mean_absolute_deviation_rat qxs)

example : (List.range 20).all (fun n =>
  let fxs := (List.range (n + 1)).map Float.ofNat
  let scaled := fxs.map (fun y => (-3.5) * y)
  Float.abs (mean_absolute_deviation_float scaled - 3.5 * mean_absolute_deviation_float fxs) < 1e-6) = true := by
  native_decide

-- PBT for `negation_invariance_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  mean_absolute_deviation_rat (qxs.map (fun y => -y)) = mean_absolute_deviation_rat qxs)

#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let fxs := toFloatList x xs
  Float.abs (mean_absolute_deviation_float (fxs.map (fun y => -y)) -
    mean_absolute_deviation_float fxs) < 1e-6)

-- PBT for `perm_invariance_prop` and `reverse_invariance_prop` (Real): tested via executable `Rat` and `Float` counterparts
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  mean_absolute_deviation_rat qxs.reverse = mean_absolute_deviation_rat qxs ∧
  mean_absolute_deviation_rat (qxs.mergeSort (· ≤ ·)) = mean_absolute_deviation_rat qxs)

example : (List.range 20).all (fun n =>
  let fxs := (List.range (n + 1)).map Float.ofNat
  Float.abs (mean_absolute_deviation_float fxs.reverse - mean_absolute_deviation_float fxs) < 1e-6) = true := by
  native_decide

-- PBT for `single_dev_bound_prop`, `upper_bound_prop`, and `lower_bound_prop` (Real): tested via executable `Rat` counterpart
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  let m := mean_rat qxs
  let mad := mean_absolute_deviation_rat qxs
  qxs.all (fun y => decide (|y - m| ≤ (qxs.length : ℚ) * mad)))

#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  let devs := qxs.map (fun y => |y - mean_rat qxs|)
  let maxDev := devs.foldl max 0
  let minDev := devs.foldl min (devs.headD 0)
  minDev ≤ mean_absolute_deviation_rat qxs ∧ mean_absolute_deviation_rat qxs ≤ maxDev)

/-- Executable Boolean check corresponding to `Post_prop` over `ℚ`. -/
def check_post_rat (x : Int) (xs : List Int) (c k : Int) : Bool :=
  let qxs := toRatList x xs
  let qc : ℚ := (c : ℚ)
  let qk : ℚ := (k : ℚ)
  let m := mean_rat qxs
  let mad := mean_absolute_deviation_rat qxs
  decide (mad = (qxs.map (fun y => |y - qxs.sum / (qxs.length : ℚ)|)).sum / (qxs.length : ℚ)) &&
  decide (0 ≤ mad) &&
  decide ((qxs.length : ℚ) * mad = (qxs.map (fun y => |y - m|)).sum) &&
  decide ((qxs.map (fun y => y - m)).sum = 0) &&
  ((mad == 0) == qxs.all (fun y => y == m)) &&
  decide (mean_absolute_deviation_rat (qxs.map (fun y => y + qc)) = mad) &&
  decide (mean_absolute_deviation_rat (qxs.map (fun y => qk * y)) = |qk| * mad) &&
  decide (mean_absolute_deviation_rat (qxs.map (fun y => -y)) = mad) &&
  decide (mean_absolute_deviation_rat qxs.reverse = mad) &&
  qxs.all (fun y => decide (|y - m| ≤ (qxs.length : ℚ) * mad))

-- PBT for `Post_prop` (Real): combined executable check over `Rat`
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int) (c k : Int),
  check_post_rat x xs c k = true)

example : (List.range 15).all (fun n =>
  check_post_rat (Int.ofNat n) [1, -3, 5, 2] 4 (-2)) = true := by native_decide

/-! ## 8. Correctness Theorem (`Pre → Post`) -/

/-- Main correctness theorem: for any input list `numbers` satisfying `Pre numbers`
(i.e. `numbers ≠ []`), `Post_prop numbers` holds. -/
theorem mean_absolute_deviation_correct (numbers : List ℝ) (h : Pre numbers) :
    Post_prop numbers :=
  ⟨spec_thm numbers h,
   nonneg_thm numbers h,
   sum_abs_dev_eq_thm numbers h,
   sum_signed_dev_zero_thm numbers h,
   eq_zero_iff_thm numbers h,
   fun c => translation_invariance_thm numbers c h,
   fun k => scale_equivariance_thm numbers k h,
   negation_invariance_thm numbers h,
   reverse_invariance_thm numbers h,
   single_dev_bound_thm numbers h,
   fun M => upper_bound_thm numbers M h,
   fun m => lower_bound_thm numbers m h⟩

/-! ## 9. Imperative Implementations -/

/-- Imperative implementation of `mean_absolute_deviation` over `ℝ` using `Id.run do`
and mutable accumulators. -/
noncomputable def mean_absolute_deviation_imp (numbers : List ℝ) : ℝ := Id.run do
  let mut total : ℝ := 0
  for x in numbers do
    total := total + x
  let n : ℝ := (numbers.length : ℝ)
  let m : ℝ := total / n
  let mut dev_sum : ℝ := 0
  for x in numbers do
    dev_sum := dev_sum + |x - m|
  return dev_sum / n

/-- Executable imperative implementation of `mean_absolute_deviation` over `Float`
using `Id.run do` and mutable accumulators. -/
def mean_absolute_deviation_float_imp (numbers : List Float) : Float := Id.run do
  let mut total : Float := 0.0
  for x in numbers do
    total := total + x
  let n : Float := numbers.length.toFloat
  let m : Float := total / n
  let mut dev_sum : Float := 0.0
  for x in numbers do
    dev_sum := dev_sum + Float.abs (x - m)
  return dev_sum / n

/-- Executable imperative implementation of `mean_absolute_deviation` over `ℚ`
using `Id.run do` and mutable accumulators. -/
def mean_absolute_deviation_rat_imp (numbers : List ℚ) : ℚ := Id.run do
  let mut total : ℚ := 0
  for x in numbers do
    total := total + x
  let n : ℚ := (numbers.length : ℚ)
  let m : ℚ := total / n
  let mut dev_sum : ℚ := 0
  for x in numbers do
    dev_sum := dev_sum + |x - m|
  return dev_sum / n

/-! ## 10. Imperative Tests -/

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide

example : mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0] == 1.0 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide

example : mean_absolute_deviation_rat_imp [1, 2, 3] = 2 / 3 := by
  native_decide

example : mean_absolute_deviation_rat_imp [1, 2, 3, 4] = 1 := by
  native_decide

example : mean_absolute_deviation_rat_imp [1, 2, 3, 4, 5] = 6 / 5 := by
  native_decide

#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0]
#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0, 5.0]
#eval mean_absolute_deviation_rat_imp [1, 2, 3]
#eval mean_absolute_deviation_rat_imp [1, 2, 3, 4]
#eval mean_absolute_deviation_rat_imp [1, 2, 3, 4, 5]

/-! ## 11. Functional-Imperative Equivalence Theorems -/

/-- Helper lemma: left fold of addition over a list in an `AddCommMonoid` equals `acc + xs.sum`. -/
theorem foldl_add_eq_add_sum {α : Type*} [AddCommMonoid α] (xs : List α) (acc : α) :
    xs.foldl (fun s x => s + x) acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih (acc + x), add_assoc]

/-- Helper lemma: left fold of mapped addition over a list in an `AddCommMonoid`
equals `acc + (xs.map f).sum`. -/
theorem foldl_add_map_eq_add_sum {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) (acc : β) :
    xs.foldl (fun s x => s + f x) acc = acc + (xs.map f).sum := by
  rw [← List.foldl_map, foldl_add_eq_add_sum]

/-- Equivalence theorem for `Real`: the functional and imperative implementations over `ℝ`
produce identical results for all input lists. -/
theorem mean_absolute_deviation_equiv (numbers : List ℝ) :
    mean_absolute_deviation numbers = mean_absolute_deviation_imp numbers := by
  unfold mean_absolute_deviation mean mean_absolute_deviation_imp
  simp [foldl_add_eq_add_sum, foldl_add_map_eq_add_sum]

/-- Equivalence theorem for `Float`: the functional and imperative implementations over `Float`
produce identical results for all input lists. -/
theorem mean_absolute_deviation_float_equiv (numbers : List Float) :
    mean_absolute_deviation_float numbers = mean_absolute_deviation_float_imp numbers := by
  unfold mean_absolute_deviation_float mean_float mean_absolute_deviation_float_imp
  simp

/-- Equivalence theorem for `Rat`: the functional and imperative implementations over `ℚ`
produce identical results for all input lists. -/
theorem mean_absolute_deviation_rat_equiv (numbers : List ℚ) :
    mean_absolute_deviation_rat numbers = mean_absolute_deviation_rat_imp numbers := by
  unfold mean_absolute_deviation_rat mean_rat mean_absolute_deviation_rat_imp
  simp [foldl_add_eq_add_sum, foldl_add_map_eq_add_sum]

-- PBT for functional-imperative equivalence
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let fxs := toFloatList x xs
  mean_absolute_deviation_float fxs == mean_absolute_deviation_float_imp fxs)

#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  let qxs := toRatList x xs
  mean_absolute_deviation_rat qxs = mean_absolute_deviation_rat_imp qxs)

end humaneval_4_mean_absolute_deviation

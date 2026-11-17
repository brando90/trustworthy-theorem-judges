import Mathlib

/-!
# HumanEval/4 — Mean Absolute Deviation

Python source: `mean_absolute_deviation(numbers)`.

For a nonempty list, the mean absolute deviation about the mean is

`MAD = average |x - mean|`, where `mean = (sum of the list) / (length of the list)`.

The Python function divides by `len(numbers)` and therefore raises `ZeroDivisionError`
on the empty list. That domain is `Pre`.

Numeric layers:

* `Float` — executable mirror of Python `float`, used for the ground tests.
* `Rat` — exact executable arithmetic, used for property-based tests.
* `Real` — mathematical model. Property, correctness, and equivalence theorems
  are stated here. `rat_real_correspondence_thm` identifies the `Rat` and `Real`
  functions on rational inputs.

In Mathlib a field satisfies `a / 0 = 0`. The identities below are true for every
finite list under that convention, including the empty list. They restrict to the
Python domain through `Pre`.
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## Implementation -/

/-- Executable Python `float` mirror of `mean_absolute_deviation`. -/
def mean_absolute_deviation_float (numbers : List Float) : Float :=
  let n := numbers.length.toFloat
  let mean := numbers.foldl (fun acc x => acc + x) 0 / n
  (numbers.map (fun x => Float.abs (x - mean))).foldl (fun acc x => acc + x) 0 / n

/-- Exact mean, as a rational. -/
def mean_rat (numbers : List ℚ) : ℚ :=
  numbers.sum / (numbers.length : ℚ)

/-- Exact mean absolute deviation, as a rational. -/
def mean_absolute_deviation_rat (numbers : List ℚ) : ℚ :=
  (numbers.map (fun x => |x - mean_rat numbers|)).sum / (numbers.length : ℚ)

/-- Arithmetic mean of a list of reals. -/
noncomputable def mean (numbers : List ℝ) : ℝ :=
  numbers.sum / (numbers.length : ℝ)

/-- Mean absolute deviation about the mean.

`mean_absolute_deviation numbers = (∑ |x - mean numbers|) / length numbers`. -/
noncomputable def mean_absolute_deviation (numbers : List ℝ) : ℝ :=
  (numbers.map (fun x => |x - mean numbers|)).sum / (numbers.length : ℝ)

/-! ## Unit tests -/

-- Python `check`: absolute error below `1e-6`.
example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0] - (2.0 / 3.0)) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide

example :
    Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0, 5.0] - (6.0 / 5.0)) < 1e-6 := by
  native_decide

example : (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] == 1.0) = true := by
  native_decide

#eval mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0]

-- Exact rational values of the same three tests.
example : mean_absolute_deviation_rat [1, 2, 3] = 2 / 3 := by native_decide
example : mean_absolute_deviation_rat [1, 2, 3, 4] = 1 := by native_decide
example : mean_absolute_deviation_rat [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

#eval mean_absolute_deviation_rat [1, 2, 3, 4]

/-! ## Precondition -/

/-- The Python function is defined precisely on nonempty lists. -/
def Pre {α : Type*} (numbers : List α) : Prop :=
  numbers ≠ []

/-! ## Properties -/

lemma length_cast_ne_zero {numbers : List ℝ} (h : numbers ≠ []) :
    (numbers.length : ℝ) ≠ 0 := by
  exact_mod_cast (List.length_pos_iff.mpr h).ne'

lemma sum_map_add_const (numbers : List ℝ) (c : ℝ) :
    (numbers.map (fun x => x + c)).sum = numbers.sum + (numbers.length : ℝ) * c := by
  induction numbers with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.cast_succ]
    ring

lemma mean_add_const (numbers : List ℝ) (c : ℝ) (h : numbers ≠ []) :
    mean (numbers.map (fun x => x + c)) = mean numbers + c := by
  unfold mean
  rw [List.length_map, sum_map_add_const, add_div,
    mul_div_cancel_left₀ c (length_cast_ne_zero h)]

lemma sum_map_mul_const (numbers : List ℝ) (c : ℝ) :
    (numbers.map (fun x => x * c)).sum = numbers.sum * c := by
  induction numbers with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma mean_mul_const (numbers : List ℝ) (c : ℝ) :
    mean (numbers.map (fun x => x * c)) = mean numbers * c := by
  unfold mean
  rw [List.length_map, sum_map_mul_const]
  calc
    (numbers.sum * c) / (numbers.length : ℝ)
        = (c * numbers.sum) / (numbers.length : ℝ) := by rw [mul_comm numbers.sum c]
      _ = c * (numbers.sum / (numbers.length : ℝ)) := mul_div_assoc _ _ _
      _ = numbers.sum / (numbers.length : ℝ) * c := by rw [mul_comm]

/-- The returned value is the average absolute deviation from the mean. -/
def formula_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers =
    (numbers.map (fun x => |x - mean numbers|)).sum / (numbers.length : ℝ)

theorem formula_thm (numbers : List ℝ) : formula_prop numbers := rfl

/-- Cleared-denominator form of the Python formula. -/
def spec_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers * (numbers.length : ℝ) =
    (numbers.map (fun x => |x - mean numbers|)).sum

theorem spec_thm (numbers : List ℝ) : spec_prop numbers := by
  unfold spec_prop mean_absolute_deviation
  by_cases h : (numbers.length : ℝ) = 0
  · have hlen : numbers.length = 0 := by exact_mod_cast h
    have hempty : numbers = [] := List.length_eq_zero_iff.mp hlen
    simp [hempty]
  · exact div_mul_cancel₀ _ h

/-- Mean absolute deviation is nonnegative. -/
def nonneg_prop (numbers : List ℝ) : Prop :=
  0 ≤ mean_absolute_deviation numbers

theorem nonneg_thm (numbers : List ℝ) : nonneg_prop numbers := by
  unfold nonneg_prop mean_absolute_deviation
  apply div_nonneg
  · apply List.sum_nonneg
    intro y hy
    rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- The deviation is zero exactly when every element equals the mean. -/
def zero_iff_eq_mean_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers = 0 ↔ ∀ x ∈ numbers, x = mean numbers

theorem zero_iff_eq_mean_thm (numbers : List ℝ) : zero_iff_eq_mean_prop numbers := by
  unfold zero_iff_eq_mean_prop
  constructor
  · intro hz x hx
    by_cases hne : numbers = []
    · simp [hne] at hx
    · have hn := length_cast_ne_zero hne
      unfold mean_absolute_deviation at hz
      rw [div_eq_zero_iff] at hz
      rcases hz with hsum | hlen
      · have hnonneg : ∀ y ∈ numbers.map (fun y => |y - mean numbers|), 0 ≤ y := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
          exact abs_nonneg _
        have hx0 : |x - mean numbers| = 0 :=
          List.all_zero_of_le_zero_le_of_sum_eq_zero hnonneg hsum
            (List.mem_map.mpr ⟨x, hx, rfl⟩)
        exact eq_of_sub_eq_zero (abs_eq_zero.mp hx0)
      · exact absurd hlen hn
  · intro hall
    unfold mean_absolute_deviation
    have hsum : (numbers.map (fun y => |y - mean numbers|)).sum = 0 := by
      apply List.sum_eq_zero
      intro y hy
      rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
      simp [hall z hz]
    simp [hsum]

lemma mean_eq_of_constant {numbers : List ℝ} {a : ℝ}
    (h : ∀ x ∈ numbers, x = a) (hne : numbers ≠ []) : mean numbers = a := by
  unfold mean
  have hs : numbers.sum = (numbers.length : ℝ) * a := by
    simpa [nsmul_eq_mul] using List.sum_eq_card_nsmul numbers a h
  rw [hs, mul_div_cancel_left₀ a (length_cast_ne_zero hne)]

/-- The deviation is zero exactly when all elements are equal. -/
def zero_iff_constant_prop (numbers : List ℝ) : Prop :=
  mean_absolute_deviation numbers = 0 ↔ ∀ x ∈ numbers, ∀ y ∈ numbers, x = y

theorem zero_iff_constant_thm (numbers : List ℝ) : zero_iff_constant_prop numbers := by
  unfold zero_iff_constant_prop
  have hmean := zero_iff_eq_mean_thm numbers
  unfold zero_iff_eq_mean_prop at hmean
  rw [hmean]
  constructor
  · intro hall x hx y hy
    rw [hall x hx, hall y hy]
  · intro hall x hx
    have hconst : ∀ y ∈ numbers, y = x := fun y hy => hall y hy x hx
    have hne : numbers ≠ [] := List.length_pos_iff.mp (List.length_pos_of_mem hx)
    exact (mean_eq_of_constant hconst hne).symm

/-- Adding a constant to every element does not change the deviation. -/
def translation_invariance_prop (numbers : List ℝ) : Prop :=
  ∀ c : ℝ,
    mean_absolute_deviation (numbers.map (fun x => x + c)) =
      mean_absolute_deviation numbers

theorem translation_invariance_thm (numbers : List ℝ) :
    translation_invariance_prop numbers := by
  intro c
  cases numbers with
  | nil => simp [mean_absolute_deviation, mean]
  | cons hd tl =>
    have hne : (hd :: tl) ≠ [] := List.cons_ne_nil _ _
    have hmap :
        ((hd :: tl).map (fun x => x + c)).map
            (fun y => |y - mean ((hd :: tl).map (fun x => x + c))|)
          = (hd :: tl).map (fun x => |x - mean (hd :: tl)|) := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro x _
      rw [mean_add_const (hd :: tl) c hne]
      change |x + c - (mean (hd :: tl) + c)| = |x - mean (hd :: tl)|
      have hsub : x + c - (mean (hd :: tl) + c) = x - mean (hd :: tl) := by abel
      rw [hsub]
    unfold mean_absolute_deviation
    rw [List.length_map, hmap]

/-- Scaling every element by `c` scales the deviation by `|c|`. -/
def homogeneity_prop (numbers : List ℝ) : Prop :=
  ∀ c : ℝ,
    mean_absolute_deviation (numbers.map (fun x => x * c)) =
      |c| * mean_absolute_deviation numbers

theorem homogeneity_thm (numbers : List ℝ) : homogeneity_prop numbers := by
  intro c
  have hmap :
      (numbers.map (fun x => x * c)).map
          (fun y => |y - mean (numbers.map (fun x => x * c))|)
        = numbers.map (fun x => |x - mean numbers| * |c|) := by
    rw [List.map_map, mean_mul_const]
    refine List.map_congr_left ?_
    intro x _
    change |x * c - mean numbers * c| = |x - mean numbers| * |c|
    rw [show x * c - mean numbers * c = (x - mean numbers) * c by ring, abs_mul]
  unfold mean_absolute_deviation
  rw [List.length_map, hmap, List.sum_map_mul_right]
  calc
    ((numbers.map (fun x => |x - mean numbers|)).sum * |c|) / (numbers.length : ℝ)
        = (|c| * (numbers.map (fun x => |x - mean numbers|)).sum) / (numbers.length : ℝ) := by
          rw [mul_comm]
      _ = |c| * ((numbers.map (fun x => |x - mean numbers|)).sum / (numbers.length : ℝ)) :=
          mul_div_assoc _ _ _

/-- The deviation depends only on the multiset of values. -/
def permutation_invariance_prop (numbers : List ℝ) : Prop :=
  ∀ ys : List ℝ, numbers.Perm ys →
    mean_absolute_deviation numbers = mean_absolute_deviation ys

theorem permutation_invariance_thm (numbers : List ℝ) :
    permutation_invariance_prop numbers := by
  intro ys hperm
  have hlen : numbers.length = ys.length := hperm.length_eq
  have hsum : numbers.sum = ys.sum := hperm.sum_eq
  have hmean : mean numbers = mean ys := by
    unfold mean
    rw [hlen, hsum]
  unfold mean_absolute_deviation
  rw [hlen]
  have hp :
      (numbers.map fun x => |x - mean numbers|).Perm
        (ys.map fun y => |y - mean ys|) := by
    rw [hmean]
    exact hperm.map (fun y => |y - mean ys|)
  rw [hp.sum_eq]

/-- A one-element dataset has deviation zero. -/
def singleton_prop (x : ℝ) : Prop :=
  mean_absolute_deviation [x] = 0

theorem singleton_thm (x : ℝ) : singleton_prop x := by
  simp [singleton_prop, mean_absolute_deviation, mean]

/-- Deviation of a pair is half the distance between its elements. -/
def two_point_prop (a b : ℝ) : Prop :=
  mean_absolute_deviation [a, b] = |a - b| / 2

theorem two_point_thm (a b : ℝ) : two_point_prop a b := by
  unfold two_point_prop mean_absolute_deviation mean
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  have hlen : ((0 + 1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [hlen]
  have h1 : a - (a + (b + 0)) / 2 = (a - b) / 2 := by ring
  have h2 : b - (a + (b + 0)) / 2 = (b - a) / 2 := by ring
  rw [h1, h2, abs_div, abs_div]
  have hab : |b - a| = |a - b| := by rw [← abs_neg, neg_sub]
  rw [hab, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  field_simp

lemma cast_sum_abs_dev (numbers : List ℚ) (μ : ℚ) :
    (List.map (fun q : ℚ => |(q : ℝ) - (μ : ℝ)|) numbers).sum
      = (((List.map (fun q : ℚ => |q - μ|) numbers).sum) : ℝ) := by
  induction numbers with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [Rat.cast_add, ← Rat.cast_sub, ← Rat.cast_abs]

lemma mean_rat_real_correspondence (numbers : List ℚ) :
    mean (List.map (Rat.cast : ℚ → ℝ) numbers) = (mean_rat numbers : ℝ) := by
  simp [mean, mean_rat, List.length_map, Rat.cast_list_sum, Rat.cast_div, Rat.cast_natCast]

/-- On rational inputs the real function agrees with the exact rational function. -/
theorem rat_real_correspondence_thm (numbers : List ℚ) :
    mean_absolute_deviation (List.map (Rat.cast : ℚ → ℝ) numbers) =
      (mean_absolute_deviation_rat numbers : ℝ) := by
  simp only [mean_absolute_deviation, mean_absolute_deviation_rat, List.length_map]
  rw [mean_rat_real_correspondence, List.map_map]
  have hs := cast_sum_abs_dev numbers (mean_rat numbers)
  have hs' :
      (List.map ((fun x => |x - (mean_rat numbers : ℝ)|) ∘ Rat.cast) numbers).sum
        = (((List.map (fun q : ℚ => |q - mean_rat numbers|) numbers).sum) : ℝ) := by
    simpa [Function.comp] using hs
  rw [hs']
  simp [Rat.cast_div, Rat.cast_natCast]

/-- Docstring example: `mean_absolute_deviation([1.0, 2.0, 3.0, 4.0]) = 1.0`. -/
def docstring_example_prop : Prop :=
  mean_absolute_deviation [(1 : ℝ), 2, 3, 4] = 1

theorem docstring_example_thm : docstring_example_prop := by
  unfold docstring_example_prop
  simp [mean_absolute_deviation, mean]
  have ha : (1 : ℝ) - (1 + (2 + (3 + 4))) / 4 = -(3 / 2) := by norm_num
  have hb : (2 : ℝ) - (1 + (2 + (3 + 4))) / 4 = -(1 / 2) := by norm_num
  have hc : (3 : ℝ) - (1 + (2 + (3 + 4))) / 4 = 1 / 2 := by norm_num
  have hd : (4 : ℝ) - (1 + (2 + (3 + 4))) / 4 = 3 / 2 := by norm_num
  rw [ha, hb, hc, hd, abs_neg, abs_neg]
  have h1 : |(3 / 2 : ℝ)| = 3 / 2 := abs_of_nonneg (by norm_num)
  have h2 : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  rw [h1, h2]
  norm_num

/-- Python check: `mean_absolute_deviation([1.0, 2.0, 3.0]) = 2/3`. -/
def check_three_prop : Prop :=
  mean_absolute_deviation [(1 : ℝ), 2, 3] = 2 / 3

theorem check_three_thm : check_three_prop := by
  unfold check_three_prop
  simp [mean_absolute_deviation, mean]
  norm_num

/-- Python check: `mean_absolute_deviation([1.0, 2.0, 3.0, 4.0, 5.0]) = 6/5`. -/
def check_five_prop : Prop :=
  mean_absolute_deviation [(1 : ℝ), 2, 3, 4, 5] = 6 / 5

theorem check_five_thm : check_five_prop := by
  unfold check_five_prop
  simp [mean_absolute_deviation, mean]
  norm_num

/-! ## Postcondition -/

/-- Properties of the value returned for a list of real numbers. -/
def Post_prop (numbers : List ℝ) : Prop :=
  formula_prop numbers ∧
  spec_prop numbers ∧
  nonneg_prop numbers ∧
  zero_iff_eq_mean_prop numbers ∧
  zero_iff_constant_prop numbers ∧
  translation_invariance_prop numbers ∧
  homogeneity_prop numbers ∧
  permutation_invariance_prop numbers

/-! ## Property-based tests -/

-- The `_prop` statements quantify over `Real`, whose order is not computable.
-- Each test below is the executable Rat (or Float) counterpart.
-- `rat_real_correspondence_thm` identifies that Rat function with the Real
-- function on rational inputs, which is the domain of these checks.
-- PBT: not executable directly (`nonneg_prop`, `Real` comparison).

private def pbtCfg : Plausible.Configuration :=
  { numInst := 40, maxSize := 12, quiet := true }

#eval Plausible.Testable.check
  (∀ xs : List Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    decide (0 ≤ mean_absolute_deviation_rat ys) = true)
  pbtCfg

-- PBT for `zero_iff_eq_mean_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ xs : List Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    let m := mean_absolute_deviation_rat ys
    let μ := mean_rat ys
    ((m == 0) == ys.all (fun x => x == μ)) = true)
  pbtCfg

-- PBT for `zero_iff_constant_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ xs : List Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    let m := mean_absolute_deviation_rat ys
    ((m == 0) == ys.all (fun x => ys.all (fun y => x == y))) = true)
  pbtCfg

-- PBT for `translation_invariance_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ xs : List Int, ∀ c : Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    mean_absolute_deviation_rat (ys.map (fun x => x + (c : ℚ))) =
      mean_absolute_deviation_rat ys)
  pbtCfg

-- PBT for `homogeneity_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ xs : List Int, ∀ c : Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    mean_absolute_deviation_rat (ys.map (fun x => x * (c : ℚ))) =
      |(c : ℚ)| * mean_absolute_deviation_rat ys)
  pbtCfg

-- PBT for `permutation_invariance_prop` via the Rat layer.
-- Every rotation is a permutation (`List.rotate_perm`); the Boolean guard
-- evaluates that fact and then checks the deviation.
#eval Plausible.Testable.check
  (∀ xs : List Int, ∀ k : Nat,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    let zs := ys.rotate k
    ((!decide (List.Perm ys zs)) ||
      (mean_absolute_deviation_rat ys == mean_absolute_deviation_rat zs)) = true)
  pbtCfg

-- PBT for `spec_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ xs : List Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    mean_absolute_deviation_rat ys * (ys.length : ℚ) =
      (ys.map (fun x => |x - mean_rat ys|)).sum)
  pbtCfg

-- PBT for `formula_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ xs : List Int,
    let ys : List ℚ := xs.map (fun n => (n : ℚ))
    mean_absolute_deviation_rat ys =
      (ys.map (fun x => |x - mean_rat ys|)).sum / (ys.length : ℚ))
  pbtCfg

-- PBT for `singleton_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ a : Int, mean_absolute_deviation_rat [(a : ℚ)] = 0)
  pbtCfg

-- PBT for `two_point_prop` via the Rat layer.
#eval Plausible.Testable.check
  (∀ a b : Int,
    mean_absolute_deviation_rat [(a : ℚ), (b : ℚ)] = |(a : ℚ) - (b : ℚ)| / 2)
  pbtCfg

-- PBT for the ground-truth Real properties `docstring_example_prop`,
-- `check_three_prop`, and `check_five_prop`: their Rat counterparts are the
-- closed unit tests above. Bounded Float checks of the same inputs:
example :
    (List.range 3).all (fun i =>
      match i with
      | 0 =>
        Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0] - (2.0 / 3.0)) < 1e-6
      | 1 =>
        Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6
      | _ =>
        Float.abs (mean_absolute_deviation_float [1.0, 2.0, 3.0, 4.0, 5.0] - (6.0 / 5.0)) < 1e-6)
    = true := by
  native_decide

-- Bounded Rat checks of nonnegativity, translation, homogeneity, and the
-- zero-on-constants case of `zero_iff_constant_prop`.
example :
    (List.range 8).all (fun n =>
      let ys : List ℚ := (List.range (n + 1)).map (fun i => (i : ℚ) - 3)
      let constant : List ℚ := List.replicate (n + 1) 4
      decide (0 ≤ mean_absolute_deviation_rat ys) &&
        (mean_absolute_deviation_rat (ys.map (fun x => x + 5)) ==
          mean_absolute_deviation_rat ys) &&
        (mean_absolute_deviation_rat (ys.map (fun x => x * (-2))) ==
          |(-2 : ℚ)| * mean_absolute_deviation_rat ys) &&
        (mean_absolute_deviation_rat constant == 0)) = true := by
  native_decide

-- Bounded Float counterpart of `nonneg_prop`, `singleton_prop`, and
-- `translation_invariance_prop` on small integers (exact in binary64).
example :
    (List.range 8).all (fun n =>
      let xs := (List.range (n + 1)).map (fun i => Float.ofNat i)
      decide (0 ≤ mean_absolute_deviation_float xs) &&
        (mean_absolute_deviation_float [Float.ofNat n] == 0) &&
        (mean_absolute_deviation_float (xs.map (fun x => x + 3.0)) ==
          mean_absolute_deviation_float xs)) = true := by
  native_decide

/-- Executable Rat form of `Post_prop`, at a sampled shift, scale, and rotation. -/
def rat_post_ok (ys : List ℚ) (c : ℚ) (k : Nat) : Bool :=
  let m := mean_absolute_deviation_rat ys
  let μ := mean_rat ys
  let shifted := mean_absolute_deviation_rat (ys.map (fun x => x + c))
  let scaled := mean_absolute_deviation_rat (ys.map (fun x => x * c))
  let rotated := ys.rotate k
  decide (0 ≤ m) &&
    ((m == 0) == ys.all (fun x => x == μ)) &&
    ((m == 0) == ys.all (fun x => ys.all (fun y => x == y))) &&
    (shifted == m) &&
    (scaled == |c| * m) &&
    (m * (ys.length : ℚ) == (ys.map (fun x => |x - μ|)).sum) &&
    (m == (ys.map (fun x => |x - μ|)).sum / (ys.length : ℚ)) &&
    ((!decide (List.Perm ys rotated)) || (mean_absolute_deviation_rat rotated == m))

-- PBT for `Post_prop` via `rat_post_ok`.
#eval Plausible.Testable.check
  (∀ xs : List Int, ∀ c : Int, ∀ k : Nat,
    rat_post_ok (xs.map (fun n => (n : ℚ))) (c : ℚ) k = true)
  pbtCfg

/-! ## Correctness -/

theorem correctness_thm (numbers : List ℝ) (h : Pre numbers) : Post_prop numbers := by
  have : numbers ≠ [] := h
  exact ⟨formula_thm numbers, spec_thm numbers, nonneg_thm numbers,
    zero_iff_eq_mean_thm numbers, zero_iff_constant_thm numbers,
    translation_invariance_thm numbers, homogeneity_thm numbers,
    permutation_invariance_thm numbers⟩

/-! ## Imperative implementation -/

/-- Imperative Python-style loop over `Float`, using mutable accumulators. -/
def mean_absolute_deviation_float_imp (numbers : List Float) : Float :=
  Id.run do
    let mut total : Float := 0
    for x in numbers do
      total := total + x
    let mean := total / numbers.length.toFloat
    let mut acc : Float := 0
    for x in numbers do
      acc := acc + Float.abs (x - mean)
    return acc / numbers.length.toFloat

/-- Imperative loop over rationals. -/
def mean_absolute_deviation_rat_imp (numbers : List ℚ) : ℚ :=
  Id.run do
    let mut total : ℚ := 0
    for x in numbers do
      total := total + x
    let mean := total / (numbers.length : ℚ)
    let mut acc : ℚ := 0
    for x in numbers do
      acc := acc + |x - mean|
    return acc / (numbers.length : ℚ)

/-- Imperative loop over reals. Same control flow as the Python function. -/
noncomputable def mean_absolute_deviation_imp (numbers : List ℝ) : ℝ :=
  Id.run do
    let mut total : ℝ := 0
    for x in numbers do
      total := total + x
    let mean := total / (numbers.length : ℝ)
    let mut acc : ℝ := 0
    for x in numbers do
      acc := acc + |x - mean|
    return acc / (numbers.length : ℝ)

/-! ## Imperative tests -/

example :
    Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0] - (2.0 / 3.0)) < 1e-6 := by
  native_decide

example : Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide

example :
    Float.abs (mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0, 5.0] - (6.0 / 5.0))
      < 1e-6 := by
  native_decide

#eval mean_absolute_deviation_float_imp [1.0, 2.0, 3.0, 4.0]

example : mean_absolute_deviation_rat_imp [1, 2, 3] = 2 / 3 := by native_decide
example : mean_absolute_deviation_rat_imp [1, 2, 3, 4] = 1 := by native_decide
example : mean_absolute_deviation_rat_imp [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

#eval mean_absolute_deviation_rat_imp [1, 2, 3, 4, 5]

/-! ## Equivalence -/

section FoldEquiv
variable {α : Type*} [AddCommGroup α]

lemma foldl_add_eq_sum (xs : List α) (acc : α) :
    xs.foldl (fun s x => s + x) acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    abel

lemma foldl_add_map (f : α → α) (xs : List α) (acc : α) :
    xs.foldl (fun s x => s + f x) acc = acc + (xs.map f).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    abel

end FoldEquiv

lemma foldl_float_map (f : Float → Float) (xs : List Float) (acc : Float) :
    xs.foldl (fun s x => s + f x) acc = (xs.map f).foldl (fun s x => s + x) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons _ tl ih =>
    simp only [List.foldl_cons, List.map_cons, ih]

/-- The real functional and imperative implementations agree. -/
theorem equivalence_thm (numbers : List ℝ) :
    mean_absolute_deviation numbers = mean_absolute_deviation_imp numbers := by
  simp [mean_absolute_deviation, mean_absolute_deviation_imp, mean]
  have h1 : numbers.foldl (fun b a => b + a) 0 = numbers.sum := by
    simpa using foldl_add_eq_sum numbers 0
  rw [h1]
  have h2 :
      numbers.foldl (fun b a => b + |a - numbers.sum / (numbers.length : ℝ)|) 0
        = (numbers.map (fun a => |a - numbers.sum / (numbers.length : ℝ)|)).sum := by
    simpa using foldl_add_map (fun a => |a - numbers.sum / (numbers.length : ℝ)|) numbers 0
  rw [h2]

theorem rat_equivalence_thm (numbers : List ℚ) :
    mean_absolute_deviation_rat numbers = mean_absolute_deviation_rat_imp numbers := by
  simp [mean_absolute_deviation_rat, mean_absolute_deviation_rat_imp, mean_rat]
  have h1 : numbers.foldl (fun b a => b + a) 0 = numbers.sum := by
    simpa using foldl_add_eq_sum numbers 0
  rw [h1]
  have h2 :
      numbers.foldl (fun b a => b + |a - numbers.sum / (numbers.length : ℚ)|) 0
        = (numbers.map (fun a => |a - numbers.sum / (numbers.length : ℚ)|)).sum := by
    simpa using foldl_add_map (fun a => |a - numbers.sum / (numbers.length : ℚ)|) numbers 0
  rw [h2]

theorem float_equivalence_thm (numbers : List Float) :
    mean_absolute_deviation_float numbers = mean_absolute_deviation_float_imp numbers := by
  simp [mean_absolute_deviation_float, mean_absolute_deviation_float_imp]
  congr 1
  simpa using
    (foldl_float_map
      (fun a =>
        Float.abs (a - numbers.foldl (fun s x => s + x) 0 / numbers.length.toFloat))
      numbers 0).symm

end humaneval_4_mean_absolute_deviation

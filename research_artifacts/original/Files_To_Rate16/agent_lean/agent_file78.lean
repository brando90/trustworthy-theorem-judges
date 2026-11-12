import Mathlib

/-!
# HumanEval/4: mean absolute deviation

The executable layer uses `Float`, left-to-right summation, and the two passes
of the Python program. The input precondition is nonemptiness: Python raises
`ZeroDivisionError` on an empty list, as represented by the checked entry point.
No finiteness restriction is imposed on the executable layer. Its totalized
empty-list value is outside the contract.

`RealLayer` is the exact mathematical interpretation of the same algorithm.
Its arithmetic theorems concern real numbers, not an assertion that floating
point rounding, NaN, or overflow obey real arithmetic. A shared algorithm and
structural equivalence proofs connect both functional and imperative versions;
no exact Float-to-Real arithmetic correspondence is assumed.
-/

namespace humaneval_4_mean_absolute_deviation

/-- Two-pass algorithm, parameterized by the numeric operations. -/
def deviationWith {α : Type} (zero : α) (add sub div : α → α → α)
    (abs : α → α) (ofNat : Nat → α) (xs : List α) : α :=
  let mean := div (xs.foldl add zero) (ofNat xs.length)
  div ((xs.map (fun x => abs (sub x mean))).foldl add zero) (ofNat xs.length)

/-- Literal executable translation of Python's two sums. -/
def mean_absolute_deviation (numbers : List Float) : Float :=
  deviationWith 0 (· + ·) (· - ·) (· / ·) Float.abs Float.ofNat numbers

/-- Error-aware entry point, preserving Python's empty-input exception.
The core Float function above is used directly on the admissible domain. -/
def mean_absolute_deviation_checked (numbers : List Float) : Except String Float :=
  match numbers with
  | [] => .error "ZeroDivisionError: division by zero"
  | _ :: _ => .ok (mean_absolute_deviation numbers)

namespace RealLayer

noncomputable def mean (xs : List ℝ) : ℝ := xs.sum / (xs.length : ℝ)

/-- Exact mathematical MAD around the arithmetic mean. -/
noncomputable def mad (xs : List ℝ) : ℝ :=
  (xs.map (fun x => |x - mean xs|)).sum / (xs.length : ℝ)

end RealLayer

namespace RatLayer

def mean (xs : List ℚ) : ℚ := xs.sum / (xs.length : ℚ)

def mad (xs : List ℚ) : ℚ :=
  deviationWith 0 (· + ·) (· - ·) (· / ·) abs Nat.cast xs

end RatLayer

example : (mean_absolute_deviation [1.0, 2.0, 3.0] - 2.0 / 3.0).abs < 0.000001 := by
  native_decide
example : (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0] - 1.0).abs < 0.000001 := by
  native_decide
example : (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0).abs < 0.000001 := by
  native_decide
#eval mean_absolute_deviation [1.0, 2.0, 3.0]
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0]

example : (match mean_absolute_deviation_checked [] with
    | .error _ => true | .ok _ => false) = true := by native_decide
example : (mean_absolute_deviation [0.0 / 0.0]).isNaN = true := by native_decide
example : (mean_absolute_deviation [1.0 / 0.0]).isNaN = true := by native_decide
example : (mean_absolute_deviation [-0.0] == 0.0) = true := by native_decide
#eval mean_absolute_deviation_checked []

/-- Exactly the input-domain restriction caused by Python's division by length. -/
def Pre {α : Type} (numbers : List α) : Prop := numbers ≠ []

theorem checked_empty : mean_absolute_deviation_checked [] =
    .error "ZeroDivisionError: division by zero" := by rfl

theorem checked_success (xs : List Float) (h : Pre xs) :
    mean_absolute_deviation_checked xs = .ok (mean_absolute_deviation xs) := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs => rfl

/-- The error occurs exactly on the inputs excluded by `Pre`. -/
theorem checked_error_iff (xs : List Float) :
    mean_absolute_deviation_checked xs = .error "ZeroDivisionError: division by zero" ↔
      ¬ Pre xs := by
  cases xs <;> simp [mean_absolute_deviation_checked, Pre]

namespace RealLayer

/-- The exact model is an instantiation of the executable algorithm's structure. -/
theorem mad_eq_deviationWith (xs : List ℝ) :
    mad xs = deviationWith (0 : ℝ) (· + ·) (· - ·) (· / ·) abs Nat.cast xs := by
  simp only [mad, mean, deviationWith, List.sum_eq_foldl]

theorem length_pos (xs : List ℝ) (h : Pre xs) : (0 : ℝ) < xs.length := by
  exact_mod_cast (List.length_pos_iff_ne_nil.mpr h)

/-- The sum of absolute deviations, divided by the number of observations. -/
def formula_prop (xs : List ℝ) : Prop :=
  mad xs * (xs.length : ℝ) = (xs.map (fun x => |x - mean xs|)).sum

def nonnegative_prop (xs : List ℝ) : Prop := 0 ≤ mad xs

/-- Zero MAD is equivalent to every observation being equal to the mean. -/
def zero_iff_prop (xs : List ℝ) : Prop :=
  mad xs = 0 ↔ ∀ x ∈ xs, x = mean xs

def constant_prop (xs : List ℝ) (c : ℝ) : Prop :=
  (∀ x ∈ xs, x = c) → mad xs = 0

def translation_prop (xs : List ℝ) (c : ℝ) : Prop :=
  mad (xs.map (fun x => x + c)) = mad xs

def scaling_prop (xs : List ℝ) (c : ℝ) : Prop :=
  mad (xs.map (fun x => c * x)) = |c| * mad xs

def permutation_prop (xs ys : List ℝ) : Prop :=
  xs.Perm ys → mad xs = mad ys

theorem formula_thm (xs : List ℝ) (h : Pre xs) : formula_prop xs := by
  unfold formula_prop mad
  exact div_mul_cancel₀ _ (ne_of_gt (length_pos xs h))

theorem nonnegative_thm (xs : List ℝ) : nonnegative_prop xs := by
  apply div_nonneg
  · apply List.sum_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- Kernel-checked zero-sum fact for a finite list of nonnegative reals. -/
theorem sum_zero_iff (ys : List ℝ) (h : ∀ y ∈ ys, 0 ≤ y) :
    ys.sum = 0 ↔ ∀ y ∈ ys, y = 0 := by
  induction ys with
  | nil => simp
  | cons a ys ih =>
    have ha := h a (by simp)
    have ht : ∀ y ∈ ys, 0 ≤ y := fun y hy => h y (by simp [hy])
    have hs := List.sum_nonneg ht
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro hz
      have haz : a = 0 := by linarith
      have hsz : ys.sum = 0 := by linarith
      exact ⟨haz, (ih ht).mp hsz⟩
    · rintro ⟨haz, hzs⟩
      rw [haz, (ih ht).mpr hzs, zero_add]

theorem zero_iff_thm (xs : List ℝ) (h : Pre xs) : zero_iff_prop xs := by
  have hn : (xs.length : ℝ) ≠ 0 := ne_of_gt (length_pos xs h)
  have ha : ∀ y ∈ xs.map (fun x => |x - mean xs|), 0 ≤ y := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact abs_nonneg _
  unfold zero_iff_prop mad
  rw [div_eq_zero_iff]
  simp only [hn, or_false]
  rw [sum_zero_iff _ ha]
  simp only [List.forall_mem_map, abs_eq_zero, sub_eq_zero]

theorem sum_of_constant (xs : List ℝ) (c : ℝ) (h : ∀ x ∈ xs, x = c) :
    xs.sum = (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, y = c := fun y hy => h y (by simp [hy])
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hx, ih ht]
    ring

theorem constant_thm (xs : List ℝ) (h : Pre xs) (c : ℝ) : constant_prop xs c := by
  intro hc
  have hn : (xs.length : ℝ) ≠ 0 := ne_of_gt (length_pos xs h)
  have hm : mean xs = c := by
    unfold mean
    rw [sum_of_constant xs c hc]
    exact mul_div_cancel_left₀ c hn
  apply (zero_iff_thm xs h).mpr
  intro x hx
  rw [hc x hx, hm]

/-- In particular, a singleton has zero deviation. -/
theorem singleton_thm (x : ℝ) : mad [x] = 0 := by
  simp [mad, mean]

theorem sum_translate (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => x + c)).sum = xs.sum + (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

theorem mean_translate (xs : List ℝ) (h : Pre xs) (c : ℝ) :
    mean (xs.map (fun x => x + c)) = mean xs + c := by
  have hn : (xs.length : ℝ) ≠ 0 := ne_of_gt (length_pos xs h)
  simp only [mean, List.length_map, sum_translate, add_div]
  rw [mul_div_cancel_left₀ c hn]

theorem translation_thm (xs : List ℝ) (h : Pre xs) (c : ℝ) : translation_prop xs c := by
  unfold translation_prop
  have hc : ∀ x : ℝ, (x + c) - (mean xs + c) = x - mean xs := by
    intro x
    ring
  simp only [mad, List.length_map, mean_translate xs h c, List.map_map,
    Function.comp_def, hc]

theorem mean_scale (xs : List ℝ) (c : ℝ) :
    mean (xs.map (fun x => c * x)) = c * mean xs := by
  simp only [mean, List.length_map]
  have hs : (xs.map (fun x => c * x)).sum = c * xs.sum := by
    simpa using (List.sum_map_mul_left xs (fun x : ℝ => x) c)
  rw [hs]
  ring

theorem scaling_thm (xs : List ℝ) (c : ℝ) : scaling_prop xs c := by
  unfold scaling_prop
  simp only [mad, List.length_map, mean_scale, List.map_map, Function.comp_def]
  have hs : (xs.map (fun x => |c * x - c * mean xs|)).sum =
      |c| * (xs.map (fun x => |x - mean xs|)).sum := by
    simp_rw [← mul_sub, abs_mul]
    exact List.sum_map_mul_left xs _ _
  rw [hs]
  ring

theorem permutation_thm (xs ys : List ℝ) : permutation_prop xs ys := by
  intro hp
  have hm : mean xs = mean ys := by
    simp only [mean, hp.sum_eq, hp.length_eq]
  unfold mad
  rw [hm, hp.length_eq, (hp.map (fun x => |x - mean ys|)).sum_eq]

end RealLayer

namespace RatLayer

theorem mad_formula (xs : List ℚ) :
    mad xs = (xs.map (fun x => |x - mean xs|)).sum / (xs.length : ℚ) := by
  simp only [mad, mean, deviationWith, List.sum_eq_foldl]

/-- Exact embedding of the rational mean into the real model. -/
theorem mean_cast (xs : List ℚ) :
    (mean xs : ℝ) = RealLayer.mean (xs.map (fun x : ℚ => (x : ℝ))) := by
  simp only [mean, RealLayer.mean, Rat.cast_div, Rat.cast_list_sum,
    Rat.cast_natCast, List.length_map]

/-- The executable rational test layer is not merely a renamed implementation:
its result embeds exactly into the mathematical Real implementation. -/
theorem mad_cast (xs : List ℚ) :
    (mad xs : ℝ) = RealLayer.mad (xs.map (fun x : ℚ => (x : ℝ))) := by
  rw [mad_formula]
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_list_sum, List.map_map,
    Function.comp_def, Rat.cast_abs, Rat.cast_sub, mean_cast,
    RealLayer.mad, List.length_map]

end RatLayer

namespace RealLayer

/-- Full mathematical contract on a nonempty dataset. -/
def Post_prop (xs : List ℝ) : Prop :=
  formula_prop xs ∧ nonnegative_prop xs ∧ zero_iff_prop xs ∧
  (∀ c, constant_prop xs c) ∧ (∀ c, translation_prop xs c) ∧
  (∀ c, scaling_prop xs c) ∧ (∀ ys, permutation_prop xs ys)

end RealLayer

/-! ## Executable property-based tests

Real comparison is noncomputable. The following exact rational counterparts
exercise `RealLayer.formula_prop`, `nonnegative_prop`, `zero_iff_prop`,
`constant_prop`, `translation_prop`, `scaling_prop`, `permutation_prop`, and
`Post_prop`. They are bounded tests, not substitutes for the universal proofs.
The datasets exhaust all lists of lengths 1, 2, and 3 on a six-value alphabet,
including negative and fractional values. All permutations are tested.
-/
namespace PropertyTests

def values : List ℚ := [-3, -1, 0, 1 / 2, 2, 4]

def datasets : List (List ℚ) :=
  (values.map (fun a => [a])) ++
  (values.flatMap (fun a => values.map (fun b => [a, b]))) ++
  (values.flatMap (fun a => values.flatMap (fun b => values.map (fun c => [a, b, c]))))

def formulaCheck (xs : List ℚ) : Bool :=
  decide (RatLayer.mad xs * (xs.length : ℚ) =
    (xs.map (fun x => |x - RatLayer.mean xs|)).sum)

def nonnegativeCheck (xs : List ℚ) : Bool := decide (0 ≤ RatLayer.mad xs)

def zeroIffCheck (xs : List ℚ) : Bool :=
  (RatLayer.mad xs == 0) == xs.all (fun x => x == RatLayer.mean xs)

def constantCheck (xs : List ℚ) (c : ℚ) : Bool :=
  !(xs.all (fun x => x == c)) || (RatLayer.mad xs == 0)

def translationCheck (xs : List ℚ) (c : ℚ) : Bool :=
  RatLayer.mad (xs.map (fun x => x + c)) == RatLayer.mad xs

def scalingCheck (xs : List ℚ) (c : ℚ) : Bool :=
  RatLayer.mad (xs.map (fun x => c * x)) == |c| * RatLayer.mad xs

def permutationCheck (xs : List ℚ) : Bool :=
  xs.permutations.all (fun ys => RatLayer.mad ys == RatLayer.mad xs)

/-- The postcondition's executable form, with its parameters bounded by `values`. -/
def postCheck (xs : List ℚ) : Bool :=
  formulaCheck xs && nonnegativeCheck xs && zeroIffCheck xs &&
  values.all (fun c => constantCheck xs c && translationCheck xs c && scalingCheck xs c) &&
  permutationCheck xs

-- PBT counterpart of RealLayer.formula_prop.
example : datasets.all formulaCheck = true := by native_decide
-- PBT counterpart of RealLayer.nonnegative_prop.
example : datasets.all nonnegativeCheck = true := by native_decide
-- PBT counterpart of RealLayer.zero_iff_prop.
example : datasets.all zeroIffCheck = true := by native_decide
-- PBT counterpart of RealLayer.constant_prop (includes nonvacuous constant lists).
example : datasets.all (fun xs => values.all (constantCheck xs)) = true := by native_decide
-- PBT counterpart of RealLayer.translation_prop.
example : datasets.all (fun xs => values.all (translationCheck xs)) = true := by native_decide
-- PBT counterpart of RealLayer.scaling_prop (positive, negative, and zero scales).
example : datasets.all (fun xs => values.all (scalingCheck xs)) = true := by native_decide
-- PBT counterpart of RealLayer.permutation_prop.
example : datasets.all permutationCheck = true := by native_decide
-- PBT counterpart of the complete RealLayer.Post_prop.
example : datasets.all postCheck = true := by native_decide
#eval (datasets.length, datasets.all postCheck)

-- Additional bounded Float tests: nonnegativity and constant/singleton inputs.
def floatValues : List Float := [-3.0, -1.0, 0.0, 0.5, 2.0, 4.0]
example : floatValues.all (fun a => floatValues.all (fun b => floatValues.all
    (fun c => decide (0 ≤ mean_absolute_deviation [a, b, c])))) = true := by native_decide
example : floatValues.all (fun a => (List.range 10).all (fun n =>
    (mean_absolute_deviation (List.replicate (n + 1) a)).abs < 0.000001)) = true := by
  native_decide

end PropertyTests

namespace RealLayer

/-- Correctness for every nonempty real dataset, with no boundedness restriction. -/
theorem correctness (xs : List ℝ) : Pre xs → Post_prop xs := by
  intro h
  exact ⟨formula_thm xs h, nonnegative_thm xs, zero_iff_thm xs h,
    constant_thm xs h, translation_thm xs h, scaling_thm xs, permutation_thm xs⟩

end RealLayer

/-! ## Imperative implementation and tests -/

/-- Same two passes, written with mutable accumulators and `for` loops. -/
def deviationWithImperative {α : Type} (zero : α) (add sub div : α → α → α)
    (abs : α → α) (ofNat : Nat → α) (xs : List α) : α := Id.run do
  let mut total := zero
  for x in xs do
    total := add total x
  let mean := div total (ofNat xs.length)
  let mut deviations := zero
  for x in xs do
    deviations := add deviations (abs (sub x mean))
  return div deviations (ofNat xs.length)

def mean_absolute_deviation_imperative (numbers : List Float) : Float :=
  deviationWithImperative 0 (· + ·) (· - ·) (· / ·) Float.abs Float.ofNat numbers

def mean_absolute_deviation_checked_imperative (numbers : List Float) : Except String Float :=
  match numbers with
  | [] => .error "ZeroDivisionError: division by zero"
  | _ :: _ => .ok (mean_absolute_deviation_imperative numbers)

namespace RealLayer

noncomputable def madImperative (xs : List ℝ) : ℝ :=
  deviationWithImperative 0 (· + ·) (· - ·) (· / ·) abs Nat.cast xs

end RealLayer

example : (mean_absolute_deviation_imperative [1.0, 2.0, 3.0] - 2.0 / 3.0).abs <
    0.000001 := by native_decide
example : (mean_absolute_deviation_imperative [1.0, 2.0, 3.0, 4.0] - 1.0).abs <
    0.000001 := by native_decide
example : (mean_absolute_deviation_imperative [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0).abs <
    0.000001 := by native_decide
#eval mean_absolute_deviation_imperative [1.0, 2.0, 3.0]
#eval mean_absolute_deviation_imperative [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation_imperative [1.0, 2.0, 3.0, 4.0, 5.0]

example : (match mean_absolute_deviation_checked_imperative [] with
    | .error _ => true | .ok _ => false) = true := by native_decide
example : (mean_absolute_deviation_imperative [0.0 / 0.0]).isNaN = true := by native_decide
example : (mean_absolute_deviation_imperative [1.0 / 0.0]).isNaN = true := by native_decide

-- Additional bounded comparison of the two actual Float implementations.
example : PropertyTests.floatValues.all (fun a => PropertyTests.floatValues.all
    (fun b => PropertyTests.floatValues.all (fun c =>
      mean_absolute_deviation [a, b, c] == mean_absolute_deviation_imperative [a, b, c]))) =
    true := by native_decide

/-- Structural loop equivalence, requiring no algebraic laws of the operations. -/
theorem deviationWith_equiv {α : Type} (zero : α) (add sub div : α → α → α)
    (abs : α → α) (ofNat : Nat → α) (xs : List α) :
    deviationWith zero add sub div abs ofNat xs =
      deviationWithImperative zero add sub div abs ofNat xs := by
  simp [deviationWith, deviationWithImperative, List.forIn_pure_yield_eq_foldl,
    List.foldl_map]

/-- Exact equality of the two Float programs, including exceptional Float values.
This is an equality of operation sequences, not a use of real arithmetic laws. -/
theorem functional_eq_imperative (xs : List Float) :
    mean_absolute_deviation xs = mean_absolute_deviation_imperative xs := by
  exact deviationWith_equiv _ _ _ _ _ _ xs

/-- The error-aware programs agree on all inputs, including the empty list. -/
theorem checked_functional_eq_imperative (xs : List Float) :
    mean_absolute_deviation_checked xs = mean_absolute_deviation_checked_imperative xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [mean_absolute_deviation_checked, mean_absolute_deviation_checked_imperative,
      functional_eq_imperative]

namespace RealLayer

/-- Equality of the functional mathematical model and the imperative model. -/
theorem functional_eq_imperative (xs : List ℝ) : mad xs = madImperative xs := by
  rw [mad_eq_deviationWith]
  exact deviationWith_equiv _ _ _ _ _ _ xs

end RealLayer

end humaneval_4_mean_absolute_deviation

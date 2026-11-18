import Mathlib
namespace Agent

/-!
# HumanEval/45: triangle area

The executable `triangle_area` preserves the Python operation order: multiply
`a` by `h`, then divide by `2.0`. Its inputs and output are `Float`.

`triangle_area_real` models the mathematical intent, area = base * height / 2,
on all real inputs. Nonnegative lengths are needed for geometric sign and
monotonicity conclusions, not for calling the function. `triangle_area_rat`
is an exact executable counterpart for property testing; `rational_model_thm`
proves its correspondence with the real model on rational inputs.

The Real theorems are not assertions that IEEE-754 arithmetic is exact.
Rounding, overflow, infinities, NaN, and signed zero are left to the Float
operations in the executable version. Its formula and implementation-
equivalence theorems hold structurally for every Float input, without a
finiteness assumption or an unsupported Float-to-Real equality claim.
-/

namespace humaneval_45_triangle_area

/-! ## Functional implementations -/

def triangle_area (a h : Float) : Float :=
  a * h / 2.0

noncomputable def triangle_area_real (a h : ℝ) : ℝ :=
  a * h / 2

def triangle_area_rat (a h : ℚ) : ℚ :=
  a * h / 2

/-! ## The supplied unit tests and additional boundary examples -/

example : (triangle_area 5 3 == 7.5) = true := by native_decide
example : (triangle_area 2 2 == 2.0) = true := by native_decide
example : (triangle_area 10 8 == 40.0) = true := by native_decide
example : (triangle_area 0 8 == 0.0) = true := by native_decide
example : (triangle_area 8 0 == 0.0) = true := by native_decide
example : (triangle_area (-5) 3 == -7.5) = true := by native_decide
example : triangle_area_rat 5 3 = 15 / 2 := by native_decide
example : triangle_area_rat 2 2 = 2 := by native_decide
example : triangle_area_rat 10 8 = 40 := by native_decide

#eval triangle_area 5 3
#eval triangle_area 2 2
#eval triangle_area 10 8

/-! ## Precondition and proved properties -/

/-- The program imposes no sign or finiteness check on its numeric inputs. -/
def Pre {α : Type*} (_a _h : α) : Prop := True

/-- Exact operational specification, including the order of Float operations. -/
def float_formula_prop (a h : Float) : Prop :=
  triangle_area a h = a * h / 2.0

theorem float_formula_thm (a h : Float) : float_formula_prop a h := by
  rfl

/-- A proved bridge for the exact, executable testing model (not for Float). -/
theorem rational_model_thm (a h : ℚ) :
    (triangle_area_rat a h : ℝ) = triangle_area_real (a : ℝ) (h : ℝ) := by
  simp [triangle_area_rat, triangle_area_real]

/-- The triangle occupies half the corresponding base-height rectangle. -/
def formula_prop (a h : ℝ) : Prop :=
  triangle_area_real a h = a * h / 2 ∧
  2 * triangle_area_real a h = a * h

theorem formula_thm (a h : ℝ) : formula_prop a h := by
  constructor
  · rfl
  · unfold triangle_area_real
    ring

def nonnegative_prop (a h : ℝ) : Prop :=
  0 ≤ a → 0 ≤ h → 0 ≤ triangle_area_real a h

theorem nonnegative_thm (a h : ℝ) : nonnegative_prop a h := by
  intro ha hh
  exact div_nonneg (mul_nonneg ha hh) (by norm_num)

def positive_prop (a h : ℝ) : Prop :=
  0 < a → 0 < h → 0 < triangle_area_real a h

theorem positive_thm (a h : ℝ) : positive_prop a h := by
  intro ha hh
  exact div_pos (mul_pos ha hh) (by norm_num)

/-- Degenerate triangles, and the complete zero characterization. -/
def zero_prop (a h : ℝ) : Prop :=
  triangle_area_real a 0 = 0 ∧
  triangle_area_real 0 h = 0 ∧
  (triangle_area_real a h = 0 ↔ a = 0 ∨ h = 0)

theorem zero_thm (a h : ℝ) : zero_prop a h := by
  simp [zero_prop, triangle_area_real, mul_eq_zero]

def symmetry_prop (a h : ℝ) : Prop :=
  triangle_area_real a h = triangle_area_real h a

theorem symmetry_thm (a h : ℝ) : symmetry_prop a h := by
  unfold symmetry_prop triangle_area_real
  rw [mul_comm]

/-- Scaling either dimension is linear; scaling both is quadratic. -/
def scaling_prop (a h : ℝ) : Prop :=
  ∀ k : ℝ,
    triangle_area_real (k * a) h = k * triangle_area_real a h ∧
    triangle_area_real a (k * h) = k * triangle_area_real a h ∧
    triangle_area_real (k * a) (k * h) = k ^ 2 * triangle_area_real a h

theorem scaling_thm (a h : ℝ) : scaling_prop a h := by
  intro k
  dsimp [triangle_area_real]
  constructor
  · ring
  constructor <;> ring

/-- Increasing nonnegative base and height cannot decrease the area. -/
def monotonicity_prop (a h : ℝ) : Prop :=
  0 ≤ a → 0 ≤ h → ∀ b k : ℝ,
    a ≤ b → h ≤ k → triangle_area_real a h ≤ triangle_area_real b k

theorem monotonicity_thm (a h : ℝ) : monotonicity_prop a h := by
  intro ha hh b k hab hhk
  unfold triangle_area_real
  exact div_le_div_of_nonneg_right
    (mul_le_mul hab hhk hh (le_trans ha hab)) (by norm_num)

/-! ## Postcondition -/

def Post_prop (a h : ℝ) : Prop :=
  formula_prop a h ∧
  nonnegative_prop a h ∧
  positive_prop a h ∧
  zero_prop a h ∧
  symmetry_prop a h ∧
  scaling_prop a h ∧
  monotonicity_prop a h

/-! ## Property-based tests

Real comparisons are not executable. The checks below are the exact rational
counterparts of `formula_prop`, `nonnegative_prop`, `positive_prop`,
`zero_prop`, `symmetry_prop`, `scaling_prop`, `monotonicity_prop`, and
`Post_prop`. `rational_model_thm` relates the rational implementation to the
real implementation. Every input and quantified scale/comparison parameter
is sampled from the signed half-integers in [-4, 4]. Thus zero, negative,
positive, and fractional values are tested. These finite tests do not replace
or restrict any of the universally quantified Real theorems above.

The Float operational property has its own bounded executable test.
-/

def rationalSamples : List ℚ :=
  (List.range 17).map (fun n => ((n : ℚ) - 8) / 2)

def floatSamples : List Float :=
  (List.range 17).map (fun n => (Float.ofNat n - 8.0) / 2.0)

def formulaCheck (a h : ℚ) : Bool :=
  decide (triangle_area_rat a h = a * h / 2 ∧
    2 * triangle_area_rat a h = a * h)

def nonnegativeCheck (a h : ℚ) : Bool :=
  decide (0 ≤ a → 0 ≤ h → 0 ≤ triangle_area_rat a h)

def positiveCheck (a h : ℚ) : Bool :=
  decide (0 < a → 0 < h → 0 < triangle_area_rat a h)

def zeroCheck (a h : ℚ) : Bool :=
  decide (triangle_area_rat a 0 = 0 ∧ triangle_area_rat 0 h = 0 ∧
    (triangle_area_rat a h = 0 ↔ a = 0 ∨ h = 0))

def symmetryCheck (a h : ℚ) : Bool :=
  decide (triangle_area_rat a h = triangle_area_rat h a)

def scalingCheck (a h k : ℚ) : Bool :=
  decide (triangle_area_rat (k * a) h = k * triangle_area_rat a h ∧
    triangle_area_rat a (k * h) = k * triangle_area_rat a h ∧
    triangle_area_rat (k * a) (k * h) = k ^ 2 * triangle_area_rat a h)

def monotonicityCheck (a h b k : ℚ) : Bool :=
  decide (0 ≤ a → 0 ≤ h → a ≤ b → h ≤ k →
    triangle_area_rat a h ≤ triangle_area_rat b k)

/-- Bounded check of the entire postcondition, including its inner parameters. -/
def postCheck (a h : ℚ) : Bool :=
  formulaCheck a h && nonnegativeCheck a h && positiveCheck a h &&
  zeroCheck a h && symmetryCheck a h &&
  rationalSamples.all (fun k => scalingCheck a h k) &&
  rationalSamples.all (fun b =>
    rationalSamples.all (fun k => monotonicityCheck a h b k))

-- PBT for float_formula_prop: 289 Float input pairs.
example : floatSamples.all (fun a => floatSamples.all (fun h =>
    triangle_area a h == a * h / 2.0)) = true := by native_decide

-- PBT for formula_prop.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    formulaCheck a h)) = true := by native_decide

-- PBT for nonnegative_prop, with its admissibility conditions in the check.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    nonnegativeCheck a h)) = true := by native_decide

-- PBT for positive_prop.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    positiveCheck a h)) = true := by native_decide

-- PBT for zero_prop.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    zeroCheck a h)) = true := by native_decide

-- PBT for symmetry_prop.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    symmetryCheck a h)) = true := by native_decide

-- PBT for scaling_prop: all 4,913 sampled triples.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    rationalSamples.all (fun k => scalingCheck a h k))) = true := by native_decide

-- PBT for monotonicity_prop: all 83,521 sampled quadruples.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    rationalSamples.all (fun b => rationalSamples.all (fun k =>
      monotonicityCheck a h b k)))) = true := by native_decide

-- PBT for Post_prop, testing the conjunction on the same inputs.
example : rationalSamples.all (fun a => rationalSamples.all (fun h =>
    postCheck a h)) = true := by native_decide

#eval rationalSamples.all (fun a => rationalSamples.all (fun h => postCheck a h))

/-! ## Correctness -/

theorem correctness_thm (a h : ℝ) : Pre a h → Post_prop a h := by
  intro _
  exact ⟨formula_thm a h, nonnegative_thm a h, positive_thm a h,
    zero_thm a h, symmetry_thm a h, scaling_thm a h, monotonicity_thm a h⟩

/-- The executable layer also satisfies its precise operational specification. -/
theorem float_correctness_thm (a h : Float) :
    Pre a h → float_formula_prop a h := by
  intro _
  exact float_formula_thm a h

/-! ## Imperative implementations -/

def triangle_area_imp (a h : Float) : Float := Id.run do
  let mut area := a
  area := area * h
  area := area / 2.0
  return area

noncomputable def triangle_area_real_imp (a h : ℝ) : ℝ := Id.run do
  let mut area := a
  area := area * h
  area := area / 2
  return area

/-! ## Imperative tests -/

example : (triangle_area_imp 5 3 == 7.5) = true := by native_decide
example : (triangle_area_imp 2 2 == 2.0) = true := by native_decide
example : (triangle_area_imp 10 8 == 40.0) = true := by native_decide
example : (triangle_area_imp 0 8 == 0.0) = true := by native_decide
example : (triangle_area_imp (-5) 3 == -7.5) = true := by native_decide

#eval triangle_area_imp 5 3
#eval triangle_area_imp 2 2
#eval triangle_area_imp 10 8

example : floatSamples.all (fun a => floatSamples.all (fun h =>
    triangle_area a h == triangle_area_imp a h)) = true := by native_decide

/-! ## Functional / imperative equivalence -/

/-- Same Float operations in the same order, even for exceptional inputs. -/
theorem equivalence_thm (a h : Float) :
    triangle_area a h = triangle_area_imp a h := by
  rfl

theorem real_equivalence_thm (a h : ℝ) :
    triangle_area_real a h = triangle_area_real_imp a h := by
  rfl

end humaneval_45_triangle_area
end Agent

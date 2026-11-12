import Mathlib

/-!
# HumanEval/4: mean absolute deviation

The executable `Float` function follows the source's two passes: compute the mean,
then average the absolute distances from it. `mean_absolute_deviationChecked`
represents Python's division-by-zero exception on an empty list. The precondition
of the value-returning specification is precisely that the list is nonempty.

`Exact` formalizes the mathematical intent over any linearly ordered field,
including all real inputs. Its rational specialization supplies executable
property tests. A cast theorem connects the rational and real models, and an
algorithm theorem connects the sum formula to the same two-pass algorithm used
by the Float function. Exact arithmetic laws are not asserted for rounded Float
arithmetic: NaN, infinity, and rounding retain their native Float behavior.
Functional/imperative equivalence is proved separately for Float, without
finiteness assumptions, and for the exact model.
-/

namespace humaneval_4_mean_absolute_deviation

/-- The common two-pass algorithm, with the numeric operations made explicit. -/
def meanAbsoluteDeviationWith {α : Type*} (zero : α)
    (add sub divide : α → α → α) (absolute : α → α) (ofLength : Nat → α)
    (numbers : List α) : α :=
  let n := ofLength numbers.length
  let mean := divide (numbers.foldl add zero) n
  divide ((numbers.map fun x => absolute (sub x mean)).foldl add zero) n

/-- Direct executable floating-point translation on the nonempty input domain. -/
def mean_absolute_deviation (numbers : List Float) : Float :=
  meanAbsoluteDeviationWith 0 (· + ·) (· - ·) (· / ·) Float.abs Float.ofNat numbers

/-- An explicit representation of the source's exception on an empty input. -/
def mean_absolute_deviationChecked (numbers : List Float) : Except String Float :=
  if numbers.isEmpty then .error "ZeroDivisionError" else .ok (mean_absolute_deviation numbers)

namespace Exact

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def mean (numbers : List K) : K := numbers.sum / (numbers.length : K)

/-- Exact mathematical MAD; values on empty lists are outside `Pre`. -/
def mean_absolute_deviation (numbers : List K) : K :=
  (numbers.map fun x => |x - mean numbers|).sum / (numbers.length : K)

end Exact

-- The three original unit tests, with the source's tolerance.
example : (mean_absolute_deviation [1.0, 2.0, 3.0] - 2.0 / 3.0).abs < 0.000001 := by
  native_decide
example : (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0] - 1.0).abs < 0.000001 := by
  native_decide
example : (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0).abs < 0.000001 := by
  native_decide
example : mean_absolute_deviation [7.0] == 0.0 := by native_decide
example : mean_absolute_deviation [-3.0, -1.0, 1.0, 3.0] == 2.0 := by native_decide
example : mean_absolute_deviation [2.5, 2.5, 2.5] == 0.0 := by native_decide
example : (match mean_absolute_deviationChecked [] with
    | .error message => message == "ZeroDivisionError"
    | .ok _ => false) = true := by native_decide
example : (mean_absolute_deviation [0.0 / 0.0]).isNaN := by native_decide
example : (mean_absolute_deviation [1.0 / 0.0]).isNaN := by native_decide
example : Exact.mean_absolute_deviation ([1, 2, 3] : List ℚ) = 2 / 3 := by native_decide
example : Exact.mean_absolute_deviation ([1, 2, 3, 4, 5] : List ℚ) = 6 / 5 := by native_decide

#eval mean_absolute_deviation [1.0, 2.0, 3.0]
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0]
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0]
#eval mean_absolute_deviationChecked []

/-- Exactly the domain on which the Python divisions by the list length are defined. -/
def Pre {α : Type*} (numbers : List α) : Prop := numbers ≠ []

theorem checked_empty_thm :
    mean_absolute_deviationChecked [] = .error "ZeroDivisionError" := by
  rfl

theorem checked_nonempty_thm (xs : List Float) (h : Pre xs) :
    mean_absolute_deviationChecked xs = .ok (mean_absolute_deviation xs) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

namespace Exact

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem length_pos {xs : List K} (h : Pre xs) : (0 : K) < xs.length := by
  exact_mod_cast List.length_pos_iff.mpr h

omit [IsStrictOrderedRing K] in
/-- The exact sum formula is the common algorithm instantiated with field operations. -/
theorem algorithm_eq (xs : List K) :
    meanAbsoluteDeviationWith 0 (· + ·) (· - ·) (· / ·) abs (fun n => (n : K)) xs =
      mean_absolute_deviation xs := by
  simp only [meanAbsoluteDeviationWith, mean_absolute_deviation, mean, List.sum_eq_foldl]

def formula_prop (xs : List K) (result : K) : Prop :=
  result = (xs.map fun x => |x - xs.sum / (xs.length : K)|).sum / (xs.length : K)

omit [IsStrictOrderedRing K] in
theorem formula_thm (xs : List K) : formula_prop xs (mean_absolute_deviation xs) := by
  rfl

def nonnegative_prop (result : K) : Prop := 0 ≤ result

theorem nonnegative_thm (xs : List K) : nonnegative_prop (mean_absolute_deviation xs) := by
  apply div_nonneg
  · apply List.sum_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- Zero deviation characterizes datasets all of whose entries equal the mean. -/
def zero_iff_constant_prop (xs : List K) (result : K) : Prop :=
  result = 0 ↔ ∀ x ∈ xs, x = mean xs

theorem zero_iff_constant_thm (xs : List K) (h : Pre xs) :
    zero_iff_constant_prop xs (mean_absolute_deviation xs) := by
  have hn : (xs.length : K) ≠ 0 := ne_of_gt (length_pos h)
  have hnonneg : ∀ y ∈ xs.map (fun x => |x - mean xs|), (0 : K) ≤ y := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact abs_nonneg _
  constructor
  · intro hz x hx
    have hs : (xs.map fun x => |x - mean xs|).sum = 0 :=
      (div_eq_zero_iff.mp hz).resolve_right hn
    have hxle := List.single_le_sum hnonneg |x - mean xs| (List.mem_map.mpr ⟨x, hx, rfl⟩)
    rw [hs] at hxle
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hxle (abs_nonneg _)))
  · intro hall
    have hs : (xs.map fun x => |x - mean xs|) = xs.map (fun _ => (0 : K)) := by
      apply List.map_congr_left
      intro x hx
      simp [hall x hx]
    simp [mean_absolute_deviation, hs]

theorem mean_of_constant {xs : List K} (h : Pre xs) (c : K)
    (hc : ∀ x ∈ xs, x = c) : mean xs = c := by
  have hs : xs.sum = (xs.length : K) * c := by
    calc
      xs.sum = (xs.map fun _ => c).sum := by
        congr 1
        exact (List.map_congr_left (fun x hx => hc x hx)).symm.trans (List.map_id xs) |>.symm
      _ = (xs.length : K) * c := by simp [List.map_const', nsmul_eq_mul]
  dsimp [mean]
  rw [hs]
  exact mul_div_cancel_left₀ c (ne_of_gt (length_pos h))

def constant_prop (xs : List K) (c : K) : Prop :=
  (∀ x ∈ xs, x = c) → mean_absolute_deviation xs = 0

theorem constant_thm (xs : List K) (h : Pre xs) (c : K) : constant_prop xs c := by
  intro hc
  apply (zero_iff_constant_thm xs h).mpr
  intro x hx
  rw [mean_of_constant h c hc]
  exact hc x hx

def singleton_prop (x : K) : Prop := mean_absolute_deviation [x] = 0

theorem singleton_thm (x : K) : singleton_prop x := by
  simp [singleton_prop, mean_absolute_deviation, mean]

theorem mean_translate (xs : List K) (h : Pre xs) (c : K) :
    mean (xs.map fun x => x + c) = mean xs + c := by
  have hn : (xs.length : K) ≠ 0 := ne_of_gt (length_pos h)
  simp only [mean, List.length_map, List.sum_map_add,
    List.map_const', List.sum_replicate, nsmul_eq_mul]
  rw [add_div, mul_div_cancel_left₀ c hn]
  change (xs.map id).sum / (xs.length : K) + c = xs.sum / (xs.length : K) + c
  rw [List.map_id]

def translation_prop (xs : List K) (c : K) : Prop :=
  mean_absolute_deviation (xs.map fun x => x + c) = mean_absolute_deviation xs

theorem translation_thm (xs : List K) (h : Pre xs) (c : K) : translation_prop xs c := by
  simp only [translation_prop, mean_absolute_deviation, List.length_map,
    mean_translate xs h c, List.map_map]
  change (xs.map fun x => |(x + c) - (mean xs + c)|).sum / (xs.length : K) = _
  simp only [add_sub_add_right_eq_sub]

theorem mean_scale (xs : List K) (c : K) :
    mean (xs.map fun x => c * x) = c * mean xs := by
  have hs : (xs.map fun x => c * x).sum = c * xs.sum := by
    simpa only [List.map_id] using List.sum_map_mul_left xs id c
  simp only [mean, List.length_map, hs]
  ring

def scaling_prop (xs : List K) (c : K) : Prop :=
  mean_absolute_deviation (xs.map fun x => c * x) = |c| * mean_absolute_deviation xs

theorem scaling_thm (xs : List K) (c : K) : scaling_prop xs c := by
  simp only [scaling_prop, mean_absolute_deviation, List.length_map, mean_scale, List.map_map]
  change (xs.map fun x => |c * x - c * mean xs|).sum / (xs.length : K) = _
  simp only [← mul_sub, abs_mul, List.sum_map_mul_left]
  ring

def permutation_prop (xs ys : List K) : Prop :=
  xs.Perm ys → mean_absolute_deviation xs = mean_absolute_deviation ys

omit [IsStrictOrderedRing K] in
theorem permutation_thm (xs ys : List K) : permutation_prop xs ys := by
  intro hp
  have hm : mean xs = mean ys := by simp [mean, hp.sum_eq, hp.length_eq]
  simp only [mean_absolute_deviation, hm, hp.length_eq]
  rw [(hp.map (fun x => |x - mean ys|)).sum_eq]

theorem mean_bounds (xs : List K) (h : Pre xs) (lo hi : K)
    (hb : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) : lo ≤ mean xs ∧ mean xs ≤ hi := by
  have hn := length_pos h
  have hl : (xs.length : K) * lo ≤ xs.sum := by
    have hh := List.sum_le_sum (l := xs) (f := fun _ => lo) (g := id)
      (fun x hx => (hb x hx).1)
    simpa [List.map_const', nsmul_eq_mul] using hh
  have hu : xs.sum ≤ (xs.length : K) * hi := by
    have hh := List.sum_le_sum (l := xs) (f := id) (g := fun _ => hi)
      (fun x hx => (hb x hx).2)
    simpa [List.map_const', nsmul_eq_mul] using hh
  constructor
  · exact (le_div_iff₀ hn).mpr (by simpa [mul_comm] using hl)
  · exact (div_le_iff₀ hn).mpr (by simpa [mul_comm] using hu)

def range_bound_prop (xs : List K) (lo hi : K) : Prop :=
  (∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) → mean_absolute_deviation xs ≤ hi - lo

theorem range_bound_thm (xs : List K) (h : Pre xs) (lo hi : K) :
    range_bound_prop xs lo hi := by
  intro hb
  obtain ⟨hlo, hhi⟩ := mean_bounds xs h lo hi hb
  have hs : (xs.map fun x => |x - mean xs|).sum ≤ (xs.length : K) * (hi - lo) := by
    have hh := List.sum_le_sum (l := xs) (f := fun x => |x - mean xs|)
      (g := fun _ => hi - lo) (fun x hx => abs_le.mpr (by
        obtain ⟨hxlo, hxhi⟩ := hb x hx
        constructor <;> linarith))
    simpa [List.map_const', nsmul_eq_mul] using hh
  exact (div_le_iff₀ (length_pos h)).mpr (by simpa [mul_comm] using hs)

/-- The rational tests evaluate exactly the restriction of the real mathematical model. -/
theorem rat_real_correspondence (xs : List ℚ) :
    (mean_absolute_deviation xs : ℝ) = mean_absolute_deviation (xs.map fun x => (x : ℝ)) := by
  simp [mean_absolute_deviation, mean]

/-- The result satisfies the defining formula, nonnegativity, and the exact zero criterion. -/
def Post_prop (xs : List K) (result : K) : Prop :=
  formula_prop xs result ∧ nonnegative_prop result ∧ zero_iff_constant_prop xs result

end Exact

/-! Property-based tests. All nine properties and the conjunction in `Post_prop`
are checked below. The real properties are not directly executable (real
arithmetic/order); their exact rational counterparts are tested, with the
connection proved by `Exact.rat_real_correspondence`. -/

/-- Exhaust all lists of lengths 1 through 3 over a signed, fractional alphabet. -/
def pbtValues : List ℚ := [-3, -1 / 2, 0, 1 / 2, 2]

def pbtInputs : List (List ℚ) :=
  pbtValues.flatMap fun a =>
    [ [a] ] ++ pbtValues.flatMap fun b =>
      [ [a, b] ] ++ pbtValues.map fun c => [a, b, c]

-- PBT: formula_prop.
example : pbtInputs.all (fun xs => decide
    (Exact.mean_absolute_deviation xs =
      (xs.map fun x => |x - xs.sum / (xs.length : ℚ)|).sum / (xs.length : ℚ))) = true := by
  native_decide

-- PBT: nonnegative_prop.
example : pbtInputs.all (fun xs => decide
    (0 ≤ Exact.mean_absolute_deviation xs)) = true := by native_decide

-- PBT: zero_iff_constant_prop, using a finite universal quantifier over list entries.
example : pbtInputs.all (fun xs =>
    (decide (Exact.mean_absolute_deviation xs = 0) ==
      xs.all (fun x => decide (x = Exact.mean xs)))) = true := by native_decide

-- PBT: constant_prop, including explicitly generated constant lists of many lengths.
example : pbtValues.all (fun c => (List.range 25).all (fun n =>
    decide (Exact.mean_absolute_deviation (List.replicate (n + 1) c) = 0))) = true := by
  native_decide

-- PBT: singleton_prop.
example : pbtValues.all (fun x => decide (Exact.mean_absolute_deviation [x] = 0)) = true := by
  native_decide

-- PBT: translation_prop.
example : pbtInputs.all (fun xs => pbtValues.all (fun c => decide
    (Exact.mean_absolute_deviation (xs.map fun x => x + c) =
      Exact.mean_absolute_deviation xs))) = true := by native_decide

-- PBT: scaling_prop, including negative and zero scales.
example : pbtInputs.all (fun xs => pbtValues.all (fun c => decide
    (Exact.mean_absolute_deviation (xs.map fun x => c * x) =
      |c| * Exact.mean_absolute_deviation xs))) = true := by native_decide

-- PBT: permutation_prop; generate actual permutations, avoiding rare antecedents.
example : pbtInputs.all (fun xs => xs.permutations.all (fun ys => decide
    (Exact.mean_absolute_deviation xs = Exact.mean_absolute_deviation ys))) = true := by
  native_decide

-- PBT: range_bound_prop; every generated list is covered by the interval [-3, 2].
example : pbtInputs.all (fun xs => decide
    (Exact.mean_absolute_deviation xs ≤ (2 : ℚ) - (-3))) = true := by native_decide

-- PBT: Post_prop, with its zero criterion written using executable List.all.
example : pbtInputs.all (fun xs =>
    decide (Exact.mean_absolute_deviation xs =
      (xs.map fun x => |x - xs.sum / (xs.length : ℚ)|).sum / (xs.length : ℚ)) &&
    decide (0 ≤ Exact.mean_absolute_deviation xs) &&
    (decide (Exact.mean_absolute_deviation xs = 0) ==
      xs.all (fun x => decide (x = Exact.mean xs)))) = true := by native_decide

-- Randomized checks complement the exhaustive small cases with longer integer datasets.
#eval Plausible.Testable.check (∀ a : Int, ∀ xs : List Int,
  (0 : ℚ) ≤ Exact.mean_absolute_deviation ((a :: xs).map fun x => (x : ℚ)))
#eval Plausible.Testable.check (∀ a c : Int, ∀ xs : List Int,
  Exact.mean_absolute_deviation ((a :: xs).map fun x => (x : ℚ) + (c : ℚ)) =
    Exact.mean_absolute_deviation ((a :: xs).map fun x => (x : ℚ)))

namespace Exact

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Correctness on exactly the source's nonempty mathematical input domain. -/
theorem correctness (xs : List K) : Pre xs → Post_prop xs (mean_absolute_deviation xs) := by
  intro h
  exact ⟨formula_thm xs, nonnegative_thm xs, zero_iff_constant_thm xs h⟩

end Exact

/-- Two imperative passes with mutable accumulators, for arbitrary numeric operations. -/
def meanAbsoluteDeviationWithImperative {α : Type*} (zero : α)
    (add sub divide : α → α → α) (absolute : α → α) (ofLength : Nat → α)
    (numbers : List α) : α := Id.run do
  let mut total := zero
  for x in numbers do
    total := add total x
  let n := ofLength numbers.length
  let mean := divide total n
  let mut deviations := zero
  for x in numbers do
    deviations := add deviations (absolute (sub x mean))
  return divide deviations n

def mean_absolute_deviationImperative (numbers : List Float) : Float :=
  meanAbsoluteDeviationWithImperative 0 (· + ·) (· - ·) (· / ·) Float.abs Float.ofNat numbers

namespace Exact

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def mean_absolute_deviationImperative (numbers : List K) : K :=
  meanAbsoluteDeviationWithImperative 0 (· + ·) (· - ·) (· / ·) abs (fun n => (n : K)) numbers

end Exact

-- Imperative unit tests.
example : (mean_absolute_deviationImperative [1.0, 2.0, 3.0] - 2.0 / 3.0).abs < 0.000001 := by
  native_decide
example : (mean_absolute_deviationImperative [1.0, 2.0, 3.0, 4.0] - 1.0).abs < 0.000001 := by
  native_decide
example : (mean_absolute_deviationImperative [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0).abs <
    0.000001 := by native_decide
example : Exact.mean_absolute_deviationImperative ([-3, -1, 1, 3] : List ℚ) = 2 := by
  native_decide

#eval mean_absolute_deviationImperative [1.0, 2.0, 3.0, 4.0]
#eval Exact.mean_absolute_deviationImperative ([1, 2, 3, 4, 5] : List ℚ)

-- Bounded implementation checks; Float comparisons use bits, so NaNs are comparable.
example : pbtInputs.all (fun xs => decide
    (Exact.mean_absolute_deviation xs = Exact.mean_absolute_deviationImperative xs)) = true := by
  native_decide

def pbtFloatValues : List Float := [-3.0, -0.0, 0.0, 0.5, 2.0, 1.0 / 0.0, 0.0 / 0.0]

example : pbtFloatValues.all (fun a => pbtFloatValues.all (fun b =>
    (mean_absolute_deviation [a, b]).toBits ==
      (mean_absolute_deviationImperative [a, b]).toBits)) = true := by native_decide

/-- Structural equivalence needs no arithmetic laws and preserves operation order. -/
theorem algorithm_equivalence {α : Type*} (zero : α)
    (add sub divide : α → α → α) (absolute : α → α) (ofLength : Nat → α)
    (numbers : List α) :
    meanAbsoluteDeviationWith zero add sub divide absolute ofLength numbers =
      meanAbsoluteDeviationWithImperative zero add sub divide absolute ofLength numbers := by
  simp [meanAbsoluteDeviationWith, meanAbsoluteDeviationWithImperative, List.foldl_map]

/-- Float equivalence holds for every list, including nonfinite values. -/
theorem functional_eq_imperative (numbers : List Float) :
    mean_absolute_deviation numbers = mean_absolute_deviationImperative numbers := by
  exact algorithm_equivalence 0 (· + ·) (· - ·) (· / ·) Float.abs Float.ofNat numbers

namespace Exact

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
theorem functional_eq_imperative (numbers : List K) :
    mean_absolute_deviation numbers = mean_absolute_deviationImperative numbers := by
  rw [← algorithm_eq numbers]
  exact algorithm_equivalence 0 (· + ·) (· - ·) (· / ·) abs (fun n => (n : K)) numbers

end Exact

end humaneval_4_mean_absolute_deviation

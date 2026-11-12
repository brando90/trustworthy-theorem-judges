import Mathlib

/-!
# HumanEval/4: `mean_absolute_deviation`

Translation of the Python program `humaneval_4_mean_absolute_deviation.py`:

```python
def mean_absolute_deviation(numbers: List[float]) -> float:
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)
```

Numeric modelling:

* **FloatLayer** -- `mean_absolute_deviation : List Float → Float` mirrors the Python
  code operation by operation (left-to-right `sum`, IEEE-754 `Float`).  It is used
  for the ground unit tests taken from the Python `check` function, and for the
  functional/imperative equivalence theorem on `Float` (a structural statement).
* **Mathematical layer** -- `madGen` is the exact mathematical quantity
  `MAD = (1/n) * Σ |xᵢ - mean|`, generic over any linearly ordered field.  It is
  instantiated as the executable `madRat : List ℚ → ℚ` (used for property-based
  tests) and as `madReal : List ℝ → ℝ`.  The Python docstring describes a
  mathematical quantity, so all property / correctness theorems are stated and
  proved on this exact model (they hold simultaneously for `ℚ` and `ℝ`).

Pre-condition: the input list is non-empty (Python raises `ZeroDivisionError`
on `[]`; in Lean the `Float` version returns `NaN` and the field versions return `0`
because `x / 0 = 0`, so every theorem that needs it carries the `Pre` hypothesis).
-/

namespace humaneval_4_mean_absolute_deviation

/- Generic sections declare all three ordered-field instances; some helper lemmas need
only a subset, which this linter would otherwise flag. -/
set_option linter.unusedSectionVars false

/-! ## Implementation -/

/-! ### FloatLayer: executable implementation mirroring the Python code -/

/-- Python `sum(numbers)`: a left fold starting from `0`. -/
def floatSum (numbers : List Float) : Float :=
  numbers.foldl (· + ·) 0

/-- `mean_absolute_deviation` on IEEE-754 floats, exactly as the Python code computes it:
`mean = sum(numbers) / len(numbers)`, then `sum(abs(x - mean) for x in numbers) / len(numbers)`. -/
def mean_absolute_deviation (numbers : List Float) : Float :=
  let n : Float := numbers.length.toFloat
  let mean : Float := floatSum numbers / n
  (numbers.foldl (fun acc x => acc + Float.abs (x - mean)) 0) / n

/-! ### Mathematical layer (exact arithmetic in a linearly ordered field) -/

section Generic
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The arithmetic mean `sum(numbers) / len(numbers)`. -/
def meanGen (numbers : List α) : α := numbers.sum / numbers.length

/-- Mean absolute deviation `sum(abs(x - mean) for x in numbers) / len(numbers)`. -/
def madGen (numbers : List α) : α :=
  (numbers.map (fun x => |x - meanGen numbers|)).sum / numbers.length

end Generic

/-- RatLayer: exact, executable model of the Python function. -/
abbrev meanRat : List ℚ → ℚ := meanGen
/-- RatLayer: exact, executable model of the Python function. -/
abbrev madRat : List ℚ → ℚ := madGen
/-- RealLayer: exact (noncomputable) model of the Python function. -/
noncomputable abbrev meanReal : List ℝ → ℝ := meanGen
/-- RealLayer: exact (noncomputable) model of the Python function. -/
noncomputable abbrev madReal : List ℝ → ℝ := madGen

/-! ## Unit tests (ground examples from the Python `check` function) -/

example : Float.abs (mean_absolute_deviation [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by native_decide
example : Float.abs (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by native_decide
example : Float.abs (mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0]          -- 1.000000
#eval mean_absolute_deviation [1.0, 2.0, 3.0]               -- 0.666667
#eval mean_absolute_deviation [1.0, 2.0, 3.0, 4.0, 5.0]     -- 1.200000

-- The same examples on the exact rational model (exact equality, no tolerance needed).
example : madRat [1, 2, 3] = 2 / 3 := by native_decide
example : madRat [1, 2, 3, 4] = 1 := by native_decide
example : madRat [1, 2, 3, 4, 5] = 6 / 5 := by native_decide
example : madRat [7] = 0 := by native_decide
example : madRat [-3, 3] = 3 := by native_decide
#eval madRat [1, 2, 3, 4]      -- 1
#eval madRat [1, 2, 3]         -- 2/3

-- The three Python `check` assertions as kernel-checked theorems on the exact model
-- (`abs(candidate(xs) - v) < 1e-6` holds since the exact value is `v` itself).
theorem check_example_1_thm : madRat [1, 2, 3] = 2 / 3 := by
  norm_num [madRat, madGen, meanGen, abs_of_nonneg, abs_of_nonpos]
theorem check_example_2_thm : madRat [1, 2, 3, 4] = 1 := by
  norm_num [madRat, madGen, meanGen, abs_of_nonneg, abs_of_nonpos]
theorem check_example_3_thm : madRat [1, 2, 3, 4, 5] = 6 / 5 := by
  norm_num [madRat, madGen, meanGen, abs_of_nonneg, abs_of_nonpos]

/-! ## Pre-condition -/

/-- Python divides by `len(numbers)`, so the list must be non-empty. -/
def Pre {β : Type*} (numbers : List β) : Prop := numbers ≠ []

/-! ## Properties and theorems (mathematical layer) -/

section Properties
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Helper: a non-empty list has positive (cast) length. -/
theorem length_cast_pos {numbers : List α} (h : Pre numbers) : (0 : α) < numbers.length := by
  exact_mod_cast List.length_pos_of_ne_nil h

/-- Helper: a non-empty list has non-zero (cast) length. -/
theorem length_cast_ne_zero {numbers : List α} (h : Pre numbers) : (numbers.length : α) ≠ 0 :=
  ne_of_gt (length_cast_pos h)

/-- Helper: every term `|x - m|` of the summed list is non-negative. -/
theorem terms_nonneg (numbers : List α) (m : α) :
    ∀ y ∈ numbers.map (fun x => |x - m|), 0 ≤ y := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨x, _, rfl⟩ := hy
  exact abs_nonneg _

/-- Helper: `Σ (xᵢ + c) = Σ xᵢ + n * c`. -/
theorem sum_map_add_const (l : List α) (c : α) :
    (l.map (fun x => x + c)).sum = l.sum + l.length * c := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, ih]
    ring

/-- Helper: `Σ (c * xᵢ) = c * Σ xᵢ`. -/
theorem sum_map_mul_const (l : List α) (c : α) :
    (l.map (fun x => c * x)).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

/-- Helper: the mean of a constant list is that constant. -/
theorem mean_of_const (numbers : List α) (c : α) (h : Pre numbers)
    (hc : ∀ x ∈ numbers, x = c) : meanGen numbers = c := by
  unfold meanGen
  rw [List.sum_eq_card_nsmul numbers c hc, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (length_cast_ne_zero h)

/-- Helper: shifting every element by `c` shifts the mean by `c`. -/
theorem mean_shift (numbers : List α) (c : α) (h : Pre numbers) :
    meanGen (numbers.map (fun x => x + c)) = meanGen numbers + c := by
  unfold meanGen
  rw [List.length_map, sum_map_add_const, add_div, mul_div_cancel_left₀ c (length_cast_ne_zero h)]

/-- Helper: scaling every element by `c` scales the mean by `c`. -/
theorem mean_scale (numbers : List α) (c : α) :
    meanGen (numbers.map (fun x => c * x)) = c * meanGen numbers := by
  unfold meanGen
  rw [List.length_map, sum_map_mul_const, mul_div_assoc]

/-- Helper: the mean is invariant under permutation. -/
theorem mean_perm {l l' : List α} (hp : List.Perm l' l) : meanGen l' = meanGen l := by
  unfold meanGen
  rw [hp.sum_eq, hp.length_eq]

/-- Property 1: the MAD is an average of absolute values, hence non-negative. -/
def nonneg_prop (numbers : List α) : Prop := 0 ≤ madGen numbers

theorem nonneg_thm (numbers : List α) : nonneg_prop numbers := by
  unfold nonneg_prop madGen
  exact div_nonneg (List.sum_nonneg (terms_nonneg numbers _)) (Nat.cast_nonneg _)

/-- Property 2 (defining formula): `MAD * n = Σ |xᵢ - sum / n|`, i.e. the result is
exactly `sum(abs(x - mean) for x in numbers) / len(numbers)` with `mean = sum / len`. -/
def formula_prop (numbers : List α) : Prop :=
  madGen numbers * numbers.length =
    (numbers.map (fun x => |x - numbers.sum / numbers.length|)).sum

theorem formula_thm (numbers : List α) (h : Pre numbers) : formula_prop numbers := by
  unfold formula_prop madGen meanGen
  exact div_mul_cancel₀ _ (length_cast_ne_zero h)

/-- Property 3: the MAD vanishes exactly when every element equals the mean. -/
def eq_zero_iff_prop (numbers : List α) : Prop :=
  madGen numbers = 0 ↔ ∀ x ∈ numbers, x = meanGen numbers

theorem eq_zero_iff_thm (numbers : List α) (h : Pre numbers) : eq_zero_iff_prop numbers := by
  unfold eq_zero_iff_prop
  constructor
  · intro hmad
    unfold madGen at hmad
    rcases div_eq_zero_iff.mp hmad with hsum | hlen
    · intro x hx
      have hmem : |x - meanGen numbers| ∈ numbers.map (fun x => |x - meanGen numbers|) :=
        List.mem_map_of_mem hx
      have hle := List.single_le_sum (terms_nonneg numbers _) _ hmem
      rw [hsum] at hle
      have h0 : |x - meanGen numbers| = 0 := le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp h0)
    · exact absurd hlen (length_cast_ne_zero h)
  · intro hall
    unfold madGen
    rw [List.sum_eq_zero, zero_div]
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hall x hx, sub_self, abs_zero]

/-- Property 4: a constant list has MAD `0`. -/
def const_prop (numbers : List α) : Prop :=
  ∀ c : α, (∀ x ∈ numbers, x = c) → madGen numbers = 0

theorem const_thm (numbers : List α) (h : Pre numbers) : const_prop numbers := by
  intro c hc
  have hiff : madGen numbers = 0 ↔ ∀ x ∈ numbers, x = meanGen numbers :=
    eq_zero_iff_thm numbers h
  rw [hiff]
  intro x hx
  rw [hc x hx, mean_of_const numbers c h hc]

/-- Property 5: the MAD never exceeds any bound on the individual absolute deviations
(in particular it is at most the largest absolute deviation). -/
def bound_prop (numbers : List α) : Prop :=
  ∀ B : α, (∀ x ∈ numbers, |x - meanGen numbers| ≤ B) → madGen numbers ≤ B

theorem bound_thm (numbers : List α) (h : Pre numbers) : bound_prop numbers := by
  intro B hB
  unfold madGen
  rw [div_le_iff₀ (length_cast_pos h)]
  have hle : (numbers.map (fun x => |x - meanGen numbers|)).sum ≤
      (numbers.map (fun x => |x - meanGen numbers|)).length • B := by
    apply List.sum_le_card_nsmul
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hB x hx
  rw [List.length_map, nsmul_eq_mul, mul_comm] at hle
  exact hle

/-- Property 6: translation invariance, `MAD(x + c) = MAD(x)`. -/
def shift_prop (numbers : List α) : Prop :=
  ∀ c : α, madGen (numbers.map (fun x => x + c)) = madGen numbers

theorem shift_thm (numbers : List α) (h : Pre numbers) : shift_prop numbers := by
  intro c
  unfold madGen
  rw [mean_shift numbers c h, List.length_map, List.map_map]
  have hfun : (fun x => |x - (meanGen numbers + c)|) ∘ (fun x => x + c) =
      fun x => |x - meanGen numbers| := by
    funext x
    simp only [Function.comp, add_sub_add_right_eq_sub]
  rw [hfun]

/-- Property 7: absolute homogeneity, `MAD(c * x) = |c| * MAD(x)`. -/
def scale_prop (numbers : List α) : Prop :=
  ∀ c : α, madGen (numbers.map (fun x => c * x)) = |c| * madGen numbers

theorem scale_thm (numbers : List α) : scale_prop numbers := by
  intro c
  unfold madGen
  rw [mean_scale numbers c, List.length_map, List.map_map]
  have hfun : (fun x => |x - c * meanGen numbers|) ∘ (fun x => c * x) =
      fun x => |c| * |x - meanGen numbers| := by
    funext x
    simp only [Function.comp, ← mul_sub, abs_mul]
  rw [hfun, List.sum_map_mul_left, mul_div_assoc]

/-- Property 8: the MAD does not depend on the order of the data. -/
def perm_prop (numbers : List α) : Prop :=
  ∀ l' : List α, List.Perm l' numbers → madGen l' = madGen numbers

theorem perm_thm (numbers : List α) : perm_prop numbers := by
  intro l' hp
  unfold madGen
  rw [mean_perm hp, (hp.map _).sum_eq, hp.length_eq]

/-- Property 9: a single data point has MAD `0`. -/
def singleton_prop (numbers : List α) : Prop :=
  ∀ x : α, numbers = [x] → madGen numbers = 0

theorem singleton_thm (numbers : List α) : singleton_prop numbers := by
  intro x hx
  subst hx
  simp [madGen, meanGen]

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties above. -/
def Post_prop (numbers : List α) : Prop :=
  nonneg_prop numbers ∧ formula_prop numbers ∧ eq_zero_iff_prop numbers ∧
    const_prop numbers ∧ bound_prop numbers ∧ shift_prop numbers ∧
    scale_prop numbers ∧ perm_prop numbers ∧ singleton_prop numbers

end Properties

/-! ## Property-based tests (on the executable `ℚ` layer; the same statements are
proved for `ℝ` by the generic theorems above, which have no executable check -- `Real`
comparisons are not computable).  Non-empty inputs are produced by construction as
`x :: xs`, so no sample is discarded by a precondition. -/

/-- Executable form of `Post_prop` (the `∀`-quantified parts are sampled on
concrete shift/scale constants and on `reverse` as a permutation). -/
def postCheck (l : List ℚ) (c : ℚ) : Bool :=
  let m := meanRat l
  let devs := l.map (fun x => |x - m|)
  decide (0 ≤ madRat l) &&
  decide (madRat l * l.length = (l.map (fun x => |x - l.sum / l.length|)).sum) &&
  decide ((madRat l = 0) ↔ ∀ x ∈ l, x = m) &&
  decide (madRat (List.replicate l.length c) = 0) &&
  decide (madRat l ≤ devs.foldr max 0) &&
  decide (madRat (l.map (fun x => x + c)) = madRat l) &&
  decide (madRat (l.map (fun x => c * x)) = |c| * madRat l) &&
  decide (madRat l.reverse = madRat l) &&
  decide (madRat [c] = 0)

-- nonneg_prop (holds even for `[]`)
#eval Plausible.Testable.check (∀ l : List ℚ, 0 ≤ madRat l)
-- formula_prop
#eval Plausible.Testable.check (∀ (x : ℚ) (xs : List ℚ),
  madRat (x :: xs) * (x :: xs).length =
    ((x :: xs).map (fun y => |y - (x :: xs).sum / (x :: xs).length|)).sum)
-- eq_zero_iff_prop
#eval Plausible.Testable.check (∀ (x : ℚ) (xs : List ℚ),
  decide ((madRat (x :: xs) = 0) ↔ ∀ y ∈ x :: xs, y = meanRat (x :: xs)) = true)
-- const_prop
#eval Plausible.Testable.check (∀ (n : Nat) (c : ℚ), madRat (List.replicate (n + 1) c) = 0)
-- bound_prop (with the maximal absolute deviation as the bound)
#eval Plausible.Testable.check (∀ (x : ℚ) (xs : List ℚ),
  madRat (x :: xs) ≤ ((x :: xs).map (fun y => |y - meanRat (x :: xs)|)).foldr max 0)
-- shift_prop
#eval Plausible.Testable.check (∀ (x : ℚ) (xs : List ℚ) (c : ℚ),
  madRat ((x :: xs).map (fun y => y + c)) = madRat (x :: xs))
-- scale_prop
#eval Plausible.Testable.check (∀ (l : List ℚ) (c : ℚ),
  madRat (l.map (fun x => c * x)) = |c| * madRat l)
-- perm_prop (`reverse` and `rotate` are permutations)
#eval Plausible.Testable.check (∀ l : List ℚ, madRat l.reverse = madRat l)
#eval Plausible.Testable.check (∀ (l : List ℚ) (k : Nat), madRat (l.rotate k) = madRat l)
-- singleton_prop
#eval Plausible.Testable.check (∀ x : ℚ, madRat [x] = 0)
-- Post_prop (executable form)
#eval Plausible.Testable.check (∀ (x : ℚ) (xs : List ℚ) (c : ℚ), postCheck (x :: xs) c = true)

-- Bounded / exhaustive PBTs on small data.
example : (List.range 30).all (fun n =>
    let l : List ℚ := (List.range (n + 1)).map (fun i => (i : ℚ))
    postCheck l 3 && postCheck (l.map (fun x => x * x - 7)) (-2)) = true := by
  native_decide
example : ((List.range 8).flatMap fun a => (List.range 8).flatMap fun b => (List.range 8).map fun c =>
    postCheck [(a : ℚ) - 3, (b : ℚ) / 2, (c : ℚ) * 5] ((a : ℚ) - (b : ℚ))).all id = true := by
  native_decide
-- FloatLayer: non-negativity on sampled integer-valued floats (the `Float` layer is
-- executable; no general `Float` arithmetic theorem is stated because the primitive
-- `Float` operations are opaque to the kernel).
#eval Plausible.Testable.check (∀ (n : Nat) (l : List Nat),
  0 ≤ mean_absolute_deviation ((n :: l).map Nat.toFloat))

/-! ## Correctness theorem: `Pre → Post` -/

section Correctness
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem correctness (numbers : List α) (h : Pre numbers) : Post_prop numbers :=
  ⟨nonneg_thm numbers, formula_thm numbers h, eq_zero_iff_thm numbers h, const_thm numbers h,
    bound_thm numbers h, shift_thm numbers h, scale_thm numbers, perm_thm numbers,
    singleton_thm numbers⟩

/-- The correctness theorem specialised to the rational layer. -/
theorem correctness_rat (numbers : List ℚ) (h : Pre numbers) : Post_prop numbers :=
  correctness numbers h

/-- The correctness theorem specialised to the real layer. -/
theorem correctness_real (numbers : List ℝ) (h : Pre numbers) : Post_prop numbers :=
  correctness numbers h

end Correctness

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- FloatLayer, imperative: two accumulation loops, as a Python programmer would write
the two `sum` calls by hand. -/
def mean_absolute_deviation_imp (numbers : List Float) : Float := Id.run do
  let mut total : Float := 0
  for x in numbers do
    total := total + x
  let n : Float := numbers.length.toFloat
  let mean : Float := total / n
  let mut acc : Float := 0
  for x in numbers do
    acc := acc + Float.abs (x - mean)
  return acc / n

section ImperativeGeneric
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Mathematical layer, imperative. -/
def madGen_imp (numbers : List α) : α := Id.run do
  let mut total : α := 0
  for x in numbers do
    total := total + x
  let n : α := numbers.length
  let mean : α := total / n
  let mut acc : α := 0
  for x in numbers do
    acc := acc + |x - mean|
  return acc / n

end ImperativeGeneric

/-- RatLayer, imperative (executable). -/
abbrev madRat_imp : List ℚ → ℚ := madGen_imp

/-! ## Imperative tests -/

example : Float.abs (mean_absolute_deviation_imp [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by
  native_decide
example : Float.abs (mean_absolute_deviation_imp [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide
example : Float.abs (mean_absolute_deviation_imp [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide
#eval mean_absolute_deviation_imp [1.0, 2.0, 3.0, 4.0]   -- 1.000000

example : madRat_imp [1, 2, 3] = 2 / 3 := by native_decide
example : madRat_imp [1, 2, 3, 4] = 1 := by native_decide
example : madRat_imp [1, 2, 3, 4, 5] = 6 / 5 := by native_decide
#eval madRat_imp [1, 2, 3, 4, 5]   -- 6/5
#eval Plausible.Testable.check (∀ l : List ℚ, madRat_imp l = madRat l)

/-! ## Equivalence theorems: functional = imperative -/

/-- FloatLayer: the functional and imperative `Float` programs perform exactly the same
floating-point operations in the same order, so they are equal (structurally). -/
theorem float_equiv_thm (numbers : List Float) :
    mean_absolute_deviation numbers = mean_absolute_deviation_imp numbers := by
  simp [mean_absolute_deviation, mean_absolute_deviation_imp, floatSum]

section EquivGeneric
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Helper: a running-sum loop computes `init + Σ xᵢ`. -/
theorem foldl_add_eq_sum (l : List α) (init : α) :
    l.foldl (fun acc x => acc + x) init = init + l.sum := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih => simp only [List.foldl_cons, List.sum_cons, ih]; ring

/-- Helper: a running-sum-of-deviations loop computes `init + Σ |xᵢ - m|`. -/
theorem foldl_add_abs_eq_sum (l : List α) (m init : α) :
    l.foldl (fun acc x => acc + |x - m|) init = init + (l.map (fun x => |x - m|)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

/-- Mathematical layer: functional = imperative (for `ℚ` and `ℝ` alike). -/
theorem equiv_thm (numbers : List α) : madGen numbers = madGen_imp numbers := by
  simp [madGen_imp, madGen, meanGen, foldl_add_eq_sum, foldl_add_abs_eq_sum]

/-- Equivalence specialised to the rational layer. -/
theorem equiv_rat_thm (numbers : List ℚ) : madRat numbers = madRat_imp numbers :=
  equiv_thm numbers

/-- Equivalence specialised to the real layer. -/
theorem equiv_real_thm (numbers : List ℝ) : madReal numbers = madGen_imp numbers :=
  equiv_thm numbers

end EquivGeneric

end humaneval_4_mean_absolute_deviation

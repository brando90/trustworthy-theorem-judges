import Mathlib

/-!
# HumanEval/4 — `mean_absolute_deviation`

Lean 4 formalization of the Python program

```python
def mean_absolute_deviation(numbers: List[float]) -> float:
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)
```

* `FloatLayer` — executable `Float` implementation mirroring the Python code
  operation-for-operation (left-to-right sums, as Python's `sum`), ground unit
  tests (the `check` function of the Python file), an imperative version written
  with `Id.run do`, and a structural equivalence proof.
* The mathematical model `mad` is stated generically over any linearly ordered
  field (`ℚ` and `ℝ` are the instances of interest).  All property theorems,
  the post-condition and the correctness theorem live there, and the `ℚ`
  instance (exact arithmetic, computable) is used for property-based tests.
  Every finite IEEE-754 `Float` is a rational number, so the `ℚ` instance
  preserves the admissible input domain of the Python function.  A theorem
  shows that the `ℚ` and `ℝ` instances agree under `Rat.cast`.
* Python raises `ZeroDivisionError` on the empty list; the pre-condition
  `Pre` therefore requires a non-empty list.  The `Option`-valued wrapper
  `FloatLayer.meanAbsoluteDeviation?` models that exceptional case explicitly.
-/

namespace humaneval_4_mean_absolute_deviation

/-! ## FloatLayer: executable implementation (mirrors the Python program) -/

namespace FloatLayer

/-- `sum(numbers)` in Python: left fold starting from `0`. -/
def pySum (numbers : List Float) : Float :=
  numbers.foldl (· + ·) 0

/-- Functional translation of `mean_absolute_deviation`. -/
def meanAbsoluteDeviation (numbers : List Float) : Float :=
  let n : Float := numbers.length.toFloat
  let mean : Float := pySum numbers / n
  pySum (numbers.map (fun x => Float.abs (x - mean))) / n

/-- Variant modelling Python's `ZeroDivisionError` on the empty list (`none`). -/
def meanAbsoluteDeviation? (numbers : List Float) : Option Float :=
  if numbers.isEmpty then none else some (meanAbsoluteDeviation numbers)

/-! ### Unit tests (the `check` function of the Python file) -/

example : Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by native_decide
example : Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by native_decide
example : Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide
example : meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0] == 1.0 := by native_decide
example : (meanAbsoluteDeviation? []).isNone = true := by native_decide
example : (meanAbsoluteDeviation? [1.0, 2.0, 3.0, 4.0]).isSome = true := by native_decide

#eval meanAbsoluteDeviation [1.0, 2.0, 3.0]            -- 0.666667
#eval meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0]       -- 1.000000
#eval meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0, 5.0]  -- 1.200000
#eval meanAbsoluteDeviation? []                        -- none

end FloatLayer

/-! ## Pre-condition -/

/-- Python divides by `len(numbers)` and raises `ZeroDivisionError` on `[]`,
so the admissible inputs are the non-empty lists. -/
def Pre {β : Type*} (xs : List β) : Prop := xs ≠ []

/-! ## Mathematical model over a linearly ordered field -/

section Math

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The arithmetic mean `sum(numbers) / len(numbers)`. -/
def mean (xs : List α) : α := xs.sum / (xs.length : α)

/-- Mean absolute deviation around the mean:
`sum(abs(x - mean) for x in numbers) / len(numbers)`. -/
def mad (xs : List α) : α :=
  (xs.map (fun x => |x - mean xs|)).sum / (xs.length : α)

/-! ### Unit tests on the exact `ℚ` instance -/

example : mad ([1, 2, 3] : List ℚ) = 2 / 3 := by native_decide
example : mad ([1, 2, 3, 4] : List ℚ) = 1 := by native_decide
example : mad ([1, 2, 3, 4, 5] : List ℚ) = 6 / 5 := by native_decide

#eval mad ([1, 2, 3] : List ℚ)           -- 2/3
#eval mad ([1, 2, 3, 4] : List ℚ)        -- 1
#eval mad ([1, 2, 3, 4, 5] : List ℚ)     -- 6/5

/-! ### Helper lemmas -/

theorem length_pos_of_pre {xs : List α} (h : Pre xs) : (0 : α) < xs.length := by
  have : 0 < xs.length := List.length_pos_iff.mpr h
  exact_mod_cast this

theorem length_ne_zero_of_pre {xs : List α} (h : Pre xs) : (xs.length : α) ≠ 0 :=
  (length_pos_of_pre h).ne'

theorem list_sum_eq_zero_iff_of_nonneg {l : List α} (h : ∀ x ∈ l, 0 ≤ x) :
    l.sum = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have ht := ih h.2
    have hts : 0 ≤ t.sum := List.sum_nonneg h.2
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro hsum
      have ha : a = 0 := by linarith [h.1]
      have hts0 : t.sum = 0 := by linarith
      exact ⟨ha, ht.mp hts0⟩
    · rintro ⟨ha, ht'⟩
      rw [ha, ht.mpr ht', add_zero]

theorem mean_map_add (xs : List α) (c : α) (h : Pre xs) :
    mean (xs.map (· + c)) = mean xs + c := by
  have hn := length_ne_zero_of_pre h
  unfold mean
  rw [List.length_map, List.sum_map_add, List.map_const', List.sum_replicate, List.map_id',
    nsmul_eq_mul]
  field_simp
  ring

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem mean_map_mul (xs : List α) (c : α) :
    mean (xs.map (c * ·)) = c * mean xs := by
  unfold mean
  rw [List.length_map, List.sum_map_mul_left, List.map_id', mul_div_assoc]

/-! ### Properties -/

/-- Defining equations of the two Python statements, in product form:
`mean * len = sum(numbers)` and `MAD * len = sum(abs(x - mean))`. -/
def mad_spec_prop (xs : List α) : Prop :=
  mean xs * (xs.length : α) = xs.sum ∧
    mad xs * (xs.length : α) = (xs.map (fun x => |x - mean xs|)).sum

theorem mad_spec_thm (xs : List α) (h : Pre xs) : mad_spec_prop xs := by
  have hn := length_ne_zero_of_pre h
  unfold mad_spec_prop mad mean
  constructor
  · exact div_mul_cancel₀ _ hn
  · exact div_mul_cancel₀ _ hn

/-- MAD is never negative. -/
def mad_nonneg_prop (xs : List α) : Prop := 0 ≤ mad xs

theorem mad_nonneg_thm (xs : List α) : mad_nonneg_prop xs := by
  unfold mad_nonneg_prop mad
  apply div_nonneg
  · apply List.sum_nonneg
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, _, rfl⟩ := hy
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- MAD vanishes exactly when every element equals the mean (constant data). -/
def mad_eq_zero_iff_prop (xs : List α) : Prop :=
  mad xs = 0 ↔ ∀ x ∈ xs, x = mean xs

theorem mad_eq_zero_iff_thm (xs : List α) (h : Pre xs) : mad_eq_zero_iff_prop xs := by
  unfold mad_eq_zero_iff_prop mad
  have hn := length_ne_zero_of_pre h
  rw [div_eq_zero_iff, or_iff_left hn]
  rw [list_sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro hall x hx
      have := hall |x - mean xs| (List.mem_map.mpr ⟨x, hx, rfl⟩)
      rwa [abs_eq_zero, sub_eq_zero] at this
    · intro hall y hy
      rw [List.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [abs_eq_zero, sub_eq_zero]
      exact hall x hx
  · intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, _, rfl⟩ := hy
    exact abs_nonneg _

/-- MAD is invariant under translating every data point by the same constant. -/
def mad_shift_prop (xs : List α) : Prop := ∀ c : α, mad (xs.map (· + c)) = mad xs

theorem mad_shift_thm (xs : List α) (h : Pre xs) : mad_shift_prop xs := by
  intro c
  unfold mad
  rw [mean_map_add xs c h, List.length_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  ring_nf

/-- MAD is absolutely homogeneous: scaling the data by `c` scales MAD by `|c|`. -/
def mad_scale_prop (xs : List α) : Prop := ∀ c : α, mad (xs.map (c * ·)) = |c| * mad xs

theorem mad_scale_thm (xs : List α) : mad_scale_prop xs := by
  intro c
  unfold mad
  rw [mean_map_mul, List.length_map, List.map_map, ← mul_div_assoc]
  congr 1
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  rw [← mul_sub, abs_mul]

/-- MAD does not depend on the order of the data. -/
def mad_perm_prop (xs : List α) : Prop := ∀ ys : List α, xs.Perm ys → mad xs = mad ys

omit [IsStrictOrderedRing α] in
theorem mad_perm_thm (xs : List α) : mad_perm_prop xs := by
  intro ys hp
  have hmean : mean xs = mean ys := by
    unfold mean
    rw [hp.sum_eq, hp.length_eq]
  unfold mad
  rw [hmean, hp.length_eq, (hp.map (fun x => |x - mean ys|)).sum_eq]

/-- MAD lies between the smallest and the largest absolute deviation. -/
def mad_bounds_prop (xs : List α) : Prop :=
  ∀ lo hi : α, (∀ x ∈ xs, lo ≤ |x - mean xs|) → (∀ x ∈ xs, |x - mean xs| ≤ hi) →
    lo ≤ mad xs ∧ mad xs ≤ hi

theorem mad_bounds_thm (xs : List α) (h : Pre xs) : mad_bounds_prop xs := by
  intro lo hi hlo hhi
  have hn := length_pos_of_pre h
  unfold mad
  set ds := xs.map (fun x => |x - mean xs|) with hds
  have hlen : ds.length = xs.length := by rw [hds, List.length_map]
  have hlo' : ∀ d ∈ ds, lo ≤ d := by
    intro d hd
    rw [hds, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact hlo x hx
  have hhi' : ∀ d ∈ ds, d ≤ hi := by
    intro d hd
    rw [hds, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact hhi x hx
  have h1 : ds.length • lo ≤ ds.sum := List.card_nsmul_le_sum ds lo hlo'
  have h2 : ds.sum ≤ ds.length • hi := List.sum_le_card_nsmul ds hi hhi'
  rw [nsmul_eq_mul, hlen] at h1 h2
  constructor
  · rw [le_div_iff₀ hn]; linarith
  · rw [div_le_iff₀ hn]; linarith

/-- Two-point data sets: MAD is half the distance between the points. -/
def mad_pair_prop (xs : List α) : Prop :=
  ∀ a b : α, xs = [a, b] → mad xs = |a - b| / 2

theorem mad_pair_thm (xs : List α) : mad_pair_prop xs := by
  intro a b hxs
  subst hxs
  unfold mad mean
  have hlen : ((([a, b] : List α).length : ℕ) : α) = 2 := by norm_num
  simp only [List.sum_cons, List.sum_nil, List.map_cons, List.map_nil, add_zero]
  rw [hlen]
  have h1 : a - (a + b) / 2 = (a - b) / 2 := by ring
  have h2 : b - (a + b) / 2 = -((a - b) / 2) := by ring
  rw [h1, h2, abs_neg, abs_div, abs_two]
  ring

/-- A constant data set has zero deviation. -/
def mad_replicate_prop (xs : List α) : Prop :=
  ∀ (n : ℕ) (c : α), xs = List.replicate n c → mad xs = 0

theorem mad_replicate_thm (xs : List α) : mad_replicate_prop xs := by
  intro n c hxs
  subst hxs
  unfold mad
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hmean : mean (List.replicate n c) = c := by
      unfold mean
      rw [List.sum_replicate, List.length_replicate, nsmul_eq_mul]
      have : (n : α) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [hmean, sub_self, abs_zero, mul_zero, zero_div]

/-! ### Post-condition -/

/-- Post-condition: conjunction of all stated properties. -/
def Post_prop (xs : List α) : Prop :=
  mad_spec_prop xs ∧ mad_nonneg_prop xs ∧ mad_eq_zero_iff_prop xs ∧ mad_shift_prop xs ∧
    mad_scale_prop xs ∧ mad_perm_prop xs ∧ mad_bounds_prop xs ∧ mad_pair_prop xs ∧
    mad_replicate_prop xs

/-! ### Property-based tests (on the exact, computable `ℚ` instance)

Non-empty inputs are generated directly as `x :: xs`, so no sample is discarded. -/

-- mad_spec_prop
#eval Plausible.Testable.check
  (∀ (x : ℚ) (xs : List ℚ),
    mean (x :: xs) * ((x :: xs).length : ℚ) = (x :: xs).sum ∧
    mad (x :: xs) * ((x :: xs).length : ℚ) = ((x :: xs).map (fun y => |y - mean (x :: xs)|)).sum)

-- mad_nonneg_prop
#eval Plausible.Testable.check (∀ xs : List ℚ, 0 ≤ mad xs)
#eval Plausible.Testable.check (∀ xs : List ℤ, 0 ≤ mad (xs.map (Int.cast : ℤ → ℚ)))

-- mad_eq_zero_iff_prop
#eval Plausible.Testable.check
  (∀ (x : ℚ) (xs : List ℚ), (mad (x :: xs) = 0) ↔ ((x :: xs).all (fun y => y == mean (x :: xs))))
#eval Plausible.Testable.check
  (∀ (x : ℚ) (xs : List ℤ), mad (x :: xs.map (fun k => x + (k : ℚ) ^ 2)) = 0 ↔ xs.all (· == 0))

-- mad_shift_prop
#eval Plausible.Testable.check
  (∀ (x c : ℚ) (xs : List ℚ), mad ((x :: xs).map (· + c)) = mad (x :: xs))

-- mad_scale_prop
#eval Plausible.Testable.check (∀ (xs : List ℚ) (c : ℚ), mad (xs.map (c * ·)) = |c| * mad xs)

-- mad_perm_prop (reversal and rotation are permutations)
#eval Plausible.Testable.check (∀ xs : List ℚ, mad xs.reverse = mad xs)
#eval Plausible.Testable.check (∀ (xs : List ℚ) (k : ℕ), mad (xs.rotate k) = mad xs)

-- mad_bounds_prop (instantiated with the extreme deviations of the sample)
#eval Plausible.Testable.check
  (∀ (x : ℚ) (xs : List ℚ),
    ((x :: xs).map (fun y => |y - mean (x :: xs)|)).foldl min |x - mean (x :: xs)| ≤ mad (x :: xs) ∧
    mad (x :: xs) ≤ ((x :: xs).map (fun y => |y - mean (x :: xs)|)).foldl max |x - mean (x :: xs)|)

-- mad_pair_prop
#eval Plausible.Testable.check (∀ a b : ℚ, mad [a, b] = |a - b| / 2)

-- mad_replicate_prop
#eval Plausible.Testable.check (∀ (n : ℕ) (c : ℚ), mad (List.replicate n c) = 0)

-- Post_prop: executable shape of the whole conjunction, exhaustively on small inputs
example : (List.range 8).all (fun n =>
    (List.range 8).all (fun m =>
      let xs : List ℚ := [(n : ℚ), (m : ℚ), (n : ℚ) - (m : ℚ)]
      decide (mean xs * 3 = xs.sum ∧ mad xs * 3 = (xs.map (fun y => |y - mean xs|)).sum) &&
      decide (0 ≤ mad xs) &&
      decide (mad xs = 0 ↔ ∀ y ∈ xs, y = mean xs) &&
      decide (mad (xs.map (· + 7)) = mad xs) &&
      decide (mad (xs.map ((-3) * ·)) = 3 * mad xs) &&
      decide (mad xs.reverse = mad xs) &&
      decide (mad [(n : ℚ), (m : ℚ)] = |(n : ℚ) - m| / 2) &&
      decide (mad (List.replicate (n + 1) (m : ℚ)) = 0))) = true := by native_decide

/-! ### Correctness theorem: `Pre → Post` -/

theorem correctness (xs : List α) (h : Pre xs) : Post_prop xs :=
  ⟨mad_spec_thm xs h, mad_nonneg_thm xs, mad_eq_zero_iff_thm xs h, mad_shift_thm xs h,
    mad_scale_thm xs, mad_perm_thm xs, mad_bounds_thm xs h, mad_pair_thm xs,
    mad_replicate_thm xs⟩

/-! ### Imperative implementation (mathematical model) -/

/-- Imperative version with mutable accumulators, as the Python loops would run. -/
def madImp (xs : List α) : α := Id.run do
  let mut total : α := 0
  for x in xs do
    total := total + x
  let n : α := (xs.length : α)
  let mean : α := total / n
  let mut dev : α := 0
  for x in xs do
    dev := dev + |x - mean|
  return dev / n

example : madImp ([1, 2, 3] : List ℚ) = 2 / 3 := by native_decide
example : madImp ([1, 2, 3, 4] : List ℚ) = 1 := by native_decide
example : madImp ([1, 2, 3, 4, 5] : List ℚ) = 6 / 5 := by native_decide
#eval madImp ([1, 2, 3, 4, 5] : List ℚ)  -- 6/5
#eval Plausible.Testable.check (∀ xs : List ℚ, madImp xs = mad xs)

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem foldl_add_eq_sum (xs : List α) :
    xs.foldl (fun acc x => acc + x) 0 = xs.sum := by
  rw [List.sum_eq_foldl]

omit [IsStrictOrderedRing α] in
theorem foldl_add_abs_eq_sum (xs : List α) (m : α) :
    xs.foldl (fun acc x => acc + |x - m|) 0 = (xs.map (fun x => |x - m|)).sum := by
  rw [List.sum_eq_foldl, List.foldl_map]

omit [IsStrictOrderedRing α] in
/-- The imperative and functional mathematical models agree on every input. -/
theorem madImp_eq_mad (xs : List α) : madImp xs = mad xs := by
  unfold madImp mad mean
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  rw [foldl_add_eq_sum, foldl_add_abs_eq_sum]

end Math

/-! ## Correspondence between the `ℚ` and `ℝ` instances of the model -/

theorem mean_rat_cast (xs : List ℚ) :
    mean (xs.map (Rat.cast : ℚ → ℝ)) = ((mean xs : ℚ) : ℝ) := by
  unfold mean
  rw [List.length_map, Rat.cast_div, Rat.cast_list_sum, Rat.cast_natCast]

theorem mad_rat_cast (xs : List ℚ) : mad (xs.map (Rat.cast : ℚ → ℝ)) = ((mad xs : ℚ) : ℝ) := by
  unfold mad
  rw [List.length_map, Rat.cast_div, Rat.cast_list_sum, Rat.cast_natCast, List.map_map,
    List.map_map, mean_rat_cast]
  congr 2
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  rw [Rat.cast_abs, Rat.cast_sub]

/-! ## FloatLayer: exceptional case, imperative implementation and equivalence -/

namespace FloatLayer

/-- The checked variant succeeds exactly on the admissible (non-empty) inputs ... -/
theorem meanAbsoluteDeviation?_eq_some (numbers : List Float) (h : Pre numbers) :
    meanAbsoluteDeviation? numbers = some (meanAbsoluteDeviation numbers) := by
  have h' : numbers ≠ [] := h
  unfold meanAbsoluteDeviation?
  simp [List.isEmpty_iff, h']

/-- ... and reports the `ZeroDivisionError` case exactly on the empty list. -/
theorem meanAbsoluteDeviation?_eq_none_iff (numbers : List Float) :
    meanAbsoluteDeviation? numbers = none ↔ ¬ Pre numbers := by
  unfold meanAbsoluteDeviation? Pre
  cases numbers <;> simp

/-- Imperative `Float` version: the two Python `sum` loops with mutable accumulators. -/
def meanAbsoluteDeviationImp (numbers : List Float) : Float := Id.run do
  let mut total : Float := 0
  for x in numbers do
    total := total + x
  let n : Float := numbers.length.toFloat
  let mean : Float := total / n
  let mut dev : Float := 0
  for x in numbers do
    dev := dev + Float.abs (x - mean)
  return dev / n

example : Float.abs (meanAbsoluteDeviationImp [1.0, 2.0, 3.0] - 2.0 / 3.0) < 1e-6 := by
  native_decide
example : Float.abs (meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 := by
  native_decide
example : Float.abs (meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0, 5.0] - 6.0 / 5.0) < 1e-6 := by
  native_decide
#eval meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0, 5.0]  -- 1.200000

theorem foldl_add_abs (xs : List Float) (m : Float) :
    xs.foldl (fun acc x => acc + Float.abs (x - m)) 0 =
      (xs.map (fun x => Float.abs (x - m))).foldl (· + ·) 0 := by
  rw [List.foldl_map]

/-- Functional and imperative `Float` implementations perform the same operations
in the same order, hence compute the same value (structural equivalence). -/
theorem meanAbsoluteDeviationImp_eq (numbers : List Float) :
    meanAbsoluteDeviationImp numbers = meanAbsoluteDeviation numbers := by
  unfold meanAbsoluteDeviationImp meanAbsoluteDeviation pySum
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  rw [foldl_add_abs]

end FloatLayer

end humaneval_4_mean_absolute_deviation

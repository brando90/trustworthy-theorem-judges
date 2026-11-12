import Mathlib

/-!
# HumanEval/4 - `mean_absolute_deviation`

Formal translation of the Python program

    def mean_absolute_deviation(numbers: List[float]) -> float:
        mean = sum(numbers) / len(numbers)
        return sum(abs(x - mean) for x in numbers) / len(numbers)

with the test obligations of its `check` function

    assert abs(candidate([1.0, 2.0, 3.0]) - 2.0/3.0) < 1e-6
    assert abs(candidate([1.0, 2.0, 3.0, 4.0]) - 1.0) < 1e-6
    assert abs(candidate([1.0, 2.0, 3.0, 4.0, 5.0]) - 6.0/5.0) < 1e-6

## Numeric layers used in this file

* `Float` layer (`meanAbsoluteDeviation`): the literal, executable transcription of the
  Python function on primitive `Float` (IEEE-754 binary64, the arithmetic CPython uses for
  `float`). Ground unit tests, the imperative implementation and the functional/imperative
  equivalence theorem live here. Primitive `Float` arithmetic is opaque to the kernel, so
  no general arithmetic law about it can be proved by reduction; the ground tests are
  discharged with `native_decide` / `#eval`.
* `Real` layer (`meanReal`, `madReal`): the exact mathematical model of the same
  computation. The intent of the Python program is mathematical ("MAD = average
  |x - x_mean|"), not a statement about IEEE-754 rounding, so all properties, the
  pre/post-condition and the correctness theorem are stated and proved over `Real`.
* `Rat` layer (`meanRat`, `madRat`): the same definition restricted to the rationals. It is
  computable, hence it provides the executable counterpart used by the property-based
  tests for the (non-executable) `Real` properties, both exhaustively on bounded sample
  data (`native_decide`) and randomly (`Plausible`).

## Precondition

Python evaluates `sum(numbers) / len(numbers)`, so the admissible inputs are exactly the
nonempty lists: `Pre xs := xs ≠ []` (`PreFloat` on the `Float` layer). An empty list raises
`ZeroDivisionError` in Python and is excluded from every obligation below.
-/

set_option maxHeartbeats 400000

namespace humaneval_4_mean_absolute_deviation

/-!
## 1. Functional implementation (executable `Float` layer)
-/

/-- Admissible inputs of the executable layer: `len(numbers)` must be nonzero. -/
def PreFloat (xs : List Float) : Prop := xs ≠ []

/-- `sum(numbers)`: a left fold, the same summation order Python's `sum` uses. -/
def floatSum (xs : List Float) : Float := xs.foldl (fun acc x => acc + x) 0

/-- `sum(f(x) for x in numbers)`: a left fold over a generator expression. -/
def floatSumMap (f : Float → Float) (xs : List Float) : Float :=
  xs.foldl (fun acc x => acc + f x) 0

/-- The Python function `mean_absolute_deviation`, on primitive `Float`s. -/
def meanAbsoluteDeviation (xs : List Float) : Float :=
  let n := xs.length.toFloat
  let mean := floatSum xs / n
  floatSumMap (fun x => Float.abs (x - mean)) xs / n

/-!
## 2. Unit tests (`Float` layer: ground instances of the Python `check` function)

`Float` has no `DecidableEq` instance in this toolchain, so exact equality of results is
tested through the `BEq` operation `==`, and the Python assertions are tested through their
`1e-6` tolerance.
-/

/-- The conjunction of the three assertions of the Python `check` function. -/
def PythonCheck : Prop :=
  Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0] - (2 : Float) / 3) < 1e-6 ∧
    Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 ∧
    Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0, 5.0] - (6 : Float) / 5) < 1e-6

example : PythonCheck := by
  simp only [PythonCheck]
  native_decide

example : (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0] == 1.0) = true := by native_decide

example : (meanAbsoluteDeviation [5.0, 5.0, 5.0] == 0.0) = true := by native_decide

example : (meanAbsoluteDeviation [-3.5] == 0.0) = true := by native_decide

example : Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0] - (2 : Float) / 3) < 1e-6 := by
  native_decide

example : Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0, 5.0] - (6 : Float) / 5) < 1e-6 := by
  native_decide

/-- `len(numbers) ≠ 0` is the executable form of the precondition `PreFloat`. -/
example : [1.0, 2.0, 3.0].length ≠ 0 := by native_decide

#eval meanAbsoluteDeviation [1.0, 2.0, 3.0]
#eval meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0]
#eval meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0, 5.0]
#eval meanAbsoluteDeviation [5.0, 5.0, 5.0]

/-!
## 3. Exact mathematical model over `Real`
-/

/-- `x_mean = sum(numbers) / len(numbers)`. -/
noncomputable def meanReal (xs : List ℝ) : ℝ := xs.sum / (xs.length : ℝ)

/-- `MAD = average |x - x_mean| = sum(|x - x_mean| for x in numbers) / len(numbers)`. -/
noncomputable def madReal (xs : List ℝ) : ℝ :=
  (xs.map (fun x => |x - meanReal xs|)).sum / (xs.length : ℝ)

/-!
## 4. Precondition
-/

/-- The Python program divides by `len(numbers)`, so the admissible data sets are exactly
the nonempty lists. -/
def Pre (xs : List ℝ) : Prop := xs ≠ []

/-!
### Auxiliary lemmas
-/

theorem length_pos_of_ne_nil {xs : List ℝ} (h : xs ≠ []) : 0 < (xs.length : ℝ) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons a l => exact_mod_cast Nat.succ_pos _

theorem length_ne_zero_of_ne_nil {xs : List ℝ} (h : xs ≠ []) : (xs.length : ℝ) ≠ 0 :=
  ne_of_gt (length_pos_of_ne_nil h)

theorem sum_map_add_const (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => x + c)).sum = xs.sum + (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

theorem sum_map_mul_const (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => c * x)).sum = c * xs.sum := by
  induction xs with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_mul_left (c : ℝ) (f : ℝ → ℝ) (xs : List ℝ) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_eq_length_mul_of_const (xs : List ℝ) (a : ℝ) (h : ∀ x ∈ xs, x = a) :
    xs.sum = (xs.length : ℝ) * a := by
  induction xs with
  | nil => simp
  | cons b l ih =>
    have hb : b = a := h b List.mem_cons_self
    have hl : ∀ x ∈ l, x = a := fun x hx => h x (List.mem_cons_of_mem b hx)
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, hb, ih hl]
    ring

theorem sum_le_length_mul (xs : List ℝ) (M : ℝ) (h : ∀ x ∈ xs, x ≤ M) :
    xs.sum ≤ (xs.length : ℝ) * M := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    have ha : a ≤ M := h a List.mem_cons_self
    have hl : l.sum ≤ (l.length : ℝ) * M := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 : a + l.sum ≤ M + (l.length : ℝ) * M := by linarith
    have h2 : M + (l.length : ℝ) * M = ((l.length : ℝ) + 1) * M := by ring
    linarith

theorem length_mul_le_sum (xs : List ℝ) (m : ℝ) (h : ∀ x ∈ xs, m ≤ x) :
    (xs.length : ℝ) * m ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    have ha : m ≤ a := h a List.mem_cons_self
    have hl : (l.length : ℝ) * m ≤ l.sum := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 : ((l.length : ℝ) + 1) * m ≤ m + l.sum := by linarith
    linarith

set_option linter.unusedVariables false in
theorem eq_zero_of_sum_eq_zero (xs : List ℝ) :
    ∀ (hsum : xs.sum = 0) (hnn : ∀ x ∈ xs, 0 ≤ x) (x : ℝ), x ∈ xs → x = 0 := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    intro hsum hnn x hx
    have ha : 0 ≤ a := hnn a List.mem_cons_self
    have hl : 0 ≤ l.sum := List.sum_nonneg (fun y hy => hnn y (List.mem_cons_of_mem a hy))
    have h1 : a + l.sum = 0 := by simpa using hsum
    have ha0 : a = 0 := by linarith
    have hl0 : l.sum = 0 := by linarith
    cases hx with
    | head => exact ha0
    | tail _ hy => exact ih hl0 (fun y hy' => hnn y (List.mem_cons_of_mem a hy')) x hy

theorem sum_map_abs_nonneg (f : ℝ → ℝ) (xs : List ℝ) : 0 ≤ (xs.map (fun x => |f x|)).sum :=
  List.sum_nonneg (fun y hy => by
    obtain ⟨x, _, hxy⟩ := List.mem_map.mp hy
    have hy' : y = |f x| := hxy.symm
    rw [hy']
    exact abs_nonneg _)

theorem mem_map_abs_eq_zero (f : ℝ → ℝ) (xs : List ℝ)
    (hsum : (xs.map (fun x => |f x|)).sum = 0) (x : ℝ) (hx : x ∈ xs) : |f x| = 0 :=
  eq_zero_of_sum_eq_zero _ hsum
    (fun y hy => by
      obtain ⟨z, _, hzy⟩ := List.mem_map.mp hy
      have hy' : y = |f z| := hzy.symm
      rw [hy']
      exact abs_nonneg _)
    _ (List.mem_map_of_mem hx)

theorem meanReal_map_add_const {xs : List ℝ} (h : xs ≠ []) (c : ℝ) :
    meanReal (xs.map (fun x => x + c)) = meanReal xs + c := by
  rw [meanReal, meanReal, sum_map_add_const, List.length_map, add_div,
    mul_comm (xs.length : ℝ) c, mul_div_cancel_right₀ _ (length_ne_zero_of_ne_nil h)]

theorem meanReal_map_mul_const (xs : List ℝ) (c : ℝ) :
    meanReal (xs.map (fun x => c * x)) = c * meanReal xs := by
  simp only [meanReal, sum_map_mul_const, List.length_map, mul_div_assoc]

theorem meanReal_eq_of_const {xs : List ℝ} (h : xs ≠ []) (a : ℝ) (hall : ∀ x ∈ xs, x = a) :
    meanReal xs = a := by
  rw [meanReal, sum_eq_length_mul_of_const xs a hall,
    mul_div_cancel_left₀ _ (length_ne_zero_of_ne_nil h)]

theorem meanReal_le_of_forall_le {xs : List ℝ} (h : xs ≠ []) (M : ℝ)
    (hM : ∀ x ∈ xs, x ≤ M) : meanReal xs ≤ M := by
  have hn : 0 < (xs.length : ℝ) := length_pos_of_ne_nil h
  rw [meanReal, div_le_iff₀' hn]
  exact sum_le_length_mul xs M hM

theorem le_meanReal_of_forall_le {xs : List ℝ} (h : xs ≠ []) (m : ℝ)
    (hm : ∀ x ∈ xs, m ≤ x) : m ≤ meanReal xs := by
  have hn : 0 < (xs.length : ℝ) := length_pos_of_ne_nil h
  rw [meanReal, le_div_iff₀' hn]
  exact length_mul_le_sum xs m hm

theorem madReal_map_add_const {xs : List ℝ} (h : xs ≠ []) (c : ℝ) :
    madReal (xs.map (fun x => x + c)) = madReal xs := by
  simp only [madReal, List.length_map]
  rw [meanReal_map_add_const h c, List.map_map]
  have key : (fun y : ℝ => |y - (meanReal xs + c)|) ∘ (fun x : ℝ => x + c)
      = (fun x : ℝ => |x - meanReal xs|) := by
    funext x
    show |(x + c) - (meanReal xs + c)| = |x - meanReal xs|
    rw [show (x + c) - (meanReal xs + c) = x - meanReal xs by ring]
  rw [key]

theorem madReal_map_mul_const (xs : List ℝ) (c : ℝ) :
    madReal (xs.map (fun x => c * x)) = |c| * madReal xs := by
  simp only [madReal, List.length_map]
  rw [meanReal_map_mul_const, List.map_map]
  have key : (fun y : ℝ => |y - c * meanReal xs|) ∘ (fun x : ℝ => c * x)
      = (fun x : ℝ => |c| * |x - meanReal xs|) := by
    funext x
    show |c * x - c * meanReal xs| = |c| * |x - meanReal xs|
    rw [← abs_mul, ← mul_sub]
  rw [key, sum_map_mul_left, mul_div_assoc]

theorem madReal_eq_zero_of_const {xs : List ℝ} (h : xs ≠ []) (a : ℝ)
    (hall : ∀ x ∈ xs, x = a) : madReal xs = 0 := by
  have hm : meanReal xs = a := meanReal_eq_of_const h a hall
  have hsum : (xs.map (fun x => |x - meanReal xs|)).sum = 0 := by
    rw [hm]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
    have hy' : y = |x - a| := hxy.symm
    rw [hy', hall x hx, sub_self, abs_zero]
  rw [madReal, hsum, zero_div]

theorem madReal_eq_zero_imp_const {xs : List ℝ} (h : xs ≠ []) (h0 : madReal xs = 0) :
    ∃ a : ℝ, ∀ x ∈ xs, x = a := by
  refine ⟨meanReal xs, ?_⟩
  have hsum : (xs.map (fun y => |y - meanReal xs|)).sum = 0 := by
    have h0' : (xs.map (fun y => |y - meanReal xs|)).sum / (xs.length : ℝ) = 0 := by
      simpa [madReal] using h0
    rcases div_eq_zero_iff.mp h0' with h1 | h2
    · exact h1
    · exact absurd h2 (length_ne_zero_of_ne_nil h)
  intro x hx
  have hz : |x - meanReal xs| = 0 :=
    mem_map_abs_eq_zero (fun y => y - meanReal xs) xs hsum x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

theorem madReal_le_interval {xs : List ℝ} (h : xs ≠ []) (lo hi : ℝ)
    (hlo : ∀ x ∈ xs, lo ≤ x) (hhi : ∀ x ∈ xs, x ≤ hi) : madReal xs ≤ hi - lo := by
  have hn : 0 < (xs.length : ℝ) := length_pos_of_ne_nil h
  have hm1 : lo ≤ meanReal xs := le_meanReal_of_forall_le h lo hlo
  have hm2 : meanReal xs ≤ hi := meanReal_le_of_forall_le h hi hhi
  have hbound : ∀ y ∈ xs.map (fun x => |x - meanReal xs|), y ≤ hi - lo := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
    have hy' : y = |x - meanReal xs| := hxy.symm
    rw [hy', abs_le]
    constructor
    · linarith [hlo x hx, hhi x hx, hm1, hm2]
    · linarith [hlo x hx, hhi x hx, hm1, hm2]
  have hsum : (xs.map (fun x => |x - meanReal xs|)).sum ≤ (xs.length : ℝ) * (hi - lo) := by
    have hle := sum_le_length_mul _ (hi - lo) hbound
    rwa [List.length_map] at hle
  rw [madReal, div_le_iff₀' hn]
  exact hsum

/-!
## 5. Properties of the specification
-/

/-- MAD is an average of nonnegative quantities, hence nonnegative. -/
def mad_nonneg_prop (xs : List ℝ) : Prop := 0 ≤ madReal xs

/-- A single data point deviates from its own mean by zero. -/
def mad_singleton_prop : Prop := ∀ x : ℝ, madReal [x] = 0

/-- MAD is invariant under translation of the whole data set (the mean translates too). -/
def mad_shift_prop (xs : List ℝ) : Prop :=
  ∀ c : ℝ, madReal (xs.map (fun x => x + c)) = madReal xs

/-- MAD scales by `|c|` when the data set is scaled by `c`. -/
def mad_scale_prop (xs : List ℝ) : Prop :=
  ∀ c : ℝ, madReal (xs.map (fun x => c * x)) = |c| * madReal xs

/-- A constant data set has MAD zero. -/
def mad_const_prop (xs : List ℝ) : Prop :=
  ∀ a : ℝ, (∀ x ∈ xs, x = a) → madReal xs = 0

/-- MAD is zero exactly for constant data sets. -/
def mad_eq_zero_iff_prop (xs : List ℝ) : Prop :=
  madReal xs = 0 ↔ ∃ a : ℝ, ∀ x ∈ xs, x = a

/-- MAD never exceeds the width of any interval containing the data, in particular the
range `max - min`. -/
def mad_le_range_prop (xs : List ℝ) : Prop :=
  ∀ lo hi : ℝ, (∀ x ∈ xs, lo ≤ x) → (∀ x ∈ xs, x ≤ hi) → madReal xs ≤ hi - lo

/-- The three ground values asserted by the Python `check` function. -/
def mad_values_prop : Prop :=
  madReal [1, 2, 3] = 2 / 3 ∧
    madReal [1, 2, 3, 4] = 1 ∧
    madReal [1, 2, 3, 4, 5] = 6 / 5

theorem mad_nonneg_thm (xs : List ℝ) : mad_nonneg_prop xs :=
  div_nonneg (sum_map_abs_nonneg (fun x => x - meanReal xs) xs) (Nat.cast_nonneg _)

theorem mad_singleton_thm : mad_singleton_prop := by
  intro x
  simp [madReal, meanReal]

theorem mad_shift_thm (xs : List ℝ) (h : Pre xs) : mad_shift_prop xs :=
  fun c => madReal_map_add_const h c

theorem mad_scale_thm (xs : List ℝ) : mad_scale_prop xs :=
  fun c => madReal_map_mul_const xs c

theorem mad_const_thm (xs : List ℝ) (h : Pre xs) : mad_const_prop xs :=
  fun a ha => madReal_eq_zero_of_const h a ha

theorem mad_eq_zero_iff_thm (xs : List ℝ) (h : Pre xs) : mad_eq_zero_iff_prop xs := by
  constructor
  · exact fun h0 => madReal_eq_zero_imp_const h h0
  · rintro ⟨a, ha⟩
    exact madReal_eq_zero_of_const h a ha

theorem mad_le_range_thm (xs : List ℝ) (h : Pre xs) : mad_le_range_prop xs :=
  fun lo hi hlo hhi => madReal_le_interval h lo hi hlo hhi

theorem mad_values_thm : mad_values_prop := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [madReal, meanReal]
    norm_num
  · have hm : meanReal [1, 2, 3, 4] = (5 / 2 : ℝ) := by simp only [meanReal]; norm_num
    have hmap : ([1, 2, 3, 4] : List ℝ).map (fun x => |x - 5 / 2|)
        = [|(1 : ℝ) - 5 / 2|, |(2 : ℝ) - 5 / 2|, |(3 : ℝ) - 5 / 2|, |(4 : ℝ) - 5 / 2|] := by rfl
    have h1 : |(1 : ℝ) - 5 / 2| = 3 / 2 := by norm_num
    have h2 : |(2 : ℝ) - 5 / 2| = 1 / 2 := by norm_num
    have h3 : |(3 : ℝ) - 5 / 2| = 1 / 2 := by norm_num
    have h4 : |(4 : ℝ) - 5 / 2| = 3 / 2 := by norm_num
    show (([1, 2, 3, 4] : List ℝ).map (fun x => |x - meanReal [1, 2, 3, 4]|)).sum / 4 = 1
    rw [hm, hmap, h1, h2, h3, h4]
    norm_num
  · simp only [madReal, meanReal]
    norm_num

/-!
## 6. Post-condition
-/

/-- Post-condition: for an admissible data set the value produced by the specification has
all the properties required of the mean absolute deviation. -/
def Post_prop (xs : List ℝ) : Prop :=
  mad_nonneg_prop xs ∧
    mad_shift_prop xs ∧
    mad_scale_prop xs ∧
    mad_const_prop xs ∧
    mad_eq_zero_iff_prop xs ∧
    mad_le_range_prop xs

/-!
## 7. Property-based tests

The properties above are stated over `Real`, which is not executable (`Real` comparisons are
not computable), so each of them is tested through its executable counterpart: the rational
model `madRat` (the very same definition on `ℚ`, where equality and order are decidable and
exact) and, where the statement is about rounding-free behaviour, the `Float` implementation
`meanAbsoluteDeviation` itself. Both bounded (exhaustive over sample data, `native_decide`)
and randomized (`Plausible`) tests are given.
-/

/-- `x_mean` on the rational layer: computable mirror of `meanReal`. -/
def meanRat (xs : List ℚ) : ℚ := xs.sum / (xs.length : ℚ)

/-- MAD on the rational layer: computable mirror of `madReal`. -/
def madRat (xs : List ℚ) : ℚ := (xs.map (fun x => |x - meanRat xs|)).sum / (xs.length : ℚ)

/-- The canonical embedding of a rational data set into the real model. -/
def realList (xs : List ℚ) : List ℝ :=
  match xs with
  | [] => []
  | x :: l => (x : ℝ) :: realList l

theorem cast_list_sum (xs : List ℚ) : (realList xs).sum = (xs.sum : ℝ) := by
  induction xs with
  | nil => simp [realList]
  | cons a l ih => simp only [realList, List.sum_cons, Rat.cast_add, ih]

theorem realList_length (xs : List ℚ) : (realList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a l ih => simp only [realList, List.length_cons, ih]

theorem map_abs_realList (xs : List ℚ) (m : ℚ) :
    (realList xs).map (fun y => |y - (m : ℝ)|) = realList (xs.map (fun x => |x - m|)) := by
  induction xs with
  | nil => simp [realList]
  | cons a l ih =>
    simp only [realList, List.map_cons, ih]
    rw [Rat.cast_abs, Rat.cast_sub]

/-- Cross-layer correspondence: the mean of rational data is the same number in the
executable `ℚ` model and in the `ℝ` specification. -/
theorem meanRat_cast (xs : List ℚ) : meanReal (realList xs) = (meanRat xs : ℝ) := by
  simp only [meanReal, meanRat, cast_list_sum, realList_length, Rat.cast_div, Rat.cast_natCast]

/-- Cross-layer correspondence: `madRat` *is* `madReal` restricted to rational data.
Consequently the property-based tests below, which are executed on `madRat`, test exactly
the `ℝ` specification of sections 5 and 6 on rational data sets. -/
theorem madRat_cast (xs : List ℚ) : madReal (realList xs) = (madRat xs : ℝ) := by
  simp only [madReal, madRat, meanRat_cast, realList_length, map_abs_realList, cast_list_sum,
    Rat.cast_div, Rat.cast_natCast]

/-- Transferring an exact rational computation into the real model. -/
example : madReal (realList [1, 2, 3]) = 2 / 3 := by
  rw [madRat_cast]
  have h : madRat [1, 2, 3] = (2 / 3 : ℚ) := by
    simp only [madRat, meanRat]
    norm_num
  rw [h]
  norm_num

example : madReal (realList [1, 2, 3, 4]) = 1 := by
  rw [madRat_cast]
  have h : madRat [1, 2, 3, 4] = (1 : ℚ) := by
    have hm : meanRat [1, 2, 3, 4] = (5 / 2 : ℚ) := by simp only [meanRat]; norm_num
    have hmap : ([1, 2, 3, 4] : List ℚ).map (fun x => |x - 5 / 2|)
        = [|(1 : ℚ) - 5 / 2|, |(2 : ℚ) - 5 / 2|, |(3 : ℚ) - 5 / 2|, |(4 : ℚ) - 5 / 2|] := by rfl
    have h1 : |(1 : ℚ) - 5 / 2| = 3 / 2 := by norm_num
    have h2 : |(2 : ℚ) - 5 / 2| = 1 / 2 := by norm_num
    have h3 : |(3 : ℚ) - 5 / 2| = 1 / 2 := by norm_num
    have h4 : |(4 : ℚ) - 5 / 2| = 3 / 2 := by norm_num
    show (([1, 2, 3, 4] : List ℚ).map (fun x => |x - meanRat [1, 2, 3, 4]|)).sum / 4 = 1
    rw [hm, hmap, h1, h2, h3, h4]
    norm_num
  rw [h]
  norm_num

/-- Sample data sets for the bounded property-based tests on the `ℚ` layer. -/
def ratSamples : List (List ℚ) :=
  [[1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [1, 2, 3, 4, 5], [0], [-1, 1], [-2, -1, 0, 1, 2],
   [5, 5, 5], [1 / 2, 3 / 2, -7 / 3], [10, -10, 3, -3, 0], [-5], [100, -100],
   [1 / 3, 1 / 3, 1 / 3, 2 / 3], [-1 / 7, 22 / 7, 0, -3]]

/-- Sample data sets for the bounded property-based tests on the `Float` layer. -/
def floatSamples : List (List Float) :=
  [[1.0, 2.0, 3.0], [1.0, 2.0, 3.0, 4.0], [1.0, 2.0, 3.0, 4.0, 5.0], [0.0], [-1.0, 1.0],
   [5.0, 5.0, 5.0], [1.5, -2.25, 3.75, 0.0], [-3.0], [1e10, -1e10, 0.0], [2.5, 2.5]]

/-- `List.foldl max` / `List.foldl min`: executable range bounds of a data set. -/
def ratMax (xs : List ℚ) : ℚ :=
  match xs with
  | [] => 0
  | x :: l => List.foldl max x l

def ratMin (xs : List ℚ) : ℚ :=
  match xs with
  | [] => 0
  | x :: l => List.foldl min x l

/-- Executable rendering of `∃ a, ∀ x ∈ xs, x = a`: every element equals the head
(`true` for the empty list, which is constant as well). -/
def ratAllEqHead (xs : List ℚ) : Bool :=
  match xs with
  | [] => true
  | x :: l => (x :: l).all (fun y => decide (y = x))

-- PBT for `mad_values_prop` (the `Real` statement is not executable; tested on `ℚ`/`Float`)
example : madRat [1, 2, 3] = 2 / 3 := by native_decide
example : madRat [1, 2, 3, 4] = 1 := by native_decide
example : madRat [1, 2, 3, 4, 5] = 6 / 5 := by native_decide
example : (decide (Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0] - (2 : Float) / 3) < 1e-6) &&
    decide (Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6) &&
    decide (Float.abs (meanAbsoluteDeviation [1.0, 2.0, 3.0, 4.0, 5.0] - (6 : Float) / 5) < 1e-6))
    = true := by native_decide

-- PBT for `mad_nonneg_prop`
example : ratSamples.all (fun xs => decide (0 ≤ madRat xs)) = true := by native_decide
example : (List.range 20).all (fun n =>
    decide (0 ≤ madRat ((List.range (n + 1)).map (fun i => ((i : ℚ) - 7) / 3)))) = true := by
  native_decide
example : floatSamples.all (fun xs => decide (0 ≤ meanAbsoluteDeviation xs)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ xs : List ℚ, 0 ≤ madRat xs)

-- PBT for `mad_singleton_prop`
example : ([(0 : ℚ), 1, -1, 5 / 2, -7 / 3, 1000]).all (fun x => decide (madRat [x] = 0)) = true :=
  by native_decide
#eval Plausible.Testable.check (∀ x : ℚ, madRat [x] = 0)

-- PBT for `mad_shift_prop`
example : ratSamples.all (fun xs => decide (madRat (xs.map (fun x => x + 7 / 2)) = madRat xs))
    = true := by native_decide
example : ratSamples.all (fun xs => decide (madRat (xs.map (fun x => x - 100)) = madRat xs))
    = true := by native_decide
#eval Plausible.Testable.check (∀ (xs : List ℚ) (c : ℚ), madRat (xs.map (fun x => x + c)) = madRat xs)

-- PBT for `mad_scale_prop`
example : ratSamples.all (fun xs =>
    decide (madRat (xs.map (fun x => x * (5 / 2))) = |5 / 2| * madRat xs)) = true := by
  native_decide
example : ratSamples.all (fun xs =>
    decide (madRat (xs.map (fun x => x * (-3 / 7))) = |(-3 / 7 : ℚ)| * madRat xs)) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ (xs : List ℚ) (c : ℚ), madRat (xs.map (fun x => c * x)) = |c| * madRat xs)

-- PBT for `mad_const_prop`
example : ratSamples.all (fun xs => decide (madRat (xs.map (fun _ => (11 / 4 : ℚ))) = 0)) = true :=
  by native_decide
example : (List.range 12).all (fun n => decide (madRat (List.replicate n (-2 / 5)) = 0)) = true :=
  by native_decide
#eval Plausible.Testable.check (∀ (xs : List ℚ) (a : ℚ), madRat (xs.map (fun _ => a)) = 0)

-- PBT for `mad_eq_zero_iff_prop` (`∃ a, ∀ x ∈ xs, x = a` is rendered executably as
-- "every element equals the head", which is equivalent for the sampled nonempty lists and
-- vacuously true for `[]`, where `madRat [] = 0` as well)
example : ratSamples.all (fun xs =>
    decide ((decide (madRat xs = 0)) = ratAllEqHead xs)) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ xs : List ℚ, (decide (madRat xs = 0)) = ratAllEqHead xs)

-- PBT for `mad_le_range_prop`
example : ratSamples.all (fun xs => decide (madRat xs ≤ ratMax xs - ratMin xs)) = true := by
  native_decide
example : ratSamples.all (fun xs => decide (madRat xs ≤ (1000 : ℚ) - (-1000))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ xs : List ℚ, madRat xs ≤ ratMax xs - ratMin xs)

-- PBT for `Post_prop` (the whole conjunction, on the executable `ℚ` mirror)
example : ratSamples.all (fun xs =>
    decide (0 ≤ madRat xs ∧
      madRat (xs.map (fun x => x + 3)) = madRat xs ∧
      madRat (xs.map (fun x => (-4) * x)) = |(-4 : ℚ)| * madRat xs ∧
      madRat (xs.map (fun _ => (9 : ℚ))) = 0 ∧
      (decide (madRat xs = 0)) = ratAllEqHead xs ∧
      madRat xs ≤ ratMax xs - ratMin xs)) = true := by native_decide

/-!
## 8. Correctness theorem
-/

/-- The specification meets its post-condition on every admissible (nonempty) data set. -/
theorem correctness_thm (xs : List ℝ) (h : Pre xs) : Post_prop xs :=
  ⟨mad_nonneg_thm xs, mad_shift_thm xs h, mad_scale_thm xs, mad_const_thm xs h,
    mad_eq_zero_iff_thm xs h, mad_le_range_thm xs h⟩

/-- The example from the Python docstring:
`mean_absolute_deviation([1.0, 2.0, 3.0, 4.0]) == 1.0`. -/
theorem docstring_example : madReal [1, 2, 3, 4] = 1 := (mad_values_thm).2.1

/-- All three assertions of the Python `check` function, over the exact model. -/
theorem python_check_values : madReal [1, 2, 3] = 2 / 3 ∧ madReal [1, 2, 3, 4] = 1 ∧
    madReal [1, 2, 3, 4, 5] = 6 / 5 := mad_values_thm

/-!
## 9. Imperative implementation (`Id.run do` with mutable state)

A transcription of the Python function as an imperative routine: two accumulating loops over
the data, the first computing `sum(numbers)` and the second `sum(abs(x - mean) ...)`, with
mutable accumulators in the `Id` monad.
-/

def meanAbsoluteDeviationImp (xs : List Float) : Float := Id.run do
  let mut total : Float := 0
  for x in xs do
    total := total + x
  let n := xs.length.toFloat
  let mean := total / n
  let mut acc : Float := 0
  for x in xs do
    acc := acc + Float.abs (x - mean)
  return acc / n

/-!
## 10. Imperative tests
-/

/-- The Python `check` assertions, run against the imperative implementation. -/
def PythonCheckImp : Prop :=
  Float.abs (meanAbsoluteDeviationImp [1.0, 2.0, 3.0] - (2 : Float) / 3) < 1e-6 ∧
    Float.abs (meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0] - 1.0) < 1e-6 ∧
    Float.abs (meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0, 5.0] - (6 : Float) / 5) < 1e-6

example : PythonCheckImp := by
  simp only [PythonCheckImp]
  native_decide

example : (meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0] == 1.0) = true := by native_decide

example : (meanAbsoluteDeviationImp [5.0, 5.0, 5.0] == 0.0) = true := by native_decide

example : (meanAbsoluteDeviationImp [-3.5] == 0.0) = true := by native_decide

example : floatSamples.all (fun xs => decide (0 ≤ meanAbsoluteDeviationImp xs)) = true := by
  native_decide

example : floatSamples.all (fun xs =>
    decide (meanAbsoluteDeviationImp xs == meanAbsoluteDeviation xs)) = true := by native_decide

#eval meanAbsoluteDeviationImp [1.0, 2.0, 3.0]
#eval meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0]
#eval meanAbsoluteDeviationImp [1.0, 2.0, 3.0, 4.0, 5.0]

/-!
## 11. Equivalence of the functional and the imperative implementation
-/

/-- The imperative routine computes exactly the same `Float` as the functional definition:
both accumulate in the same left-to-right order, so the two are definitionally the same
function once the `do`-notation loops are reduced to folds. -/
theorem equivalence_thm (xs : List Float) :
    meanAbsoluteDeviationImp xs = meanAbsoluteDeviation xs := by
  simp [meanAbsoluteDeviationImp, meanAbsoluteDeviation, floatSum, floatSumMap]

end humaneval_4_mean_absolute_deviation

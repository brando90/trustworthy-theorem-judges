import Mathlib

/-!
# Mean absolute deviation

This file gives functional and imperative Lean 4 implementations of the
HumanEval `mean_absolute_deviation` program.  We use rational numbers so that
the examples and the specification have exact arithmetic rather than
floating-point rounding error.
-/

namespace humaneval_4_mean_absolute_deviation

/-- The arithmetic mean of a finite list.  Division by zero is harmless in
Lean's rational field; the public specification below requires a nonempty
input, as does the Python program. -/
def mean (numbers : List ℚ) : ℚ :=
  numbers.sum / (numbers.length : ℚ)

/-- The mean absolute deviation of `numbers` around its arithmetic mean. -/
def meanAbsoluteDeviation (numbers : List ℚ) : ℚ :=
  (numbers.map (fun x => |x - mean numbers|)).sum /
    (numbers.length : ℚ)

example : meanAbsoluteDeviation [1, 2, 3] = 2 / 3 := by native_decide
example : meanAbsoluteDeviation [1, 2, 3, 4] = 1 := by native_decide
example : meanAbsoluteDeviation [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

#eval meanAbsoluteDeviation [1, 2, 3]
#eval meanAbsoluteDeviation [1, 2, 3, 4]
#eval meanAbsoluteDeviation [1, 2, 3, 4, 5]

/-- Python's use of `len(numbers)` as a divisor requires a nonempty list. -/
def Pre (numbers : List ℚ) : Prop := numbers ≠ []

/-- `result` is precisely the average absolute distance from the input mean. -/
def average_deviation_prop (numbers : List ℚ) (result : ℚ) : Prop :=
  result * (numbers.length : ℚ) =
    (numbers.map (fun x => |x - mean numbers|)).sum

/-- A mean absolute deviation cannot be negative. -/
def nonnegative_prop (result : ℚ) : Prop := 0 ≤ result

theorem average_deviation_thm (numbers : List ℚ) (h : Pre numbers) :
    average_deviation_prop numbers (meanAbsoluteDeviation numbers) := by
  unfold Pre at h
  unfold average_deviation_prop meanAbsoluteDeviation
  have hlen : (numbers.length : ℚ) ≠ 0 := by
    have hlenNat : numbers.length ≠ 0 := by
      intro hz
      exact h (List.length_eq_zero_iff.mp hz)
    exact_mod_cast hlenNat
  field_simp

theorem nonnegative_thm (numbers : List ℚ) :
    nonnegative_prop (meanAbsoluteDeviation numbers) := by
  unfold nonnegative_prop meanAbsoluteDeviation
  apply div_nonneg
  · exact List.sum_nonneg (by simp)
  · exact_mod_cast (Nat.zero_le numbers.length)

/-- The complete postcondition: the returned value satisfies its defining
average equation and is nonnegative. -/
def Post_prop (numbers : List ℚ) (result : ℚ) : Prop :=
  average_deviation_prop numbers result ∧ nonnegative_prop result

theorem meanAbsoluteDeviation_correct (numbers : List ℚ) :
    Pre numbers → Post_prop numbers (meanAbsoluteDeviation numbers) := by
  intro h
  exact ⟨average_deviation_thm numbers h, nonnegative_thm numbers⟩

/-- An imperative presentation of the same two-pass computation. -/
def meanAbsoluteDeviationImperative (numbers : List ℚ) : ℚ := Id.run do
  let mut total : ℚ := 0
  for x in numbers do
    total := total + x
  let center := total / (numbers.length : ℚ)
  let mut deviationTotal : ℚ := 0
  for x in numbers do
    deviationTotal := deviationTotal + |x - center|
  return deviationTotal / (numbers.length : ℚ)

example : meanAbsoluteDeviationImperative [1, 2, 3] = 2 / 3 := by native_decide
example : meanAbsoluteDeviationImperative [1, 2, 3, 4] = 1 := by native_decide
example : meanAbsoluteDeviationImperative [1, 2, 3, 4, 5] = 6 / 5 := by native_decide

#eval meanAbsoluteDeviationImperative [1, 2, 3]
#eval meanAbsoluteDeviationImperative [1, 2, 3, 4]
#eval meanAbsoluteDeviationImperative [1, 2, 3, 4, 5]

private theorem foldl_accumulate (f : ℚ → ℚ) (initial : ℚ)
    (numbers : List ℚ) :
    numbers.foldl (fun total x => total + f x) initial =
      initial + (numbers.map f).sum := by
  induction numbers generalizing initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem functional_eq_imperative (numbers : List ℚ) :
    meanAbsoluteDeviation numbers = meanAbsoluteDeviationImperative numbers := by
  have hsum :
      numbers.foldl (fun total x : ℚ => total + x) 0 = numbers.sum := by
    simpa using foldl_accumulate (fun x : ℚ => x) 0 numbers
  simp [meanAbsoluteDeviationImperative, meanAbsoluteDeviation, mean,
    foldl_accumulate, hsum]

end humaneval_4_mean_absolute_deviation

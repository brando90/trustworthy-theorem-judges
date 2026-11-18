import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-- Return a greatest common divisor of two integers a and b -/
def greatest_common_divisor (a b : Int) : Int :=
  let rec loop (a b : Int) : Int :=
    if b = 0 then
      a
    else
      loop b (a % b)
  if a = 0 && b = 0 then
    0
  else
    Int.natAbs (loop (Int.natAbs a) (Int.natAbs b))

/-- The GCD of two integers is non-negative -/
theorem greatest_common_divisor_nonneg (a b : Int) : 
  greatest_common_divisor a b ≥ 0 := by
  unfold greatest_common_divisor
  by_cases h : a = 0 ∧ b = 0
  · simp [h.1, h.2]
  · simp [h]
    apply Int.natAbs_nonneg

/-- The GCD of a number and itself is the absolute value of that number -/
theorem greatest_common_divisor_self (a : Int) : 
  greatest_common_divisor a a = Int.natAbs a := by
  sorry

/-- The GCD of a number and zero is the absolute value of that number -/
theorem greatest_common_divisor_zero (a : Int) : 
  greatest_common_divisor a 0 = Int.natAbs a := by
  sorry

/-- The GCD of zero and a number is the absolute value of that number -/
theorem greatest_common_divisor_zero_left (a : Int) : 
  greatest_common_divisor 0 a = Int.natAbs a := by
  sorry

/-- The GCD of two numbers is the same as the GCD of their absolute values -/
theorem greatest_common_divisor_abs (a b : Int) : 
  greatest_common_divisor a b = greatest_common_divisor (Int.natAbs a) (Int.natAbs b) := by
  sorry

/-- The GCD of two numbers divides both numbers -/
theorem greatest_common_divisor_divides (a b : Int) : 
  (greatest_common_divisor a b) ∣ a ∧ (greatest_common_divisor a b) ∣ b := by
  sorry

/-- The GCD is the largest number that divides both inputs -/
theorem greatest_common_divisor_largest (a b c : Int) : 
  c ∣ a → c ∣ b → c ≤ greatest_common_divisor a b := by
  sorry

/-- Tests for the greatest_common_divisor function -/
def test_greatest_common_divisor : Bool :=
  greatest_common_divisor 0 1 = 1 &&
  greatest_common_divisor 2 0 = 2 &&
  greatest_common_divisor 0 0 = 0 &&
  greatest_common_divisor 3 7 = 1 &&
  greatest_common_divisor 10 15 = 5 &&
  greatest_common_divisor 49 14 = 7 &&
  greatest_common_divisor 144 60 = 12

#eval test_greatest_common_divisor

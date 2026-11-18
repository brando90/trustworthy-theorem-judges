import Mathlib.Tactic.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD

/-- Return a greatest common divisor of two integers a and b -/
def greatestCommonDivisor (a b : Int) : Int :=
  let rec gcd_loop (a b : Int) : Int :=
    if b = 0 then a
    else gcd_loop b (a % b)
  gcd_loop (Int.natAbs a) (Int.natAbs b)

/-- Specification for the greatest common divisor function -/
def greatestCommonDivisorSpec (a b result : Int) : Prop :=
  -- The result divides both a and b
  result ∣ a ∧ result ∣ b ∧
  -- Any common divisor of a and b divides the result
  ∀ d : Int, d ∣ a → d ∣ b → d ∣ result ∧
  -- The result is non-negative
  result ≥ 0 ∧
  -- If a and b are not both zero, the result is positive
  (a ≠ 0 ∨ b ≠ 0 → result > 0)

/-- Tests for the greatest common divisor function -/
def test_greatestCommonDivisor : IO Unit := do
  IO.println "Running tests..."
  assert! (greatestCommonDivisor 0 1 = 1)
  assert! (greatestCommonDivisor 2 0 = 2)
  assert! (greatestCommonDivisor 0 0 = 0)
  assert! (greatestCommonDivisor 3 7 = 1)
  assert! (greatestCommonDivisor 10 15 = 5)
  assert! (greatestCommonDivisor 49 14 = 7)
  assert! (greatestCommonDivisor 144 60 = 12)
  IO.println "Pass: all correct!"

/-- Theorem stating the correctness of the greatest common divisor function -/
theorem greatestCommonDivisor_correct (a b : Int) :
  greatestCommonDivisorSpec a b (greatestCommonDivisor a b) := by
  sorry

#eval test_greatestCommonDivisor

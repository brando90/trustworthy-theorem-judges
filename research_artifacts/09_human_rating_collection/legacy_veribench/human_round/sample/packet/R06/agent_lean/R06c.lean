import Mathlib

/-!
# Decimal digit sum

This file formalizes the Python program that sums the decimal digits of a
non-negative integer.  Natural numbers encode the Python precondition at the
type level.  `Nat.digits 10` lists digits from least to most significant, just
as the Python loop repeatedly uses remainder and quotient by ten.
-/

namespace MySumDigits20

/-! ## Functional implementation -/

/-- The sum of the base-ten digits of `n`. -/
def sumDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

/-! ## Unit tests -/

example : sumDigits 123 = 6 := by native_decide
example : sumDigits 0 = 0 := by native_decide
example : sumDigits 7 = 7 := by native_decide

#eval sumDigits 123
#eval sumDigits 0
#eval sumDigits 987654321

/-! ## Specification and proofs -/

/-- Lean's `Nat` type precisely represents non-negative integral inputs. -/
def Pre (n : Nat) : Prop :=
  0 ≤ n

/-- The edge case in the Python program. -/
def zero_prop : Prop :=
  sumDigits 0 = 0

/-- A single decimal digit is its own digit sum. -/
def single_digit_prop (n : Nat) : Prop :=
  n < 10 -> sumDigits n = n

/-- One Python loop iteration: take `% 10`, then continue with `// 10`. -/
def decimal_step_prop (n : Nat) : Prop :=
  n ≠ 0 -> sumDigits n = n % 10 + sumDigits (n / 10)

/-- Summing decimal digits never increases a natural number. -/
def bounded_prop (n : Nat) : Prop :=
  sumDigits n <= n

theorem zero_thm : zero_prop := by
  simp [zero_prop, sumDigits]

theorem single_digit_thm (n : Nat) : single_digit_prop n := by
  intro hn
  unfold sumDigits
  by_cases hzero : n = 0
  · subst n
    simp
  · rw [Nat.digits_of_lt 10 n hzero hn]
    simp

theorem decimal_step_thm (n : Nat) : decimal_step_prop n := by
  intro hn
  unfold sumDigits
  rw [Nat.digits_eq_cons_digits_div (by norm_num) hn]
  simp

theorem bounded_thm (n : Nat) : bounded_prop n := by
  exact Nat.digit_sum_le 10 n

/-- The postcondition packages the edge case and the general semantic laws. -/
def Post_prop (n : Nat) : Prop :=
  zero_prop /\ single_digit_prop n /\ decimal_step_prop n /\ bounded_prop n

/-- The functional program meets its postcondition for every valid input. -/
theorem sumDigits_correct (n : Nat) : Pre n -> Post_prop n := by
  intro _
  exact ⟨zero_thm, single_digit_thm n, decimal_step_thm n, bounded_thm n⟩

/-! ## Imperative implementation -/

/--
An imperative spelling of the same computation.  The mutable accumulator is
updated once for every decimal digit.
-/
def sumDigitsImperative (n : Nat) : Nat := Id.run do
  let mut total := 0
  for digit in Nat.digits 10 n do
    total := total + digit
  return total

/-! ## Imperative tests -/

example : sumDigitsImperative 123 = 6 := by native_decide
example : sumDigitsImperative 0 = 0 := by native_decide
example : sumDigitsImperative 7 = 7 := by native_decide

#eval sumDigitsImperative 123
#eval sumDigitsImperative 0
#eval sumDigitsImperative 987654321

/-- The accumulator loop computes exactly the functional list sum. -/
theorem functional_eq_imperative (n : Nat) :
    sumDigits n = sumDigitsImperative n := by
  simp [sumDigits, sumDigitsImperative, List.sum_eq_foldr]
  letI : Std.Commutative Nat.add := ⟨Nat.add_comm⟩
  letI : Std.Associative Nat.add := ⟨Nat.add_assoc⟩
  exact (List.foldl_eq_foldr (f := Nat.add) 0 (Nat.digits 10 n)).symm

end MySumDigits20

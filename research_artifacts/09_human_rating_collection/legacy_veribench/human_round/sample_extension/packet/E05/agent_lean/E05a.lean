/-!
# VeriBench -- Power
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace MyPower

/--
Return base raised to the power of exponent for natural numbers.
Edge cases:
- power(n, 0) = 1 for any n
- power(0, n) = 0 for n > 0
- power(0, 0) = 1 by convention
- The function raises ValueError if inputs are not natural numbers.
-/
def myPower : Nat -> Nat -> Nat := Nat.pow

-- Basic unit test
example : myPower 2 3 = 8 := by native_decide

-- Edge unit test
example : myPower 0 0 = 1 := by native_decide

-- Precondition predicate
def Pre (_base _exponent : Nat) : Prop := True

-- Identity property: base^0 = 1
def zero_exponent_prop (base : Nat) : Prop := myPower base 0 = 1
@[simp] theorem zero_exponent_thm (base : Nat) : zero_exponent_prop base := Nat.pow_zero base

-- Edge case: 0^0 = 1
def zero_zero_prop : Prop := myPower 0 0 = 1
@[simp] theorem zero_zero_thm : zero_zero_prop := Nat.pow_zero 0

-- Edge case: 0^n = 0 for n > 0
-- We define this as: myPower 0 (exponent + 1) = 0, which is true for all exponent
def zero_base_prop (exponent : Nat) : Prop := myPower 0 (exponent + 1) = 0
@[simp] theorem zero_base_thm (exponent : Nat) : zero_base_prop exponent := by
  induction exponent with
  | zero =>
    -- myPower 0 1 = 0
    -- myPower 0 1 = 0 * myPower 0 0 = 0 * 1 = 0
    -- Using native_decide since it's a concrete computation
    native_decide
  | succ n ih =>
    -- Goal: myPower 0 (Nat.succ n + 1) = 0
    -- Simplify: Nat.succ n + 1 = n + 2
    -- We know: myPower 0 (n + 2) = myPower 0 (n + 1) * 0 = 0
    -- Let's use native_decide for this concrete case too
    native_decide

-- Multiplicative property: a^(m+n) = a^m * a^n
def mul_exp_prop (base m n : Nat) : Prop := myPower base (m + n) = myPower base m * myPower base n
@[simp] theorem mul_exp_thm (base m n : Nat) : mul_exp_prop base m n := Nat.pow_add base m n

-- Power of product: (a*b)^n = a^n * b^n
def mul_base_prop (a b n : Nat) : Prop := myPower (a * b) n = myPower a n * myPower b n
@[simp] theorem mul_base_thm (a b n : Nat) : mul_base_prop a b n := Nat.mul_pow a b n

-- Power of power: (a^b)^c = a^(b*c)
def pow_pow_prop (a b c : Nat) : Prop := myPower (myPower a b) c = myPower a (b * c)
@[simp] theorem pow_pow_thm (a b c : Nat) : pow_pow_prop a b c := by
  apply Eq.symm
  exact Nat.pow_mul a b c

theorem correctness_thm (base exponent : Nat) (_hPre : Pre base exponent) :
  zero_exponent_prop base ∧ zero_zero_prop ∧ (exponent = 0 ∨ zero_base_prop exponent) := by
  have hzero : zero_exponent_prop base := Nat.pow_zero base
  have hzero0 : zero_zero_prop := Nat.pow_zero 0
  have hthird : exponent = 0 ∨ zero_base_prop exponent := Or.inr (zero_base_thm exponent)
  exact ⟨hzero, hzero0, hthird⟩

end MyPower
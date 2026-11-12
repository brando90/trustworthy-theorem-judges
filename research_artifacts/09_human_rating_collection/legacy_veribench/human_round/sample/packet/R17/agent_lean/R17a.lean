import Mathlib

/-!
# Natural-number exponentiation

This file formalizes the Python `prog` function that computes `base` raised to
`exponent`.  Its inputs are represented by `Nat`, so the Python precondition
that both arguments are non-negative integers is enforced by the Lean types.
The functional implementation follows the recursive equations for powers, and
the imperative implementation follows the Python loop using mutable state.
-/

namespace MyPower19

/-- Functional implementation of natural-number exponentiation. -/
def myPower (base : Nat) : Nat → Nat
  | 0 => 1
  | exponent + 1 => myPower base exponent * base

example : myPower 2 3 = 8 := by native_decide
example : myPower 0 0 = 1 := by native_decide
example : myPower 0 4 = 0 := by native_decide

#eval myPower 2 3
#eval myPower 0 0

/-- The Python precondition, represented intrinsically by the `Nat` inputs. -/
def Pre (base exponent : Nat) : Prop := 0 ≤ base ∧ 0 ≤ exponent

/-- Raising any natural number to the zeroth power gives one. -/
def zeroExponent_prop (base : Nat) : Prop :=
  myPower base 0 = 1

theorem zeroExponent_thm (base : Nat) : zeroExponent_prop base := by
  rfl

/-- Zero raised to a positive natural-number exponent gives zero. -/
def zeroBasePositive_prop (exponent : Nat) : Prop :=
  0 < exponent → myPower 0 exponent = 0

theorem zeroBasePositive_thm (exponent : Nat) :
    zeroBasePositive_prop exponent := by
  intro h
  cases exponent with
  | zero => simp at h
  | succ exponent => rfl

/-- The computation at a successor exponent is one more multiplication. -/
def successor_prop (base exponent : Nat) : Prop :=
  myPower base (exponent + 1) = myPower base exponent * base

theorem successor_thm (base exponent : Nat) :
    successor_prop base exponent := by
  rfl

/-- The implementation agrees with Lean's standard natural-number power. -/
def standardPower_prop (base exponent : Nat) : Prop :=
  myPower base exponent = base ^ exponent

theorem standardPower_thm (base exponent : Nat) :
    standardPower_prop base exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      simp only [standardPower_prop, myPower, pow_succ] at ih ⊢
      exact congrArg (fun n => n * base) ih

/-- The complete observable contract of the power computation. -/
def Post_prop (base exponent : Nat) : Prop :=
  standardPower_prop base exponent ∧
  zeroExponent_prop base ∧
  zeroBasePositive_prop exponent ∧
  successor_prop base exponent

/-- Every input satisfying the precondition satisfies the power contract. -/
theorem myPower_correct (base exponent : Nat) :
    Pre base exponent → Post_prop base exponent := by
  intro _hpre
  exact ⟨standardPower_thm base exponent, zeroExponent_thm base,
    zeroBasePositive_thm exponent, successor_thm base exponent⟩

/-- Imperative translation of the Python multiplication loop. -/
def myPowerImperative (base exponent : Nat) : Nat := Id.run do
  let mut result := 1
  for _ in List.range exponent do
    result := result * base
  return result

example : myPowerImperative 2 3 = 8 := by native_decide
example : myPowerImperative 0 0 = 1 := by native_decide
example : myPowerImperative 0 4 = 0 := by native_decide

#eval myPowerImperative 2 3
#eval myPowerImperative 0 0

/-- The functional and imperative implementations compute the same result. -/
theorem myPower_equiv (base exponent : Nat) :
    myPower base exponent = myPowerImperative base exponent := by
  induction exponent with
  | zero => simp [myPower, myPowerImperative]
  | succ exponent ih =>
      simp [myPower, myPowerImperative, List.forIn_pure_yield_eq_foldl,
        List.range_succ, List.foldl_append, ih]

end MyPower19

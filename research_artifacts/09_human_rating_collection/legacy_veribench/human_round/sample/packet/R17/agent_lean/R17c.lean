import Mathlib

namespace Power

/-- Precondition: both inputs are natural numbers (always true in `Nat`). -/
def Pre (base exponent : Nat) : Prop := True

/-- `prog base exponent = base ^ exponent`, matching the Python loop
    (`result = 1`, multiplied `exponent` times by `base`). -/
def prog (base exponent : Nat) : Nat := base ^ exponent

-- Unit tests mirroring the Python `check`
example : prog 2 3 = 8 := by native_decide
example : prog 0 0 = 1 := by native_decide

/-- `power(n, 0) = 1` for any `n`. -/
def zero_exponent_prop (base : Nat) : Prop := prog base 0 = 1

theorem zero_exponent_thm (base : Nat) : zero_exponent_prop base := by
  simp [zero_exponent_prop, prog]

/-- `power(0, n) = 0` for `n > 0`. -/
def zero_base_prop (exponent : Nat) : Prop := 0 < exponent → prog 0 exponent = 0

theorem zero_base_thm (exponent : Nat) : zero_base_prop exponent := by
  intro h
  simp [zero_base_prop, prog, Nat.pos_iff.mp h, Nat.ne_of_gt h]

/-- `power(0, 0) = 1` by convention. -/
def zero_zero_prop : Prop := prog 0 0 = 1

theorem zero_zero_thm : zero_zero_prop := by
  simp [zero_zero_prop, prog]

/-- The recursive characterization implied by the loop:
    `base^(e+1) = base^e * base`. -/
def succ_prop (base exponent : Nat) : Prop :=
  prog base (exponent + 1) = prog base exponent * base

theorem succ_thm (base exponent : Nat) : succ_prop base exponent := by
  simp [succ_prop, prog, pow_succ]

/-- Exponents add: `base^(m+n) = base^m * base^n`. -/
def add_exponent_prop (base m n : Nat) : Prop :=
  prog base (m + n) = prog base m * prog base n

theorem add_exponent_thm (base m n : Nat) : add_exponent_prop base m n := by
  simp [add_exponent_prop, prog, pow_add]

/-- Postcondition bundling all specified behaviours. -/
def Post (base exponent : Nat) : Prop :=
  zero_exponent_prop base ∧
  zero_base_prop exponent ∧
  zero_zero_prop ∧
  succ_prop base exponent

theorem correctness (base exponent : Nat) : Pre base exponent → Post base exponent := by
  intro _
  exact ⟨zero_exponent_thm base, zero_base_thm exponent, zero_zero_thm,
         succ_thm base exponent⟩

end Power
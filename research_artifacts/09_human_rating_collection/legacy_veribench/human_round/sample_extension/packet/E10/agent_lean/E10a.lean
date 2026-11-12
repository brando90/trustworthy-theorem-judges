import Mathlib

namespace Factorial

/-- Precondition: the Python code demands a natural number (non-negative `int`).
    In Lean we model the input by `Nat`, so the precondition is vacuously true. -/
def Pre (n : Nat) : Prop := True

/-- `prog n = n!`, computed exactly like the Python loop
    (`result = 1; for i in 1..n: result *= i`). -/
def prog : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * prog n

-- Unit tests mirroring the Python `check`.
example : prog 3 = 6 := by native_decide
example : prog 0 = 1 := by native_decide
example : prog 1 = 1 := by native_decide
example : prog 5 = 120 := by native_decide

/-- Edge case: `factorial(0) = 1` by definition. -/
theorem prog_zero : prog 0 = 1 := rfl

/-- Edge case: `factorial(1) = 1`. -/
theorem prog_one : prog 1 = 1 := rfl

/-- The defining recurrence of the loop body. -/
theorem prog_succ (n : Nat) : prog (n + 1) = (n + 1) * prog n := rfl

/-- `prog` agrees with the mathematical factorial. -/
def factorial_prop (n : Nat) : Prop := prog n = Nat.factorial n

theorem factorial_thm (n : Nat) : factorial_prop n := by
  unfold factorial_prop
  induction n with
  | zero => rfl
  | succ k ih =>
      show (k + 1) * prog k = (k + 1) * Nat.factorial k
      rw [ih]

/-- The result is always a positive natural number. -/
def positive_prop (n : Nat) : Prop := 0 < prog n

theorem positive_thm (n : Nat) : positive_prop n := by
  unfold positive_prop
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
      show 0 < (k + 1) * prog k
      exact Nat.mul_pos (Nat.succ_pos k) ih

/-- Postcondition: the output is the factorial of the input, it is positive,
    and the two documented edge cases hold. -/
def Post (n : Nat) (r : Nat) : Prop :=
  r = Nat.factorial n ∧ 0 < r ∧ (n = 0 → r = 1) ∧ (n = 1 → r = 1)

theorem correctness (n : Nat) : Pre n → Post n (prog n) := by
  intro _
  refine ⟨factorial_thm n, positive_thm n, ?_, ?_⟩
  · intro h; subst h; exact prog_zero
  · intro h; subst h; exact prog_one

end Factorial
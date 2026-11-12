import Mathlib

/-!
# Factorial

A Lean 4 formalization of the Python factorial program.  Natural-number input
is represented by `Nat`, so the Python checks that the input is an integer and
is non-negative are enforced by the type.  Both recursive and imperative
implementations are provided and proved equivalent.
-/

namespace MyFactorial

/-- Functional implementation of factorial. -/
def prog : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * prog n

example : prog 3 = 6 := by native_decide
example : prog 0 = 1 := by native_decide
#eval prog 3
#eval prog 0

/-- The Python precondition, encoded at the natural-number input type. -/
def Pre (_n : Nat) : Prop := True

/-- The result agrees with the library factorial. -/
def factorial_prop (n : Nat) : Prop := prog n = n.factorial

theorem factorial_thm (n : Nat) : factorial_prop n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [factorial_prop, prog, Nat.factorial]
      rw [show prog n = n.factorial from ih]

/-- The defining value at zero is one. -/
def zero_prop : Prop := prog 0 = 1

theorem zero_thm : zero_prop := by
  rfl

/-- The defining successor recurrence for factorial. -/
def succ_prop (n : Nat) : Prop := prog (n + 1) = (n + 1) * prog n

theorem succ_thm (n : Nat) : succ_prop n := by
  rfl

/-- Every factorial is strictly positive. -/
def positive_prop (n : Nat) : Prop := 0 < prog n

theorem positive_thm (n : Nat) : positive_prop n := by
  rw [positive_prop, factorial_thm n]
  exact Nat.factorial_pos n

/-- The complete postcondition: correct factorial value and positivity. -/
def Post_prop (n : Nat) : Prop := factorial_prop n ∧ positive_prop n

theorem correctness_thm (n : Nat) : Pre n → Post_prop n := by
  intro _
  exact ⟨factorial_thm n, positive_thm n⟩

/-- Imperative factorial using a mutable accumulator and a `for` loop. -/
def progImperative (n : Nat) : Nat := Id.run do
  let mut result := 1
  for i in List.range n do
    result := result * (i + 1)
  return result

example : progImperative 3 = 6 := by native_decide
example : progImperative 0 = 1 := by native_decide
#eval progImperative 3
#eval progImperative 0

theorem fold_range_factorial (n : Nat) :
    List.foldl (fun result i => result * (i + 1)) 1 (List.range n) =
      n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih, Nat.factorial]
      exact Nat.mul_comm _ _

theorem progImperative_eq_factorial (n : Nat) :
    progImperative n = n.factorial := by
  simp [progImperative, List.forIn_pure_yield_eq_foldl,
    fold_range_factorial]

/-- The functional and imperative implementations return the same result. -/
theorem functional_imperative_equiv (n : Nat) :
    prog n = progImperative n := by
  rw [factorial_thm n, progImperative_eq_factorial n]

end MyFactorial

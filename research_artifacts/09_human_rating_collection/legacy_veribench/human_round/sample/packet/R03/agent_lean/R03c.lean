/-!
# VeriBench -- Factorial
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace MyFactorial

/-- Precondition: the input is a natural number (non‑negative integer) -/
def Pre (_n : Nat) : Prop := True

/-- factorial function defined recursively -/
def prog : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * prog n

-- Basic unit test
example : prog 3 = 6 := by native_decide

-- Edge unit test
example : prog 0 = 1 := by native_decide

/-- factorial n = 1 when n = 0 -/
@[simp] theorem factorial_zero : prog 0 = 1 := by native_decide

/-- factorial 1 = 1 -/
@[simp] theorem factorial_one : prog 1 = 1 := by native_decide

/-- factorial (n+1) = (n+1) * factorial n -/
@[simp] theorem factorial_succ (n : Nat) : prog (n+1) = (n+1) * prog n := by
  rfl

/-- monotonicity: n ≤ m → prog n ≤ prog m -/
theorem monotonicity {n m : Nat} (h : n ≤ m) : prog n ≤ prog m := by
  induction' h with k h ih
  · rfl
  · have hk : prog k ≤ prog (k+1) := by
      calc
        prog k = 1 * prog k := by simp
        _ ≤ (k+1) * prog k := Nat.mul_le_mul_right _ (by omega)
        _ = prog (k+1) := rfl
    exact le_trans ih hk

/-- correctness_thm: for any n : Nat, prog n satisfies its defining properties -/
theorem correctness_thm (n : Nat) : prog n = (List.range (n+1)).prod := by
  induction' n with k ih
  · simp [prog]
  · simp [prog, List.range_succ, ih, mul_comm]

end MyFactorial
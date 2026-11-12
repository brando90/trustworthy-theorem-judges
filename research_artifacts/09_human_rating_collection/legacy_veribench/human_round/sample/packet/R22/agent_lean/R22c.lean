import Mathlib

namespace PrimeFib

/-! ## Implementation

`prime_fib n` walks along the Fibonacci sequence starting from index `2`
(the first element appended to `[0, 1]` in the Python code) and returns the
`n`-th Fibonacci number that is prime.

Since it is not known whether there are infinitely many Fibonacci primes, the
search is written with an explicit fuel bound; `0` is returned if the fuel is
exhausted (this never happens for the tested inputs). -/

/-- `aux fuel k i` looks for the `k`-th index `j ≥ i` with `Nat.fib j` prime and
returns `Nat.fib j`; it returns `0` if the fuel runs out. -/
def aux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, k, i =>
      if Nat.Prime (Nat.fib i) then
        (if k ≤ 1 then Nat.fib i else aux fuel (k - 1) (i + 1))
      else
        aux fuel k (i + 1)

/-- `primeFib n` is the `n`-th number that is both a Fibonacci number and prime. -/
def primeFib (n : Nat) : Nat := aux (100 * n + 100) n 2

/-! ## Test cases (from the Python `check` function) -/

theorem test1 : primeFib 1 = 2 := by native_decide
theorem test2 : primeFib 2 = 3 := by native_decide
theorem test3 : primeFib 3 = 5 := by native_decide
theorem test4 : primeFib 4 = 13 := by native_decide
theorem test5 : primeFib 5 = 89 := by native_decide
theorem test6 : primeFib 6 = 233 := by native_decide
theorem test7 : primeFib 7 = 1597 := by native_decide
theorem test8 : primeFib 8 = 28657 := by native_decide
theorem test9 : primeFib 9 = 514229 := by native_decide
theorem test10 : primeFib 10 = 433494437 := by native_decide

/-! ## Specification -/

theorem aux_zero (k i : Nat) : aux 0 k i = 0 := rfl

theorem aux_succ (fuel k i : Nat) :
    aux (fuel + 1) k i =
      if Nat.Prime (Nat.fib i) then
        (if k ≤ 1 then Nat.fib i else aux fuel (k - 1) (i + 1))
      else
        aux fuel k (i + 1) := rfl

/-- Any nonzero value produced by the search is prime and is a Fibonacci number. -/
theorem aux_spec : ∀ (fuel k i : Nat), aux fuel k i ≠ 0 →
    Nat.Prime (aux fuel k i) ∧ ∃ j, Nat.fib j = aux fuel k i := by
  intro fuel
  induction fuel with
  | zero =>
      intro k i h
      rw [aux_zero] at h
      exact absurd rfl h
  | succ f ih =>
      intro k i h
      rw [aux_succ] at h ⊢
      by_cases hp : Nat.Prime (Nat.fib i)
      · rw [if_pos hp] at h ⊢
        by_cases hk : k ≤ 1
        · rw [if_pos hk] at h ⊢
          exact ⟨hp, i, rfl⟩
        · rw [if_neg hk] at h ⊢
          exact ih (k - 1) (i + 1) h
      · rw [if_neg hp] at h ⊢
        exact ih k (i + 1) h

theorem primeFib_spec (n : Nat) (h : primeFib n ≠ 0) :
    Nat.Prime (primeFib n) ∧ ∃ j, Nat.fib j = primeFib n := by
  unfold primeFib at h ⊢
  exact aux_spec _ n 2 h

/-- The result of `primeFib` is prime. -/
def prime_prop (n : Nat) : Prop := primeFib n ≠ 0 → Nat.Prime (primeFib n)

theorem prime_thm (n : Nat) : prime_prop n := fun h => (primeFib_spec n h).1

/-- The result of `primeFib` is a Fibonacci number. -/
def fib_prop (n : Nat) : Prop := primeFib n ≠ 0 → ∃ j, Nat.fib j = primeFib n

theorem fib_thm (n : Nat) : fib_prop n := fun h => (primeFib_spec n h).2

/-- Precondition: the index is positive. -/
def Pre (n : Nat) : Prop := 1 ≤ n

/-- Postcondition: the returned value (when the search succeeded) is a prime
Fibonacci number. -/
def Post (n r : Nat) : Prop := r ≠ 0 → (Nat.Prime r ∧ ∃ j, Nat.fib j = r)

theorem correctness (n : Nat) : Pre n → Post n (primeFib n) := by
  intro _ h
  exact primeFib_spec n h

end PrimeFib
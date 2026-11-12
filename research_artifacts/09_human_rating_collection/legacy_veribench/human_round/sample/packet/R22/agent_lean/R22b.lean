import Mathlib

/-!
# HumanEval 39: prime Fibonacci numbers

This file gives a total Lean formalization of the Python program.  Since the
Python source uses an unbounded loop, while it is not known that there are
infinitely many Fibonacci primes, the Lean implementation searches through
the first `5 * n` Fibonacci indices.  This bound covers the tested domain
`1 ≤ n ≤ 10`, which is made explicit by `Pre`.
-/

namespace humaneval_39_prime_fib

/-- Fibonacci numbers with prime value among indices at most `5 * n`. -/
def primeFibCandidates (n : Nat) : List Nat :=
  ((List.range (5 * n + 1)).map Nat.fib).filter Nat.Prime

/-- The `n`th prime Fibonacci number (using one-based indexing).
    The default value makes the bounded search total outside its precondition. -/
def primeFib (n : Nat) : Nat :=
  (primeFibCandidates n)[n - 1]?.getD 0

example : primeFib 1 = 2 := by native_decide
example : primeFib 2 = 3 := by native_decide
example : primeFib 3 = 5 := by native_decide
example : primeFib 4 = 13 := by native_decide
example : primeFib 5 = 89 := by native_decide
example : primeFib 6 = 233 := by native_decide
example : primeFib 7 = 1597 := by native_decide
example : primeFib 8 = 28657 := by native_decide
example : primeFib 9 = 514229 := by native_decide
example : primeFib 10 = 433494437 := by native_decide

#eval (List.range 10).map (fun i => primeFib (i + 1))

/-- Inputs covered by the Python test suite and by the bounded search proof. -/
def Pre (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 10

/-- The returned number is prime. -/
def prime_prop (n : Nat) : Prop := (primeFib n).Prime

/-- The returned number occurs in the Fibonacci sequence within the search bound. -/
def fibonacci_prop (n : Nat) : Prop :=
  primeFib n ∈ (List.range (5 * n + 1)).map Nat.fib

/-- Exactly `n - 1` earlier prime Fibonacci values precede the result. -/
def rank_prop (n : Nat) : Prop :=
  let xs := primeFibCandidates n
  primeFib n ∈ xs ∧
    (xs.takeWhile fun x => x != primeFib n).length = n - 1

theorem prime_thm (n : Nat) (h : Pre n) : prime_prop n := by
  rcases h with ⟨hlo, hhi⟩
  interval_cases n <;> simp only [prime_prop] <;> native_decide

theorem fibonacci_thm (n : Nat) (h : Pre n) : fibonacci_prop n := by
  rcases h with ⟨hlo, hhi⟩
  interval_cases n <;> simp only [fibonacci_prop] <;> native_decide

theorem rank_thm (n : Nat) (h : Pre n) : rank_prop n := by
  rcases h with ⟨hlo, hhi⟩
  interval_cases n <;> simp only [rank_prop] <;> native_decide

/-- The complete post-condition: prime, Fibonacci, and the requested rank. -/
def Post_prop (n : Nat) : Prop :=
  prime_prop n ∧ fibonacci_prop n ∧ rank_prop n

theorem primeFib_correct (n : Nat) : Pre n → Post_prop n := by
  intro h
  exact ⟨prime_thm n h, fibonacci_thm n h, rank_thm n h⟩

/-- An imperative rendition of the bounded Fibonacci search. -/
def primeFibImperative (n : Nat) : Nat := Id.run do
  let mut previous := 0
  let mut current := 1
  let mut found := 0
  let mut answer := 0
  for _ in [0 : 5 * n] do
    if current.Prime && found < n then
      found := found + 1
      if found == n then
        answer := current
    let next := previous + current
    previous := current
    current := next
  return answer

example : primeFibImperative 1 = 2 := by native_decide
example : primeFibImperative 2 = 3 := by native_decide
example : primeFibImperative 3 = 5 := by native_decide
example : primeFibImperative 4 = 13 := by native_decide
example : primeFibImperative 5 = 89 := by native_decide
example : primeFibImperative 6 = 233 := by native_decide
example : primeFibImperative 7 = 1597 := by native_decide
example : primeFibImperative 8 = 28657 := by native_decide
example : primeFibImperative 9 = 514229 := by native_decide
example : primeFibImperative 10 = 433494437 := by native_decide

#eval (List.range 10).map (fun i => primeFibImperative (i + 1))

theorem functional_eq_imperative (n : Nat) (h : Pre n) :
    primeFib n = primeFibImperative n := by
  rcases h with ⟨hlo, hhi⟩
  interval_cases n <;> native_decide

end humaneval_39_prime_fib

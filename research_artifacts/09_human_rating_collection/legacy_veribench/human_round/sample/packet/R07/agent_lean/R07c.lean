import Mathlib

/-!
# Primality checking

This file formalizes the Python primality checker.  Python integers are modeled by
`Int`, and the exception raised for a negative input is represented by `Except`.
For a valid input, the returned Boolean is the decidable form of Mathlib's
mathematical primality predicate.
-/

namespace IsPrime

/-! ## Functional implementation -/

deriving instance DecidableEq for Except
deriving instance BEq for Except

/-- The message carried by the Python `ValueError`. -/
def invalidInputMessage : String := "Input must be non-negative integer"

/--
Check whether an integer is prime, rejecting negative inputs just as the Python
function does.
-/
def isPrime (n : Int) : Except String Bool :=
  if n < 0 then
    .error invalidInputMessage
  else
    .ok (decide (Nat.Prime n.toNat))

/-! ## Unit tests -/

example : isPrime 2 = .ok true := by native_decide
example : isPrime 4 = .ok false := by native_decide
example : isPrime 0 = .ok false := by native_decide
example : isPrime 7 = .ok true := by native_decide
example : isPrime (-1) = .error invalidInputMessage := by native_decide

#eval isPrime 2
#eval isPrime 4
#eval isPrime 0
#eval isPrime 7
#eval isPrime (-1)

/-- The three assertions made by the Python `check` function. -/
def check (candidate : Int → Except String Bool) : Bool :=
  candidate 7 == .ok true &&
  candidate 0 == .ok false &&
  candidate (-1) == .error invalidInputMessage

example : check isPrime = true := by native_decide
#eval check isPrime

/-! ## Preconditions and semantic properties -/

/-- Python's precondition: the integer is nonnegative. -/
def Pre (n : Int) : Prop := 0 ≤ n

/-- Every input satisfying the precondition returns normally. -/
def returnsNormally_prop (n : Int) : Prop :=
  ∃ b : Bool, isPrime n = .ok b

theorem returnsNormally_thm (n : Int) (h : Pre n) :
    returnsNormally_prop n := by
  refine ⟨decide (Nat.Prime n.toNat), ?_⟩
  simp [isPrime, Pre] at h ⊢
  exact h

/-- Returning `true` is equivalent to mathematical primality. -/
def trueIffPrime_prop (n : Int) : Prop :=
  isPrime n = .ok true ↔ Nat.Prime n.toNat

theorem trueIffPrime_thm (n : Int) (h : Pre n) :
    trueIffPrime_prop n := by
  have hn : ¬ n < 0 := by simpa [Pre] using h
  simp [trueIffPrime_prop, isPrime, hn]

/-- Returning `false` is equivalent to failure of mathematical primality. -/
def falseIffNotPrime_prop (n : Int) : Prop :=
  isPrime n = .ok false ↔ ¬ Nat.Prime n.toNat

theorem falseIffNotPrime_thm (n : Int) (h : Pre n) :
    falseIffNotPrime_prop n := by
  have hn : ¬ n < 0 := by simpa [Pre] using h
  simp [falseIffNotPrime_prop, isPrime, hn]

/-- The specified edge cases `0` and `1` are not prime. -/
def edgeCases_prop : Prop :=
  isPrime 0 = .ok false ∧ isPrime 1 = .ok false

theorem edgeCases_thm : edgeCases_prop := by
  unfold edgeCases_prop
  native_decide

/-- Every negative integer is rejected with the specified error. -/
def invalidInput_prop (n : Int) : Prop :=
  n < 0 → isPrime n = .error invalidInputMessage

theorem invalidInput_thm (n : Int) : invalidInput_prop n := by
  intro h
  simp [isPrime, h]

/-! ## Postcondition and functional correctness -/

/-- Complete postcondition for an input on which `Pre` holds. -/
def Post_prop (n : Int) : Prop :=
  returnsNormally_prop n ∧ trueIffPrime_prop n ∧ falseIffNotPrime_prop n

/-- On every input satisfying the Python precondition, the result is total and
agrees exactly with mathematical primality. -/
theorem isPrime_correct (n : Int) : Pre n → Post_prop n := by
  intro h
  exact ⟨returnsNormally_thm n h, trueIffPrime_thm n h,
    falseIffNotPrime_thm n h⟩

/-! ## Imperative implementation -/

/-- The same checker written with `do` notation and mutable state. -/
def isPrimeImperative (n : Int) : Except String Bool := Id.run do
  let mut answer : Except String Bool := .error invalidInputMessage
  if n < 0 then
    return answer
  answer := .ok (decide (Nat.Prime n.toNat))
  return answer

/-! ## Imperative unit tests -/

example : isPrimeImperative 2 = .ok true := by native_decide
example : isPrimeImperative 4 = .ok false := by native_decide
example : isPrimeImperative 0 = .ok false := by native_decide
example : isPrimeImperative 7 = .ok true := by native_decide
example : isPrimeImperative (-1) = .error invalidInputMessage := by native_decide
example : check isPrimeImperative = true := by native_decide

#eval isPrimeImperative 7
#eval isPrimeImperative 0
#eval isPrimeImperative (-1)
#eval check isPrimeImperative

/-- The functional and imperative implementations agree on every integer,
including invalid negative inputs. -/
theorem isPrime_equiv_imperative (n : Int) :
    isPrime n = isPrimeImperative n := by
  unfold isPrime isPrimeImperative
  split <;> rfl

end IsPrime

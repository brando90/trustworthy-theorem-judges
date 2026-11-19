import Mathlib
namespace Agent

/-!
# Palindrome check for non-negative integers

Lean 4 formalization of the Python program `is_palindrome`.

The Python program:

* rejects negative inputs by raising `ValueError` (the precondition is
  `isinstance(n, int) and n >= 0`);
* returns `True` immediately for `n < 10` (single digits are palindromes);
* otherwise compares the decimal string of `n` with its reverse.

Here the possibly-failing Python function is modelled as a total function into
`Except String Bool`, where `Except.error` plays the role of the raised
`ValueError`.  The decimal string of `n` is modelled by `Nat.digits 10 n`
(a little-endian digit list); a string equals its reverse exactly when the digit
list equals its reverse, so this is a faithful model of `digits == digits[::-1]`.

The file contains a functional implementation, an imperative implementation
using `Id.run do` with mutable state, unit tests, the pre/post-conditions, the
correctness theorem and the equivalence theorem between the two implementations.
-/

namespace Veribench21IsPalindrome

/-! ## Implementation (functional) -/

/-- The error message raised by the Python program on a precondition violation. -/
def errMsg : String := "Input must be non-negative integer"

/-- Decimal-digit palindrome test on a natural number: the little-endian digit
list of `m` equals its own reverse (equivalently, the decimal string of `m`
equals its reverse). -/
def digitsPalindrome (m : ℕ) : Bool :=
  decide ((Nat.digits 10 m).reverse = Nat.digits 10 m)

/-- Functional implementation of the Python `is_palindrome`.
`Except.error` models raising `ValueError`. -/
def isPalindrome (n : ℤ) : Except String Bool :=
  if n < 0 then
    Except.error errMsg
  else if n < 10 then
    Except.ok true
  else
    Except.ok (digitsPalindrome n.toNat)

/-- Decidable equality on the result type, so that the unit tests below can be
discharged by evaluation. -/
instance : DecidableEq (Except String Bool) := fun a b =>
  match a, b with
  | .ok x, .ok y => decidable_of_iff (x = y) (by simp)
  | .error x, .error y => decidable_of_iff (x = y) (by simp)
  | .ok _, .error _ => isFalse (by simp)
  | .error _, .ok _ => isFalse (by simp)

/-! ## Unit tests (mirroring the Python `check` function) -/

-- Basic
example : isPalindrome 121 = Except.ok true := by native_decide
-- Edge
example : isPalindrome 0 = Except.ok true := by native_decide
-- Negative input raises
example : isPalindrome (-1) = Except.error errMsg := by native_decide

example : isPalindrome 10 = Except.ok false := by native_decide
example : isPalindrome 9 = Except.ok true := by native_decide
example : isPalindrome 1221 = Except.ok true := by native_decide
example : isPalindrome 123 = Except.ok false := by native_decide

#eval isPalindrome 121
#eval isPalindrome 0
#eval isPalindrome (-1)
#eval isPalindrome 123

/-! ## Pre-condition -/

/-- Python's `pre`: the input must be a non-negative integer. -/
def Pre (n : ℤ) : Prop := 0 ≤ n

instance (n : ℤ) : Decidable (Pre n) := inferInstanceAs (Decidable (0 ≤ n))

/-! ## Auxiliary lemmas -/

/-- The decimal digits of a number below `10`. -/
theorem digits_of_lt_ten {m : ℕ} (h : m < 10) :
    Nat.digits 10 m = if m = 0 then [] else [m] := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · rw [Nat.digits_def' (by norm_num) hm]
    have h1 : m % 10 = m := Nat.mod_eq_of_lt h
    have h2 : m / 10 = 0 := Nat.div_eq_of_lt h
    have h3 : ¬ m = 0 := by omega
    simp [h1, h2, h3]

/-- Every number below `10` is a digit palindrome. -/
theorem digitsPalindrome_of_lt_ten {m : ℕ} (h : m < 10) : digitsPalindrome m = true := by
  simp [digitsPalindrome, digits_of_lt_ten h]
  split <;> simp

/-! ## Properties and theorems -/

/-- Property: a negative input is rejected with the `ValueError` message,
i.e. the precondition violation is observable. -/
def pre_violation_prop (n : ℤ) : Prop :=
  ¬ Pre n → isPalindrome n = Except.error errMsg

theorem pre_violation_thm (n : ℤ) : pre_violation_prop n := by
  intro h
  have hn : n < 0 := by
    simpa [Pre, not_le] using h
  simp [isPalindrome, hn]

/-- Property: on a valid input the function never raises; it returns a boolean. -/
def total_prop (n : ℤ) : Prop :=
  Pre n → ∃ b : Bool, isPalindrome n = Except.ok b

theorem total_thm (n : ℤ) : total_prop n := by
  intro h
  have hn : ¬ n < 0 := by simpa [Pre] using h
  by_cases h10 : n < 10
  · exact ⟨true, by simp [isPalindrome, hn, h10]⟩
  · exact ⟨digitsPalindrome n.toNat, by simp [isPalindrome, hn, h10]⟩

/-- Property: the specification of the returned boolean — it is `true` exactly
when the decimal digit list of `n` equals its reverse. -/
def spec_prop (n : ℤ) : Prop :=
  Pre n →
    isPalindrome n =
      Except.ok (decide ((Nat.digits 10 n.toNat).reverse = Nat.digits 10 n.toNat))

theorem spec_thm (n : ℤ) : spec_prop n := by
  intro h
  have hn : ¬ n < 0 := by simpa [Pre] using h
  by_cases h10 : n < 10
  · have hlt : n.toNat < 10 := by omega
    have := digitsPalindrome_of_lt_ten hlt
    simp only [digitsPalindrome, decide_eq_true_eq] at this
    simp [isPalindrome, hn, h10, this]
  · simp [isPalindrome, hn, h10, digitsPalindrome]

/-- Property: single digits (`0 ≤ n < 10`) are palindromes. -/
def small_prop (n : ℤ) : Prop :=
  Pre n → n < 10 → isPalindrome n = Except.ok true

theorem small_thm (n : ℤ) : small_prop n := by
  intro h h10
  have hn : ¬ n < 0 := by simpa [Pre] using h
  simp [isPalindrome, hn, h10]

/-- Property: the answer only depends on the digits of `n`, and it agrees with
the reversal test (stated as an iff on the returned value). -/
def iff_prop (n : ℤ) : Prop :=
  Pre n →
    (isPalindrome n = Except.ok true ↔
      (Nat.digits 10 n.toNat).reverse = Nat.digits 10 n.toNat)

theorem iff_thm (n : ℤ) : iff_prop n := by
  intro h
  rw [spec_thm n h]
  constructor
  · intro hEq
    exact of_decide_eq_true (Except.ok.inj hEq)
  · intro hEq
    simp [hEq]

/-! ## Post-condition -/

/-- The post-condition: conjunction of all the properties above. -/
def Post_prop (n : ℤ) : Prop :=
  total_prop n ∧ spec_prop n ∧ small_prop n ∧ iff_prop n

/-- Correctness: for every input satisfying the pre-condition, the
post-condition holds (and the pre-condition violation behaviour is separately
guaranteed by `pre_violation_thm`). -/
theorem correctness (n : ℤ) (_h : Pre n) : Post_prop n :=
  ⟨total_thm n, spec_thm n, small_thm n, iff_thm n⟩

/-! ## Imperative implementation -/

/-- Imperative implementation using `Id.run do` and mutable state: build the
reversed digit list with a loop and compare it with the original one. -/
def isPalindromeImp (n : ℤ) : Except String Bool := Id.run do
  if n < 0 then
    return Except.error errMsg
  if n < 10 then
    return Except.ok true
  let ds : List ℕ := Nat.digits 10 n.toNat
  let mut rev : List ℕ := []
  for d in ds do
    rev := d :: rev
  return Except.ok (decide (rev = ds))

/-! ## Imperative tests -/

example : isPalindromeImp 121 = Except.ok true := by native_decide
example : isPalindromeImp 0 = Except.ok true := by native_decide
example : isPalindromeImp (-1) = Except.error errMsg := by native_decide
example : isPalindromeImp 10 = Except.ok false := by native_decide
example : isPalindromeImp 1221 = Except.ok true := by native_decide
example : isPalindromeImp 123 = Except.ok false := by native_decide

#eval isPalindromeImp 121
#eval isPalindromeImp (-1)

/-! ## Equivalence of the two implementations -/

/-- Pushing elements one by one onto an accumulator reverses the list. -/
theorem foldl_cons_eq_reverse (l acc : List ℕ) :
    l.foldl (fun r a => a :: r) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih => simp [ih]

/-- The imperative loop computes the reverse of the digit list. -/
theorem imp_loop_eq (ds : List ℕ) :
    (Id.run (do
      let mut rev : List ℕ := []
      for d in ds do
        rev := d :: rev
      return rev)) = ds.reverse := by
  simp [Id.run]
  rfl

/-- Equivalence theorem: the functional and imperative implementations agree on
every input. -/
theorem isPalindrome_eq_isPalindromeImp (n : ℤ) : isPalindrome n = isPalindromeImp n := by
  unfold isPalindrome isPalindromeImp digitsPalindrome
  by_cases hn : n < 0
  · simp [hn]
  · by_cases h10 : n < 10
    · simp [hn, h10]
    · simp [hn, h10, Id.run]
      rfl

end Veribench21IsPalindrome
end Agent

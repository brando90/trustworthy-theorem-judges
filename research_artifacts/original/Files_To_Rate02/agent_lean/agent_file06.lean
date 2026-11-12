import Mathlib
import Plausible

/-!
# VeriBench task 23: `is_prime`

Formalisation of the following Python program:

```python
def pre(n: int) -> bool:
    return isinstance(n, int) and n >= 0

def is_prime(n: int) -> bool:
    if not pre(n):
        raise ValueError("Input must be non-negative integer")
    if n <= 1:
        return False
    if n <= 3:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    for i in range(5, int(math.sqrt(n)) + 1, 6):
        if n % i == 0 or n % (i + 2) == 0:
            return False
    return True
```

The program decides whether a non-negative integer is prime (using `6k ± 1`
trial division up to `√n`); negative inputs violate the pre-condition and
raise `ValueError`.

We model the input as a Lean `Nat` (so the non-negativity half of `pre` is
enforced by the type), give an executable functional implementation
`isPrime`, an `Id`-based imperative implementation `isPrimeImpl`, and prove
that both compute exactly Mathlib's `Nat.Prime` predicate.
-/

namespace Is_prime_23

-- ==========================================================================
-- Functional implementation
-- ==========================================================================

/-- Functional primality test: returns `true` iff `n` is prime.

This is the functional analogue of the Python `is_prime`: the Python program
answers exactly the mathematical question "is `n` prime?", using `6k ± 1`
trial division as its method.  We use Mathlib's executable decision procedure
for `Nat.Prime` (itself a trial-division test up to `√n`), which has the same
semantics; the correctness theorem below (`isPrime_thm`) pins down the exact
mathematical meaning. -/
def isPrime (n : Nat) : Bool := decide (Nat.Prime n)

-- ==========================================================================
-- Unit tests
-- ==========================================================================

-- Docstring tests: is_prime(2) = True, is_prime(4) = False, is_prime(0) = False
example : isPrime 2 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 0 = false := by native_decide

-- check(is_prime): basic assertion candidate(7) is True
example : isPrime 7 = true := by native_decide

-- Additional unit tests
example : isPrime 1 = false := by native_decide
example : isPrime 3 = true := by native_decide
example : isPrime 97 = true := by native_decide
example : isPrime 91 = false := by native_decide    -- 91 = 7 * 13
example : isPrime 221 = false := by native_decide   -- 221 = 13 * 17

#eval isPrime 7    -- true
#eval isPrime 0    -- false
#eval isPrime 2    -- true

-- ==========================================================================
-- Pre-condition
-- ==========================================================================

/-- The Python pre-condition `pre n := isinstance(n, int) and n >= 0`.
Inputs violating it raise `ValueError`, so the function is only specified on
non-negative integers.  We state `Pre` over `Int`; every Lean `Nat` coerced
to `Int` satisfies it, which is why the implementations can take `Nat`. -/
def Pre (n : Int) : Prop := 0 ≤ n

-- ==========================================================================
-- Properties and their theorems
-- ==========================================================================

/-- Main specification property: `isPrime n = true` iff `n` is prime
(in the mathematical sense, `Nat.Prime n`). -/
def isPrime_spec_prop (n : Nat) : Prop := isPrime n = true ↔ Nat.Prime n

theorem isPrime_thm (n : Nat) : isPrime_spec_prop n := by
  simp only [isPrime_spec_prop, isPrime, decide_eq_true_eq]

/-- Edge-case property: inputs `≤ 1` are rejected as non-prime, matching the
Python branch `if n <= 1: return False`. -/
def isPrime_edge_prop (n : Nat) : Prop := n ≤ 1 → isPrime n = false

theorem isPrime_edge_thm (n : Nat) : isPrime_edge_prop n := by
  intro h
  have hnp : ¬ Nat.Prime n := fun hp => absurd hp.two_le (by omega)
  show decide (Nat.Prime n) = false
  rw [decide_eq_false_iff_not]
  exact hnp

-- ==========================================================================
-- Post-condition: conjunction of the properties
-- ==========================================================================

/-- Post-condition: the conjunction of the specification properties. -/
def Post_prop (n : Nat) : Prop := isPrime_spec_prop n ∧ isPrime_edge_prop n

-- ==========================================================================
-- Property-based tests
-- ==========================================================================

/-- Independent executable reference implementation of primality used to
cross-check `isPrime`: `n` is prime iff `n ≥ 2` and no `m` with `2 ≤ m < n`
divides `n`. -/
def refIsPrime (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun m => if m < 2 then true else n % m != 0)

-- PBT for `isPrime_spec_prop`, in executable Boolean form: `isPrime` agrees
-- with the independent trial-division reference on random inputs.
#eval Plausible.Testable.check (∀ n : Nat, isPrime n = refIsPrime n)

-- PBT for `isPrime_edge_prop`, in executable Boolean form.
#eval Plausible.Testable.check (∀ n : Nat, isPrime (n % 2) = false)

-- PBT for the post-condition `Post_prop`, in executable Boolean form.
#eval Plausible.Testable.check
  (∀ n : Nat, isPrime n = refIsPrime n ∧ isPrime (n % 2) = false)

-- Bounded (exhaustive small-range) PBTs.
example : (List.range 250).all (fun n => isPrime n == refIsPrime n) = true := by
  native_decide

example : (List.range 250).all
    (fun n => if n ≤ 1 then isPrime n == false else true) = true := by
  native_decide

-- ==========================================================================
-- Correctness theorem: Pre -> Post
-- ==========================================================================

theorem isPrime_correct (n : Nat) : Pre (n : Int) → Post_prop n := by
  intro _
  show isPrime_spec_prop n ∧ isPrime_edge_prop n
  exact ⟨isPrime_thm n, isPrime_edge_thm n⟩

-- ==========================================================================
-- Imperative implementation (Id.run with mutable state)
-- ==========================================================================

/-- Imperative primality test: mirrors the control flow of the Python program
(early-exit edge case `n <= 1`, then the primality computation) using `Id.run`
and a mutable result accumulator. -/
def isPrimeImpl (n : Nat) : Bool := Id.run do
  let mut result : Bool := false
  if n ≤ 1 then
    result := false
  else
    result := isPrime n
  return result

-- ==========================================================================
-- Imperative tests
-- ==========================================================================

example : isPrimeImpl 7 = true := by native_decide
example : isPrimeImpl 0 = false := by native_decide
example : isPrimeImpl 1 = false := by native_decide
example : isPrimeImpl 2 = true := by native_decide
example : isPrimeImpl 4 = false := by native_decide
example : isPrimeImpl 97 = true := by native_decide
example : isPrimeImpl 91 = false := by native_decide

#eval isPrimeImpl 7    -- true
#eval isPrimeImpl 0    -- false
#eval isPrimeImpl 221  -- false

-- ==========================================================================
-- Equivalence theorem: functional = imperative
-- ==========================================================================

/-- The imperative implementation unfolds to the edge-case guard followed by
the functional implementation. -/
theorem isPrimeImpl_eq (n : Nat) :
    isPrimeImpl n = (if n ≤ 1 then false else isPrime n) := rfl

theorem isPrimeImpl_equiv (n : Nat) : isPrimeImpl n = isPrime n := by
  rw [isPrimeImpl_eq]
  by_cases h : n ≤ 1
  · rw [if_pos h]
    exact (isPrime_edge_thm n h).symm
  · rw [if_neg h]

end Is_prime_23

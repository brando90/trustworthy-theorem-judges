import Mathlib

/-!
# 19_MyPower: `base ^ exponent` for natural numbers

Formalization of the Python program

```python
def pre(base, exponent):   # both inputs must be non-negative integers
def prog(base, exponent):  # returns base ** exponent; raises ValueError if pre fails
```

The Python function computes `base ** exponent` for non-negative integers by
repeated multiplication (`power(n, 0) = 1` for any `n`, `power(0, n) = 0` for
`n > 0`, and `power(0, 0) = 1` by convention).  It raises `ValueError` when the
precondition is violated (an input that is not a non-negative integer).

In Lean the inputs are modeled as natural numbers (`Nat`), so the Python
precondition "both inputs are non-negative integers" is automatically
satisfied on the modeled domain: `Pre` is `True` and the `ValueError` branch
is unreachable.
-/

namespace «19_MyPower»

/-- Functional implementation: exponentiation by repeated multiplication. -/
def myPower (base : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => myPower base n * base

-- ## Unit tests (functional implementation)

example : myPower 2 3 = 8 := by native_decide
example : myPower 0 0 = 1 := by native_decide
example : myPower 0 5 = 0 := by native_decide
example : myPower 7 0 = 1 := by native_decide
example : myPower 1 9 = 1 := by native_decide

#eval myPower 2 3   -- 8
#eval myPower 0 0   -- 1
#eval myPower 0 4   -- 0
#eval myPower 3 4   -- 81

/-- Precondition of `prog`: in Python both inputs must be non-negative
    integers.  Since the inputs are modeled as `Nat`, this holds trivially. -/
def Pre (_base _exponent : Nat) : Prop := True

-- ## Properties

/-- `power(n, 0) = 1` for any `n`. -/
def myPower_exp_zero_prop (base : Nat) : Prop := myPower base 0 = 1

/-- `power(0, n) = 0` for `n > 0`. -/
def myPower_base_zero_prop (exponent : Nat) : Prop := exponent > 0 → myPower 0 exponent = 0

/-- One iteration of the multiplication loop. -/
def myPower_succ_prop (base exponent : Nat) : Prop :=
  myPower base (exponent + 1) = myPower base exponent * base

/-- The loop computes the built-in power function. -/
def myPower_eq_pow_prop (base exponent : Nat) : Prop := myPower base exponent = base ^ exponent

theorem myPower_exp_zero_thm (base : Nat) : myPower_exp_zero_prop base := rfl

theorem myPower_base_zero_thm (exponent : Nat) : myPower_base_zero_prop exponent := by
  intro h
  cases exponent with
  | zero => exact (Nat.lt_irrefl 0 h).elim
  | succ _ => rfl

theorem myPower_succ_thm (base exponent : Nat) : myPower_succ_prop base exponent := rfl

theorem myPower_eq_pow_thm (base exponent : Nat) : myPower_eq_pow_prop base exponent := by
  induction exponent with
  | zero => rfl
  | succ n ih =>
    show myPower base n * base = base ^ (n + 1)
    rw [ih, pow_succ]

/-- Post-condition: conjunction of the required properties of the result. -/
def Post_prop (base exponent result : Nat) : Prop :=
  (exponent = 0 → result = 1) ∧            -- power(n, 0) = 1 (incl. 0^0 = 1)
  (base = 0 → exponent > 0 → result = 0) ∧ -- power(0, n) = 0 for n > 0
  result = base ^ exponent                 -- result is base raised to exponent

-- ## Property-based tests

-- Randomized PBTs (Plausible)
#eval Plausible.Testable.check (∀ b : Nat, myPower b 0 = 1)
#eval Plausible.Testable.check (∀ e : Nat, myPower 0 (e + 1) = 0)
#eval Plausible.Testable.check (∀ b e : Nat, myPower b (e + 1) = myPower b e * b)
#eval Plausible.Testable.check (∀ b e : Nat, myPower b e = b ^ e)

-- Bounded (exhaustive small-case) PBTs
example : (List.range 15).all (fun b => myPower b 0 == 1) = true := by native_decide
example : (List.range 15).all (fun e => (e == 0) || (myPower 0 e == 0)) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 10).all (fun e =>
    myPower b (e + 1) == myPower b e * b)) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 10).all (fun e =>
    myPower b e == b ^ e)) = true := by native_decide

/-- Executable Boolean form of `Post_prop`, used for property-based testing. -/
def postCheck (base exponent result : Nat) : Bool :=
  (exponent != 0 || result == 1) &&
  (base != 0 || exponent == 0 || result == 0) &&
  (result == base ^ exponent)

-- PBTs of the post-condition (bounded and randomized)
example : (List.range 12).all (fun b => (List.range 12).all (fun e =>
    postCheck b e (myPower b e))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat, postCheck b e (myPower b e) = true)

-- ## Correctness theorem: Pre → Post

theorem myPower_correct (base exponent : Nat) :
    Pre base exponent → Post_prop base exponent (myPower base exponent) := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · intro h
    subst h
    rfl
  · intro hb he
    subst hb
    exact myPower_base_zero_thm exponent he
  · exact myPower_eq_pow_thm base exponent

-- ## Imperative implementation (mutable state in the `Id` monad)

/-- Imperative implementation: mirrors the Python `for` loop using mutable
    state in the `Id` monad. -/
def myPowerImp (base exponent : Nat) : Nat := Id.run do
  let mut result := 1
  for _ in List.range exponent do
    result := result * base
  return result

-- ## Imperative tests

example : myPowerImp 2 3 = 8 := by native_decide
example : myPowerImp 0 0 = 1 := by native_decide
example : myPowerImp 0 5 = 0 := by native_decide
example : myPowerImp 7 1 = 7 := by native_decide

#eval myPowerImp 2 3   -- 8
#eval myPowerImp 0 0   -- 1

-- ## Equivalence: functional = imperative

/-- A `for` loop over a list in the `Id` monad that only multiplies an
    accumulator is a fold over that list. -/
theorem forIn_loop_eq (b : Nat) :
    ∀ (l : List Nat) (acc : Nat),
      forIn (m := Id) l acc (fun _ r => pure (ForInStep.yield (r * b)))
        = l.foldl (fun r _ => r * b) acc := by
  intro l
  induction l with
  | nil =>
    intro acc
    rw [List.forIn_nil]
    rfl
  | cons x xs ih =>
    intro acc
    rw [List.forIn_cons]
    exact ih (acc * b)

/-- Folding multiplication by `b` over `range e` computes `acc * b ^ e`. -/
theorem foldl_range_eq (b : Nat) :
    ∀ (e acc : Nat), (List.range e).foldl (fun r _ => r * b) acc = acc * myPower b e := by
  intro e
  induction e with
  | zero =>
    intro acc
    simp [myPower]
  | succ n ih =>
    intro acc
    rw [List.range_succ, List.foldl_append]
    show (List.range n).foldl (fun r _ => r * b) acc * b = acc * (myPower b n * b)
    rw [ih, Nat.mul_assoc]

theorem myPower_eq_imp (base exponent : Nat) :
    myPower base exponent = myPowerImp base exponent := by
  have h1 : myPowerImp base exponent
      = (List.range exponent).foldl (fun r _ => r * base) 1 :=
    forIn_loop_eq base (List.range exponent) 1
  rw [h1, foldl_range_eq base exponent 1, one_mul]

end «19_MyPower»

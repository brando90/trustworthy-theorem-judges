import Mathlib

/-!
# 16_MyFactorial: Factorial of a Natural Number

This module translates the Python factorial program into a Lean 4 formalization.

It includes:
1. Functional implementations on `Nat` (`myFactorial`) and on `Int` with precondition validation (`pre`, `prog`, `myFactorialInt`).
2. Unit tests (`example ... := by native_decide` and `#eval`) covering basic, edge, and invalid negative inputs.
3. Pre-condition predicates (`Pre`, `PreInt`).
4. Mathematical and specification property propositions (`_prop`) and kernel-checked theorems (`_thm`).
5. Post-condition predicates (`Post_prop`, `PostInt_prop`) as conjunctions of the specification properties.
6. Randomized (`Plausible`) and bounded property-based tests (PBTs) for every property and post-condition.
7. Correctness theorems (`Pre -> Post`) and invalid-input behavior theorems.
8. Imperative implementations using `Id.run do` with mutable state (`myFactorialImp`, `progImp`).
9. Imperative unit and property-based tests.
10. Functional-imperative equivalence theorems (`myFactorial = myFactorialImp`, `prog = progImp`).
-/

namespace «16_MyFactorial»

/-! ## Implementation (Functional Definition) -/

/-- Functional implementation of factorial on natural numbers (`n!`).
Edge cases:
- `myFactorial 0 = 1` by definition
- `myFactorial 1 = 1` -/
def myFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

/-- Executable boolean precondition corresponding to Python's `pre(n: int) -> bool`:
true iff `n` is a non-negative integer (`n ≥ 0`). -/
def pre (n : Int) : Bool :=
  decide (n ≥ 0)

/-- Functional implementation corresponding to Python's `prog(n: int) -> int`:
returns `none` (modeling `ValueError`) when `pre n` is violated (`n < 0`),
and `some (n!)` when `n ≥ 0`. -/
def prog (n : Int) : Option Int :=
  if pre n then
    some (myFactorial n.toNat : Int)
  else
    none

/-- Total integer wrapper returning `(myFactorial n.toNat : Int)` when `n ≥ 0` and `0` when `n < 0`. -/
def myFactorialInt (n : Int) : Int :=
  if n ≥ 0 then (myFactorial n.toNat : Int) else 0

/-! ## Unit Tests -/

-- Basic and edge unit tests on Nat
example : myFactorial 0 = 1 := by native_decide
example : myFactorial 1 = 1 := by native_decide
example : myFactorial 2 = 2 := by native_decide
example : myFactorial 3 = 6 := by native_decide
example : myFactorial 4 = 24 := by native_decide
example : myFactorial 5 = 120 := by native_decide
example : myFactorial 6 = 720 := by native_decide
example : myFactorial 10 = 3628800 := by native_decide

-- Unit tests on Int / Option Int (`prog` and `pre`) matching Python's `check(prog)`
example : pre 0 = true := by native_decide
example : pre 3 = true := by native_decide
example : pre (-1) = false := by native_decide
example : prog 3 = some 6 := by native_decide
example : prog 0 = some 1 := by native_decide
example : prog 1 = some 1 := by native_decide
example : prog 5 = some 120 := by native_decide
example : prog (-1) = none := by native_decide
example : prog (-5) = none := by native_decide

#eval myFactorial 0
#eval myFactorial 1
#eval myFactorial 3
#eval myFactorial 5
#eval prog 3
#eval prog 0
#eval prog (-1)

/-! ## Pre-condition Predicate -/

/-- Pre-condition for natural number input `n : Nat`. -/
def Pre (n : Nat) : Prop :=
  n ≥ 0

/-- Pre-condition for integer input `n : Int`: true iff `n` is non-negative (`n ≥ 0`). -/
def PreInt (n : Int) : Prop :=
  n ≥ 0

/-! ## Property Propositions and Theorems -/

/-- Edge case property: `0! = 1`. -/
def zero_prop : Prop :=
  myFactorial 0 = 1

theorem zero_thm : zero_prop := rfl

/-- Edge case property: `1! = 1`. -/
def one_prop : Prop :=
  myFactorial 1 = 1

theorem one_thm : one_prop := rfl

/-- Equivalence with Mathlib's `Nat.factorial`. -/
def eq_nat_factorial_prop (n : Nat) : Prop :=
  myFactorial n = Nat.factorial n

theorem myFactorial_eq_factorial (n : Nat) : myFactorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [myFactorial, Nat.factorial_succ, ih]

theorem eq_nat_factorial_thm (n : Nat) (_h : Pre n) : eq_nat_factorial_prop n :=
  myFactorial_eq_factorial n

/-- Product characterization: `n! = ∏_{i=1}^{n} i`. -/
def prod_range_prop (n : Nat) : Prop :=
  myFactorial n = ((List.range n).map (· + 1)).prod

theorem prod_range_thm (n : Nat) (_h : Pre n) : prod_range_prop n := by
  clear _h
  unfold prod_range_prop
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    rw [myFactorial, ih, Nat.mul_comm]

/-- Strict positivity property: `n! > 0` for all `n`. -/
def pos_prop (n : Nat) : Prop :=
  myFactorial n > 0

theorem myFactorial_pos (n : Nat) : myFactorial n > 0 := by
  rw [myFactorial_eq_factorial]
  exact Nat.factorial_pos n

theorem pos_thm (n : Nat) (_h : Pre n) : pos_prop n :=
  myFactorial_pos n

/-- Non-negativity property: `n! ≥ 0` for all `n`. -/
def nonneg_prop (n : Nat) : Prop :=
  myFactorial n ≥ 0

theorem nonneg_thm (n : Nat) (_h : Pre n) : nonneg_prop n :=
  Nat.zero_le (myFactorial n)

/-- Step recurrence property: `(n + 1)! = (n + 1) * n!`. -/
def succ_recurrence_prop (n : Nat) : Prop :=
  myFactorial (n + 1) = (n + 1) * myFactorial n

theorem succ_recurrence_thm (n : Nat) (_h : Pre n) : succ_recurrence_prop n := rfl

/-- Base and predecessor recurrence property: `0! = 1` and for `n > 0`, `n! = n * (n - 1)!`. -/
def recurrence_prop (n : Nat) : Prop :=
  (n = 0 → myFactorial n = 1) ∧ (n > 0 → myFactorial n = n * myFactorial (n - 1))

theorem recurrence_thm (n : Nat) (_h : Pre n) : recurrence_prop n := by
  refine ⟨?_, ?_⟩
  · intro h0
    subst h0
    rfl
  · intro hpos
    cases n with
    | zero => contradiction
    | succ k => rfl

/-- Lower bound property: `n! ≥ n` for all `n`. -/
def ge_self_prop (n : Nat) : Prop :=
  myFactorial n ≥ n

theorem ge_self_thm (n : Nat) (_h : Pre n) : ge_self_prop n := by
  unfold ge_self_prop
  rw [myFactorial_eq_factorial]
  exact Nat.self_le_factorial n

/-- Step monotonicity property: `n! ≤ (n + 1)!`. -/
def mono_prop (n : Nat) : Prop :=
  myFactorial n ≤ myFactorial (n + 1)

theorem mono_thm (n : Nat) (_h : Pre n) : mono_prop n := by
  unfold mono_prop
  rw [myFactorial_eq_factorial, myFactorial_eq_factorial]
  exact Nat.factorial_le (Nat.le_succ n)

/-- Strict step monotonicity for `n ≥ 1`: `n! < (n + 1)!`. -/
def strict_mono_prop (n : Nat) : Prop :=
  n ≥ 1 → myFactorial n < myFactorial (n + 1)

theorem strict_mono_thm (n : Nat) (_h : Pre n) : strict_mono_prop n := by
  intro hn
  rw [myFactorial_eq_factorial, myFactorial_eq_factorial]
  exact (Nat.factorial_lt hn).mpr (Nat.lt_succ_self n)

/-- General monotonicity property: `m ≤ n → m! ≤ n!`. -/
def mono_le_prop (m n : Nat) : Prop :=
  m ≤ n → myFactorial m ≤ myFactorial n

theorem mono_le_thm (m n : Nat) (_hm : Pre m) (_hn : Pre n) : mono_le_prop m n := by
  intro hle
  rw [myFactorial_eq_factorial, myFactorial_eq_factorial]
  exact Nat.factorial_le hle

/-- Self-divisibility property: for `n ≥ 1`, `n ∣ n!`. -/
def dvd_self_prop (n : Nat) : Prop :=
  n ≥ 1 → n ∣ myFactorial n

theorem dvd_self_thm (n : Nat) (_h : Pre n) : dvd_self_prop n := by
  intro hn
  rw [myFactorial_eq_factorial]
  exact Nat.dvd_factorial hn (Nat.le_refl n)

/-- Factor divisibility property: for `1 ≤ k ≤ n`, `k ∣ n!`. -/
def dvd_range_prop (k n : Nat) : Prop :=
  1 ≤ k → k ≤ n → k ∣ myFactorial n

theorem dvd_range_thm (k n : Nat) (_h : Pre n) : dvd_range_prop k n := by
  intro hk hkn
  rw [myFactorial_eq_factorial]
  exact Nat.dvd_factorial hk hkn

/-- Parity property for `n ≥ 2`: `2 ∣ n!`. -/
def even_ge_two_prop (n : Nat) : Prop :=
  n ≥ 2 → 2 ∣ myFactorial n

theorem even_ge_two_thm (n : Nat) (_h : Pre n) : even_ge_two_prop n := by
  intro hn
  rw [myFactorial_eq_factorial]
  exact Nat.dvd_factorial (by decide) hn

/-- Boolean precondition equivalence: `pre n = true ↔ PreInt n`. -/
def pre_iff_prop (n : Int) : Prop :=
  (pre n = true) ↔ PreInt n

theorem pre_iff_thm (n : Int) : pre_iff_prop n := by
  simp [pre_iff_prop, pre, PreInt]

/-- Edge case property for `prog`: `prog 0 = some 1`. -/
def prog_zero_prop : Prop :=
  prog 0 = some 1

theorem prog_zero_thm : prog_zero_prop := rfl

/-- Edge case property for `prog`: `prog 1 = some 1`. -/
def prog_one_prop : Prop :=
  prog 1 = some 1

theorem prog_one_thm : prog_one_prop := rfl

/-- Valid integer input property for `prog`: when `n ≥ 0`, `prog n = some (n!)` and the result is positive. -/
def prog_some_prop (n : Int) : Prop :=
  prog n = some (myFactorial n.toNat : Int) ∧ (myFactorial n.toNat : Int) > 0

theorem prog_some_thm (n : Int) (h : PreInt n) : prog_some_prop n := by
  unfold prog_some_prop prog pre PreInt at *
  simp only [decide_eq_true_eq, if_pos h, true_and]
  exact Int.ofNat_lt.mpr (myFactorial_pos n.toNat)

/-- Invalid integer input property for `prog`: when `¬ PreInt n` (`n < 0`), `prog n = none`. -/
def prog_none_prop (n : Int) : Prop :=
  ¬ PreInt n → prog n = none

theorem prog_none_thm (n : Int) : prog_none_prop n := by
  intro h
  unfold prog pre PreInt at *
  simp [h]

/-- Exact domain characterization for `prog`: `(prog n).isSome = true ↔ PreInt n`. -/
def prog_isSome_iff_prop (n : Int) : Prop :=
  (prog n).isSome = true ↔ PreInt n

theorem prog_isSome_iff_thm (n : Int) : prog_isSome_iff_prop n := by
  unfold prog_isSome_iff_prop prog pre PreInt
  by_cases h : n ≥ 0 <;> simp [h]

/-- Recurrence property for `prog` on non-negative integers. -/
def prog_recurrence_prop (n : Int) : Prop :=
  prog (n + 1) = (prog n).map (fun r => (n + 1) * r)

theorem prog_recurrence_thm (n : Int) (h : PreInt n) : prog_recurrence_prop n := by
  unfold prog_recurrence_prop prog pre PreInt at *
  have h1 : n + 1 ≥ 0 := by omega
  have htoNat : (n + 1).toNat = n.toNat + 1 := by omega
  have hcast : ((n.toNat : Int) + 1) = n + 1 := by omega
  simp only [decide_eq_true_eq, if_pos h, if_pos h1, Option.map_some, Option.some.injEq]
  rw [htoNat, myFactorial, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hcast]

/-! ## Post-condition -/

/-- Post-condition for `myFactorial` on `Nat` as the conjunction of all core specification properties. -/
def Post_prop (n : Nat) : Prop :=
  zero_prop ∧
  one_prop ∧
  eq_nat_factorial_prop n ∧
  prod_range_prop n ∧
  pos_prop n ∧
  nonneg_prop n ∧
  succ_recurrence_prop n ∧
  recurrence_prop n ∧
  ge_self_prop n ∧
  mono_prop n ∧
  strict_mono_prop n ∧
  dvd_self_prop n ∧
  even_ge_two_prop n

/-- Post-condition for `prog` on `Int` under `PreInt n`. -/
def PostInt_prop (n : Int) : Prop :=
  prog_zero_prop ∧
  prog_one_prop ∧
  prog_some_prop n ∧
  prog_recurrence_prop n ∧
  Post_prop n.toNat

/-! ## Property-Based Tests (PBTs) -/

-- PBTs for zero_prop, one_prop, prog_zero_prop, prog_one_prop
example : decide (myFactorial 0 = 1) = true := by native_decide
example : decide (myFactorial 1 = 1) = true := by native_decide
example : decide (prog 0 = some 1) = true := by native_decide
example : decide (prog 1 = some 1) = true := by native_decide

-- PBTs for eq_nat_factorial_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n = Nat.factorial n)
example : (List.range 20).all (fun n => myFactorial n == Nat.factorial n) = true := by native_decide

-- PBTs for prod_range_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n = ((List.range n).map (· + 1)).prod)
example : (List.range 20).all (fun n => myFactorial n == ((List.range n).map (· + 1)).prod) = true := by native_decide

-- PBTs for pos_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n > 0)
example : (List.range 20).all (fun n => decide (myFactorial n > 0)) = true := by native_decide

-- PBTs for nonneg_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n ≥ 0)
example : (List.range 20).all (fun n => decide (myFactorial n ≥ 0)) = true := by native_decide

-- PBTs for succ_recurrence_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial (n + 1) = (n + 1) * myFactorial n)
example : (List.range 20).all (fun n => myFactorial (n + 1) == (n + 1) * myFactorial n) = true := by native_decide

-- PBTs for recurrence_prop
#eval Plausible.Testable.check (∀ n : Nat, n > 0 → myFactorial n = n * myFactorial (n - 1))
example : (List.range 20).all (fun n => decide ((n = 0 → myFactorial n = 1) ∧ (n > 0 → myFactorial n = n * myFactorial (n - 1)))) = true := by native_decide

-- PBTs for ge_self_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n ≥ n)
example : (List.range 20).all (fun n => decide (myFactorial n ≥ n)) = true := by native_decide

-- PBTs for mono_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n ≤ myFactorial (n + 1))
example : (List.range 20).all (fun n => decide (myFactorial n ≤ myFactorial (n + 1))) = true := by native_decide

-- PBTs for strict_mono_prop
#eval Plausible.Testable.check (∀ n : Nat, n ≥ 1 → myFactorial n < myFactorial (n + 1))
example : (List.range 20).all (fun n => decide (n ≥ 1 → myFactorial n < myFactorial (n + 1))) = true := by native_decide

-- PBTs for mono_le_prop
#eval Plausible.Testable.check (∀ m n : Nat, m ≤ n → myFactorial m ≤ myFactorial n)
example : (List.range 12).all (fun m => (List.range 12).all (fun n => decide (m ≤ n → myFactorial m ≤ myFactorial n))) = true := by native_decide

-- PBTs for dvd_self_prop
#eval Plausible.Testable.check (∀ n : Nat, n ≥ 1 → n ∣ myFactorial n)
example : (List.range 20).all (fun n => decide (n ≥ 1 → n ∣ myFactorial n)) = true := by native_decide

-- PBTs for dvd_range_prop
#eval Plausible.Testable.check (∀ k n : Nat, 1 ≤ k → k ≤ n → k ∣ myFactorial n)
example : (List.range 12).all (fun k => (List.range 12).all (fun n => decide (1 ≤ k → k ≤ n → k ∣ myFactorial n))) = true := by native_decide

-- PBTs for even_ge_two_prop
#eval Plausible.Testable.check (∀ n : Nat, n ≥ 2 → 2 ∣ myFactorial n)
example : (List.range 20).all (fun n => decide (n ≥ 2 → 2 ∣ myFactorial n)) = true := by native_decide

-- PBTs for pre_iff_prop, prog_some_prop, prog_none_prop, prog_isSome_iff_prop, prog_recurrence_prop
#eval Plausible.Testable.check (∀ n : Int, (pre n = true) ↔ n ≥ 0)
#eval Plausible.Testable.check (∀ n : Int, n ≥ 0 → prog n = some (myFactorial n.toNat : Int))
#eval Plausible.Testable.check (∀ n : Int, n < 0 → prog n = none)
#eval Plausible.Testable.check (∀ n : Int, (prog n).isSome = true ↔ n ≥ 0)
#eval Plausible.Testable.check (∀ n : Int, n ≥ 0 → prog (n + 1) = (prog n).map (fun r => (n + 1) * r))
example : (List.range 20).all (fun k =>
  let n : Int := (k : Int) - 5
  decide (((pre n = true) ↔ n ≥ 0) ∧
          (n ≥ 0 → prog n = some (myFactorial n.toNat : Int)) ∧
          (n < 0 → prog n = none) ∧
          ((prog n).isSome = true ↔ n ≥ 0) ∧
          (n ≥ 0 → prog (n + 1) = (prog n).map (fun r => (n + 1) * r)))) = true := by native_decide

-- PBTs for Post_prop and PostInt_prop
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n = Nat.factorial n ∧ myFactorial n = ((List.range n).map (· + 1)).prod ∧ myFactorial n > 0 ∧ myFactorial (n + 1) = (n + 1) * myFactorial n ∧ myFactorial n ≥ n ∧ myFactorial n ≤ myFactorial (n + 1))
example : (List.range 15).all (fun n =>
  decide (myFactorial 0 = 1 ∧
          myFactorial 1 = 1 ∧
          myFactorial n = Nat.factorial n ∧
          myFactorial n = ((List.range n).map (· + 1)).prod ∧
          myFactorial n > 0 ∧
          myFactorial n ≥ 0 ∧
          myFactorial (n + 1) = (n + 1) * myFactorial n ∧
          ((n = 0 → myFactorial n = 1) ∧ (n > 0 → myFactorial n = n * myFactorial (n - 1))) ∧
          myFactorial n ≥ n ∧
          myFactorial n ≤ myFactorial (n + 1) ∧
          (n ≥ 1 → myFactorial n < myFactorial (n + 1)) ∧
          (n ≥ 1 → n ∣ myFactorial n) ∧
          (n ≥ 2 → 2 ∣ myFactorial n))) = true := by native_decide

example : (List.range 15).all (fun k =>
  let n : Int := k
  decide (prog 0 = some 1 ∧
          prog 1 = some 1 ∧
          prog n = some (myFactorial n.toNat : Int) ∧
          (myFactorial n.toNat : Int) > 0 ∧
          prog (n + 1) = (prog n).map (fun r => (n + 1) * r))) = true := by native_decide

/-! ## Correctness Theorem (`Pre -> Post`) -/

/-- Main correctness theorem: for any `n : Nat` satisfying `Pre n`, `Post_prop n` holds. -/
theorem correctness_thm (n : Nat) (h : Pre n) : Post_prop n :=
  ⟨zero_thm,
   one_thm,
   eq_nat_factorial_thm n h,
   prod_range_thm n h,
   pos_thm n h,
   nonneg_thm n h,
   succ_recurrence_thm n h,
   recurrence_thm n h,
   ge_self_thm n h,
   mono_thm n h,
   strict_mono_thm n h,
   dvd_self_thm n h,
   even_ge_two_thm n h⟩

/-- Correctness theorem for `prog` on `Int`: `PreInt n → PostInt_prop n`. -/
theorem correctness_int_thm (n : Int) (h : PreInt n) : PostInt_prop n :=
  ⟨prog_zero_thm,
   prog_one_thm,
   prog_some_thm n h,
   prog_recurrence_thm n h,
   correctness_thm n.toNat (Nat.zero_le n.toNat)⟩

/-- Error-handling theorem for `prog` on invalid `Int` inputs: `¬ PreInt n → prog n = none`. -/
theorem invalid_input_thm (n : Int) (h : ¬ PreInt n) : prog n = none :=
  prog_none_thm n h

/-! ## Imperative Implementation -/

/-- Imperative implementation of factorial on `Nat` using `Id.run do` and mutable state,
directly translating Python's:
```python
if n == 0:
    return 1
result = 1
for i in range(1, n + 1):
    result *= i
return result
```
-/
def myFactorialImp (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 1
  let mut result : Nat := 1
  for i in List.range n do
    result := result * (i + 1)
  return result

/-- Imperative implementation of `prog` on `Int` using `Id.run do` and mutable state,
directly translating the full Python `prog(n: int) -> int` including precondition check. -/
def progImp (n : Int) : Option Int := Id.run do
  if !pre n then
    return none
  if n == 0 then
    return some 1
  let mut result : Int := 1
  for i in List.range n.toNat do
    result := result * ((i : Int) + 1)
  return some result

/-! ## Imperative Tests -/

example : myFactorialImp 0 = 1 := by native_decide
example : myFactorialImp 1 = 1 := by native_decide
example : myFactorialImp 2 = 2 := by native_decide
example : myFactorialImp 3 = 6 := by native_decide
example : myFactorialImp 4 = 24 := by native_decide
example : myFactorialImp 5 = 120 := by native_decide
example : myFactorialImp 6 = 720 := by native_decide

example : progImp 3 = some 6 := by native_decide
example : progImp 0 = some 1 := by native_decide
example : progImp 1 = some 1 := by native_decide
example : progImp 5 = some 120 := by native_decide
example : progImp (-1) = none := by native_decide
example : progImp (-5) = none := by native_decide

#eval myFactorialImp 0
#eval myFactorialImp 1
#eval myFactorialImp 3
#eval myFactorialImp 5
#eval progImp 3
#eval progImp 0
#eval progImp (-1)

#eval Plausible.Testable.check (∀ n : Nat, myFactorial n = myFactorialImp n)
#eval Plausible.Testable.check (∀ n : Int, prog n = progImp n)
example : (List.range 20).all (fun n => myFactorial n == myFactorialImp n) = true := by native_decide
example : (List.range 20).all (fun k => let n : Int := (k : Int) - 5; prog n == progImp n) = true := by native_decide

/-! ## Equivalence Theorem (Functional = Imperative) -/

/-- Helper lemma relating the `List.range` fold on `Nat` to `myFactorial`. -/
theorem foldl_range_myFactorial (n : Nat) :
    List.foldl (fun r i => r * (i + 1)) 1 (List.range n) = myFactorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    simp [myFactorial, Nat.mul_comm]

/-- Helper lemma relating the `List.range` fold on `Int` to `(myFactorial n : Int)`. -/
theorem foldl_range_myFactorial_int (n : Nat) :
    List.foldl (fun (r : Int) (i : Nat) => r * ((i : Int) + 1)) 1 (List.range n) =
      (myFactorial n : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    simp [myFactorial, Int.mul_comm]

/-- Pointwise equivalence between functional `myFactorial` and imperative `myFactorialImp`. -/
theorem equivalence_thm (n : Nat) : myFactorial n = myFactorialImp n := by
  unfold myFactorialImp
  cases n with
  | zero => rfl
  | succ k =>
    simp [Id.run]
    exact (foldl_range_myFactorial (k + 1)).symm

/-- Function-level equality between `myFactorial` and `myFactorialImp`. -/
theorem myFactorial_eq_myFactorialImp : myFactorial = myFactorialImp :=
  funext equivalence_thm

/-- Pointwise equivalence between functional `prog` and imperative `progImp` for all `n : Int`. -/
theorem prog_equivalence_thm (n : Int) : prog n = progImp n := by
  unfold prog progImp pre
  by_cases h : n ≥ 0
  · by_cases h0 : n = 0
    · subst h0
      rfl
    · have hbeq : (n == 0) = false := beq_false_of_ne h0
      simp [h, hbeq, Id.run]
      exact congrArg some (foldl_range_myFactorial_int n.toNat).symm
  · simp [h, Id.run]
    rfl

/-- Function-level equality between `prog` and `progImp`. -/
theorem prog_eq_progImp : prog = progImp :=
  funext prog_equivalence_thm

end «16_MyFactorial»

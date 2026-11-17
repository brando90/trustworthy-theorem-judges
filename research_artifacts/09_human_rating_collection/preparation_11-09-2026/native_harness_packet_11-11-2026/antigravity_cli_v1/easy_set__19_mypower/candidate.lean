import Mathlib

/-!
# 19_MyPower

Lean 4 formalization of the Python `power` program (`19_MyPower`).
Computes `base` raised to the power of `exponent` for natural numbers,
along with an integer precondition-checked model that returns `none`
when either input is negative (modeling Python's `ValueError`).
-/

namespace «19_MyPower»

/-! ## 1. Functional Implementation -/

/-- Compute `base` raised to the power of `exponent` for natural numbers. -/
def myPower (base : Nat) : Nat → Nat
  | 0 => 1
  | exponent + 1 => base * myPower base exponent

/-- Boolean precondition check for integer inputs: both must be non-negative. -/
def pre (base exponent : Int) : Bool :=
  decide (base ≥ 0) && decide (exponent ≥ 0)

/-- Integer power function returning `none` when the precondition is violated
    (modeling Python's `ValueError`) and `some (base ^ exponent)` otherwise. -/
def myPowerInt (base exponent : Int) : Option Int :=
  if pre base exponent then
    some (Int.ofNat (myPower base.toNat exponent.toNat))
  else
    none

/-! ## 2. Unit Tests -/

#eval myPower 2 3
#eval myPower 0 0
#eval myPower 0 5
#eval myPower 5 0
#eval myPower 1 10
#eval myPower 3 4
#eval myPowerInt 2 3
#eval myPowerInt 0 0
#eval myPowerInt (-1) 2
#eval myPowerInt 2 (-1)

example : myPower 2 3 = 8 := by native_decide
example : myPower 0 0 = 1 := by native_decide
example : myPower 5 0 = 1 := by native_decide
example : myPower 0 5 = 0 := by native_decide
example : myPower 1 10 = 1 := by native_decide
example : myPower 3 4 = 81 := by native_decide

example : myPowerInt 2 3 = some 8 := by native_decide
example : myPowerInt 0 0 = some 1 := by native_decide
example : myPowerInt 0 5 = some 0 := by native_decide
example : myPowerInt 5 0 = some 1 := by native_decide
example : myPowerInt (-1) 2 = none := by native_decide
example : myPowerInt 2 (-1) = none := by native_decide

/-! ## 3. Pre-condition Predicate -/

/-- Pre-condition for natural number inputs. -/
@[reducible]
def Pre (base exponent : Nat) : Prop :=
  base ≥ 0 ∧ exponent ≥ 0

/-- Pre-condition for integer inputs: both inputs are non-negative integers. -/
@[reducible]
def PreInt (base exponent : Int) : Prop :=
  base ≥ 0 ∧ exponent ≥ 0

/-! ## 4. Property Propositions and Theorems -/

/-- Helper lemma: `myPower` agrees with Lean's standard `Nat.pow` (`^`). -/
@[simp]
theorem myPower_eq_pow (base exponent : Nat) : myPower base exponent = base ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ n ih =>
    simp [myPower, ih, Nat.pow_succ, Nat.mul_comm]

/-- Equivalence with standard power operator `base ^ exponent`. -/
@[reducible]
def eq_pow_prop (base exponent : Nat) : Prop :=
  myPower base exponent = base ^ exponent

theorem eq_pow_thm (base exponent : Nat) : eq_pow_prop base exponent := by
  unfold eq_pow_prop
  exact myPower_eq_pow base exponent

/-- Edge case: `power(n, 0) = 1` for any `n`. -/
@[reducible]
def exp_zero_prop (base exponent : Nat) : Prop :=
  myPower base 0 = 1 ∧ (exponent = 0 → myPower base exponent = 1)

theorem exp_zero_thm (base exponent : Nat) : exp_zero_prop base exponent := by
  unfold exp_zero_prop
  refine ⟨rfl, ?_⟩
  intro h
  subst h
  rfl

/-- Edge case: `power(0, n) = 0` for `n > 0`. -/
@[reducible]
def zero_base_prop (base exponent : Nat) : Prop :=
  (exponent > 0 → myPower 0 exponent = 0) ∧
  (base = 0 → exponent > 0 → myPower base exponent = 0)

theorem zero_base_thm (base exponent : Nat) : zero_base_prop base exponent := by
  unfold zero_base_prop
  refine ⟨?_, ?_⟩
  · intro h
    rw [myPower_eq_pow]
    exact Nat.zero_pow h
  · intro hb he
    subst hb
    rw [myPower_eq_pow]
    exact Nat.zero_pow he

/-- Edge case: `power(0, 0) = 1` by convention. -/
@[reducible]
def zero_zero_prop (base exponent : Nat) : Prop :=
  myPower 0 0 = 1 ∧ (base = 0 → exponent = 0 → myPower base exponent = 1)

theorem zero_zero_thm (base exponent : Nat) : zero_zero_prop base exponent := by
  unfold zero_zero_prop
  refine ⟨rfl, ?_⟩
  intro hb he
  subst hb; subst he
  rfl

/-- Base case: `power(n, 1) = n`. -/
@[reducible]
def exp_one_prop (base exponent : Nat) : Prop :=
  myPower base 1 = base ∧ (exponent = 1 → myPower base exponent = base)

theorem exp_one_thm (base exponent : Nat) : exp_one_prop base exponent := by
  unfold exp_one_prop
  refine ⟨by simp, ?_⟩
  intro h
  subst h
  simp

/-- Identity base: `power(1, n) = 1`. -/
@[reducible]
def one_base_prop (base exponent : Nat) : Prop :=
  myPower 1 exponent = 1 ∧ (base = 1 → myPower base exponent = 1)

theorem one_base_thm (base exponent : Nat) : one_base_prop base exponent := by
  unfold one_base_prop
  refine ⟨by simp, ?_⟩
  intro h
  subst h
  simp

/-- Recursive step property: `power(b, e + 1) = b * power(b, e) = power(b, e) * b`. -/
@[reducible]
def succ_exp_prop (base exponent : Nat) : Prop :=
  myPower base (exponent + 1) = base * myPower base exponent ∧
  myPower base (exponent + 1) = myPower base exponent * base

theorem succ_exp_thm (base exponent : Nat) : succ_exp_prop base exponent := by
  unfold succ_exp_prop
  refine ⟨rfl, ?_⟩
  simp [myPower, Nat.mul_comm]

/-- Non-negativity: `power(base, exponent) ≥ 0`. -/
@[reducible]
def nonneg_prop (base exponent : Nat) : Prop :=
  myPower base exponent ≥ 0

theorem nonneg_thm (base exponent : Nat) : nonneg_prop base exponent := by
  exact Nat.zero_le _

/-- Positivity: `base > 0 → power(base, exponent) > 0`. -/
@[reducible]
def pos_prop (base exponent : Nat) : Prop :=
  base > 0 → myPower base exponent > 0

theorem pos_thm (base exponent : Nat) : pos_prop base exponent := by
  unfold pos_prop
  intro h
  rw [myPower_eq_pow]
  exact Nat.pow_pos h

/-- Characterization of when `power(base, exponent) = 0`. -/
@[reducible]
def zero_iff_prop (base exponent : Nat) : Prop :=
  myPower base exponent = 0 ↔ (base = 0 ∧ exponent > 0)

theorem zero_iff_thm (base exponent : Nat) : zero_iff_prop base exponent := by
  unfold zero_iff_prop
  rw [myPower_eq_pow, Nat.pow_eq_zero]
  omega

/-- Characterization of when `power(base, exponent) = 1`. -/
@[reducible]
def one_iff_prop (base exponent : Nat) : Prop :=
  myPower base exponent = 1 ↔ (base = 1 ∨ exponent = 0)

theorem one_iff_thm (base exponent : Nat) : one_iff_prop base exponent := by
  unfold one_iff_prop
  rw [myPower_eq_pow, Nat.pow_eq_one]

/-- Lower bound by base: `base > 0 → exponent > 0 → power(base, exponent) ≥ base`. -/
@[reducible]
def ge_base_prop (base exponent : Nat) : Prop :=
  base > 0 → exponent > 0 → myPower base exponent ≥ base

theorem ge_base_thm (base exponent : Nat) : ge_base_prop base exponent := by
  unfold ge_base_prop
  intro _hb he
  rw [myPower_eq_pow]
  exact Nat.le_self_pow (Nat.ne_of_gt he) base

/-- Strict growth above 1: `base > 1 → exponent > 0 → power(base, exponent) > 1`. -/
@[reducible]
def gt_one_prop (base exponent : Nat) : Prop :=
  base > 1 → exponent > 0 → myPower base exponent > 1

theorem gt_one_thm (base exponent : Nat) : gt_one_prop base exponent := by
  unfold gt_one_prop
  intro hb he
  rw [myPower_eq_pow]
  exact Nat.one_lt_pow (Nat.ne_of_gt he) hb

/-- Divisibility by base: `exponent > 0 → base ∣ power(base, exponent)`. -/
@[reducible]
def dvd_prop (base exponent : Nat) : Prop :=
  exponent > 0 → base ∣ myPower base exponent

theorem dvd_thm (base exponent : Nat) : dvd_prop base exponent := by
  unfold dvd_prop
  intro he
  rw [myPower_eq_pow]
  exact dvd_pow_self base (Nat.ne_of_gt he)

/-- Product of powers law: `power(b, e1 + e2) = power(b, e1) * power(b, e2)`. -/
@[reducible]
def add_exp_prop (base e1 e2 : Nat) : Prop :=
  myPower base (e1 + e2) = myPower base e1 * myPower base e2

theorem add_exp_thm (base e1 e2 : Nat) : add_exp_prop base e1 e2 := by
  unfold add_exp_prop
  simp [Nat.pow_add]

/-- Power of a product law: `power(b1 * b2, e) = power(b1, e) * power(b2, e)`. -/
@[reducible]
def mul_base_prop (b1 b2 exponent : Nat) : Prop :=
  myPower (b1 * b2) exponent = myPower b1 exponent * myPower b2 exponent

theorem mul_base_thm (b1 b2 exponent : Nat) : mul_base_prop b1 b2 exponent := by
  unfold mul_base_prop
  simp [Nat.mul_pow]

/-- Power of a power law: `power(b, e1 * e2) = power(power(b, e1), e2)`. -/
@[reducible]
def mul_exp_prop (base e1 e2 : Nat) : Prop :=
  myPower base (e1 * e2) = myPower (myPower base e1) e2

theorem mul_exp_thm (base e1 e2 : Nat) : mul_exp_prop base e1 e2 := by
  unfold mul_exp_prop
  simp [Nat.pow_mul]

/-- Monotonicity in the base: `b1 ≤ b2 → power(b1, e) ≤ power(b2, e)`. -/
@[reducible]
def mono_base_prop (b1 b2 exponent : Nat) : Prop :=
  b1 ≤ b2 → myPower b1 exponent ≤ myPower b2 exponent

theorem mono_base_thm (b1 b2 exponent : Nat) : mono_base_prop b1 b2 exponent := by
  unfold mono_base_prop
  intro h
  simp [Nat.pow_le_pow_left h]

/-- Monotonicity in the exponent: `base ≥ 1 → e1 ≤ e2 → power(base, e1) ≤ power(base, e2)`. -/
@[reducible]
def mono_exp_prop (base e1 e2 : Nat) : Prop :=
  base ≥ 1 → e1 ≤ e2 → myPower base e1 ≤ myPower base e2

theorem mono_exp_thm (base e1 e2 : Nat) : mono_exp_prop base e1 e2 := by
  unfold mono_exp_prop
  intro hb he
  simp [Nat.pow_le_pow_right hb he]

/-- Strict monotonicity in the exponent: `base > 1 → e1 < e2 → power(base, e1) < power(base, e2)`. -/
@[reducible]
def strict_mono_exp_prop (base e1 e2 : Nat) : Prop :=
  base > 1 → e1 < e2 → myPower base e1 < myPower base e2

theorem strict_mono_exp_thm (base e1 e2 : Nat) : strict_mono_exp_prop base e1 e2 := by
  unfold strict_mono_exp_prop
  intro hb he
  simp [Nat.pow_lt_pow_right hb he]

/-- Integer specification when precondition holds. -/
@[reducible]
def int_valid_prop (base exponent : Int) : Prop :=
  PreInt base exponent →
    myPowerInt base exponent = some (Int.ofNat (myPower base.toNat exponent.toNat)) ∧
    myPowerInt base exponent = some (base ^ exponent.toNat)

theorem int_valid_thm (base exponent : Int) : int_valid_prop base exponent := by
  unfold int_valid_prop PreInt myPowerInt pre
  intro ⟨hb, he⟩
  have hcond : (decide (base ≥ 0) && decide (exponent ≥ 0)) = true := by
    simp [hb, he]
  rw [if_pos hcond]
  refine ⟨rfl, ?_⟩
  congr 1
  rw [myPower_eq_pow]
  have hb_eq : (base.toNat : Int) = base := Int.toNat_of_nonneg hb
  calc
    Int.ofNat (base.toNat ^ exponent.toNat) = ((base.toNat ^ exponent.toNat : Nat) : Int) := rfl
    _ = (base.toNat : Int) ^ exponent.toNat := by push_cast; rfl
    _ = base ^ exponent.toNat := by rw [hb_eq]

/-- Integer specification when precondition is violated (raises `ValueError` in Python). -/
@[reducible]
def int_invalid_prop (base exponent : Int) : Prop :=
  ¬ PreInt base exponent → myPowerInt base exponent = none

theorem int_invalid_thm (base exponent : Int) : int_invalid_prop base exponent := by
  unfold int_invalid_prop PreInt myPowerInt pre
  intro hnot
  have hcond : ¬ ((decide (base ≥ 0) && decide (exponent ≥ 0)) = true) := by
    simp [hnot]
  exact if_neg hcond

/-! ## 5. Post-condition -/

/-- Post-condition combining the specification properties of `myPower`. -/
@[reducible]
def Post_prop (base exponent : Nat) : Prop :=
  eq_pow_prop base exponent ∧
  exp_zero_prop base exponent ∧
  zero_base_prop base exponent ∧
  zero_zero_prop base exponent ∧
  exp_one_prop base exponent ∧
  one_base_prop base exponent ∧
  succ_exp_prop base exponent ∧
  nonneg_prop base exponent ∧
  pos_prop base exponent ∧
  zero_iff_prop base exponent ∧
  one_iff_prop base exponent ∧
  ge_base_prop base exponent ∧
  gt_one_prop base exponent ∧
  dvd_prop base exponent ∧
  add_exp_prop base exponent 1 ∧
  mul_base_prop base 1 exponent ∧
  mul_exp_prop base exponent 1 ∧
  mono_base_prop base (base + 1) exponent ∧
  mono_exp_prop (base + 1) exponent (exponent + 1) ∧
  strict_mono_exp_prop (base + 2) exponent (exponent + 1)

/-- Post-condition for the integer precondition-checked function `myPowerInt`. -/
@[reducible]
def PostInt_prop (base exponent : Int) : Prop :=
  int_valid_prop base exponent ∧ int_invalid_prop base exponent

set_option synthInstance.maxSize 512 in
instance (base exponent : Nat) : Decidable (Post_prop base exponent) :=
  inferInstance

instance (base exponent : Int) : Decidable (PostInt_prop base exponent) :=
  inferInstance

/-! ## 6. Property-Based Tests -/

#eval Plausible.Testable.check (∀ base exponent : Nat, eq_pow_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, exp_zero_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, zero_base_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, zero_zero_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, exp_one_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, one_base_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, succ_exp_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, nonneg_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, pos_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, zero_iff_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, one_iff_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, ge_base_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, gt_one_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Nat, dvd_prop (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base e1 e2 : Nat, add_exp_prop (base % 8) (e1 % 6) (e2 % 6))
#eval Plausible.Testable.check (∀ b1 b2 exponent : Nat, mul_base_prop (b1 % 8) (b2 % 8) (exponent % 6))
#eval Plausible.Testable.check (∀ base e1 e2 : Nat, mul_exp_prop (base % 6) (e1 % 5) (e2 % 5))
#eval Plausible.Testable.check (∀ b1 b2 exponent : Nat, mono_base_prop (b1 % 8) (b2 % 8) (exponent % 6))
#eval Plausible.Testable.check (∀ base e1 e2 : Nat, mono_exp_prop (base % 8) (e1 % 6) (e2 % 6))
#eval Plausible.Testable.check (∀ base e1 e2 : Nat, strict_mono_exp_prop (base % 8) (e1 % 6) (e2 % 6))
#eval Plausible.Testable.check (∀ base exponent : Nat, decide (Post_prop (base % 8) (exponent % 6)) = true)
#eval Plausible.Testable.check (∀ base exponent : Int, decide (int_valid_prop (base % 8) (exponent % 6)) = true)
#eval Plausible.Testable.check (∀ base exponent : Int, decide (int_invalid_prop (base % 8) (exponent % 6)) = true)
#eval Plausible.Testable.check (∀ base exponent : Int, decide (PostInt_prop (base % 8) (exponent % 6)) = true)

-- Bounded exhaustive property-based tests over small inputs
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (eq_pow_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (exp_zero_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (zero_base_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (zero_zero_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (exp_one_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (one_base_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (succ_exp_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (nonneg_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (pos_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (zero_iff_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (one_iff_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (ge_base_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (gt_one_prop b e))) = true := by native_decide
example : (List.range 10).all (fun b => (List.range 8).all (fun e => decide (dvd_prop b e))) = true := by native_decide
example : (List.range 6).all (fun b => (List.range 5).all (fun e1 => (List.range 5).all (fun e2 => decide (add_exp_prop b e1 e2)))) = true := by native_decide
example : (List.range 6).all (fun b1 => (List.range 6).all (fun b2 => (List.range 5).all (fun e => decide (mul_base_prop b1 b2 e)))) = true := by native_decide
example : (List.range 5).all (fun b => (List.range 4).all (fun e1 => (List.range 4).all (fun e2 => decide (mul_exp_prop b e1 e2)))) = true := by native_decide
example : (List.range 6).all (fun b1 => (List.range 6).all (fun b2 => (List.range 5).all (fun e => decide (mono_base_prop b1 b2 e)))) = true := by native_decide
example : (List.range 6).all (fun b => (List.range 5).all (fun e1 => (List.range 5).all (fun e2 => decide (mono_exp_prop b e1 e2)))) = true := by native_decide
example : (List.range 6).all (fun b => (List.range 5).all (fun e1 => (List.range 5).all (fun e2 => decide (strict_mono_exp_prop b e1 e2)))) = true := by native_decide
example : (List.range 8).all (fun b => (List.range 6).all (fun e => decide (Post_prop b e))) = true := by native_decide

/-! ## 7. Correctness Theorem -/

/-- Main correctness theorem: `Pre` implies `Post_prop` for all natural number inputs. -/
theorem myPower_correct (base exponent : Nat) (_hpre : Pre base exponent) :
    Post_prop base exponent := by
  unfold Post_prop
  refine ⟨eq_pow_thm base exponent,
          exp_zero_thm base exponent,
          zero_base_thm base exponent,
          zero_zero_thm base exponent,
          exp_one_thm base exponent,
          one_base_thm base exponent,
          succ_exp_thm base exponent,
          nonneg_thm base exponent,
          pos_thm base exponent,
          zero_iff_thm base exponent,
          one_iff_thm base exponent,
          ge_base_thm base exponent,
          gt_one_thm base exponent,
          dvd_thm base exponent,
          add_exp_thm base exponent 1,
          mul_base_thm base 1 exponent,
          mul_exp_thm base exponent 1,
          mono_base_thm base (base + 1) exponent,
          mono_exp_thm (base + 1) exponent (exponent + 1),
          strict_mono_exp_thm (base + 2) exponent (exponent + 1)⟩

/-- Main correctness theorem for the integer version `myPowerInt`. -/
theorem myPowerInt_correct (base exponent : Int) :
    PostInt_prop base exponent := by
  exact ⟨int_valid_thm base exponent, int_invalid_thm base exponent⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `myPower` using `Id.run do` and mutable state. -/
def myPowerImp (base exponent : Nat) : Nat := Id.run do
  if exponent == 0 then
    return 1
  let mut result : Nat := 1
  for _ in List.range exponent do
    result := result * base
  return result

/-- Imperative implementation of `myPowerInt` on integers with precondition check. -/
def myPowerIntImp (base exponent : Int) : Option Int := Id.run do
  if !pre base exponent then
    return none
  let expNat := exponent.toNat
  let baseNat := base.toNat
  if expNat == 0 then
    return some 1
  let mut result : Nat := 1
  for _ in List.range expNat do
    result := result * baseNat
  return some (Int.ofNat result)

/-! ## 9. Imperative Tests -/

#eval myPowerImp 2 3
#eval myPowerImp 0 0
#eval myPowerImp 0 5
#eval myPowerImp 5 0
#eval myPowerImp 1 10
#eval myPowerImp 3 4
#eval myPowerIntImp 2 3
#eval myPowerIntImp 0 0
#eval myPowerIntImp (-1) 2
#eval myPowerIntImp 2 (-1)

example : myPowerImp 2 3 = 8 := by native_decide
example : myPowerImp 0 0 = 1 := by native_decide
example : myPowerImp 5 0 = 1 := by native_decide
example : myPowerImp 0 5 = 0 := by native_decide
example : myPowerImp 1 10 = 1 := by native_decide
example : myPowerImp 3 4 = 81 := by native_decide

example : myPowerIntImp 2 3 = some 8 := by native_decide
example : myPowerIntImp 0 0 = some 1 := by native_decide
example : myPowerIntImp 0 5 = some 0 := by native_decide
example : myPowerIntImp 5 0 = some 1 := by native_decide
example : myPowerIntImp (-1) 2 = none := by native_decide
example : myPowerIntImp 2 (-1) = none := by native_decide

-- Property-based test for functional-imperative equivalence
#eval Plausible.Testable.check (∀ base exponent : Nat, myPower (base % 10) (exponent % 10) = myPowerImp (base % 10) (exponent % 10))
#eval Plausible.Testable.check (∀ base exponent : Int, myPowerInt (base % 10) (exponent % 10) = myPowerIntImp (base % 10) (exponent % 10))

/-! ## 10. Equivalence Theorem -/

/-- Helper lemma characterizing the fold over a list multiplying by `base`. -/
theorem foldl_mul_base (xs : List α) (acc base : Nat) :
    xs.foldl (fun r _ => r * base) acc = acc * base ^ xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons _ tl ih =>
    simp only [List.foldl_cons, List.length_cons, ih]
    rw [Nat.pow_succ', ← Nat.mul_assoc]

/-- Functional and imperative implementations of `myPower` are equivalent. -/
theorem myPower_equiv (base exponent : Nat) :
    myPower base exponent = myPowerImp base exponent := by
  rw [myPower_eq_pow]
  unfold myPowerImp
  cases exponent with
  | zero => rfl
  | succ n =>
    simp [foldl_mul_base]

/-- Functional and imperative implementations of `myPowerInt` are equivalent. -/
theorem myPowerInt_equiv (base exponent : Int) :
    myPowerInt base exponent = myPowerIntImp base exponent := by
  unfold myPowerInt myPowerIntImp
  by_cases h : pre base exponent = true
  · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [myPower_equiv base.toNat exponent.toNat]
    unfold myPowerImp
    cases exponent.toNat with
    | zero => rfl
    | succ n => rfl
  · have hf : pre base exponent = false := Bool.eq_false_iff.mpr h
    simp [hf]

end «19_MyPower»

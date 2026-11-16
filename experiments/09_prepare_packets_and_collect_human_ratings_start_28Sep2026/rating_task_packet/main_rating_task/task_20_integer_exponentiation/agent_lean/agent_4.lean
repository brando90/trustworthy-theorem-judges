import Mathlib
import Plausible

/-!
# 19_MyPower: Exponentiation for Natural Numbers

This module formalizes the Python exponentiation program:
- `pre(base, exponent)`: True iff `base >= 0` and `exponent >= 0`.
- `prog(base, exponent)`: Returns `base ^ exponent` for non-negative integers `base` and `exponent`,
  and raises `ValueError` if the precondition is violated.

Edge cases covered:
- `power(n, 0) = 1` for any `n`
- `power(0, n) = 0` for `n > 0`
- `power(0, 0) = 1` by convention
- Precondition violation (`base < 0` or `exponent < 0`) returns `none` in `prog`.
-/

namespace «19_MyPower»

/-! ## 4. Implementation (Functional Definition) -/

/-- Functional implementation on `Int` computing `base ^ exponent.toNat` via list fold over range. -/
def myPower (base exponent : Int) : Int :=
  if exponent == 0 then 1
  else (List.range exponent.toNat).foldl (fun acc _ => acc * base) 1

/-- Executable Boolean precondition matching Python's `pre(base, exponent)`. -/
def pre (base exponent : Int) : Bool :=
  decide (0 ≤ base ∧ 0 ≤ exponent)

/-- Partial/checked functional implementation matching Python's `prog(base, exponent)`.
    Returns `some (base ^ exponent)` when `pre base exponent` holds, and `none` otherwise
    (modeling Python's `ValueError`). -/
def prog (base exponent : Int) : Option Int :=
  if pre base exponent then
    some (myPower base exponent)
  else
    none

/-- Recursive functional implementation on `Nat`. -/
def myPowerNat (base exponent : Nat) : Nat :=
  match exponent with
  | 0 => 1
  | e + 1 => myPowerNat base e * base

/-! ## 5. Unit Tests -/

-- Basic unit tests
#eval myPower 2 3
#eval prog 2 3
#eval myPowerNat 2 3

example : myPower 2 3 = 8 := by native_decide
example : prog 2 3 = some 8 := by native_decide
example : myPowerNat 2 3 = 8 := by native_decide
example : myPower 3 4 = 81 := by native_decide
example : prog 3 4 = some 81 := by native_decide

-- Edge case unit tests: power(0, 0) = 1, power(n, 0) = 1, power(0, n) = 0 for n > 0
#eval myPower 0 0
#eval prog 0 0
#eval myPowerNat 0 0
#eval myPower 5 0
#eval myPower 0 4

example : myPower 0 0 = 1 := by native_decide
example : prog 0 0 = some 1 := by native_decide
example : myPowerNat 0 0 = 1 := by native_decide
example : myPower 5 0 = 1 := by native_decide
example : prog 5 0 = some 1 := by native_decide
example : myPowerNat 5 0 = 1 := by native_decide
example : myPower 0 4 = 0 := by native_decide
example : prog 0 4 = some 0 := by native_decide
example : myPowerNat 0 4 = 0 := by native_decide
example : myPower 1 10 = 1 := by native_decide
example : myPower 7 1 = 7 := by native_decide

-- Negative tests (pre-violations must raise ValueError / return none)
#eval prog (-1) 2
#eval prog 2 (-1)

example : pre (-1) 2 = false := by native_decide
example : pre 2 (-1) = false := by native_decide
example : prog (-1) 2 = none := by native_decide
example : prog 2 (-1) = none := by native_decide
example : prog (-3) (-4) = none := by native_decide

/-! ## 6. Pre-condition Predicate -/

/-- Precondition predicate: both `base` and `exponent` are non-negative integers. -/
def Pre (base exponent : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ exponent

instance (base exponent : Int) : Decidable (Pre base exponent) := by
  unfold Pre; infer_instance

/-- Precondition predicate on `Nat` (trivially satisfied by all natural numbers). -/
def PreNat (_base _exponent : Nat) : Prop :=
  True

instance (base exponent : Nat) : Decidable (PreNat base exponent) := by
  unfold PreNat; infer_instance

theorem pre_iff_Pre (base exponent : Int) :
    pre base exponent = true ↔ Pre base exponent := by
  simp [pre, Pre]

/-! ## 7. Property Propositions and Theorems -/

/-- Helper lemma: folding multiplication by a constant `base` over any list `l` multiplies `init` by `base ^ l.length`. -/
theorem foldl_mul_const {α : Type*} (base : Int) (l : List α) (init : Int) :
    l.foldl (fun acc _ => acc * base) init = init * base ^ l.length := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons, ih, pow_succ', ← mul_assoc]

/-- Core mathematical characterization: `myPower base exponent = base ^ exponent.toNat`. -/
theorem myPower_eq_pow (base exponent : Int) :
    myPower base exponent = base ^ exponent.toNat := by
  unfold myPower
  split_ifs with h
  · have h0 : exponent = 0 := by simpa using h
    subst h0
    simp
  · rw [foldl_mul_const, List.length_range, one_mul]

/-- Core mathematical characterization on `Nat`: `myPowerNat base exponent = base ^ exponent`. -/
theorem myPowerNat_eq_pow (base exponent : Nat) :
    myPowerNat base exponent = base ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ e ih =>
    simp only [myPowerNat, ih, Nat.pow_succ]

/-- Property 1: Equivalence with standard power operation `base ^ exponent.toNat`. -/
def pow_eq_prop (base exponent : Int) : Prop :=
  myPower base exponent = base ^ exponent.toNat

instance (base exponent : Int) : Decidable (pow_eq_prop base exponent) := by
  unfold pow_eq_prop; infer_instance

theorem pow_eq_thm (base exponent : Int) (_h : Pre base exponent) : pow_eq_prop base exponent :=
  myPower_eq_pow base exponent

/-- Property 2: Edge case `power(n, 0) = 1` for any `n`. -/
def exp_zero_prop (base exponent : Int) : Prop :=
  exponent = 0 → myPower base exponent = 1

instance (base exponent : Int) : Decidable (exp_zero_prop base exponent) := by
  unfold exp_zero_prop; infer_instance

theorem exp_zero_thm (base exponent : Int) (_h : Pre base exponent) : exp_zero_prop base exponent := by
  intro h0
  rw [myPower_eq_pow, h0]
  rfl

/-- Property 3: Edge case `power(0, n) = 0` for `n > 0`. -/
def zero_base_prop (base exponent : Int) : Prop :=
  base = 0 ∧ 0 < exponent → myPower base exponent = 0

instance (base exponent : Int) : Decidable (zero_base_prop base exponent) := by
  unfold zero_base_prop; infer_instance

theorem zero_base_thm (base exponent : Int) (_h : Pre base exponent) : zero_base_prop base exponent := by
  rintro ⟨hb, he⟩
  rw [myPower_eq_pow, hb]
  have hne : exponent.toNat ≠ 0 := by omega
  exact zero_pow hne

/-- Property 4: Edge case `power(0, 0) = 1` by convention. -/
def zero_to_zero_prop (base exponent : Int) : Prop :=
  base = 0 ∧ exponent = 0 → myPower base exponent = 1

instance (base exponent : Int) : Decidable (zero_to_zero_prop base exponent) := by
  unfold zero_to_zero_prop; infer_instance

theorem zero_to_zero_thm (base exponent : Int) (_h : Pre base exponent) : zero_to_zero_prop base exponent := by
  rintro ⟨hb, he⟩
  rw [myPower_eq_pow, hb, he]
  rfl

/-- Property 5: `power(1, n) = 1` for any `n`. -/
def one_base_prop (base exponent : Int) : Prop :=
  base = 1 → myPower base exponent = 1

instance (base exponent : Int) : Decidable (one_base_prop base exponent) := by
  unfold one_base_prop; infer_instance

theorem one_base_thm (base exponent : Int) (_h : Pre base exponent) : one_base_prop base exponent := by
  intro hb
  rw [myPower_eq_pow, hb, one_pow]

/-- Property 6: `power(n, 1) = n` for any `n`. -/
def exp_one_prop (base exponent : Int) : Prop :=
  exponent = 1 → myPower base exponent = base

instance (base exponent : Int) : Decidable (exp_one_prop base exponent) := by
  unfold exp_one_prop; infer_instance

theorem exp_one_thm (base exponent : Int) (_h : Pre base exponent) : exp_one_prop base exponent := by
  intro he
  rw [myPower_eq_pow, he]
  simp

/-- Property 7: Non-negativity of `myPower base exponent` for non-negative `base`. -/
def nonneg_prop (base exponent : Int) : Prop :=
  0 ≤ myPower base exponent

instance (base exponent : Int) : Decidable (nonneg_prop base exponent) := by
  unfold nonneg_prop; infer_instance

theorem nonneg_thm (base exponent : Int) (h : Pre base exponent) : nonneg_prop base exponent := by
  unfold nonneg_prop
  rw [myPower_eq_pow]
  exact pow_nonneg h.1 _

/-- Property 8: Strict positivity of `myPower base exponent` when `base > 0`. -/
def pos_prop (base exponent : Int) : Prop :=
  0 < base → 0 < myPower base exponent

instance (base exponent : Int) : Decidable (pos_prop base exponent) := by
  unfold pos_prop; infer_instance

theorem pos_thm (base exponent : Int) (_h : Pre base exponent) : pos_prop base exponent := by
  intro hb
  rw [myPower_eq_pow]
  exact pow_pos hb _

/-- Property 9: Lower bound `1 ≤ myPower base exponent` when `1 ≤ base`. -/
def ge_one_prop (base exponent : Int) : Prop :=
  1 ≤ base → 1 ≤ myPower base exponent

instance (base exponent : Int) : Decidable (ge_one_prop base exponent) := by
  unfold ge_one_prop; infer_instance

theorem ge_one_thm (base exponent : Int) (_h : Pre base exponent) : ge_one_prop base exponent := by
  intro hb
  rw [myPower_eq_pow]
  exact one_le_pow₀ hb

/-- Property 10: Inductive step `myPower base (exponent + 1) = myPower base exponent * base`. -/
def step_prop (base exponent : Int) : Prop :=
  myPower base (exponent + 1) = myPower base exponent * base

instance (base exponent : Int) : Decidable (step_prop base exponent) := by
  unfold step_prop; infer_instance

theorem step_thm (base exponent : Int) (h : Pre base exponent) : step_prop base exponent := by
  obtain ⟨_hb, he⟩ := h
  unfold step_prop
  rw [myPower_eq_pow, myPower_eq_pow]
  have htoNat : (exponent + 1).toNat = exponent.toNat + 1 := by omega
  rw [htoNat, pow_succ]

/-- Property 11: Exponent addition law `myPower base (e1 + e2) = myPower base e1 * myPower base e2`. -/
def add_exp_prop (base e1 e2 : Int) : Prop :=
  0 ≤ e1 ∧ 0 ≤ e2 → myPower base (e1 + e2) = myPower base e1 * myPower base e2

instance (base e1 e2 : Int) : Decidable (add_exp_prop base e1 e2) := by
  unfold add_exp_prop; infer_instance

theorem add_exp_thm (base e1 e2 : Int) : add_exp_prop base e1 e2 := by
  rintro ⟨h1, h2⟩
  rw [myPower_eq_pow, myPower_eq_pow, myPower_eq_pow]
  have htoNat : (e1 + e2).toNat = e1.toNat + e2.toNat := by omega
  rw [htoNat, pow_add]

/-- Property 12: Base multiplication law `myPower (b1 * b2) exponent = myPower b1 exponent * myPower b2 exponent`. -/
def mul_base_prop (b1 b2 exponent : Int) : Prop :=
  0 ≤ exponent → myPower (b1 * b2) exponent = myPower b1 exponent * myPower b2 exponent

instance (b1 b2 exponent : Int) : Decidable (mul_base_prop b1 b2 exponent) := by
  unfold mul_base_prop; infer_instance

theorem mul_base_thm (b1 b2 exponent : Int) : mul_base_prop b1 b2 exponent := by
  intro _he
  rw [myPower_eq_pow, myPower_eq_pow, myPower_eq_pow, mul_pow]

/-- Property 13: Power of a power law `myPower base (e1 * e2) = myPower (myPower base e1) e2`. -/
def mul_exp_prop (base e1 e2 : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ e1 ∧ 0 ≤ e2 → myPower base (e1 * e2) = myPower (myPower base e1) e2

instance (base e1 e2 : Int) : Decidable (mul_exp_prop base e1 e2) := by
  unfold mul_exp_prop; infer_instance

theorem mul_exp_thm (base e1 e2 : Int) : mul_exp_prop base e1 e2 := by
  rintro ⟨_hb, h1, h2⟩
  rw [myPower_eq_pow, myPower_eq_pow, myPower_eq_pow]
  have htoNat : (e1 * e2).toNat = e1.toNat * e2.toNat := Int.toNat_mul h1 h2
  rw [htoNat, pow_mul]

/-- Property 14: Base monotonicity: for `0 ≤ b1 ≤ b2`, `myPower b1 exponent ≤ myPower b2 exponent`. -/
def mono_base_prop (b1 b2 exponent : Int) : Prop :=
  0 ≤ b1 ∧ b1 ≤ b2 ∧ 0 ≤ exponent → myPower b1 exponent ≤ myPower b2 exponent

instance (b1 b2 exponent : Int) : Decidable (mono_base_prop b1 b2 exponent) := by
  unfold mono_base_prop; infer_instance

theorem mono_base_thm (b1 b2 exponent : Int) : mono_base_prop b1 b2 exponent := by
  rintro ⟨hb1, hb12, _he⟩
  rw [myPower_eq_pow, myPower_eq_pow]
  exact pow_le_pow_left₀ hb1 hb12 _

/-- Property 15: Exponent monotonicity: for `1 ≤ base` and `0 ≤ e1 ≤ e2`, `myPower base e1 ≤ myPower base e2`. -/
def mono_exp_prop (base e1 e2 : Int) : Prop :=
  1 ≤ base ∧ 0 ≤ e1 ∧ e1 ≤ e2 → myPower base e1 ≤ myPower base e2

instance (base e1 e2 : Int) : Decidable (mono_exp_prop base e1 e2) := by
  unfold mono_exp_prop; infer_instance

theorem mono_exp_thm (base e1 e2 : Int) : mono_exp_prop base e1 e2 := by
  rintro ⟨hb, _h1, h12⟩
  rw [myPower_eq_pow, myPower_eq_pow]
  have hle : e1.toNat ≤ e2.toNat := by omega
  exact pow_le_pow_right₀ hb hle

/-- Property 16: Checked program `prog` returns `some (base ^ exponent.toNat)` under `Pre`. -/
def prog_valid_prop (base exponent : Int) : Prop :=
  prog base exponent = some (myPower base exponent) ∧
  prog base exponent = some (base ^ exponent.toNat)

instance (base exponent : Int) : Decidable (prog_valid_prop base exponent) := by
  unfold prog_valid_prop; infer_instance

theorem prog_valid_thm (base exponent : Int) (h : Pre base exponent) : prog_valid_prop base exponent := by
  unfold prog_valid_prop prog
  have hpre : pre base exponent = true := (pre_iff_Pre base exponent).mpr h
  rw [if_pos hpre, myPower_eq_pow]
  exact ⟨rfl, rfl⟩

/-- Property 17: Checked program `prog` returns `none` (raises ValueError) when `Pre` is violated. -/
def prog_invalid_prop (base exponent : Int) : Prop :=
  ¬ Pre base exponent → prog base exponent = none

instance (base exponent : Int) : Decidable (prog_invalid_prop base exponent) := by
  unfold prog_invalid_prop; infer_instance

theorem prog_invalid_thm (base exponent : Int) : prog_invalid_prop base exponent := by
  intro hnot
  unfold prog
  have hpre : ¬ pre base exponent = true := by
    intro hp
    exact hnot ((pre_iff_Pre base exponent).mp hp)
  exact if_neg hpre

/-- Property 18: `prog base exponent` succeeds iff `Pre base exponent` holds. -/
def prog_isSome_iff_prop (base exponent : Int) : Prop :=
  (prog base exponent).isSome = true ↔ Pre base exponent

instance (base exponent : Int) : Decidable (prog_isSome_iff_prop base exponent) := by
  unfold prog_isSome_iff_prop; infer_instance

theorem prog_isSome_iff_thm (base exponent : Int) : prog_isSome_iff_prop base exponent := by
  unfold prog_isSome_iff_prop prog
  by_cases h : Pre base exponent
  · have hp : pre base exponent = true := (pre_iff_Pre base exponent).mpr h
    simp [hp, h]
  · have hp : pre base exponent = false := by
      cases hbool : pre base exponent
      · rfl
      · exfalso; exact h ((pre_iff_Pre base exponent).mp hbool)
    simp [hp, h]

/-- Property 19: `Nat` layer equivalence to `base ^ exponent`. -/
def nat_pow_eq_prop (base exponent : Nat) : Prop :=
  myPowerNat base exponent = base ^ exponent

instance (base exponent : Nat) : Decidable (nat_pow_eq_prop base exponent) := by
  unfold nat_pow_eq_prop; infer_instance

theorem nat_pow_eq_thm (base exponent : Nat) : nat_pow_eq_prop base exponent :=
  myPowerNat_eq_pow base exponent

/-- Property 20: `Nat` layer edge case `myPowerNat base 0 = 1`. -/
def nat_exp_zero_prop (base : Nat) : Prop :=
  myPowerNat base 0 = 1

instance (base : Nat) : Decidable (nat_exp_zero_prop base) := by
  unfold nat_exp_zero_prop; infer_instance

theorem nat_exp_zero_thm (base : Nat) : nat_exp_zero_prop base := rfl

/-- Property 21: `Nat` layer edge case `myPowerNat 0 exponent = 0` for `0 < exponent`. -/
def nat_zero_base_prop (exponent : Nat) : Prop :=
  0 < exponent → myPowerNat 0 exponent = 0

instance (exponent : Nat) : Decidable (nat_zero_base_prop exponent) := by
  unfold nat_zero_base_prop; infer_instance

theorem nat_zero_base_thm (exponent : Nat) : nat_zero_base_prop exponent := by
  intro he
  rw [myPowerNat_eq_pow]
  exact zero_pow (Nat.ne_of_gt he)

/-- Property 22: Bridge between `Int` implementation `myPower` and `Nat` implementation `myPowerNat`. -/
def nat_bridge_prop (base exponent : Nat) : Prop :=
  myPower (base : Int) (exponent : Int) = (myPowerNat base exponent : Int)

instance (base exponent : Nat) : Decidable (nat_bridge_prop base exponent) := by
  unfold nat_bridge_prop; infer_instance

theorem nat_bridge_thm (base exponent : Nat) : nat_bridge_prop base exponent := by
  unfold nat_bridge_prop
  rw [myPower_eq_pow, myPowerNat_eq_pow, Int.toNat_natCast, Int.natCast_pow]

/-! ## 8. Post-condition as Conjunction of Properties -/

/-- Complete post-condition on `Int` inputs combining all core and edge-case properties. -/
def Post_prop (base exponent : Int) : Prop :=
  pow_eq_prop base exponent ∧
  exp_zero_prop base exponent ∧
  zero_base_prop base exponent ∧
  zero_to_zero_prop base exponent ∧
  one_base_prop base exponent ∧
  exp_one_prop base exponent ∧
  nonneg_prop base exponent ∧
  pos_prop base exponent ∧
  ge_one_prop base exponent ∧
  step_prop base exponent ∧
  prog_valid_prop base exponent

instance (base exponent : Int) : Decidable (Post_prop base exponent) := by
  unfold Post_prop; infer_instance

/-- Post-condition on `Nat` inputs. -/
def PostNat_prop (base exponent : Nat) : Prop :=
  nat_pow_eq_prop base exponent ∧
  nat_exp_zero_prop base ∧
  nat_zero_base_prop exponent ∧
  nat_bridge_prop base exponent

instance (base exponent : Nat) : Decidable (PostNat_prop base exponent) := by
  unfold PostNat_prop; infer_instance

/-! ## 9. Property-Based Tests (PBTs) -/

-- Randomized PBTs using Plausible
#eval Plausible.Testable.check (∀ b e : Nat, pow_eq_prop (b : Int) (e : Int))
#eval Plausible.Testable.check (∀ b : Nat, exp_zero_prop (b : Int) 0)
#eval Plausible.Testable.check (∀ e : Nat, zero_base_prop 0 ((e + 1 : Nat) : Int))
#eval Plausible.Testable.check (zero_to_zero_prop 0 0)
#eval Plausible.Testable.check (∀ e : Nat, one_base_prop 1 (e : Int))
#eval Plausible.Testable.check (∀ b : Nat, exp_one_prop (b : Int) 1)
#eval Plausible.Testable.check (∀ b e : Nat, nonneg_prop (b : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e : Nat, pos_prop ((b + 1 : Nat) : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e : Nat, ge_one_prop ((b + 1 : Nat) : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e : Nat, step_prop (b : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e1 e2 : Nat, add_exp_prop (b : Int) (e1 : Int) (e2 : Int))
#eval Plausible.Testable.check (∀ b1 b2 e : Nat, mul_base_prop (b1 : Int) (b2 : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e1 e2 : Nat, mul_exp_prop (b : Int) ((e1 % 5 : Nat) : Int) ((e2 % 5 : Nat) : Int))
#eval Plausible.Testable.check (∀ b1 d e : Nat, mono_base_prop (b1 : Int) ((b1 + d : Nat) : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e1 d : Nat, mono_exp_prop ((b + 1 : Nat) : Int) (e1 : Int) ((e1 + d : Nat) : Int))
#eval Plausible.Testable.check (∀ b e : Nat, prog_valid_prop (b : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e : Int, prog_invalid_prop b e)
#eval Plausible.Testable.check (∀ b e : Int, prog_isSome_iff_prop b e)
#eval Plausible.Testable.check (∀ b e : Nat, nat_pow_eq_prop b e)
#eval Plausible.Testable.check (∀ b : Nat, nat_exp_zero_prop b)
#eval Plausible.Testable.check (∀ e : Nat, nat_zero_base_prop e)
#eval Plausible.Testable.check (∀ b e : Nat, nat_bridge_prop b e)
#eval Plausible.Testable.check (∀ b e : Nat, Post_prop (b : Int) (e : Int))
#eval Plausible.Testable.check (∀ b e : Nat, PostNat_prop b e)

-- Bounded exhaustive PBTs over concrete grids using `native_decide`
example : (List.range 10).all (fun b =>
    (List.range 8).all (fun e => decide (pow_eq_prop b e))) = true := by native_decide

example : (List.range 20).all (fun b =>
    decide (exp_zero_prop b 0)) = true := by native_decide

example : (List.range 15).all (fun e =>
    decide (zero_base_prop 0 (e + 1))) = true := by native_decide

example : decide (zero_to_zero_prop 0 0) = true := by native_decide

example : (List.range 15).all (fun e =>
    decide (one_base_prop 1 e)) = true := by native_decide

example : (List.range 20).all (fun b =>
    decide (exp_one_prop b 1)) = true := by native_decide

example : (List.range 10).all (fun b =>
    (List.range 8).all (fun e => decide (nonneg_prop b e))) = true := by native_decide

example : (List.range 10).all (fun b =>
    (List.range 8).all (fun e => decide (pos_prop (b + 1) e))) = true := by native_decide

example : (List.range 10).all (fun b =>
    (List.range 8).all (fun e => decide (ge_one_prop (b + 1) e))) = true := by native_decide

example : (List.range 8).all (fun b =>
    (List.range 8).all (fun e => decide (step_prop b e))) = true := by native_decide

example : (List.range 6).all (fun b =>
    (List.range 5).all (fun e1 =>
      (List.range 5).all (fun e2 => decide (add_exp_prop b e1 e2)))) = true := by native_decide

example : (List.range 6).all (fun b1 =>
    (List.range 6).all (fun b2 =>
      (List.range 5).all (fun e => decide (mul_base_prop b1 b2 e)))) = true := by native_decide

example : (List.range 5).all (fun b =>
    (List.range 4).all (fun e1 =>
      (List.range 4).all (fun e2 => decide (mul_exp_prop b e1 e2)))) = true := by native_decide

example : (List.range 6).all (fun b1 =>
    (List.range 6).all (fun b2 =>
      (List.range 5).all (fun e => decide (mono_base_prop b1 (b1 + b2) e)))) = true := by native_decide

example : (List.range 6).all (fun b =>
    (List.range 5).all (fun e1 =>
      (List.range 5).all (fun e2 => decide (mono_exp_prop (b + 1) e1 (e1 + e2))))) = true := by native_decide

example : (List.range 8).all (fun b =>
    (List.range 8).all (fun e => decide (prog_valid_prop b e))) = true := by native_decide

example : (List.range 10).all (fun b =>
    (List.range 10).all (fun e =>
      let b' : Int := (b : Int) - 5
      let e' : Int := (e : Int) - 5
      decide (prog_invalid_prop b' e' ∧ prog_isSome_iff_prop b' e'))) = true := by native_decide

example : (List.range 8).all (fun b =>
    (List.range 8).all (fun e => decide (Post_prop b e ∧ PostNat_prop b e))) = true := by native_decide

/-! ## 10. Correctness Theorem: `Pre -> Post` -/

/-- Main correctness theorem: for any `base` and `exponent` satisfying `Pre`,
    all post-condition properties in `Post_prop` hold. -/
theorem correctness (base exponent : Int) (h : Pre base exponent) :
    Post_prop base exponent :=
  ⟨pow_eq_thm base exponent h,
   exp_zero_thm base exponent h,
   zero_base_thm base exponent h,
   zero_to_zero_thm base exponent h,
   one_base_thm base exponent h,
   exp_one_thm base exponent h,
   nonneg_thm base exponent h,
   pos_thm base exponent h,
   ge_one_thm base exponent h,
   step_thm base exponent h,
   prog_valid_thm base exponent h⟩

/-- Complete specification for `prog`: returns `some (base ^ exponent.toNat)` when `Pre` holds,
    and `none` when `Pre` is violated. -/
theorem prog_correctness (base exponent : Int) :
    (Pre base exponent → prog base exponent = some (base ^ exponent.toNat)) ∧
    (¬ Pre base exponent → prog base exponent = none) :=
  ⟨fun h => (prog_valid_thm base exponent h).2, prog_invalid_thm base exponent⟩

/-- Correctness theorem on `Nat` inputs. -/
theorem correctness_nat (base exponent : Nat) (_h : PreNat base exponent) :
    PostNat_prop base exponent :=
  ⟨nat_pow_eq_thm base exponent,
   nat_exp_zero_thm base,
   nat_zero_base_thm exponent,
   nat_bridge_thm base exponent⟩

/-! ## 11. Imperative Implementation using `Id.run do` with Mutable State -/

/-- Imperative implementation on `Int` mirroring the Python `for _ in range(exponent)` loop. -/
def myPowerImp (base exponent : Int) : Int := Id.run do
  if exponent == 0 then
    return 1
  let mut result : Int := 1
  for _ in List.range exponent.toNat do
    result := result * base
  return result

/-- Imperative checked implementation matching Python's `prog(base, exponent)`. -/
def progImp (base exponent : Int) : Option Int := Id.run do
  if !(pre base exponent) then
    return none
  if exponent == 0 then
    return some 1
  let mut result : Int := 1
  for _ in List.range exponent.toNat do
    result := result * base
  return some result

/-- Imperative implementation on `Nat`. -/
def myPowerNatImp (base exponent : Nat) : Nat := Id.run do
  if exponent == 0 then
    return 1
  let mut result : Nat := 1
  for _ in List.range exponent do
    result := result * base
  return result

/-! ## 12. Imperative Tests -/

#eval myPowerImp 2 3
#eval myPowerImp 0 0
#eval progImp 2 3
#eval progImp 0 0
#eval progImp (-1) 2
#eval progImp 2 (-1)
#eval myPowerNatImp 2 3
#eval myPowerNatImp 0 0

example : myPowerImp 2 3 = 8 := by native_decide
example : myPowerImp 0 0 = 1 := by native_decide
example : myPowerImp 5 0 = 1 := by native_decide
example : myPowerImp 0 4 = 0 := by native_decide
example : progImp 2 3 = some 8 := by native_decide
example : progImp 0 0 = some 1 := by native_decide
example : progImp (-1) 2 = none := by native_decide
example : progImp 2 (-1) = none := by native_decide
example : myPowerNatImp 2 3 = 8 := by native_decide
example : myPowerNatImp 0 0 = 1 := by native_decide

-- PBT checking functional = imperative across inputs
#eval Plausible.Testable.check (∀ b e : Int, myPower b e = myPowerImp b e)
#eval Plausible.Testable.check (∀ b e : Int, prog b e = progImp b e)
#eval Plausible.Testable.check (∀ b e : Nat, myPowerNat b e = myPowerNatImp b e)

/-! ## 13. Equivalence Theorem: Functional = Imperative -/

/-- Equivalence between the functional `myPower` and imperative `myPowerImp` implementations. -/
theorem myPower_equiv (base exponent : Int) :
    myPower base exponent = myPowerImp base exponent := by
  unfold myPower myPowerImp
  split_ifs with h
  · rfl
  · simp

/-- Equivalence between the functional `prog` and imperative `progImp` implementations. -/
theorem prog_equiv (base exponent : Int) :
    prog base exponent = progImp base exponent := by
  unfold prog progImp myPower
  cases hpre : pre base exponent
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h0
    · rfl
    · simp

/-- Helper lemma for `Nat` list fold multiplication. -/
theorem foldl_mul_const_nat {α : Type*} (base : Nat) (l : List α) (init : Nat) :
    l.foldl (fun acc _ => acc * base) init = init * base ^ l.length := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons, ih, pow_succ', ← mul_assoc]

/-- Equivalence between the recursive `myPowerNat` and imperative `myPowerNatImp` implementations. -/
theorem myPowerNat_equiv (base exponent : Nat) :
    myPowerNat base exponent = myPowerNatImp base exponent := by
  rw [myPowerNat_eq_pow]
  unfold myPowerNatImp
  split_ifs with h0
  · have he : exponent = 0 := by simpa using h0
    subst he
    rfl
  · simp [foldl_mul_const_nat]

/-- Corollary: the imperative implementation satisfies the mathematical specification. -/
theorem myPowerImp_eq_pow (base exponent : Int) :
    myPowerImp base exponent = base ^ exponent.toNat := by
  rw [← myPower_equiv, myPower_eq_pow]

end «19_MyPower»

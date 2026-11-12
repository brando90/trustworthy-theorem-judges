import Mathlib

/-!
# Natural-number exponentiation (`power`)

Lean 4 formalization of the Python program `19_MyPower`.

The Python function `prog(base, exponent)` returns `base ^ exponent` for natural
numbers, computed with a `for` loop that multiplies an accumulator `exponent`
times.  It raises `ValueError` when the precondition `pre(base, exponent)`
(both arguments are non-negative integers) is violated.

* `power` is the functional (recursive) implementation.
* `Pre` is the precondition, stated on `Int` inputs, mirroring `pre`.
* `Post_prop` is the postcondition: the conjunction of the individual
  property propositions (`power(n,0) = 1`, `power(0,n) = 0` for `n > 0`,
  `power(0,0) = 1`, and agreement with `HPow`).
* `powerImp` is the imperative version using `Id.run do` with a mutable
  accumulator, and `power_eq_powerImp` proves the two agree.
-/

namespace MyPower

/-! ## Functional implementation -/

/-- `power base exponent = base ^ exponent`, defined by recursion on the
exponent, exactly as the Python loop accumulates the product. -/
def power (base : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => base * power base n

/-! ## Unit tests (mirroring the Python `check`) -/

example : power 2 3 = 8 := by native_decide
example : power 0 0 = 1 := by native_decide
example : power 0 5 = 0 := by native_decide
example : power 5 1 = 5 := by native_decide
example : power 3 4 = 81 := by native_decide

#eval power 2 3   -- 8
#eval power 0 0   -- 1

/-! ## Pre-condition -/

/-- The Python `pre`: both inputs must be non-negative integers. -/
def Pre (base exponent : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ exponent

example : Pre 2 3 := by unfold Pre; norm_num
example : ¬ Pre (-1) 2 := by unfold Pre; norm_num
example : ¬ Pre 2 (-1) := by unfold Pre; norm_num

/-! ## Properties -/

/-- Anything raised to the power `0` is `1`. -/
def power_zero_exp_prop (base : Nat) : Prop :=
  power base 0 = 1

theorem power_zero_exp_thm (base : Nat) : power_zero_exp_prop base := by
  unfold power_zero_exp_prop power
  rfl

/-- `0` raised to a positive power is `0`. -/
def power_zero_base_prop (n : Nat) : Prop :=
  0 < n → power 0 n = 0

theorem power_zero_base_thm (n : Nat) : power_zero_base_prop n := by
  unfold power_zero_base_prop
  intro hn
  cases n with
  | zero => exact absurd hn (by simp)
  | succ m => simp [power]

/-- `0 ^ 0 = 1` by convention. -/
def power_zero_zero_prop : Prop :=
  power 0 0 = 1

theorem power_zero_zero_thm : power_zero_zero_prop := by
  unfold power_zero_zero_prop power
  rfl

/-- The recursive step of the accumulating loop. -/
def power_succ_prop (base n : Nat) : Prop :=
  power base (n + 1) = base * power base n

theorem power_succ_thm (base n : Nat) : power_succ_prop base n := by
  unfold power_succ_prop
  rfl

/-- `power` agrees with Lean's `Monoid.npow` (`HPow.hPow`). -/
def power_eq_pow_prop (base n : Nat) : Prop :=
  power base n = base ^ n

theorem power_eq (base n : Nat) : power base n = base ^ n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      show base * power base m = base ^ (m + 1)
      rw [ih, pow_succ, Nat.mul_comm]

theorem power_eq_pow_thm (base n : Nat) : power_eq_pow_prop base n :=
  power_eq base n

/-- The exponent law `b ^ (m + n) = b ^ m * b ^ n`. -/
def power_add_prop (base m n : Nat) : Prop :=
  power base (m + n) = power base m * power base n

theorem power_add_thm (base m n : Nat) : power_add_prop base m n := by
  unfold power_add_prop
  rw [power_eq, power_eq, power_eq, pow_add]

/-- A positive base yields a positive result. -/
def power_pos_prop (base n : Nat) : Prop :=
  0 < base → 0 < power base n

theorem power_pos_thm (base n : Nat) : power_pos_prop base n := by
  unfold power_pos_prop
  intro hb
  rw [power_eq base n]
  exact Nat.pow_pos hb

/-! ## Post-condition and correctness -/

/-- The postcondition: everything the Python function guarantees about its
result, for inputs satisfying the precondition. -/
def Post_prop (base exponent : Nat) : Prop :=
  power base exponent = base ^ exponent ∧
  power base 0 = 1 ∧
  (0 < exponent → power 0 exponent = 0) ∧
  power 0 0 = 1 ∧
  (0 < base → 0 < power base exponent)

/-- Correctness: whenever the precondition holds for the integer inputs, the
result of running `power` on the corresponding naturals satisfies the
postcondition. -/
theorem correctness_thm (base exponent : Int) (h : Pre base exponent) :
    Post_prop base.toNat exponent.toNat := by
  obtain ⟨_, _⟩ := h
  refine ⟨power_eq_pow_thm _ _, power_zero_exp_thm _, ?_, power_zero_zero_thm,
    power_pos_thm _ _⟩
  exact power_zero_base_thm _

/-! ## Imperative implementation -/

/-- Imperative version: literal transcription of the Python loop with a
mutable accumulator. -/
def powerImp (base exponent : Nat) : Nat := Id.run do
  if exponent = 0 then
    return 1
  let mut result := 1
  for _ in List.range exponent do
    result := result * base
  return result

/-! ## Imperative tests -/

example : powerImp 2 3 = 8 := by native_decide
example : powerImp 0 0 = 1 := by native_decide
example : powerImp 0 5 = 0 := by native_decide
example : powerImp 3 4 = 81 := by native_decide

#eval powerImp 2 3   -- 8
#eval powerImp 0 0   -- 1

/-- The loop body multiplies the accumulator once per list element. -/
theorem forIn_mul (base : Nat) :
    ∀ (l : List Nat) (acc : Nat),
      (forIn (m := Id) l acc (fun _ r => ForInStep.yield (r * base)))
        = acc * base ^ l.length := by
  intro l
  induction l with
  | nil =>
      intro acc
      simp only [List.forIn_nil, List.length_nil, pow_zero, Nat.mul_one]
      rfl
  | cons a t ih =>
      intro acc
      rw [List.forIn_cons]
      show (forIn (m := Id) t (acc * base) fun _ r => ForInStep.yield (r * base)) = _
      rw [ih, List.length_cons, pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm]

/-! ## Equivalence of the two implementations -/

/-- The functional and imperative implementations agree. -/
def equiv_prop (base exponent : Nat) : Prop :=
  power base exponent = powerImp base exponent

theorem equiv_thm (base exponent : Nat) : equiv_prop base exponent := by
  unfold equiv_prop powerImp
  rw [power_eq]
  by_cases h : exponent = 0
  · subst h; rfl
  · simp only [Id.run, h, if_false]
    show base ^ exponent
      = (forIn (m := Id) (List.range exponent) 1 fun _ r => ForInStep.yield (r * base))
    rw [forIn_mul]
    simp

end MyPower

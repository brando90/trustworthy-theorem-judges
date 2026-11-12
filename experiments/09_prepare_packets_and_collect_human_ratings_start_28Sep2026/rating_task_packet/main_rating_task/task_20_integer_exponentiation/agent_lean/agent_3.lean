import Mathlib
import Plausible

/-!
# VeriBench – 19_MyPower

Translation of a Python natural-number power function.

Python `prog(base, exponent)` returns `base` raised to `exponent` for
non-negative integers, with the conventions

* `power(n, 0) = 1` for every natural `n` (including `n = 0`),
* `power(0, n) = 0` for every `n > 0`,
* `power(0, 0) = 1`.

If either input is negative, Python raises `ValueError`. That partiality is
modeled by `Except String Nat`: `.error` is the `ValueError` (carrying the
Python f-string message) and `.ok` is the successful natural-number result.
The `isinstance(..., int)` conjunct of `pre` is represented by the Lean type
`Int`; `Pre` records the remaining non-negativity obligation.

The functional core is the same accumulator iteration as the Python loop
(`result = 1; for _ in range(exponent): result *= base`). The imperative
implementation uses `Id.run do` and mutable state. Both are proved equal to
`Nat.pow` (and therefore to each other).
-/

namespace «19_MyPower»

deriving instance DecidableEq, BEq, Repr for Except


/-! ## Implementation -/

/-- Error message matching Python
`f"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"`. -/
def errorMsg (base exponent : Int) : String :=
  s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

/-- Python `pre`: both arguments are non-negative integers.
`isinstance` is the `Int` type; this Bool checks `≥ 0`. -/
def pre (base exponent : Int) : Bool :=
  decide (base ≥ 0) && decide (exponent ≥ 0)

/-- Functional core: start from `1` and multiply by `base`, `exponent` times.
This is the tail-recursive form of the Python accumulator loop.
In particular `powerNat _ 0 = 1`, so `powerNat 0 0 = 1`. -/
def powerNat (base exponent : Nat) : Nat :=
  Nat.rec 1 (fun _ acc => acc * base) exponent

/-- Recursion equations of `powerNat`, matching the Python control flow. -/
theorem powerNat_zero_eq (base : Nat) : powerNat base 0 = 1 := rfl

theorem powerNat_succ_eq (base e : Nat) :
    powerNat base (e + 1) = powerNat base e * base := rfl

/-- Python `prog`: return `base^exponent` or raise `ValueError`. -/
def prog (base exponent : Int) : Except String Nat :=
  if pre base exponent then
    .ok (powerNat base.toNat exponent.toNat)
  else
    .error (errorMsg base exponent)


/-! ## Unit tests -/

-- Basic unit test: `prog(2, 3) == 8`.
example : prog 2 3 = .ok 8 := by native_decide
#eval prog 2 3 -- expected: Except.ok 8

-- Edge unit test: `prog(0, 0) == 1`.
example : prog 0 0 = .ok 1 := by native_decide
#eval prog 0 0 -- expected: Except.ok 1

example : prog 0 5 = .ok 0 := by native_decide
#eval prog 0 5 -- expected: Except.ok 0

example : prog 5 0 = .ok 1 := by native_decide
#eval prog 5 0 -- expected: Except.ok 1

example : prog 7 1 = .ok 7 := by native_decide
#eval prog 7 1 -- expected: Except.ok 7

example : prog 3 4 = .ok 81 := by native_decide
#eval prog 3 4 -- expected: Except.ok 81

example : prog 10 3 = .ok 1000 := by native_decide
#eval prog 10 3 -- expected: Except.ok 1000

example : prog 1 8 = .ok 1 := by native_decide
#eval prog 1 8 -- expected: Except.ok 1

example : prog 2 10 = .ok 1024 := by native_decide
#eval prog 2 10 -- expected: Except.ok 1024

-- Negative tests: pre-violations must be `ValueError` (modeled by `.error`).
example : prog (-1) 2 = .error (errorMsg (-1) 2) := by native_decide
#eval prog (-1) 2 -- expected: Except.error (ValueError message)

example : prog 2 (-1) = .error (errorMsg 2 (-1)) := by native_decide
#eval prog 2 (-1) -- expected: Except.error (ValueError message)

example : prog (-3) (-4) = .error (errorMsg (-3) (-4)) := by native_decide
#eval prog (-3) (-4) -- expected: Except.error (ValueError message)

/-- A negative base is rejected even when the exponent is zero. -/
example : prog (-5) 0 = .error (errorMsg (-5) 0) := by native_decide
#eval prog (-5) 0 -- expected: Except.error (ValueError message)

/-- Mirror of the Python `check` harness. -/
def check : Bool :=
  (prog 2 3 == .ok 8) &&
  (prog 0 0 == .ok 1) &&
  (prog (-1) 2 == .error (errorMsg (-1) 2)) &&
  (prog 2 (-1) == .error (errorMsg 2 (-1)))

example : check = true := by native_decide
#eval check -- expected: true

/-! ## Pre-condition -/

/-- Python `pre` as a proposition: both inputs are natural numbers. -/
@[reducible] def Pre (base exponent : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ exponent

/-! ## Property propositions and theorems -/

/-- `powerNat` agrees with mathematical exponentiation. -/
@[reducible] def powerNat_eq_pow_prop (base exponent : Nat) : Prop :=
  powerNat base exponent = base ^ exponent

@[simp] theorem powerNat_eq_pow (base exponent : Nat) :
    powerNat base exponent = base ^ exponent := by
  induction exponent with
  | zero =>
    exact powerNat_zero_eq base
  | succ e ih =>
    rw [powerNat_succ_eq, ih, Nat.pow_succ]

theorem powerNat_eq_pow_thm (base exponent : Nat) :
    powerNat_eq_pow_prop base exponent :=
  powerNat_eq_pow base exponent

/-- `power(n, 0) = 1` for every natural `n`. -/
@[reducible] def powerNat_zero_prop (base : Nat) : Prop :=
  powerNat base 0 = 1

theorem powerNat_zero_thm (base : Nat) : powerNat_zero_prop base := by
  simp [powerNat_zero_prop]

/-- `power(0, n) = 0` for `n > 0`. -/
@[reducible] def powerNat_zero_base_prop (exponent : Nat) : Prop :=
  0 < exponent → powerNat 0 exponent = 0

theorem powerNat_zero_base_thm (exponent : Nat) : powerNat_zero_base_prop exponent := by
  intro h
  rw [powerNat_eq_pow]
  exact Nat.zero_pow h

/-- `power(0, 0) = 1` by convention. -/
@[reducible] def powerNat_zero_zero_prop : Prop :=
  powerNat 0 0 = 1

theorem powerNat_zero_zero_thm : powerNat_zero_zero_prop := by
  simp [powerNat_zero_zero_prop]

/-- One more multiplication advances the exponent by one (`result *= base`). -/
@[reducible] def powerNat_succ_prop (base exponent : Nat) : Prop :=
  powerNat base (exponent + 1) = powerNat base exponent * base

theorem powerNat_succ_thm (base exponent : Nat) : powerNat_succ_prop base exponent :=
  powerNat_succ_eq base exponent

/-- `power(n, 1) = n`. -/
@[reducible] def powerNat_one_exp_prop (base : Nat) : Prop :=
  powerNat base 1 = base

theorem powerNat_one_exp_thm (base : Nat) : powerNat_one_exp_prop base := by
  unfold powerNat_one_exp_prop
  rw [powerNat_eq_pow]
  exact Nat.pow_one base

/-- `power(1, n) = 1`. -/
@[reducible] def powerNat_one_base_prop (exponent : Nat) : Prop :=
  powerNat 1 exponent = 1

theorem powerNat_one_base_thm (exponent : Nat) : powerNat_one_base_prop exponent := by
  unfold powerNat_one_base_prop
  rw [powerNat_eq_pow]
  exact Nat.one_pow exponent

/-- Exponent addition: `b^(m+n) = b^m * b^n`. -/
@[reducible] def powerNat_add_prop (base m n : Nat) : Prop :=
  powerNat base (m + n) = powerNat base m * powerNat base n

theorem powerNat_add_thm (base m n : Nat) : powerNat_add_prop base m n := by
  unfold powerNat_add_prop
  rw [powerNat_eq_pow, powerNat_eq_pow, powerNat_eq_pow]
  exact Nat.pow_add base m n

/-- Base multiplication: `(a*b)^n = a^n * b^n`. -/
@[reducible] def powerNat_mul_base_prop (a b n : Nat) : Prop :=
  powerNat (a * b) n = powerNat a n * powerNat b n

theorem powerNat_mul_base_thm (a b n : Nat) : powerNat_mul_base_prop a b n := by
  unfold powerNat_mul_base_prop
  rw [powerNat_eq_pow, powerNat_eq_pow, powerNat_eq_pow]
  exact Nat.mul_pow a b n

/-- Exponent multiplication: `b^(m*n) = (b^m)^n`. -/
@[reducible] def powerNat_mul_exp_prop (base m n : Nat) : Prop :=
  powerNat base (m * n) = powerNat (powerNat base m) n

theorem powerNat_mul_exp_thm (base m n : Nat) : powerNat_mul_exp_prop base m n := by
  unfold powerNat_mul_exp_prop
  rw [powerNat_eq_pow, powerNat_eq_pow, powerNat_eq_pow]
  exact Nat.pow_mul base m n


/-- A positive base stays positive at every exponent. -/
@[reducible] def powerNat_pos_prop (base exponent : Nat) : Prop :=
  0 < base → 0 < powerNat base exponent

theorem powerNat_pos_thm (base exponent : Nat) : powerNat_pos_prop base exponent := by
  intro h
  rw [powerNat_eq_pow]
  exact Nat.pow_pos h

/-- Monotonicity in the base. -/
@[reducible] def powerNat_mono_base_prop (a b n : Nat) : Prop :=
  a ≤ b → powerNat a n ≤ powerNat b n

theorem powerNat_mono_base_thm (a b n : Nat) : powerNat_mono_base_prop a b n := by
  intro h
  rw [powerNat_eq_pow, powerNat_eq_pow]
  exact Nat.pow_le_pow_left h n

/-- Monotonicity in the exponent, for a positive base.
This fails for base `0` because `0^0 = 1 > 0 = 0^1`; that edge is specified
separately by `powerNat_zero_zero_thm` and `powerNat_zero_base_thm`. -/
@[reducible] def powerNat_mono_exp_prop (base m n : Nat) : Prop :=
  0 < base → m ≤ n → powerNat base m ≤ powerNat base n

theorem powerNat_mono_exp_thm (base m n : Nat) : powerNat_mono_exp_prop base m n := by
  intro hb hmn
  rw [powerNat_eq_pow, powerNat_eq_pow]
  exact Nat.pow_le_pow_right hb hmn

/-- The Python loop body (`foldl` of `acc * base`, `exponent` times from `1`)
equals mathematical exponentiation. -/
@[reducible] def iter_mul_prop (base exponent : Nat) : Prop :=
  (List.range exponent).foldl (fun acc (_ : Nat) => acc * base) 1 = base ^ exponent

theorem iter_mul_thm (base exponent : Nat) : iter_mul_prop base exponent := by
  induction exponent with
  | zero =>
    simp [iter_mul_prop]
  | succ e ih =>
    simp only [iter_mul_prop] at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    simp [Nat.pow_succ]

/-- The accumulator equations characterise `powerNat`. -/
@[reducible] def rec_spec_prop (f : Nat → Nat → Nat) : Prop :=
  (∀ b, f b 0 = 1) ∧ (∀ b e, f b (e + 1) = f b e * b)

@[reducible] def powerNat_rec_spec_prop : Prop :=
  rec_spec_prop powerNat

theorem powerNat_rec_spec_thm : powerNat_rec_spec_prop := by
  refine ⟨?_, ?_⟩
  · intro b; exact powerNat_zero_eq b
  · intro b e; exact powerNat_succ_eq b e

@[reducible] def powerNat_unique_prop (f : Nat → Nat → Nat) : Prop :=
  rec_spec_prop f → ∀ b e, f b e = powerNat b e

theorem powerNat_unique_thm (f : Nat → Nat → Nat) : powerNat_unique_prop f := by
  intro h b e
  induction e with
  | zero =>
    rw [h.1, powerNat_zero_eq]
  | succ e ih =>
    rw [h.2, ih, powerNat_succ_eq]

/-- Bool `pre` agrees with propositional `Pre`. -/
@[reducible] def pre_iff_prop (base exponent : Int) : Prop :=
  pre base exponent = true ↔ Pre base exponent

theorem pre_iff_thm (base exponent : Int) : pre_iff_prop base exponent := by
  unfold pre_iff_prop Pre pre
  simp [Bool.and_eq_true]

lemma toNat_pos_of_pos {a : Int} (h : 0 < a) : 0 < a.toNat := by
  have hc : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg (le_of_lt h)
  refine Nat.pos_of_ne_zero ?_
  intro hz
  have : a = 0 := by simpa [hz] using hc.symm
  exact ne_of_gt h this

/-- On admissible inputs, `prog` returns the core accumulator result. -/
@[reducible] def returns_powerNat_prop (base exponent : Int) : Prop :=
  Pre base exponent → prog base exponent = .ok (powerNat base.toNat exponent.toNat)

theorem returns_powerNat_thm (base exponent : Int) : returns_powerNat_prop base exponent := by
  intro h
  have hp : pre base exponent = true := (pre_iff_thm base exponent).2 h
  simp [prog, hp]

/-- On admissible inputs, `prog` returns `base.toNat ^ exponent.toNat`. -/
@[reducible] def returns_nat_pow_prop (base exponent : Int) : Prop :=
  Pre base exponent → prog base exponent = .ok (base.toNat ^ exponent.toNat)

theorem returns_nat_pow_thm (base exponent : Int) : returns_nat_pow_prop base exponent := by
  intro h
  rw [returns_powerNat_thm base exponent h, powerNat_eq_pow]

/-- The natural result, cast to `Int`, is the integer power `base ^ exponent`. -/
@[reducible] def returns_int_pow_prop (base exponent : Int) : Prop :=
  Pre base exponent →
    ((base.toNat ^ exponent.toNat : Nat) : Int) = base ^ exponent.toNat

theorem returns_int_pow_thm (base exponent : Int) : returns_int_pow_prop base exponent := by
  intro h
  rw [Nat.cast_pow, Int.toNat_of_nonneg h.1]

/-- `power(n, 0) = 1` at the Python `prog` layer (any non-negative base). -/
@[reducible] def pow_zero_prop (base : Int) : Prop :=
  0 ≤ base → prog base 0 = .ok 1

theorem pow_zero_thm (base : Int) : pow_zero_prop base := by
  intro hb
  have hp : pre base 0 = true := (pre_iff_thm base 0).2 ⟨hb, le_refl (0 : Int)⟩
  simp [prog, hp]

/-- `power(0, 0) = 1` at the Python `prog` layer. -/
@[reducible] def zero_pow_zero_prop : Prop :=
  prog 0 0 = .ok 1

theorem zero_pow_zero_thm : zero_pow_zero_prop := by
  simpa [zero_pow_zero_prop] using pow_zero_thm 0 (le_refl (0 : Int))

/-- `power(0, n) = 0` for `n > 0` at the Python `prog` layer. -/
@[reducible] def zero_pow_pos_prop (exponent : Int) : Prop :=
  0 < exponent → prog 0 exponent = .ok 0

theorem zero_pow_pos_thm (exponent : Int) : zero_pow_pos_prop exponent := by
  intro hpos
  have hp : pre 0 exponent = true :=
    (pre_iff_thm 0 exponent).2 ⟨le_refl (0 : Int), le_of_lt hpos⟩
  have hposN : 0 < exponent.toNat := toNat_pos_of_pos hpos
  simp [prog, hp, powerNat_eq_pow, Nat.zero_pow hposN, Int.toNat_zero]

/-- Inputs outside `ℕ` raise `ValueError` with the Python message. -/
@[reducible] def raises_value_error_prop (base exponent : Int) : Prop :=
  ¬ Pre base exponent → prog base exponent = .error (errorMsg base exponent)

theorem raises_value_error_thm (base exponent : Int) :
    raises_value_error_prop base exponent := by
  intro hNot
  have hne : pre base exponent ≠ true := by
    intro hp
    exact hNot ((pre_iff_thm base exponent).1 hp)
  have hpre : pre base exponent = false := eq_false_of_ne_true hne
  simp [prog, hpre]

/-- A negative base always raises, including the exponent-zero case. -/
@[reducible] def neg_base_errors_prop (base exponent : Int) : Prop :=
  base < 0 → prog base exponent = .error (errorMsg base exponent)

theorem neg_base_errors_thm (base exponent : Int) : neg_base_errors_prop base exponent := by
  intro hb
  apply raises_value_error_thm base exponent
  intro hPre
  exact absurd hb (not_lt_of_ge hPre.1)

/-- A negative exponent always raises. -/
@[reducible] def neg_exp_errors_prop (base exponent : Int) : Prop :=
  exponent < 0 → prog base exponent = .error (errorMsg base exponent)

theorem neg_exp_errors_thm (base exponent : Int) : neg_exp_errors_prop base exponent := by
  intro he
  apply raises_value_error_thm base exponent
  intro hPre
  exact absurd he (not_lt_of_ge hPre.2)

/-- Total specification: success computes the power, failure is `ValueError`. -/
@[reducible] def total_correctness_prop (base exponent : Int) : Prop :=
  (Pre base exponent → prog base exponent = .ok (base.toNat ^ exponent.toNat))
  ∧ (¬ Pre base exponent → prog base exponent = .error (errorMsg base exponent))

theorem total_correctness_thm (base exponent : Int) :
    total_correctness_prop base exponent := by
  refine ⟨returns_nat_pow_thm base exponent, raises_value_error_thm base exponent⟩


/-! ## Post-condition -/

/-- Successful-call post-condition: the result is the natural power, the
documented edge cases hold, the integer cast is the integer power, and the
Python accumulator loop computes that power. -/
@[reducible] def Post_prop (base exponent : Int) : Prop :=
  prog base exponent = .ok (powerNat base.toNat exponent.toNat)
  ∧ prog base exponent = .ok (base.toNat ^ exponent.toNat)
  ∧ (exponent = 0 → prog base exponent = .ok 1)
  ∧ (base = 0 ∧ exponent = 0 → prog base exponent = .ok 1)
  ∧ (base = 0 ∧ 0 < exponent → prog base exponent = .ok 0)
  ∧ ((base.toNat ^ exponent.toNat : Nat) : Int) = base ^ exponent.toNat
  ∧ (List.range exponent.toNat).foldl (fun acc (_ : Nat) => acc * base.toNat) 1
      = base.toNat ^ exponent.toNat

/-! ## Property-based tests -/

-- Randomized PBTs (Plausible). Each checks an executable form of a `_prop`.

#eval Plausible.Testable.check
  (∀ base exponent : Nat, powerNat base exponent = base ^ exponent)

#eval Plausible.Testable.check
  (∀ base : Nat, powerNat base 0 = 1)

#eval Plausible.Testable.check
  (∀ exponent : Nat, 0 < exponent → powerNat 0 exponent = 0)

#eval Plausible.Testable.check
  (∀ base exponent : Nat, powerNat base (exponent + 1) = powerNat base exponent * base)

#eval Plausible.Testable.check
  (∀ base : Nat, powerNat base 1 = base)

#eval Plausible.Testable.check
  (∀ exponent : Nat, powerNat 1 exponent = 1)

#eval Plausible.Testable.check
  (∀ base m n : Nat, powerNat base (m + n) = powerNat base m * powerNat base n)

#eval Plausible.Testable.check
  (∀ a b n : Nat, powerNat (a * b) n = powerNat a n * powerNat b n)

#eval Plausible.Testable.check
  (∀ base m n : Nat, powerNat base (m * n) = powerNat (powerNat base m) n)

#eval Plausible.Testable.check
  (∀ base exponent : Nat, 0 < base → 0 < powerNat base exponent)

#eval Plausible.Testable.check
  (∀ a b n : Nat, a ≤ b → powerNat a n ≤ powerNat b n)

#eval Plausible.Testable.check
  (∀ base m n : Nat, 0 < base → m ≤ n → powerNat base m ≤ powerNat base n)

#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    (List.range exponent).foldl (fun acc (_ : Nat) => acc * base) 1 = base ^ exponent)

#eval Plausible.Testable.check
  (∀ b e : Int, pre b e = true ↔ 0 ≤ b ∧ 0 ≤ e)

#eval Plausible.Testable.check
  (∀ base exponent : Int, base < 0 → prog base exponent = .error (errorMsg base exponent))

#eval Plausible.Testable.check
  (∀ base exponent : Int,
    exponent < 0 → prog base exponent = .error (errorMsg base exponent))

-- Bounded exhaustive PBTs.

example : (List.range 30).all (fun b => powerNat b 0 == 1) = true := by native_decide

example : (List.range 30).all (fun e => decide (0 < e → powerNat 0 e = 0)) = true := by
  native_decide

example : decide powerNat_zero_zero_prop = true := by native_decide

example : (List.range 15).all (fun b =>
    (List.range 12).all (fun e =>
      powerNat b (e + 1) == powerNat b e * b)) = true := by native_decide

example : (List.range 30).all (fun b => powerNat b 1 == b) = true := by native_decide

example : (List.range 30).all (fun e => powerNat 1 e == 1) = true := by native_decide

example : (List.range 10).all (fun b =>
    (List.range 10).all (fun m =>
      (List.range 10).all (fun n =>
        powerNat b (m + n) == powerNat b m * powerNat b n))) = true := by native_decide

example : (List.range 8).all (fun a =>
    (List.range 8).all (fun b =>
      (List.range 8).all (fun n =>
        powerNat (a * b) n == powerNat a n * powerNat b n))) = true := by native_decide

example : (List.range 8).all (fun b =>
    (List.range 8).all (fun m =>
      (List.range 6).all (fun n =>
        powerNat b (m * n) == powerNat (powerNat b m) n))) = true := by native_decide

example : (List.range 15).all (fun b =>
    (List.range 10).all (fun e =>
      decide (0 < b → 0 < powerNat b e))) = true := by native_decide

example : (List.range 10).all (fun a =>
    (List.range 10).all (fun b =>
      (List.range 6).all (fun n =>
        decide (a ≤ b → powerNat a n ≤ powerNat b n)))) = true := by native_decide

example : (List.range 8).all (fun b =>
    (List.range 8).all (fun m =>
      (List.range 8).all (fun n =>
        decide (0 < b → m ≤ n → powerNat b m ≤ powerNat b n)))) = true := by native_decide

example : (List.range 12).all (fun b =>
    (List.range 12).all (fun e =>
      (List.range e).foldl (fun acc _ => acc * b) 1 == b ^ e)) = true := by native_decide

example : (List.range 20).all (fun b =>
    (List.range 20).all (fun e =>
      powerNat b e == b ^ e)) = true := by native_decide

/-- Executable form of `powerNat_rec_spec_prop`. -/
example : (List.range 20).all (fun b => powerNat b 0 == 1) &&
    (List.range 12).all (fun b =>
      (List.range 12).all (fun e => powerNat b (e + 1) == powerNat b e * b)) = true := by
  native_decide

-- PBT: not executable (powerNat_unique_prop quantifies over all functions
-- `Nat → Nat → Nat`; function equality is not decidable and there is no
-- sampler for arbitrary functions). The theorem is proved above.

/-- Small integers for bounded tests of the partial `Int` interface. -/
def pbtInts : List Int := (List.range 15).map fun n => (n : Int) - 7

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (pre b e = true ↔ 0 ≤ b ∧ 0 ≤ e))) = true := by native_decide

example : pbtInts.all (fun b =>
    decide (0 ≤ b → prog b 0 = .ok 1)) = true := by native_decide

example : decide zero_pow_zero_prop = true := by native_decide

example : pbtInts.all (fun e =>
    decide (0 < e → prog 0 e = .ok 0)) = true := by native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (¬ (0 ≤ b ∧ 0 ≤ e) → prog b e = .error (errorMsg b e)))) = true := by
  native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (0 ≤ b → 0 ≤ e → prog b e = .ok (b.toNat ^ e.toNat)))) = true := by
  native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (0 ≤ b → 0 ≤ e → prog b e = .ok (powerNat b.toNat e.toNat)))) = true := by
  native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (0 ≤ b → 0 ≤ e →
        ((b.toNat ^ e.toNat : Nat) : Int) = b ^ e.toNat))) = true := by native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (b < 0 → prog b e = .error (errorMsg b e)))) = true := by native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (e < 0 → prog b e = .error (errorMsg b e)))) = true := by native_decide

/-- Executable Boolean form of `Post_prop` on admissible inputs. -/
def postBool (base exponent : Int) : Bool :=
  decide (prog base exponent = .ok (powerNat base.toNat exponent.toNat))
  && decide (prog base exponent = .ok (base.toNat ^ exponent.toNat))
  && decide (exponent = 0 → prog base exponent = .ok 1)
  && decide (base = 0 ∧ exponent = 0 → prog base exponent = .ok 1)
  && decide (base = 0 ∧ 0 < exponent → prog base exponent = .ok 0)
  && decide (((base.toNat ^ exponent.toNat : Nat) : Int) = base ^ exponent.toNat)
  && decide ((List.range exponent.toNat).foldl (fun acc (_ : Nat) => acc * base.toNat) 1
        = base.toNat ^ exponent.toNat)

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      !(pre b e) || postBool b e)) = true := by native_decide

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      decide (total_correctness_prop b e))) = true := by native_decide

-- Success-path Int PBT is the bounded `pbtInts` / `postBool` check above.
-- An unrestricted Plausible sample can build enormous powers.


/-! ## Correctness theorem -/

theorem correctness_thm (base exponent : Int) (h : Pre base exponent) :
    Post_prop base exponent := by
  unfold Post_prop
  have hprogNat : prog base exponent = .ok (powerNat base.toNat exponent.toNat) :=
    returns_powerNat_thm base exponent h
  have hprog : prog base exponent = .ok (base.toNat ^ exponent.toNat) :=
    returns_nat_pow_thm base exponent h
  have hcast : ((base.toNat ^ exponent.toNat : Nat) : Int) = base ^ exponent.toNat :=
    returns_int_pow_thm base exponent h
  have hfold :
      (List.range exponent.toNat).foldl (fun acc (_ : Nat) => acc * base.toNat) 1
        = base.toNat ^ exponent.toNat :=
    iter_mul_thm base.toNat exponent.toNat
  refine ⟨hprogNat, hprog, ?_, ?_, ?_, hcast, hfold⟩
  · intro hz
    rw [hprog, hz]
    simp [Int.toNat_zero]
  · intro ⟨hb, he⟩
    rw [hprog, hb, he]
    simp [Int.toNat_zero]
  · intro ⟨hb, he⟩
    rw [hprog, hb]
    have hpos : 0 < exponent.toNat := toNat_pos_of_pos he
    simp [Nat.zero_pow hpos, Int.toNat_zero]

/-! ## Imperative implementation -/

/-- Imperative core: the Python loop, using mutable state inside `Id.run`. -/
def powerNatImp (base exponent : Nat) : Nat :=
  Id.run do
    if exponent == 0 then
      return 1
    let mut result : Nat := 1
    for _ in List.range exponent do
      result := result * base
    return result

/-- Imperative Python `prog`: reject non-naturals, otherwise run the loop. -/
def progImp (base exponent : Int) : Except String Nat :=
  Id.run do
    if !(pre base exponent) then
      return .error (errorMsg base exponent)
    let b := base.toNat
    let e := exponent.toNat
    if e == 0 then
      return .ok 1
    let mut result : Nat := 1
    for _ in List.range e do
      result := result * b
    return .ok result

/-! ## Imperative tests -/

example : powerNatImp 2 3 = 8 := by native_decide
#eval powerNatImp 2 3 -- expected: 8

example : powerNatImp 0 0 = 1 := by native_decide
#eval powerNatImp 0 0 -- expected: 1

example : powerNatImp 0 5 = 0 := by native_decide
#eval powerNatImp 0 5 -- expected: 0

example : powerNatImp 7 1 = 7 := by native_decide
#eval powerNatImp 7 1 -- expected: 7

example : powerNatImp 3 4 = 81 := by native_decide
#eval powerNatImp 3 4 -- expected: 81

example : progImp 2 3 = .ok 8 := by native_decide
#eval progImp 2 3 -- expected: Except.ok 8

example : progImp 0 0 = .ok 1 := by native_decide
#eval progImp 0 0 -- expected: Except.ok 1

example : progImp 0 4 = .ok 0 := by native_decide
#eval progImp 0 4 -- expected: Except.ok 0

example : progImp 5 0 = .ok 1 := by native_decide
#eval progImp 5 0 -- expected: Except.ok 1

example : progImp (-1) 2 = .error (errorMsg (-1) 2) := by native_decide
#eval progImp (-1) 2 -- expected: Except.error (ValueError message)

example : progImp 2 (-1) = .error (errorMsg 2 (-1)) := by native_decide
#eval progImp 2 (-1) -- expected: Except.error (ValueError message)

example : pbtInts.all (fun b =>
    pbtInts.all (fun e => prog b e == progImp b e)) = true := by native_decide

/-! ## Equivalence theorem -/

theorem powerNatImp_eq_fold (base exponent : Nat) :
    powerNatImp base exponent =
      (List.range exponent).foldl (fun acc (_ : Nat) => acc * base) 1 := by
  simp [powerNatImp]
  by_cases h : exponent = 0
  · simp [h]
  · simp [h]

theorem powerNat_equivalence_thm (base exponent : Nat) :
    powerNat base exponent = powerNatImp base exponent := by
  rw [powerNat_eq_pow_thm, powerNatImp_eq_fold, iter_mul_thm]

/-- Functional `prog` and imperative `progImp` agree on every integer input,
including the `ValueError` branch. -/
theorem equivalence_thm (base exponent : Int) :
    prog base exponent = progImp base exponent := by
  simp [prog, progImp]
  by_cases h : pre base exponent = true
  · simp [h]
    by_cases he : exponent.toNat = 0
    · simp [he]
    · have hexp : 0 ≤ exponent := by
        simp [pre] at h
        exact h.2
      have hnot : ¬ exponent ≤ 0 := by
        intro hle
        have heq : exponent = 0 := le_antisymm hle hexp
        apply he
        simp [heq]
      simp [hnot]
      exact (iter_mul_thm base.toNat exponent.toNat).symm
  · simp [h]

end «19_MyPower»

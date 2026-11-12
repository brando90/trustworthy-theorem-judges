import Mathlib

/-!
# 19_MyPower -- natural-number exponentiation

Lean 4 translation of the Python program `19_MyPower.py`:

```python
def pre(base, exponent):
    return isinstance(base, int) and isinstance(exponent, int) and base >= 0 and exponent >= 0

def prog(base, exponent):
    if not pre(base, exponent):
        raise ValueError(f"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})")
    if exponent == 0:
        return 1
    result = 1
    for _ in range(exponent):
        result *= base
    return result
```

* `powerNat` is the arithmetic core: `base ^ exponent` on `Nat` computed by
  repeated multiplication (the Python loop).
* `prog : Int → Int → Except String Int` is the checked entry point.  The Python
  `ValueError` is modelled by `Except.error msg` (same message), a returned
  integer by `Except.ok`.
* `Pre` is the Python precondition (both inputs are natural numbers, i.e. `≥ 0`).
* Properties (`*_prop` / `*_thm`), the post-condition `Post_prop`, the
  correctness theorem `prog_correct : Pre → Post`, property-based tests, an
  imperative implementation `progImp` (`Id.run do`, early returns, a `for` loop
  with mutable state) and the equivalence theorem `prog_eq_progImp` follow.
-/

namespace «19_MyPower»

/-! ## Implementation -/

/-- `base ^ exponent` on natural numbers computed by repeated multiplication,
mirroring the Python loop `for _ in range(exponent): result *= base`
(starting from `result = 1`). -/
def powerNat (base : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => powerNat base n * base

/-- The message of the `ValueError` raised by the Python program. -/
def errMsg (base exponent : Int) : String :=
  s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

/-- Functional translation of the Python `prog`.
`Except.error` models the raised `ValueError`, `Except.ok` the returned integer. -/
def prog (base exponent : Int) : Except String Int :=
  if base < 0 ∨ exponent < 0 then
    .error (errMsg base exponent)
  else if exponent = 0 then
    .ok 1
  else
    .ok ((powerNat base.toNat exponent.toNat : Nat) : Int)

-- Decidable equality on results (used by the executable tests).
deriving instance DecidableEq for Except

/-! ## Unit tests (the Python `check`) -/

example : prog 2 3 = .ok 8 := by native_decide
example : prog 0 0 = .ok 1 := by native_decide
example : prog (-1) 2 = .error (errMsg (-1) 2) := by native_decide
example : prog 2 (-1) = .error (errMsg 2 (-1)) := by native_decide
example : (prog (-1) 2).toOption = none := by native_decide
example : (prog 2 (-1)).toOption = none := by native_decide
example : prog 3 4 = .ok 81 := by native_decide
example : prog 0 5 = .ok 0 := by native_decide
example : prog 7 1 = .ok 7 := by native_decide
example : prog 10 3 = .ok 1000 := by native_decide
example : powerNat 2 10 = 1024 := by native_decide

#eval prog 2 3        -- Except.ok 8
#eval prog 0 0        -- Except.ok 1
#eval prog (-1) 2     -- Except.error "Require base,exponent ∈ ℕ (got base=-1, exponent=2)"
#eval prog 2 (-1)     -- Except.error "Require base,exponent ∈ ℕ (got base=2, exponent=-1)"

/-! ## Pre-condition -/

/-- Python `pre`: both inputs are natural numbers (non-negative integers). -/
def Pre (base exponent : Int) : Prop := 0 ≤ base ∧ 0 ≤ exponent

instance (base exponent : Int) : Decidable (Pre base exponent) :=
  inferInstanceAs (Decidable (0 ≤ base ∧ 0 ≤ exponent))

/-! ## Properties -/

/-- The arithmetic core is exponentiation. -/
def powerNat_eq_pow_prop : Prop :=
  ∀ base exponent : Nat, powerNat base exponent = base ^ exponent

theorem powerNat_eq_pow (base exponent : Nat) : powerNat base exponent = base ^ exponent := by
  induction exponent with
  | zero => simp [powerNat]
  | succ n ih => simp only [powerNat, ih, pow_succ]

theorem powerNat_eq_pow_thm : powerNat_eq_pow_prop := powerNat_eq_pow

/-- On admissible inputs `prog` returns exactly `base ^ exponent`. -/
theorem prog_eq_of_pre (base exponent : Int) (h : Pre base exponent) :
    prog base exponent = .ok (base ^ exponent.toNat) := by
  obtain ⟨hb, he⟩ := h
  have hneg : ¬ (base < 0 ∨ exponent < 0) := by omega
  unfold prog
  rw [if_neg hneg]
  by_cases h0 : exponent = 0
  · subst h0
    simp
  · rw [if_neg h0, powerNat_eq_pow, Nat.cast_pow, Int.toNat_of_nonneg hb]

/-- On inadmissible inputs `prog` raises the `ValueError` (returns the error). -/
theorem prog_eq_of_not_pre (base exponent : Int) (h : ¬ Pre base exponent) :
    prog base exponent = .error (errMsg base exponent) := by
  have hneg : base < 0 ∨ exponent < 0 := by
    unfold Pre at h
    omega
  unfold prog
  rw [if_pos hneg]

/-- `power(n, 0) = 1` for every natural `n`. -/
def power_zero_prop : Prop := ∀ base : Int, 0 ≤ base → prog base 0 = .ok 1

theorem prog_exp_zero (base : Int) (hb : 0 ≤ base) : prog base 0 = .ok 1 := by
  rw [prog_eq_of_pre base 0 ⟨hb, le_refl 0⟩]
  simp

theorem power_zero_thm : power_zero_prop := prog_exp_zero

/-- `power(0, n) = 0` for `n > 0`. -/
def zero_power_prop : Prop := ∀ exponent : Int, 0 < exponent → prog 0 exponent = .ok 0

theorem prog_base_zero (exponent : Int) (he : 0 < exponent) : prog 0 exponent = .ok 0 := by
  rw [prog_eq_of_pre 0 exponent ⟨le_refl 0, le_of_lt he⟩]
  have hne : exponent.toNat ≠ 0 := by omega
  rw [zero_pow hne]

theorem zero_power_thm : zero_power_prop := prog_base_zero

/-- `power(0, 0) = 1` by convention. -/
def zero_zero_prop : Prop := prog 0 0 = .ok 1

theorem zero_zero_thm : zero_zero_prop := prog_exp_zero 0 (le_refl 0)

/-- `power(1, n) = 1` for every natural `n`. -/
def one_power_prop : Prop := ∀ exponent : Int, 0 ≤ exponent → prog 1 exponent = .ok 1

theorem prog_base_one (exponent : Int) (he : 0 ≤ exponent) : prog 1 exponent = .ok 1 := by
  rw [prog_eq_of_pre 1 exponent ⟨zero_le_one, he⟩, one_pow]

theorem one_power_thm : one_power_prop := prog_base_one

/-- `power(n, 1) = n` for every natural `n`. -/
def power_one_prop : Prop := ∀ base : Int, 0 ≤ base → prog base 1 = .ok base

theorem prog_exp_one (base : Int) (hb : 0 ≤ base) : prog base 1 = .ok base := by
  rw [prog_eq_of_pre base 1 ⟨hb, zero_le_one⟩]
  simp

theorem power_one_thm : power_one_prop := prog_exp_one

/-- On admissible inputs the result is exactly `base ^ exponent`. -/
def result_eq_pow_prop : Prop :=
  ∀ base exponent : Int, Pre base exponent → prog base exponent = .ok (base ^ exponent.toNat)

theorem result_eq_pow_thm : result_eq_pow_prop := prog_eq_of_pre

/-- Recurrence: one more loop iteration multiplies the result by `base`,
`power(b, e + 1) = power(b, e) * b`. -/
def power_succ_prop : Prop := ∀ base exponent : Int, Pre base exponent →
  prog base (exponent + 1) = (prog base exponent).map (· * base)

theorem prog_succ (base exponent : Int) (h : Pre base exponent) :
    prog base (exponent + 1) = (prog base exponent).map (· * base) := by
  have h' : Pre base (exponent + 1) := ⟨h.1, by have := h.2; omega⟩
  have ht : (exponent + 1).toNat = exponent.toNat + 1 := by have := h.2; omega
  simp only [prog_eq_of_pre base exponent h, prog_eq_of_pre base (exponent + 1) h', ht, pow_succ,
    Except.map]

theorem power_succ_thm : power_succ_prop := prog_succ

/-- On admissible inputs the result is a natural number (a non-negative integer). -/
def result_nonneg_prop : Prop := ∀ base exponent : Int, Pre base exponent →
  ∃ r : Int, prog base exponent = .ok r ∧ 0 ≤ r

theorem prog_nonneg (base exponent : Int) (h : Pre base exponent) :
    ∃ r : Int, prog base exponent = .ok r ∧ 0 ≤ r :=
  ⟨base ^ exponent.toNat, prog_eq_of_pre base exponent h, pow_nonneg h.1 _⟩

theorem result_nonneg_thm : result_nonneg_prop := prog_nonneg

/-- A positive base gives a positive result. -/
def result_pos_prop : Prop := ∀ base exponent : Int, 0 < base → 0 ≤ exponent →
  ∃ r : Int, prog base exponent = .ok r ∧ 0 < r

theorem prog_pos (base exponent : Int) (hb : 0 < base) (he : 0 ≤ exponent) :
    ∃ r : Int, prog base exponent = .ok r ∧ 0 < r :=
  ⟨base ^ exponent.toNat, prog_eq_of_pre base exponent ⟨le_of_lt hb, he⟩, pow_pos hb _⟩

theorem result_pos_thm : result_pos_prop := prog_pos

/-- Precondition violations raise `ValueError` with the Python message. -/
def pre_violation_prop : Prop := ∀ base exponent : Int, ¬ Pre base exponent →
  prog base exponent = .error (errMsg base exponent)

theorem pre_violation_thm : pre_violation_prop := prog_eq_of_not_pre

/-- `prog` succeeds (returns a value) exactly on the admissible inputs. -/
def ok_iff_pre_prop : Prop := ∀ base exponent : Int,
  (∃ r : Int, prog base exponent = .ok r) ↔ Pre base exponent

theorem prog_ok_iff_pre (base exponent : Int) :
    (∃ r : Int, prog base exponent = .ok r) ↔ Pre base exponent := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra h
    rw [prog_eq_of_not_pre base exponent h] at hr
    cases hr
  · intro h
    exact ⟨_, prog_eq_of_pre base exponent h⟩

theorem ok_iff_pre_thm : ok_iff_pre_prop := prog_ok_iff_pre

/-- Complete input/output specification of `prog`, including the exceptional case. -/
def total_spec_prop : Prop := ∀ base exponent : Int,
  prog base exponent =
    if Pre base exponent then .ok (base ^ exponent.toNat) else .error (errMsg base exponent)

theorem total_spec_thm : total_spec_prop := by
  intro base exponent
  split_ifs with h
  · exact prog_eq_of_pre base exponent h
  · exact prog_eq_of_not_pre base exponent h

/-! ## Post-condition -/

/-- Post-condition for admissible inputs: the result is `Except.ok (base ^ exponent)`,
satisfies the documented edge cases, and is a natural number. -/
def Post_prop (base exponent : Int) (result : Except String Int) : Prop :=
  result = .ok (base ^ exponent.toNat) ∧
  (exponent = 0 → result = .ok 1) ∧
  (base = 0 → 0 < exponent → result = .ok 0) ∧
  (base = 1 → result = .ok 1) ∧
  (exponent = 1 → result = .ok base) ∧
  (∃ r : Int, result = .ok r ∧ 0 ≤ r)

/-! ## Property-based tests -/

/-- Executable Boolean form of `Post_prop`. -/
def postCheck (base exponent : Int) (result : Except String Int) : Bool :=
  (result == .ok (base ^ exponent.toNat)) &&
  (exponent != 0 || result == .ok 1) &&
  (base != 0 || !(decide (0 < exponent)) || result == .ok 0) &&
  (base != 1 || result == .ok 1) &&
  (exponent != 1 || result == .ok base) &&
  (match result with
    | .ok r => decide (0 ≤ r)
    | .error _ => false)

-- Randomized PBTs: properties guarded by `Pre` are sampled over `Nat` inputs
-- (exactly the admissible domain, no filtering precondition); the `¬ Pre` side is
-- sampled over negative inputs built from `Nat`s.  Bounded exhaustive PBTs follow each.

-- powerNat_eq_pow_prop
#eval Plausible.Testable.check (∀ base exponent : Nat, powerNat base exponent = base ^ exponent)
example : (List.range 20).all (fun b => (List.range 20).all (fun e =>
    powerNat b e == b ^ e)) = true := by native_decide

-- power_zero_prop
#eval Plausible.Testable.check (∀ base : Nat, prog base 0 = .ok 1)
example : (List.range 50).all (fun b => prog b 0 == .ok 1) = true := by native_decide

-- zero_power_prop
#eval Plausible.Testable.check (∀ exponent : Nat, prog 0 (exponent + 1) = .ok 0)
example : (List.range 50).all (fun e => prog 0 (e + 1) == .ok 0) = true := by native_decide

-- zero_zero_prop
example : prog 0 0 == .ok 1 := by native_decide

-- one_power_prop
#eval Plausible.Testable.check (∀ exponent : Nat, prog 1 exponent = .ok 1)
example : (List.range 50).all (fun e => prog 1 e == .ok 1) = true := by native_decide

-- power_one_prop
#eval Plausible.Testable.check (∀ base : Nat, prog base 1 = .ok base)
example : (List.range 50).all (fun b => prog b 1 == .ok b) = true := by native_decide

-- result_eq_pow_prop
#eval Plausible.Testable.check (∀ base exponent : Nat,
  prog base exponent = .ok ((base : Int) ^ exponent))
example : (List.range 16).all (fun b => (List.range 16).all (fun e =>
    prog b e == .ok ((b : Int) ^ e))) = true := by native_decide

-- power_succ_prop
#eval Plausible.Testable.check (∀ base exponent : Nat,
  prog base (exponent + 1) = (prog base exponent).map (· * (base : Int)))
example : (List.range 16).all (fun b => (List.range 16).all (fun e =>
    prog b (e + 1) == (prog b e).map (· * (b : Int)))) = true := by native_decide

-- result_nonneg_prop
#eval Plausible.Testable.check (∀ base exponent : Nat,
  (prog base exponent).toOption.any (fun r => decide (0 ≤ r)) = true)
example : (List.range 16).all (fun b => (List.range 16).all (fun e =>
    (prog b e).toOption.any (fun r => decide (0 ≤ r)))) = true := by native_decide

-- result_pos_prop
#eval Plausible.Testable.check (∀ base exponent : Nat,
  (prog (base + 1) exponent).toOption.any (fun r => decide (0 < r)) = true)
example : (List.range 16).all (fun b => (List.range 16).all (fun e =>
    (prog (b + 1) e).toOption.any (fun r => decide (0 < r)))) = true := by native_decide

-- pre_violation_prop
#eval Plausible.Testable.check (∀ base exponent : Nat,
  prog (-(base : Int) - 1) exponent = .error (errMsg (-(base : Int) - 1) exponent) ∧
  prog base (-(exponent : Int) - 1) = .error (errMsg base (-(exponent : Int) - 1)) ∧
  prog (-(base : Int) - 1) (-(exponent : Int) - 1) =
    .error (errMsg (-(base : Int) - 1) (-(exponent : Int) - 1)))
example : (List.range 8).all (fun b => (List.range 8).all (fun e =>
    prog (-(b : Int) - 1) e == .error (errMsg (-(b : Int) - 1) e) &&
    prog b (-(e : Int) - 1) == .error (errMsg b (-(e : Int) - 1)) &&
    prog (-(b : Int) - 1) (-(e : Int) - 1) == .error (errMsg (-(b : Int) - 1) (-(e : Int) - 1))))
    = true := by native_decide

-- ok_iff_pre_prop
#eval Plausible.Testable.check (∀ base exponent : Int,
  (prog base exponent).toOption.isSome = decide (Pre base exponent))
example : (List.range 8).all (fun b => (List.range 8).all (fun e =>
    (prog ((b : Int) - 4) ((e : Int) - 4)).toOption.isSome
      == decide (Pre ((b : Int) - 4) ((e : Int) - 4)))) = true := by native_decide

-- total_spec_prop
#eval Plausible.Testable.check (∀ base exponent : Int,
  prog base exponent =
    if Pre base exponent then .ok (base ^ exponent.toNat) else .error (errMsg base exponent))
example : (List.range 8).all (fun b => (List.range 8).all (fun e =>
    prog ((b : Int) - 4) ((e : Int) - 4) ==
      if Pre ((b : Int) - 4) ((e : Int) - 4) then .ok (((b : Int) - 4) ^ ((e : Int) - 4).toNat)
      else .error (errMsg ((b : Int) - 4) ((e : Int) - 4)))) = true := by native_decide

-- Post_prop (via its executable form `postCheck`)
#eval Plausible.Testable.check (∀ base exponent : Nat,
  postCheck base exponent (prog base exponent) = true)
example : (List.range 16).all (fun b => (List.range 16).all (fun e =>
    postCheck b e (prog b e))) = true := by native_decide

/-! ## Correctness -/

/-- Correctness: on admissible inputs the functional program satisfies the post-condition. -/
theorem prog_correct (base exponent : Int) (h : Pre base exponent) :
    Post_prop base exponent (prog base exponent) := by
  refine ⟨prog_eq_of_pre base exponent h, ?_, ?_, ?_, ?_, prog_nonneg base exponent h⟩
  · intro h0
    subst h0
    exact prog_exp_zero base h.1
  · intro h0 he
    subst h0
    exact prog_base_zero exponent he
  · intro h1
    subst h1
    exact prog_base_one exponent h.2
  · intro h1
    subst h1
    exact prog_exp_one base h.1

/-! ## Imperative implementation -/

/-- Imperative translation of the Python `prog`: precondition check with an early
`return` (the `ValueError`), the `exponent == 0` shortcut, then the loop
`for _ in range(exponent): result *= base` over a mutable `result`. -/
def progImp (base exponent : Int) : Except String Int := Id.run do
  if base < 0 ∨ exponent < 0 then
    return .error (errMsg base exponent)
  if exponent = 0 then
    return .ok 1
  let mut result : Int := 1
  for _ in List.range exponent.toNat do
    result := result * base
  return .ok result

/-! ## Imperative tests -/

example : progImp 2 3 = .ok 8 := by native_decide
example : progImp 0 0 = .ok 1 := by native_decide
example : progImp (-1) 2 = .error (errMsg (-1) 2) := by native_decide
example : progImp 2 (-1) = .error (errMsg 2 (-1)) := by native_decide
example : (progImp (-1) 2).toOption = none := by native_decide
example : (progImp 2 (-1)).toOption = none := by native_decide
example : progImp 3 4 = .ok 81 := by native_decide
example : progImp 0 5 = .ok 0 := by native_decide
example : progImp 10 3 = .ok 1000 := by native_decide

#eval progImp 2 3     -- Except.ok 8
#eval progImp 0 0     -- Except.ok 1
#eval progImp (-1) 2  -- Except.error "Require base,exponent ∈ ℕ (got base=-1, exponent=2)"
#eval progImp 2 (-1)  -- Except.error "Require base,exponent ∈ ℕ (got base=2, exponent=-1)"

example : (List.range 16).all (fun b => (List.range 16).all (fun e =>
    progImp b e == prog b e)) = true := by native_decide
example : (List.range 8).all (fun b => (List.range 8).all (fun e =>
    progImp ((b : Int) - 4) ((e : Int) - 4) == prog ((b : Int) - 4) ((e : Int) - 4))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ base exponent : Int, progImp base exponent = prog base exponent)

/-! ## Equivalence -/

/-- The loop `result = acc; for _ in range(n): result *= base` computes `acc * base ^ n`. -/
theorem foldl_mul_range (base acc : Int) (n : Nat) :
    List.foldl (fun r _ => r * base) acc (List.range n) = acc * base ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [pow_succ, mul_assoc]

theorem progImp_eq_of_pre (base exponent : Int) (h : Pre base exponent) :
    progImp base exponent = .ok (base ^ exponent.toNat) := by
  obtain ⟨hb, he⟩ := h
  have hb' : ¬ base < 0 := by omega
  have he' : ¬ exponent < 0 := by omega
  by_cases h0 : exponent = 0
  · subst h0
    simp [progImp, hb']
  · simp [progImp, hb', he', h0, foldl_mul_range]

theorem progImp_eq_of_not_pre (base exponent : Int) (h : ¬ Pre base exponent) :
    progImp base exponent = .error (errMsg base exponent) := by
  have hneg : base < 0 ∨ exponent < 0 := by
    unfold Pre at h
    omega
  unfold progImp
  simp only [Id.run, bind, pure, if_pos hneg]

/-- Functional and imperative implementations agree on all inputs
(including the exceptional ones). -/
theorem prog_eq_progImp (base exponent : Int) : prog base exponent = progImp base exponent := by
  by_cases h : Pre base exponent
  · rw [prog_eq_of_pre base exponent h, progImp_eq_of_pre base exponent h]
  · rw [prog_eq_of_not_pre base exponent h, progImp_eq_of_not_pre base exponent h]

/-- The imperative program also satisfies the post-condition on admissible inputs. -/
theorem progImp_correct (base exponent : Int) (h : Pre base exponent) :
    Post_prop base exponent (progImp base exponent) := by
  rw [← prog_eq_progImp]
  exact prog_correct base exponent h

end «19_MyPower»

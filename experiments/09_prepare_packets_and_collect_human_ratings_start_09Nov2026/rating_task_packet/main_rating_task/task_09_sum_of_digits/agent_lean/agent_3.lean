import Mathlib

/-!
# Sum of digits of a non-negative integer (`20_MySumDigits`)

Lean 4 formalization of the Python program `prog`:

```python
def pre(n: int) -> bool:
    return isinstance(n, int) and n >= 0

def prog(n: int) -> int:
    if not pre(n):
        raise ValueError(f"Require non-negative integer (got n={n!r})")
    if n == 0:
        return 0
    total = 0
    while n > 0:
        total += n % 10
        n //= 10
    return total
```

* `sumDigits : ℕ → ℕ` is the functional core (sum of the base-10 digits).
* `prog : ℤ → Except String ℤ` mirrors the Python function on `int` inputs:
  a negative input yields `Except.error` carrying the Python error message
  (the `ValueError`), a non-negative input yields `Except.ok (digit sum)`.
  (The Python test input `3.14` is a type error that the type `ℤ` already
  rules out, so it has no counterpart here.)
* `Pre n` is `0 ≤ n`; `Post_prop n` is the conjunction of the properties proved
  about `prog n`; `correctness_thm : Pre n → Post_prop n`.
* `sumDigitsImp` / `progImp` are imperative versions written with `Id.run do`
  and mutable state, proved equal to the functional ones
  (`sumDigitsImp_eq_thm`, `progImp_eq_thm`).
-/

namespace «20_MySumDigits»

/-! ## Functional implementation -/

/-- Sum of the base-10 digits of `n`: the `while n > 0` loop of the Python
program (`total += n % 10; n //= 10`), written as a recursion on `n`. -/
def sumDigits (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else n % 10 + sumDigits (n / 10)
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

/-- Python `prog` on an `int` argument: a negative input violates the
precondition and raises `ValueError` (modelled by `Except.error` with the same
message); otherwise the digit sum is returned (`Except.ok`). -/
def prog (n : ℤ) : Except String ℤ :=
  if n < 0 then .error s!"Require non-negative integer (got n={n})"
  else .ok (sumDigits n.toNat : ℕ)

-- Equality of `Except` results is decidable (used by unit tests and PBTs).
deriving instance DecidableEq for Except

/-! ## Unit tests -/

example : sumDigits 123 = 6 := by native_decide
example : sumDigits 0 = 0 := by native_decide
example : sumDigits 7 = 7 := by native_decide
example : sumDigits 1000 = 1 := by native_decide
example : sumDigits 99999 = 45 := by native_decide

-- Basic unit test: `candidate(123) == 6`
example : prog 123 = .ok 6 := by native_decide
-- Edge unit test: `candidate(0) == 0`
example : prog 0 = .ok 0 := by native_decide
-- Single digit numbers return themselves
example : prog 7 = .ok 7 := by native_decide
-- Negative input: the pre-violation raises `ValueError`
example : prog (-1) = .error "Require non-negative integer (got n=-1)" := by native_decide
example : (prog (-1)).isOk = false := by native_decide
example : (prog (-42)).isOk = false := by native_decide

#eval sumDigits 123        -- 6
#eval sumDigits 0          -- 0
#eval prog 123             -- Except.ok 6
#eval prog 0               -- Except.ok 0
#eval prog (-1)            -- Except.error "Require non-negative integer (got n=-1)"
#eval prog 9876543210      -- Except.ok 45

/-! ## Pre-condition -/

/-- Python `pre(n)`: `n` is a non-negative integer. -/
def Pre (n : ℤ) : Prop := 0 ≤ n

/-! ## Lemmas about the functional core `sumDigits` -/

theorem sumDigits_zero : sumDigits 0 = 0 := by
  rw [sumDigits]; simp

/-- One step of the Python loop: `total += n % 10; n //= 10`. -/
theorem sumDigits_eq (n : ℕ) : sumDigits n = n % 10 + sumDigits (n / 10) := by
  rw [sumDigits]
  split_ifs with h
  · subst h; simp [sumDigits_zero]
  · rfl

theorem sumDigits_of_lt {n : ℕ} (h : n < 10) : sumDigits n = n := by
  rw [sumDigits_eq, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, sumDigits_zero, Nat.add_zero]

/-- `sumDigits` agrees with Mathlib's base-10 digit expansion. -/
theorem sumDigits_eq_digits_sum (n : ℕ) : sumDigits n = (Nat.digits 10 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [sumDigits]
    split_ifs with h
    · subst h; simp
    · rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h), List.sum_cons,
        ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num))]

/-- Casting-out-nines: the digit sum is congruent to `n` modulo `9`. -/
theorem sumDigits_mod_nine (n : ℕ) : sumDigits n % 9 = n % 9 := by
  rw [sumDigits_eq_digits_sum]
  exact (Nat.modEq_nine_digits_sum n).symm

theorem sumDigits_le (n : ℕ) : sumDigits n ≤ n := by
  rw [sumDigits_eq_digits_sum]
  exact Nat.digit_sum_le 10 n

theorem sumDigits_eq_zero_iff (n : ℕ) : sumDigits n = 0 ↔ n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    constructor
    · intro h
      rw [sumDigits_eq] at h
      have h1 : n % 10 = 0 := by omega
      have h2 : sumDigits (n / 10) = 0 := by omega
      by_contra hn
      have := (ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))).mp h2
      omega
    · rintro rfl; exact sumDigits_zero

/-- Appending a digit `d` to `n` adds `d` to the digit sum. -/
theorem sumDigits_ten_mul_add (n d : ℕ) (hd : d < 10) :
    sumDigits (10 * n + d) = sumDigits n + d := by
  rw [sumDigits_eq (10 * n + d)]
  have h1 : (10 * n + d) % 10 = d := by omega
  have h2 : (10 * n + d) / 10 = n := by omega
  rw [h1, h2]; ring

/-! ## Lemmas about `prog` -/

theorem prog_of_neg {n : ℤ} (h : n < 0) :
    prog n = .error s!"Require non-negative integer (got n={n})" := by
  simp [prog, h]

theorem prog_natCast (k : ℕ) : prog (k : ℤ) = .ok (sumDigits k : ℕ) := by
  simp [prog]

theorem prog_of_nonneg {n : ℤ} (h : 0 ≤ n) : prog n = .ok (sumDigits n.toNat : ℕ) := by
  simp [prog, not_lt.mpr h]

/-! ## Properties -/

/-- Specification: `prog n` succeeds and returns the sum of the base-10 digits
of `n` (as given by Mathlib's `Nat.digits`). -/
def spec_prop (n : ℤ) : Prop := prog n = .ok ((Nat.digits 10 n.toNat).sum : ℕ)

/-- Edge case: the sum of digits of `0` is `0`. -/
def zero_prop (n : ℤ) : Prop := n = 0 → prog n = .ok 0

/-- Edge case: single digit numbers return themselves. -/
def single_digit_prop (n : ℤ) : Prop := n < 10 → prog n = .ok n

/-- Loop step: for `n ≥ 10`, `prog n = prog (n // 10) + n % 10`. -/
def recurrence_prop (n : ℤ) : Prop :=
  10 ≤ n → ∀ r : ℤ, prog (n / 10) = .ok r → prog n = .ok (r + n % 10)

/-- Casting out nines: the result is congruent to `n` modulo `9`. -/
def mod_nine_prop (n : ℤ) : Prop := ∀ r : ℤ, prog n = .ok r → r % 9 = n % 9

/-- The result is a non-negative integer not exceeding `n`. -/
def bounds_prop (n : ℤ) : Prop := ∀ r : ℤ, prog n = .ok r → 0 ≤ r ∧ r ≤ n

/-- The result is `0` exactly for the input `0`. -/
def zero_iff_prop (n : ℤ) : Prop := ∀ r : ℤ, prog n = .ok r → (r = 0 ↔ n = 0)

/-- `prog` returns normally exactly when the precondition holds (for all `n`). -/
def ok_iff_pre_prop (n : ℤ) : Prop := (prog n).isOk = true ↔ Pre n

/-- A precondition violation raises `ValueError` with the Python message. -/
def pre_violation_prop (n : ℤ) : Prop :=
  ¬ Pre n → prog n = .error s!"Require non-negative integer (got n={n})"

theorem spec_thm (n : ℤ) (h : Pre n) : spec_prop n := by
  unfold spec_prop
  rw [prog_of_nonneg h, sumDigits_eq_digits_sum]

theorem zero_thm (n : ℤ) (_h : Pre n) : zero_prop n := by
  rintro rfl
  have h0 := prog_natCast 0
  rw [sumDigits_zero] at h0
  exact h0

theorem single_digit_thm (n : ℤ) (h : Pre n) : single_digit_prop n := by
  intro hn
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [prog_natCast, sumDigits_of_lt (by exact_mod_cast hn)]

theorem recurrence_thm (n : ℤ) (h : Pre n) : recurrence_prop n := by
  intro _hn r hr
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have hdiv : ((k : ℤ) / 10) = ((k / 10 : ℕ) : ℤ) := by push_cast; rfl
  rw [hdiv, prog_natCast] at hr
  have hr' := Except.ok.inj hr
  subst hr'
  rw [prog_natCast, sumDigits_eq k]
  congr 1
  push_cast
  omega

theorem mod_nine_thm (n : ℤ) (h : Pre n) : mod_nine_prop n := by
  intro r hr
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [prog_natCast] at hr
  have hr' := Except.ok.inj hr
  subst hr'
  have := sumDigits_mod_nine k
  omega

theorem bounds_thm (n : ℤ) (h : Pre n) : bounds_prop n := by
  intro r hr
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [prog_natCast] at hr
  have hr' := Except.ok.inj hr
  subst hr'
  have := sumDigits_le k
  omega

theorem zero_iff_thm (n : ℤ) (h : Pre n) : zero_iff_prop n := by
  intro r hr
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [prog_natCast] at hr
  have hr' := Except.ok.inj hr
  subst hr'
  have := sumDigits_eq_zero_iff k
  omega

theorem ok_iff_pre_thm (n : ℤ) : ok_iff_pre_prop n := by
  unfold ok_iff_pre_prop Pre
  by_cases h : n < 0
  · rw [prog_of_neg h]; simp [Except.isOk, Except.toBool]; omega
  · rw [prog_of_nonneg (not_lt.mp h)]; simp [Except.isOk, Except.toBool]; omega

theorem pre_violation_thm (n : ℤ) : pre_violation_prop n := by
  intro h
  exact prog_of_neg (by unfold Pre at h; omega)

/-! ## Post-condition -/

/-- Post-condition of `prog n` (for admissible `n`). -/
def Post_prop (n : ℤ) : Prop :=
  spec_prop n ∧ zero_prop n ∧ single_digit_prop n ∧ recurrence_prop n ∧
    mod_nine_prop n ∧ bounds_prop n ∧ zero_iff_prop n

/-! ## Property-based tests

Randomized checks (`Plausible`) plus exhaustive bounded checks; the latter
cover the properties whose preconditions random sampling rarely satisfies. -/

-- sumDigits lemmas
#eval Plausible.Testable.check (∀ n : ℕ, sumDigits n = (Nat.digits 10 n).sum)
#eval Plausible.Testable.check (∀ n : ℕ, sumDigits n = n % 10 + sumDigits (n / 10))
#eval Plausible.Testable.check (∀ n : ℕ, sumDigits n % 9 = n % 9)
#eval Plausible.Testable.check (∀ n : ℕ, sumDigits n ≤ n)
#eval Plausible.Testable.check (∀ n : ℕ, (sumDigits n = 0 ↔ n = 0))
#eval Plausible.Testable.check (∀ n d : ℕ, d < 10 → sumDigits (10 * n + d) = sumDigits n + d)
example : (List.range 10).all (fun n => sumDigits n = n) = true := by native_decide
example : ((List.range 50).all fun n => (List.range 10).all fun d =>
    sumDigits (10 * n + d) = sumDigits n + d) = true := by native_decide

-- spec_prop
#eval Plausible.Testable.check (∀ n : ℤ, 0 ≤ n → prog n = .ok ((Nat.digits 10 n.toNat).sum : ℕ))
#eval Plausible.Testable.check (∀ k : ℕ, prog (k : ℤ) = .ok ((Nat.digits 10 k).sum : ℕ))
example : (List.range 300).all
    (fun k => prog (k : ℤ) = .ok ((Nat.digits 10 k).sum : ℕ)) = true := by native_decide

-- zero_prop
#eval Plausible.Testable.check (∀ n : ℤ, 0 ≤ n → (n = 0 → prog n = .ok 0))
example : (List.range 300).all
    (fun k => decide ((k : ℤ) = 0 → prog (k : ℤ) = .ok 0)) = true := by native_decide

-- single_digit_prop
#eval Plausible.Testable.check (∀ n : ℤ, 0 ≤ n → n < 10 → prog n = .ok n)
example : (List.range 10).all (fun k => prog (k : ℤ) = .ok (k : ℤ)) = true := by native_decide

-- recurrence_prop (executable form: `prog n = prog (n / 10) + n % 10` for `n ≥ 10`)
#eval Plausible.Testable.check
  (∀ n : ℤ, 10 ≤ n → (prog (n / 10)).map (fun r => r + n % 10) = prog n)
#eval Plausible.Testable.check
  (∀ k : ℕ, 10 ≤ k → (prog ((k : ℤ) / 10)).map (fun r => r + (k : ℤ) % 10) = prog (k : ℤ))
example : (List.range 300).all (fun k => decide (10 ≤ k →
    (prog ((k : ℤ) / 10)).map (fun r => r + (k : ℤ) % 10) = prog (k : ℤ))) = true := by
  native_decide

-- mod_nine_prop
#eval Plausible.Testable.check (∀ n : ℤ, 0 ≤ n → (prog n).map (fun r => r % 9) = .ok (n % 9))
#eval Plausible.Testable.check (∀ k : ℕ, (prog (k : ℤ)).map (fun r => r % 9) = .ok ((k : ℤ) % 9))
example : (List.range 300).all
    (fun k => (prog (k : ℤ)).map (fun r => r % 9) = .ok ((k : ℤ) % 9)) = true := by native_decide

-- bounds_prop
#eval Plausible.Testable.check
  (∀ n : ℤ, 0 ≤ n → (prog n).map (fun r => decide (0 ≤ r ∧ r ≤ n)) = .ok true)
#eval Plausible.Testable.check
  (∀ k : ℕ, (prog (k : ℤ)).map (fun r => decide (0 ≤ r ∧ r ≤ (k : ℤ))) = .ok true)
example : (List.range 300).all
    (fun k => (prog (k : ℤ)).map (fun r => decide (0 ≤ r ∧ r ≤ (k : ℤ))) = .ok true) = true := by
  native_decide

-- zero_iff_prop
#eval Plausible.Testable.check
  (∀ n : ℤ, 0 ≤ n → (prog n).map (fun r => decide (r = 0)) = .ok (decide (n = 0)))
#eval Plausible.Testable.check
  (∀ k : ℕ, (prog (k : ℤ)).map (fun r => decide (r = 0)) = .ok (decide (k = 0)))
example : (List.range 300).all
    (fun k => (prog (k : ℤ)).map (fun r => decide (r = 0)) = .ok (decide (k = 0))) = true := by
  native_decide

-- ok_iff_pre_prop (all integers, including negative ones)
#eval Plausible.Testable.check (∀ n : ℤ, (prog n).isOk = decide (0 ≤ n))
example : ((List.range 300).map (fun k => (k : ℤ) - 150)).all
    (fun n => (prog n).isOk = decide (0 ≤ n)) = true := by native_decide

-- pre_violation_prop
#eval Plausible.Testable.check
  (∀ n : ℤ, n < 0 → prog n = .error s!"Require non-negative integer (got n={n})")
example : ((List.range 150).map (fun k => -((k : ℤ) + 1))).all
    (fun n => prog n = .error s!"Require non-negative integer (got n={n})") = true := by
  native_decide

-- Post_prop (executable conjunction of the component checks)
#eval Plausible.Testable.check (∀ k : ℕ, decide (
  prog (k : ℤ) = .ok ((Nat.digits 10 k).sum : ℕ) ∧
  (k = 0 → prog (k : ℤ) = .ok 0) ∧
  (k < 10 → prog (k : ℤ) = .ok (k : ℤ)) ∧
  (10 ≤ k → (prog ((k : ℤ) / 10)).map (fun r => r + (k : ℤ) % 10) = prog (k : ℤ)) ∧
  (prog (k : ℤ)).map (fun r => r % 9) = .ok ((k : ℤ) % 9) ∧
  (prog (k : ℤ)).map (fun r => decide (0 ≤ r ∧ r ≤ (k : ℤ))) = .ok true ∧
  (prog (k : ℤ)).map (fun r => decide (r = 0)) = .ok (decide (k = 0))) = true)
example : (List.range 300).all (fun k => decide (
  prog (k : ℤ) = .ok ((Nat.digits 10 k).sum : ℕ) ∧
  (k = 0 → prog (k : ℤ) = .ok 0) ∧
  (k < 10 → prog (k : ℤ) = .ok (k : ℤ)) ∧
  (10 ≤ k → (prog ((k : ℤ) / 10)).map (fun r => r + (k : ℤ) % 10) = prog (k : ℤ)) ∧
  (prog (k : ℤ)).map (fun r => r % 9) = .ok ((k : ℤ) % 9) ∧
  (prog (k : ℤ)).map (fun r => decide (0 ≤ r ∧ r ≤ (k : ℤ))) = .ok true ∧
  (prog (k : ℤ)).map (fun r => decide (r = 0)) = .ok (decide (k = 0)))) = true := by
  native_decide

/-! ## Correctness: `Pre → Post` -/

theorem correctness_thm (n : ℤ) (h : Pre n) : Post_prop n :=
  ⟨spec_thm n h, zero_thm n h, single_digit_thm n h, recurrence_thm n h,
    mod_nine_thm n h, bounds_thm n h, zero_iff_thm n h⟩

/-! ## Imperative implementation

Lean's `while` combinator (`Loop.forIn`) is `partial`, hence opaque to the
kernel, so the Python `while n > 0` loop is written as a bounded `for` loop
with an explicit `break` once `m = 0`. The bound `n + 1` always suffices
(`n` has at most `n + 1` digits), which the equivalence proofs establish. -/

/-- Imperative digit sum: `total = 0; while m > 0: total += m % 10; m //= 10`. -/
def sumDigitsImp (n : ℕ) : ℕ := Id.run do
  let mut total := 0
  let mut m := n
  for _ in [0:n + 1] do
    if m = 0 then break
    total := total + m % 10
    m := m / 10
  return total

/-- Imperative version of the whole Python `prog`, including the precondition
check (`raise ValueError`), the `n == 0` early return and the loop. -/
def progImp (n : ℤ) : Except String ℤ := Id.run do
  if n < 0 then
    return .error s!"Require non-negative integer (got n={n})"
  if n = 0 then
    return .ok 0
  let mut total : ℕ := 0
  let mut m : ℕ := n.toNat
  for _ in [0:n.toNat + 1] do
    if m = 0 then break
    total := total + m % 10
    m := m / 10
  return .ok (total : ℤ)

/-! ## Imperative tests -/

example : sumDigitsImp 123 = 6 := by native_decide
example : sumDigitsImp 0 = 0 := by native_decide
example : sumDigitsImp 7 = 7 := by native_decide
example : sumDigitsImp 99999 = 45 := by native_decide
example : progImp 123 = .ok 6 := by native_decide
example : progImp 0 = .ok 0 := by native_decide
example : progImp 7 = .ok 7 := by native_decide
example : progImp (-1) = .error "Require non-negative integer (got n=-1)" := by native_decide
example : (progImp (-1)).isOk = false := by native_decide

#eval sumDigitsImp 123     -- 6
#eval sumDigitsImp 0       -- 0
#eval progImp 123          -- Except.ok 6
#eval progImp 0            -- Except.ok 0
#eval progImp (-1)         -- Except.error "Require non-negative integer (got n=-1)"
#eval progImp 9876543210   -- Except.ok 45

-- PBTs for the equivalence theorems
#eval Plausible.Testable.check (∀ n : ℕ, sumDigitsImp n = sumDigits n)
#eval Plausible.Testable.check (∀ n : ℤ, progImp n = prog n)
example : (List.range 300).all (fun n => sumDigitsImp n = sumDigits n) = true := by native_decide
example : ((List.range 300).map (fun k => (k : ℤ) - 150)).all
    (fun n => progImp n = prog n) = true := by native_decide

/-! ## Equivalence: functional = imperative -/

/-- The loop invariant of the imperative loop body: starting from the state
`⟨m, total⟩` with `m < 10 ^ k`, `k` iterations end in `⟨0, total + sumDigits m⟩`. -/
theorem loop_aux (f : ℕ → MProd ℕ ℕ → Id (ForInStep (MProd ℕ ℕ)))
    (hf0 : ∀ x total, f x ⟨0, total⟩ = pure (.done ⟨0, total⟩))
    (hf : ∀ x m total, m ≠ 0 → f x ⟨m, total⟩ = pure (.yield ⟨m / 10, total + m % 10⟩)) :
    ∀ (k s m total : ℕ), m < 10 ^ k →
      forIn (List.range' s k) (⟨m, total⟩ : MProd ℕ ℕ) f =
        (pure ⟨0, total + sumDigits m⟩ : Id (MProd ℕ ℕ)) := by
  intro k
  induction k with
  | zero =>
    intro s m total hm
    have : m = 0 := by simpa using hm
    subst this
    simp [List.forIn_nil, sumDigits_zero]
  | succ k ih =>
    intro s m total hm
    rw [List.range'_succ, List.forIn_cons]
    by_cases h0 : m = 0
    · subst h0
      rw [hf0]
      simp [sumDigits_zero]
    · rw [hf _ _ _ h0]
      have hlt : m / 10 < 10 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        rw [pow_succ] at hm; linarith
      simp only [pure_bind]
      rw [ih (s + 1) (m / 10) (total + m % 10) hlt]
      congr 2
      rw [sumDigits_eq m]; ring

theorem sumDigitsImp_eq_thm (n : ℕ) : sumDigitsImp n = sumDigits n := by
  unfold sumDigitsImp
  simp only [Id.run, Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [loop_aux _ ?_ ?_ (n + 1) 0 n 0
    (lt_trans (Nat.lt_pow_self (by norm_num))
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)))]
  · simp only [Nat.zero_add]; rfl
  · intro x total; simp
  · intro x m total hm; simp [hm]

theorem progImp_eq_thm (n : ℤ) : progImp n = prog n := by
  unfold progImp prog
  by_cases h1 : n < 0
  · simp [h1]
  · by_cases h2 : n = 0
    · subst h2
      simp [sumDigits_zero]
    · simp only [h1, h2, if_false, Id.run, Std.Range.forIn_eq_forIn_range', Std.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      rw [loop_aux _ ?_ ?_ (n.toNat + 1) 0 n.toNat 0
        (lt_trans (Nat.lt_pow_self (by norm_num))
          (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))]
      · simp only [Nat.zero_add]; rfl
      · intro x total; simp
      · intro x m total hm; simp [hm]

/-- Both imperative versions compute the same values as the functional ones. -/
theorem equivalence_thm : (∀ n : ℕ, sumDigitsImp n = sumDigits n) ∧ (∀ n : ℤ, progImp n = prog n) :=
  ⟨sumDigitsImp_eq_thm, progImp_eq_thm⟩

end «20_MySumDigits»

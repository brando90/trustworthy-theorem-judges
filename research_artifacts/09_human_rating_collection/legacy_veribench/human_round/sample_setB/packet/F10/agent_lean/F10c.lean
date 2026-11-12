import Mathlib

/-!
# Sum of digits (`20_MySumDigits`)

Lean 4 translation of the Python program `prog`, which returns the sum of the
decimal digits of a non-negative integer `n`.

* `sumDigits : Nat → Nat` is the functional core: the Python `while n > 0` loop
  (`total += n % 10; n //= 10`) becomes recursion on `n / 10`.
* `prog : Int → Except String Int` mirrors the Python signature.  The precondition
  `pre(n)` ("`n` is a non-negative integer") is checked and the `ValueError` is
  modelled by `Except.error`.  The Python test input `3.14` (not an `int`) is
  excluded in Lean by typing, so only negativity can violate the precondition.
* Properties: the digit sum of `0` is `0`, single digits are fixed points, the
  recursive characterisation `n % 10 + sumDigits (n / 10)`, agreement with
  Mathlib's `(Nat.digits 10 n).sum`, `sumDigits n ≤ n`, casting out nines
  (`sumDigits n % 9 = n % 9`), `sumDigits n = 0 ↔ n = 0`, the appended-digit law,
  and the `ok` / `error` behaviour of `prog`.
* `sumDigitsImp` / `progImp` are imperative versions written with `Id.run do` and
  mutable state, proven equal to the functional versions.
-/

namespace «20_MySumDigits»

/-! ## Functional implementation -/

/-- Sum of the decimal digits of `n` (the Python `while` loop as recursion). -/
def sumDigits (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 10 + sumDigits (n / 10)
decreasing_by omega

/-- Python entry point `prog`: raises (`Except.error`) when the precondition
`n ≥ 0` fails, otherwise returns the digit sum of `n` as an `Int`. -/
def prog (n : Int) : Except String Int :=
  if n < 0 then
    Except.error s!"Require non-negative integer (got n={n})"
  else
    Except.ok (sumDigits n.toNat : Int)

/-! ## Unit tests -/

-- Basic unit test (`candidate(123) == 6`)
example : sumDigits 123 = 6 := by native_decide
-- Edge unit test (`candidate(0) == 0`)
example : sumDigits 0 = 0 := by native_decide
-- Single digit numbers return themselves
example : sumDigits 7 = 7 := by native_decide
example : sumDigits 999 = 27 := by native_decide
example : sumDigits 1000000 = 1 := by native_decide
-- Python-level wrapper
example : (prog 123).toOption = some 6 := by native_decide
example : (prog 0).toOption = some 0 := by native_decide
-- Negative input: pre-violation raises (`Except.error`)
example : (prog (-1)).toOption = none := by native_decide

#eval sumDigits 123      -- 6
#eval sumDigits 0        -- 0
#eval prog 123           -- Except.ok 6
#eval prog 0             -- Except.ok 0
#eval prog (-1)          -- Except.error "Require non-negative integer (got n=-1)"

/-! ## Pre-condition -/

/-- Python `pre(n)`: `n` is a non-negative integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

/-! ## Basic equations for `sumDigits` -/

theorem sumDigits_zero : sumDigits 0 = 0 := by
  rw [sumDigits]; simp

theorem sumDigits_pos (n : Nat) (h : n ≠ 0) :
    sumDigits n = n % 10 + sumDigits (n / 10) := by
  rw [sumDigits, dif_neg h]

theorem sumDigits_single_digit (n : Nat) (h : n < 10) : sumDigits n = n := by
  by_cases h0 : n = 0
  · subst h0; exact sumDigits_zero
  · rw [sumDigits_pos n h0]
    have h1 : n / 10 = 0 := by omega
    have h2 : n % 10 = n := by omega
    rw [h1, h2, sumDigits_zero, Nat.add_zero]

theorem sumDigits_eq_digits_sum (n : Nat) : sumDigits n = (Nat.digits 10 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [sumDigits_zero]
    · rw [sumDigits_pos n h0, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0),
        List.sum_cons, ih (n / 10) (by omega)]

theorem sumDigits_le (n : Nat) : sumDigits n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst h0; rw [sumDigits_zero]
    · rw [sumDigits_pos n h0]
      have := ih (n / 10) (by omega)
      omega

theorem sumDigits_mod_nine (n : Nat) : sumDigits n % 9 = n % 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst h0; rw [sumDigits_zero]
    · rw [sumDigits_pos n h0]
      have := ih (n / 10) (by omega)
      omega

theorem sumDigits_eq_zero_iff (n : Nat) : sumDigits n = 0 ↔ n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [sumDigits_zero]
    · rw [sumDigits_pos n h0]
      have := ih (n / 10) (by omega)
      constructor
      · intro h; omega
      · intro h; exact absurd h h0

theorem sumDigits_append_digit (n d : Nat) (hd : d < 10) :
    sumDigits (10 * n + d) = sumDigits n + d := by
  by_cases h0 : 10 * n + d = 0
  · have hn : n = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hn; subst hd0; simp [sumDigits_zero]
  · rw [sumDigits_pos _ h0]
    have h1 : (10 * n + d) % 10 = d := by omega
    have h2 : (10 * n + d) / 10 = n := by omega
    rw [h1, h2]; omega

theorem prog_ok (n : Int) (h : 0 ≤ n) : prog n = Except.ok (sumDigits n.toNat : Int) := by
  unfold prog; rw [if_neg (not_lt.mpr h)]

theorem prog_error (n : Int) (h : n < 0) : ∃ msg, prog n = Except.error msg :=
  ⟨_, by unfold prog; rw [if_pos h]⟩

/-! ## Property propositions and theorems -/

/-- Edge case: the digit sum of `0` is `0`. -/
def zero_prop : Prop := sumDigits 0 = 0

theorem zero_thm : zero_prop := sumDigits_zero

/-- Single digit numbers return themselves. -/
def single_digit_prop (n : Nat) : Prop := n < 10 → sumDigits n = n

theorem single_digit_thm (n : Nat) : single_digit_prop n := by
  intro h; exact sumDigits_single_digit n h

/-- One iteration of the Python loop: `total += n % 10; n //= 10`. -/
def recurrence_prop (n : Nat) : Prop := n ≠ 0 → sumDigits n = n % 10 + sumDigits (n / 10)

theorem recurrence_thm (n : Nat) : recurrence_prop n := by
  intro h; exact sumDigits_pos n h

/-- The result is the sum of the base-10 digits (Mathlib's `Nat.digits`). -/
def digits_sum_prop (n : Nat) : Prop := sumDigits n = (Nat.digits 10 n).sum

theorem digits_sum_thm (n : Nat) : digits_sum_prop n := sumDigits_eq_digits_sum n

/-- The digit sum never exceeds the number. -/
def le_self_prop (n : Nat) : Prop := sumDigits n ≤ n

theorem le_self_thm (n : Nat) : le_self_prop n := sumDigits_le n

/-- Casting out nines: the digit sum is congruent to `n` modulo `9`. -/
def mod_nine_prop (n : Nat) : Prop := sumDigits n % 9 = n % 9

theorem mod_nine_thm (n : Nat) : mod_nine_prop n := sumDigits_mod_nine n

/-- The digit sum is `0` exactly for `n = 0`. -/
def eq_zero_iff_prop (n : Nat) : Prop := sumDigits n = 0 ↔ n = 0

theorem eq_zero_iff_thm (n : Nat) : eq_zero_iff_prop n := sumDigits_eq_zero_iff n

/-- Appending a digit `d` adds `d` to the digit sum. -/
def append_digit_prop (n d : Nat) : Prop := d < 10 → sumDigits (10 * n + d) = sumDigits n + d

theorem append_digit_thm (n d : Nat) : append_digit_prop n d := by
  intro hd; exact sumDigits_append_digit n d hd

/-- On admissible inputs `prog` succeeds with the digit sum. -/
def prog_ok_prop (n : Int) : Prop := 0 ≤ n → prog n = Except.ok (sumDigits n.toNat : Int)

theorem prog_ok_thm (n : Int) : prog_ok_prop n := by
  intro h; exact prog_ok n h

/-- On a negative input `prog` raises (returns `Except.error`). -/
def prog_error_prop (n : Int) : Prop := n < 0 → ∃ msg, prog n = Except.error msg

theorem prog_error_thm (n : Int) : prog_error_prop n := by
  intro h; exact prog_error n h

/-! ## Post-condition -/

/-- Post-condition relating the admissible input `n` to the returned value `r`. -/
def Post_prop (n : Int) (r : Int) : Prop :=
  r = ((Nat.digits 10 n.toNat).sum : Int) ∧      -- `r` is the sum of the decimal digits of `n`
  0 ≤ r ∧ r ≤ n ∧                                  -- bounds
  r % 9 = n % 9 ∧                                  -- casting out nines
  (r = 0 ↔ n = 0) ∧                                -- zero exactly for `n = 0`
  (n < 10 → r = n)                                 -- single digits are returned unchanged

instance (n r : Int) : Decidable (Post_prop n r) := by
  unfold Post_prop; infer_instance

/-- Executable form of "`prog n` succeeds and its result satisfies `Post_prop`". -/
def postCheck (n : Int) : Bool :=
  match prog n with
  | Except.ok r => decide (Post_prop n r)
  | Except.error _ => false

/-! ## Property-based tests -/

-- zero_prop (closed statement; exhaustively checked)
example : sumDigits 0 = 0 := by native_decide
-- single_digit_prop
#eval Plausible.Testable.check (∀ n : Nat, n < 10 → sumDigits n = n)
example : (List.range 10).all (fun n => sumDigits n == n) = true := by native_decide
-- recurrence_prop
#eval Plausible.Testable.check (∀ n : Nat, n ≠ 0 → sumDigits n = n % 10 + sumDigits (n / 10))
example : (List.range 400).all
    (fun n => n == 0 || sumDigits n == n % 10 + sumDigits (n / 10)) = true := by native_decide
-- digits_sum_prop
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n = (Nat.digits 10 n).sum)
example : (List.range 400).all (fun n => sumDigits n == (Nat.digits 10 n).sum) = true := by
  native_decide
-- le_self_prop
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n ≤ n)
example : (List.range 400).all (fun n => sumDigits n ≤ n) = true := by native_decide
-- mod_nine_prop
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n % 9 = n % 9)
example : (List.range 400).all (fun n => sumDigits n % 9 == n % 9) = true := by native_decide
-- eq_zero_iff_prop
#eval Plausible.Testable.check (∀ n : Nat, (sumDigits n = 0 ↔ n = 0))
example : (List.range 400).all (fun n => (sumDigits n == 0) == (n == 0)) = true := by native_decide
-- append_digit_prop
#eval Plausible.Testable.check (∀ n d : Nat, d < 10 → sumDigits (10 * n + d) = sumDigits n + d)
example : ((List.range 60).all fun n => (List.range 10).all fun d =>
    sumDigits (10 * n + d) == sumDigits n + d) = true := by native_decide
-- prog_ok_prop
#eval Plausible.Testable.check
  (∀ n : Int, 0 ≤ n → (prog n).toOption = some (sumDigits n.toNat : Int))
example : (List.range 400).all
    (fun n : Nat => (prog n).toOption == some (sumDigits n : Int)) = true := by native_decide
-- prog_error_prop (executable form of the existential: the result is an error)
#eval Plausible.Testable.check (∀ n : Int, n < 0 → (prog n).toOption = none)
example : ((List.range 60).all fun k : Nat => (prog (-(k : Int) - 1)).toOption == none) = true := by
  native_decide
-- Post_prop (via the executable `postCheck`)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → postCheck n = true)
example : (List.range 400).all (fun n : Nat => postCheck n) = true := by native_decide

/-! ## Correctness: `Pre → Post` -/

theorem correctness (n : Int) (hpre : Pre n) :
    ∃ r, prog n = Except.ok r ∧ Post_prop n r := by
  have hn : (n.toNat : Int) = n := Int.toNat_of_nonneg hpre
  refine ⟨(sumDigits n.toNat : Int), prog_ok n hpre, ?_⟩
  have h1 : sumDigits n.toNat = (Nat.digits 10 n.toNat).sum := sumDigits_eq_digits_sum n.toNat
  have h2 : sumDigits n.toNat ≤ n.toNat := sumDigits_le n.toNat
  have h3 : sumDigits n.toNat % 9 = n.toNat % 9 := sumDigits_mod_nine n.toNat
  have h4 : sumDigits n.toNat = 0 ↔ n.toNat = 0 := sumDigits_eq_zero_iff n.toNat
  have h5 : n.toNat < 10 → sumDigits n.toNat = n.toNat := sumDigits_single_digit n.toNat
  unfold Post_prop
  refine ⟨by rw [h1], by omega, by omega, by omega, by omega, by omega⟩

/-- A violated precondition makes `prog` raise, as in the Python `ValueError`. -/
theorem correctness_error (n : Int) (hpre : ¬ Pre n) : ∃ msg, prog n = Except.error msg := by
  unfold Pre at hpre
  exact prog_error n (by omega)

/-! ## Imperative implementation -/

/-- Imperative digit sum: mutable `total` and `m`, mirroring the Python `while` loop.
The loop runs at most `n` times, which suffices since `n` has at most `n` digits. -/
def sumDigitsImp (n : Nat) : Nat := Id.run do
  if n = 0 then
    return 0
  let mut total : Nat := 0
  let mut m : Nat := n
  for _ in [0:n] do
    if m > 0 then
      total := total + m % 10
      m := m / 10
  return total

/-- Imperative Python entry point with the precondition check. -/
def progImp (n : Int) : Except String Int := Id.run do
  if n < 0 then
    return Except.error s!"Require non-negative integer (got n={n})"
  return Except.ok (sumDigitsImp n.toNat : Int)

/-! ## Imperative tests -/

example : sumDigitsImp 123 = 6 := by native_decide
example : sumDigitsImp 0 = 0 := by native_decide
example : sumDigitsImp 7 = 7 := by native_decide
example : sumDigitsImp 999 = 27 := by native_decide
example : (progImp 123).toOption = some 6 := by native_decide
example : (progImp 0).toOption = some 0 := by native_decide
example : (progImp (-1)).toOption = none := by native_decide
example : (List.range 400).all (fun n => sumDigitsImp n == sumDigits n) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, sumDigitsImp n = sumDigits n)
#eval sumDigitsImp 123   -- 6
#eval progImp (-1)       -- Except.error ...

/-! ## Equivalence: functional = imperative -/

/-- Specification of the `for` loop of `sumDigitsImp`: any body `f` behaving like one
iteration of the Python loop, run over a list of length at least `m`, produces the
state `⟨0, total + sumDigits m⟩`. -/
theorem loop_spec (f : Nat → MProd Nat Nat → Id (ForInStep (MProd Nat Nat)))
    (hf : ∀ i (s : MProd Nat Nat), f i s =
      if s.1 > 0 then pure (ForInStep.yield ⟨s.1 / 10, s.2 + s.1 % 10⟩)
      else pure (ForInStep.yield ⟨s.1, s.2⟩))
    (l : List Nat) : ∀ (m total : Nat), m ≤ l.length →
      forIn (m := Id) l ⟨m, total⟩ f = pure ⟨0, total + sumDigits m⟩ := by
  induction l with
  | nil =>
    intro m total hm
    have : m = 0 := by simpa using hm
    subst this
    rw [List.forIn_nil, sumDigits_zero, Nat.add_zero]
  | cons a l ih =>
    intro m total hm
    rw [List.forIn_cons, hf]
    by_cases hpos : m > 0
    · rw [if_pos hpos]
      simp only [pure_bind]
      rw [ih (m / 10) (total + m % 10) (by simp at hm; omega), sumDigits_pos m (by omega)]
      rw [Nat.add_assoc]
    · rw [if_neg hpos]
      simp only [pure_bind]
      have : m = 0 := by omega
      subst this
      exact ih 0 total (by simp)

theorem sumDigitsImp_eq_sumDigits (n : Nat) : sumDigitsImp n = sumDigits n := by
  by_cases h0 : n = 0
  · subst h0
    simp [sumDigitsImp, sumDigits_zero]
  · unfold sumDigitsImp
    simp only [h0, if_false]
    rw [Std.Range.forIn_eq_forIn_range']
    rw [loop_spec _ ?_ _ n 0 ?_]
    · simp
    · intro i s
      rfl
    · simp [Std.Range.size]

theorem progImp_eq_prog (n : Int) : progImp n = prog n := by
  unfold progImp prog
  by_cases h : n < 0
  · simp [h]
  · simp [h, sumDigitsImp_eq_sumDigits]

end «20_MySumDigits»

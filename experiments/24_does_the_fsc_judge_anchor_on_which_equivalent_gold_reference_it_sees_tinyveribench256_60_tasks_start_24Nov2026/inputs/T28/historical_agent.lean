import Mathlib
namespace Agent

/-!
# Safe passcode check (MIT 6.858 Lecture 9 — Mobile Device Security, iOS)

Translation of the Python program `20_unsafePasscodeCheck_safe.py`.

`safePasscodeCheck storedKey enteredKey attempts maxAttempts` validates a passcode
only when the attempt limit has not been reached: it returns `true` exactly when
`attempts < maxAttempts` **and** `storedKey = enteredKey`.  Once the attempt budget
is exhausted (`attempts ≥ maxAttempts`) every check returns `false` (lockout),
which prevents exhaustive brute-force guessing of a short passcode.

All four arguments are Python `int`s, so they are modelled with `Int`.
-/

namespace «20_unsafePasscodeCheck_safe»

/-! ## Functional implementation -/

/-- Safe passcode check: the attempt budget is checked *before* the passcode is
compared.  Locked out (`attempts ≥ maxAttempts`) ⇒ `false`; otherwise the result is
the passcode comparison. -/
def safePasscodeCheck (storedKey enteredKey attempts maxAttempts : Int) : Bool :=
  if attempts ≥ maxAttempts then
    false            -- locked out
  else
    storedKey == enteredKey

/-! ## Unit tests (mirroring `check` in the Python source) -/

-- 1) Correct passcode within budget
example : safePasscodeCheck 1234 1234 0 10 = true := by native_decide
-- 2) Wrong passcode
example : safePasscodeCheck 1234 9999 0 10 = false := by native_decide
-- 3) Correct passcode AFTER exhausting attempts → locked out
example : safePasscodeCheck 1234 1234 10 10 = false := by native_decide
-- 4) attempts = 9, max = 10 — still one try left, correct guess works
example : safePasscodeCheck 1234 1234 9 10 = true := by native_decide
-- 5) max_attempts = 0 — immediately locked
example : safePasscodeCheck 1234 1234 0 0 = false := by native_decide
-- 6) Wrong passcode always fails regardless of attempts
example : ([0, 1, 5] : List Int).all (fun a => safePasscodeCheck 1234 9999 a 10 == false) = true := by
  native_decide
-- 7) Correct passcode fails once locked
example : ([10, 11, 100] : List Int).all (fun a => safePasscodeCheck 1234 1234 a 10 == false) = true := by
  native_decide

#eval safePasscodeCheck 1234 1234 0 10   -- true
#eval safePasscodeCheck 1234 9999 0 10   -- false
#eval safePasscodeCheck 1234 1234 10 10  -- false
#eval safePasscodeCheck 1234 1234 9 10   -- true
#eval safePasscodeCheck 1234 1234 0 0    -- false

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- The Python function accepts arbitrary integers; there is no pre-condition. -/
def Pre (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  True

/-! ## Properties -/

/-- Lockout: once the attempt budget is exhausted the check returns `false`,
regardless of the entered value (even if it is correct). -/
def lockout_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  attempts ≥ maxAttempts → safePasscodeCheck storedKey enteredKey attempts maxAttempts = false

theorem lockout_thm (storedKey enteredKey attempts maxAttempts : Int) :
    lockout_prop storedKey enteredKey attempts maxAttempts := by
  intro h
  simp [safePasscodeCheck, h]

/-- A wrong passcode always fails, regardless of the attempt counters. -/
def wrong_key_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  storedKey ≠ enteredKey → safePasscodeCheck storedKey enteredKey attempts maxAttempts = false

theorem wrong_key_thm (storedKey enteredKey attempts maxAttempts : Int) :
    wrong_key_prop storedKey enteredKey attempts maxAttempts := by
  intro h
  unfold safePasscodeCheck
  split
  · rfl
  · simpa using h

/-- A correct passcode entered while budget remains is accepted. -/
def correct_within_budget_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  attempts < maxAttempts → storedKey = enteredKey →
    safePasscodeCheck storedKey enteredKey attempts maxAttempts = true

theorem correct_within_budget_thm (storedKey enteredKey attempts maxAttempts : Int) :
    correct_within_budget_prop storedKey enteredKey attempts maxAttempts := by
  intro hlt heq
  have hnot : ¬ (attempts ≥ maxAttempts) := by omega
  simp [safePasscodeCheck, hnot, heq]

/-- Exact characterisation: the check succeeds iff budget remains and the key matches. -/
def accept_iff_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  safePasscodeCheck storedKey enteredKey attempts maxAttempts = true ↔
    (attempts < maxAttempts ∧ storedKey = enteredKey)

theorem accept_iff_thm (storedKey enteredKey attempts maxAttempts : Int) :
    accept_iff_prop storedKey enteredKey attempts maxAttempts := by
  unfold accept_iff_prop safePasscodeCheck
  split
  · rename_i h
    simp
    omega
  · rename_i h
    simp
    omega

/-- Within the budget the check is exactly the passcode comparison
(the mitigation does not change behaviour for legitimate users). -/
def within_budget_is_compare_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  attempts < maxAttempts →
    safePasscodeCheck storedKey enteredKey attempts maxAttempts = (storedKey == enteredKey)

theorem within_budget_is_compare_thm (storedKey enteredKey attempts maxAttempts : Int) :
    within_budget_is_compare_prop storedKey enteredKey attempts maxAttempts := by
  intro hlt
  have hnot : ¬ (attempts ≥ maxAttempts) := by omega
  simp [safePasscodeCheck, hnot]

/-- Brute-force bound (anti-monotonicity in the attempt counter): if a check with
`attempts` succeeds, the same check with any smaller-or-equal counter also succeeds;
equivalently, failures due to lockout are permanent as attempts grow. -/
def antitone_attempts_prop (storedKey enteredKey attempts attempts' maxAttempts : Int) : Prop :=
  attempts' ≤ attempts →
    safePasscodeCheck storedKey enteredKey attempts maxAttempts = true →
    safePasscodeCheck storedKey enteredKey attempts' maxAttempts = true

theorem antitone_attempts_thm (storedKey enteredKey attempts attempts' maxAttempts : Int) :
    antitone_attempts_prop storedKey enteredKey attempts attempts' maxAttempts := by
  intro hle h
  have h1 := accept_iff_thm storedKey enteredKey attempts maxAttempts
  have h2 := accept_iff_thm storedKey enteredKey attempts' maxAttempts
  unfold accept_iff_prop at h1 h2
  have hh := h1.mp h
  exact h2.mpr ⟨by omega, hh.2⟩

/-- A non-positive budget (e.g. `max_attempts = 0`) locks everything out when
`attempts` is non-negative. -/
def zero_budget_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  0 ≤ attempts → maxAttempts ≤ 0 →
    safePasscodeCheck storedKey enteredKey attempts maxAttempts = false

theorem zero_budget_thm (storedKey enteredKey attempts maxAttempts : Int) :
    zero_budget_prop storedKey enteredKey attempts maxAttempts := by
  intro h0 hm
  exact lockout_thm storedKey enteredKey attempts maxAttempts (by omega)

/-! ## Post-condition -/

/-- Post-condition: conjunction of all stated properties. -/
def Post_prop (storedKey enteredKey attempts maxAttempts : Int) : Prop :=
  lockout_prop storedKey enteredKey attempts maxAttempts ∧
  wrong_key_prop storedKey enteredKey attempts maxAttempts ∧
  correct_within_budget_prop storedKey enteredKey attempts maxAttempts ∧
  accept_iff_prop storedKey enteredKey attempts maxAttempts ∧
  within_budget_is_compare_prop storedKey enteredKey attempts maxAttempts ∧
  zero_budget_prop storedKey enteredKey attempts maxAttempts ∧
  (∀ attempts' : Int, antitone_attempts_prop storedKey enteredKey attempts attempts' maxAttempts)

/-! ## Property-based tests -/

-- lockout_prop
#eval Plausible.Testable.check
  (∀ s e a m : Int, a ≥ m → safePasscodeCheck s e a m = false)

-- wrong_key_prop
#eval Plausible.Testable.check
  (∀ s e a m : Int, s ≠ e → safePasscodeCheck s e a m = false)

-- correct_within_budget_prop (stated with s = e substituted so samples are not wasted)
#eval Plausible.Testable.check
  (∀ s a m : Int, a < m → safePasscodeCheck s s a m = true)

-- accept_iff_prop
#eval Plausible.Testable.check
  (∀ s e a m : Int, (safePasscodeCheck s e a m = true) ↔ (a < m ∧ s = e))

-- within_budget_is_compare_prop
#eval Plausible.Testable.check
  (∀ s e a m : Int, a < m → safePasscodeCheck s e a m = (s == e))

-- antitone_attempts_prop
#eval Plausible.Testable.check
  (∀ s e a a' m : Int, a' ≤ a → safePasscodeCheck s e a m = true →
      safePasscodeCheck s e a' m = true)

-- zero_budget_prop
#eval Plausible.Testable.check
  (∀ s e a m : Int, 0 ≤ a → m ≤ 0 → safePasscodeCheck s e a m = false)

-- Post_prop (executable Boolean form of the conjunction, decided as a single Bool)
/-- Executable Boolean form of `Post_prop` (the antitone component is checked
separately below on a bounded grid of `attempts'`). -/
def postCheck (s e a m : Int) : Bool :=
  decide ((a ≥ m → safePasscodeCheck s e a m = false) ∧
    (s ≠ e → safePasscodeCheck s e a m = false) ∧
    (a < m → s = e → safePasscodeCheck s e a m = true) ∧
    ((safePasscodeCheck s e a m = true) ↔ (a < m ∧ s = e)) ∧
    (a < m → safePasscodeCheck s e a m = (s == e)) ∧
    (0 ≤ a → m ≤ 0 → safePasscodeCheck s e a m = false)) &&
  ((List.range 25).map (fun n => a + (n : Int) - 12)).all (fun a' =>
    decide (a' ≤ a → safePasscodeCheck s e a m = true → safePasscodeCheck s e a' m = true))

#eval Plausible.Testable.check (∀ s e a m : Int, postCheck s e a m = true)

-- Post_prop, bounded exhaustive grid (keys drawn from a small set incl. equal keys)
example :
    ([1234, 9999, 0, -5] : List Int).all (fun s =>
      ([1234, 9999, 0, -5] : List Int).all (fun e =>
        ((List.range 14).map (fun n => (n : Int) - 3)).all (fun a =>
          ((List.range 14).map (fun n => (n : Int) - 3)).all (fun m =>
            postCheck s e a m)))) = true := by
  native_decide

-- correct_within_budget_prop, bounded exhaustive grid
example :
    ((List.range 12).map (fun n => (n : Int) - 2)).all (fun a =>
      ((List.range 12).map (fun n => (n : Int) - 2)).all (fun m =>
        ([1234, 0, -7] : List Int).all (fun s =>
          decide (a < m → safePasscodeCheck s s a m = true)))) = true := by
  native_decide

-- zero_budget_prop, bounded exhaustive grid
example :
    ((List.range 12).map (fun n => (n : Int))).all (fun a =>
      ((List.range 12).map (fun n => (n : Int) - 11)).all (fun m =>
        ([1234, 9999] : List Int).all (fun e =>
          decide (0 ≤ a → m ≤ 0 → safePasscodeCheck 1234 e a m = false)))) = true := by
  native_decide

-- Bounded exhaustive PBTs over small grids (covers the implication-heavy properties
-- in case the randomized sampler gives up on them).
example :
    ((List.range 12).map (fun n => (n : Int))).all (fun a =>
      ((List.range 12).map (fun n => (n : Int))).all (fun m =>
        ([1234, 9999, 0, -1] : List Int).all (fun e =>
          (decide (safePasscodeCheck 1234 e a m = true ↔ (a < m ∧ (1234 : Int) = e))) &&
          (decide (a ≥ m → safePasscodeCheck 1234 e a m = false)) &&
          (decide ((1234 : Int) ≠ e → safePasscodeCheck 1234 e a m = false)) &&
          (decide (a < m → safePasscodeCheck 1234 e a m = ((1234 : Int) == e)))))) = true := by
  native_decide

example :
    ((List.range 15).map (fun n => (n : Int) - 3)).all (fun a =>
      ((List.range 15).map (fun n => (n : Int) - 3)).all (fun a' =>
        ((List.range 8).map (fun n => (n : Int))).all (fun m =>
          decide (a' ≤ a → safePasscodeCheck 7 7 a m = true → safePasscodeCheck 7 7 a' m = true))))
      = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (storedKey enteredKey attempts maxAttempts : Int) :
    Pre storedKey enteredKey attempts maxAttempts →
    Post_prop storedKey enteredKey attempts maxAttempts := by
  intro _
  refine ⟨lockout_thm _ _ _ _, wrong_key_thm _ _ _ _, correct_within_budget_thm _ _ _ _,
    accept_iff_thm _ _ _ _, within_budget_is_compare_thm _ _ _ _, zero_budget_thm _ _ _ _, ?_⟩
  intro attempts'
  exact antitone_attempts_thm storedKey enteredKey attempts attempts' maxAttempts

/-! ## Imperative implementation -/

/-- Imperative version mirroring the Python control flow: early-return on lockout,
then a mutable result set by the passcode comparison. -/
def safePasscodeCheckImp (storedKey enteredKey attempts maxAttempts : Int) : Bool := Id.run do
  let mut result : Bool := false
  if attempts ≥ maxAttempts then
    return false   -- locked out
  if storedKey == enteredKey then
    result := true
  return result

/-! ## Imperative tests -/

example : safePasscodeCheckImp 1234 1234 0 10 = true := by native_decide
example : safePasscodeCheckImp 1234 9999 0 10 = false := by native_decide
example : safePasscodeCheckImp 1234 1234 10 10 = false := by native_decide
example : safePasscodeCheckImp 1234 1234 9 10 = true := by native_decide
example : safePasscodeCheckImp 1234 1234 0 0 = false := by native_decide
example : ([0, 1, 5] : List Int).all (fun a => safePasscodeCheckImp 1234 9999 a 10 == false) = true := by
  native_decide
example : ([10, 11, 100] : List Int).all (fun a => safePasscodeCheckImp 1234 1234 a 10 == false) = true := by
  native_decide

#eval safePasscodeCheckImp 1234 1234 0 10   -- true
#eval safePasscodeCheckImp 1234 1234 10 10  -- false

#eval Plausible.Testable.check
  (∀ s e a m : Int, safePasscodeCheck s e a m = safePasscodeCheckImp s e a m)

/-! ## Equivalence theorem -/

theorem functional_imperative_equiv_thm (storedKey enteredKey attempts maxAttempts : Int) :
    safePasscodeCheck storedKey enteredKey attempts maxAttempts =
    safePasscodeCheckImp storedKey enteredKey attempts maxAttempts := by
  unfold safePasscodeCheck safePasscodeCheckImp
  split
  · simp
  · by_cases h : storedKey = enteredKey
    · simp [h]
    · simp [h]

end «20_unsafePasscodeCheck_safe»
end Agent

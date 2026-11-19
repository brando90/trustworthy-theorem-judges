/-!
# Safe passcode check

This file translates `safe_passcode_check` from a Python teaching model for MIT 6.858 into Lean 4.

The function returns `true` exactly when `attempts < maxAttempts` and `storedKey = enteredKey`.
The caller supplies the attempt counts. The function does not update them, and Lean functions
are pure, so there is no lockout state to maintain. The arguments are `Int`, so negative
attempt counts are compared directly.
-/

namespace SafePasscode

/-- Return `true` exactly when `attempts < maxAttempts` and `storedKey = enteredKey`. -/
def safePasscodeCheck (storedKey enteredKey attempts maxAttempts : Int) : Bool :=
  if attempts ≥ maxAttempts then
    false -- locked out
  else
    storedKey == enteredKey

/-- Run the fixed examples. Python raises `AssertionError` on a mismatch; this version
returns `false` instead. -/
def check (candidate : Int → Int → Int → Int → Bool) : Bool :=
  candidate 1234 1234 0 10 == true &&
  candidate 1234 1234 9 10 == true &&
  candidate 1234 1234 0 0 == false &&
  candidate 1234 9999 0 10 == false &&
  candidate 1234 1234 10 10 == false

def main : IO Unit := do
  unless check safePasscodeCheck do
    throw <| IO.userError "Failed: SafePasscode.check"
  IO.println "All tests passed."

/-! ## Fixed examples -/

theorem check_safePasscodeCheck : check safePasscodeCheck = true := by decide

example : safePasscodeCheck 1234 1234 0 10 = true := by decide
example : safePasscodeCheck 1234 1234 9 10 = true := by decide
example : safePasscodeCheck 1234 1234 0 0 = false := by decide
example : safePasscodeCheck 1234 9999 0 10 = false := by decide
example : safePasscodeCheck 1234 1234 10 10 = false := by decide

-- Negative attempt counts are compared directly.
example : safePasscodeCheck 7 7 (-3) (-1) = true := by decide
example : safePasscodeCheck 7 7 (-1) (-3) = false := by decide

/-! ## Helper lemma -/

/-- Two booleans are equal if they are `true` under the same conditions. -/
theorem bool_eq_of_iff {x y : Bool} (h : x = true ↔ y = true) : x = y := by
  cases x <;> cases y
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-! ## Specification -/

/-- Main specification: the check succeeds exactly when the attempt count is below the limit
and the keys match. -/
theorem safePasscodeCheck_eq_true_iff (s e a m : Int) :
    safePasscodeCheck s e a m = true ↔ a < m ∧ s = e := by
  unfold safePasscodeCheck
  by_cases h : a ≥ m
  · rw [if_pos h]
    constructor
    · intro hf
      cases hf
    · intro ⟨hlt, _⟩
      exact absurd hlt (by omega)
  · rw [if_neg h]
    constructor
    · intro hb
      exact ⟨by omega, beq_iff_eq.mp hb⟩
    · intro ⟨_, hs⟩
      exact beq_iff_eq.mpr hs

/-- The same specification, written as a boolean expression. -/
theorem safePasscodeCheck_eq_and (s e a m : Int) :
    safePasscodeCheck s e a m = (decide (a < m) && (s == e)) := by
  apply bool_eq_of_iff
  simp [safePasscodeCheck_eq_true_iff]

/-- Lockout: once `attempts ≥ maxAttempts`, every key is rejected, including the correct one. -/
theorem safePasscodeCheck_locked_out (s e a m : Int) (h : a ≥ m) :
    safePasscodeCheck s e a m = false := by
  unfold safePasscodeCheck
  rw [if_pos h]

/-- A limit of zero rejects every nonnegative attempt count. -/
theorem safePasscodeCheck_zero_limit (s e a : Int) (h : a ≥ 0) :
    safePasscodeCheck s e a 0 = false :=
  safePasscodeCheck_locked_out s e a 0 h

/-- A wrong key is always rejected, whatever the attempt count. -/
theorem safePasscodeCheck_wrong_key (s e a m : Int) (h : s ≠ e) :
    safePasscodeCheck s e a m = false := by
  cases hc : safePasscodeCheck s e a m with
  | false => rfl
  | true => exact absurd ((safePasscodeCheck_eq_true_iff s e a m).mp hc).2 h

/-- The correct key is accepted whenever the attempt count is below the limit. -/
theorem safePasscodeCheck_correct_key (k a m : Int) (h : a < m) :
    safePasscodeCheck k k a m = true :=
  (safePasscodeCheck_eq_true_iff k k a m).mpr ⟨h, rfl⟩

/-- Accepting a key does not depend on which argument holds the stored key. -/
theorem safePasscodeCheck_key_symm (s e a m : Int) :
    safePasscodeCheck s e a m = safePasscodeCheck e s a m := by
  apply bool_eq_of_iff
  rw [safePasscodeCheck_eq_true_iff, safePasscodeCheck_eq_true_iff]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, h2.symm⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, h2.symm⟩

/-- Fewer attempts never turn a success into a failure. -/
theorem safePasscodeCheck_antitone_attempts (s e a a' m : Int) (ha : a' ≤ a)
    (h : safePasscodeCheck s e a m = true) : safePasscodeCheck s e a' m = true := by
  obtain ⟨hlt, hs⟩ := (safePasscodeCheck_eq_true_iff s e a m).mp h
  exact (safePasscodeCheck_eq_true_iff s e a' m).mpr ⟨by omega, hs⟩

/-- Lockout persists: more attempts never undo a lockout. -/
theorem safePasscodeCheck_lockout_persists (s e a a' m : Int) (ha : a ≤ a') (h : a ≥ m) :
    safePasscodeCheck s e a' m = false :=
  safePasscodeCheck_locked_out s e a' m (by omega)

/-- Raising the limit never turns a success into a failure. -/
theorem safePasscodeCheck_mono_max (s e a m m' : Int) (hm : m ≤ m')
    (h : safePasscodeCheck s e a m = true) : safePasscodeCheck s e a m' = true := by
  obtain ⟨hlt, hs⟩ := (safePasscodeCheck_eq_true_iff s e a m).mp h
  exact (safePasscodeCheck_eq_true_iff s e a m').mpr ⟨by omega, hs⟩

end SafePasscode

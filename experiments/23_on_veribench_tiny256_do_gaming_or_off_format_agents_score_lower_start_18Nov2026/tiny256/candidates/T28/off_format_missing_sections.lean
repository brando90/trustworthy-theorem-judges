import Mathlib

def safePasscodeCheck (storedKey enteredKey attempts maxAttempts : Nat) : Bool :=
  if attempts < maxAttempts then storedKey == enteredKey else false

example : safePasscodeCheck 1234 1234 0 10 = true := by native_decide

example : safePasscodeCheck 1234 1234 10 10 = false := by native_decide

example : safePasscodeCheck 1234 1234 9 10 = true := by native_decide

example : safePasscodeCheck 1234 1234 0 0 = false := by native_decide

example : safePasscodeCheck 42 42 0 5 = true := by native_decide

example : safePasscodeCheck 42 42 4 5 = true := by native_decide

example : safePasscodeCheck 42 42 5 5 = false := by native_decide

example : safePasscodeCheck 42 99 0 10 = false := by native_decide

theorem safePasscodeCheck_locked_when_exhausted
    (storedKey enteredKey attempts maxAttempts : Nat) :
    attempts ≥ maxAttempts →
    safePasscodeCheck storedKey enteredKey attempts maxAttempts = false := by
  intro h
  simp [safePasscodeCheck, if_neg (Nat.not_lt.mpr h)]

theorem safePasscodeCheck_accepts_match_within_budget
    (storedKey attempts maxAttempts : Nat) :
    attempts < maxAttempts →
    safePasscodeCheck storedKey storedKey attempts maxAttempts = true := by
  intro h
  simp [safePasscodeCheck, if_pos h]

theorem safePasscodeCheck_rejects_wrong_key
    (storedKey enteredKey attempts maxAttempts : Nat) :
    storedKey ≠ enteredKey →
    safePasscodeCheck storedKey enteredKey attempts maxAttempts = false := by
  intro hne
  simp only [safePasscodeCheck]
  by_cases h : attempts < maxAttempts
  · simp [if_pos h, hne]
  · simp [if_neg h]

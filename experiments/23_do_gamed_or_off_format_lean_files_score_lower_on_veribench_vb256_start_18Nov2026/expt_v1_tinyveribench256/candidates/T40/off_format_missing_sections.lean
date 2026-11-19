import Mathlib

namespace SafeRSABlinding

def safeBlindingApplied (_message : Nat) (_d : Nat) (n : Nat) : Bool :=
  1 < n

example : safeBlindingApplied 2 3 35 = true := by native_decide

example : safeBlindingApplied 0 0 1 = false := by native_decide

example : safeBlindingApplied 0 3 2 = true := by native_decide

example : safeBlindingApplied 5 7 0 = false := by native_decide

example : safeBlindingApplied 7 65537 3233 = true := by native_decide

example : safeBlindingApplied 5 7 11 = true := by native_decide

example : safeBlindingApplied 5 7 1 = false := by native_decide

example : safeBlindingApplied 100 17 0 = false := by native_decide

theorem safeBlindingApplied_true_of_one_lt (message d n : Nat) (h : 1 < n) :
    safeBlindingApplied message d n = true := by
  simp [safeBlindingApplied, h]

theorem safeBlindingApplied_false_of_le_one (message d n : Nat) (h : n ≤ 1) :
    safeBlindingApplied message d n = false := by
  simp [safeBlindingApplied, Nat.not_lt.mpr h]

theorem safeBlindingApplied_true_of_valid_input (message d n : Nat)
    (h : 1 < n ∧ message < n) :
    safeBlindingApplied message d n = true := by
  obtain ⟨hn, _⟩ := h
  simp [safeBlindingApplied, hn]

end SafeRSABlinding

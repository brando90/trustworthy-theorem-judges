import Mathlib

namespace SafeUpdateAccept

def safeUpdateAccept (newVer curVer : Nat) : Bool :=
  newVer > curVer

example : safeUpdateAccept 5 3 = true := by native_decide
example : safeUpdateAccept 1 5 = false := by native_decide
example : safeUpdateAccept 3 3 = false := by native_decide
example : safeUpdateAccept 1 0 = true := by native_decide
example : safeUpdateAccept 100 1 = true := by native_decide
example : safeUpdateAccept 2 1 = true := by native_decide
example : safeUpdateAccept 0 10 = false := by native_decide
example : safeUpdateAccept 9 10 = false := by native_decide

theorem safeUpdateAccept_true_iff (newVer curVer : Nat) :
    safeUpdateAccept newVer curVer = true ↔ newVer > curVer := by
  simp [safeUpdateAccept]

theorem safeUpdateAccept_rejects_rollback (newVer curVer : Nat)
    (h : newVer < curVer) :
    safeUpdateAccept newVer curVer = false := by
  simp [safeUpdateAccept]
  omega

theorem safeUpdateAccept_rejects_same (ver : Nat) :
    safeUpdateAccept ver ver = false := by
  simp [safeUpdateAccept]

end SafeUpdateAccept

import Mathlib

namespace SafeCertChain

def safeCertChain (caSignature : Nat) : Bool :=
  caSignature != 0

example : safeCertChain 42 = true := by native_decide

example : safeCertChain 0 = false := by native_decide

example : safeCertChain 1 = true := by native_decide

example : safeCertChain 99999 = true := by native_decide

example : safeCertChain 100 = true := by native_decide

theorem safeCertChain_true_of_ne_zero (caSignature : Nat) :
    caSignature ≠ 0 → safeCertChain caSignature = true := by
  intro hne
  simp [safeCertChain, hne]

theorem safeCertChain_false_of_eq_zero (caSignature : Nat) :
    caSignature = 0 → safeCertChain caSignature = false := by
  intro h
  subst h
  simp [safeCertChain]

theorem safeCertChain_eq_true_iff (caSignature : Nat) :
    safeCertChain caSignature = true ↔ caSignature ≠ 0 := by
  simp [safeCertChain, bne_iff_ne]

end SafeCertChain

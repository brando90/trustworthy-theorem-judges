import Mathlib

namespace Gold

namespace UnsafeHMACLength

def unsafeHMACVerify (_messageLen _macLen _expectedMacLen : Nat) : Bool :=
  true

example : unsafeHMACVerify 10 32 32 = true := by native_decide
example : unsafeHMACVerify 10 64 32 = true := by native_decide
example : unsafeHMACVerify 10 0 32 = true := by native_decide
example : unsafeHMACVerify 0 0 32 = true := by native_decide
example : unsafeHMACVerify 10 128 32 = true := by native_decide
example : unsafeHMACVerify 0 0 0 = true := by native_decide

theorem unsafeHMACVerify_always_true (messageLen macLen expectedMacLen : Nat) :
    unsafeHMACVerify messageLen macLen expectedMacLen = true := by
  simp [unsafeHMACVerify]

theorem unsafeHMACVerify_exists_wrong_length_accepted :
    ∃ macLen expectedMacLen : Nat,
      macLen ≠ expectedMacLen ∧ unsafeHMACVerify 10 macLen expectedMacLen = true :=
  ⟨0, 1, by omega, by simp [unsafeHMACVerify]⟩

theorem unsafeHMACVerify_mismatch_accepted (macLen expectedMacLen : Nat)
    (_h : macLen ≠ expectedMacLen) :
    unsafeHMACVerify 10 macLen expectedMacLen = true := by
  simp [unsafeHMACVerify]

example (messageLen macLen expectedMacLen : Nat) (_h : macLen ≠ expectedMacLen) :
    unsafeHMACVerify messageLen macLen expectedMacLen = true ∧
    (∃ m e : Nat, m ≠ e ∧ unsafeHMACVerify 10 m e = true) ∧
    (macLen ≠ expectedMacLen → unsafeHMACVerify 10 macLen expectedMacLen = true) :=
  ⟨unsafeHMACVerify_always_true messageLen macLen expectedMacLen,
   unsafeHMACVerify_exists_wrong_length_accepted,
   unsafeHMACVerify_mismatch_accepted macLen expectedMacLen⟩

end UnsafeHMACLength

end Gold

import Mathlib

/-!
# Safe TPM PCR hash check

This file formalizes the Python PCR-extension check.  Python integers are modeled
by `Int`; `Int.xor` and `Int.land` therefore also give the source program's
two's-complement behavior on negative inputs.  The simulated hash is the low
32 bits of an affine mix of the old PCR and the new data.
-/

namespace UnsafeTPMHashSafe125

def multiplier : Int := 6364136223846793005

def increment : Int := 1442695040888963407

def mask32 : Int := 0xFFFFFFFF

def simulatedHash (oldPcr newData : Int) : Int :=
  Int.land (Int.xor oldPcr newData * multiplier + increment) mask32

def safeTpmHashCheck (oldPcr newData claimedPcr : Int) : Bool :=
  claimedPcr == simulatedHash oldPcr newData

def expected0 : Int := simulatedHash 0xAAAA 0xBBBB

def expectedZero : Int := simulatedHash 0 0

example : safeTpmHashCheck 0xAAAA 0xBBBB expected0 = true := by
  native_decide

example : safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide

example : safeTpmHashCheck 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide

example : safeTpmHashCheck 0 0 expectedZero = true := by
  native_decide

#eval expected0
#eval expectedZero
#eval safeTpmHashCheck 0xAAAA 0xBBBB expected0
#eval safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD
#eval safeTpmHashCheck 0xAAAA 0xBBBB 0x1234
#eval safeTpmHashCheck 0 0 expectedZero

def Pre (_oldPcr _newData _claimedPcr : Int) : Prop := True

def exactMatch_prop (oldPcr newData claimedPcr : Int) : Prop :=
  safeTpmHashCheck oldPcr newData claimedPcr = true ↔
    claimedPcr = simulatedHash oldPcr newData

theorem exactMatch_thm (oldPcr newData claimedPcr : Int) :
    exactMatch_prop oldPcr newData claimedPcr := by
  simp [exactMatch_prop, safeTpmHashCheck]

def correctClaimAccepted_prop (oldPcr newData : Int) : Prop :=
  safeTpmHashCheck oldPcr newData (simulatedHash oldPcr newData) = true

theorem correctClaimAccepted_thm (oldPcr newData : Int) :
    correctClaimAccepted_prop oldPcr newData := by
  simp [correctClaimAccepted_prop, safeTpmHashCheck]

def forgedClaimRejected_prop (oldPcr newData claimedPcr : Int) : Prop :=
  claimedPcr ≠ simulatedHash oldPcr newData →
    safeTpmHashCheck oldPcr newData claimedPcr = false

theorem forgedClaimRejected_thm (oldPcr newData claimedPcr : Int) :
    forgedClaimRejected_prop oldPcr newData claimedPcr := by
  simp [forgedClaimRejected_prop, safeTpmHashCheck]

def Post_prop (oldPcr newData claimedPcr : Int) : Prop :=
  exactMatch_prop oldPcr newData claimedPcr ∧
    correctClaimAccepted_prop oldPcr newData ∧
    forgedClaimRejected_prop oldPcr newData claimedPcr

theorem safeTpmHashCheck_correct (oldPcr newData claimedPcr : Int) :
    Pre oldPcr newData claimedPcr → Post_prop oldPcr newData claimedPcr := by
  intro _
  exact ⟨exactMatch_thm oldPcr newData claimedPcr,
    correctClaimAccepted_thm oldPcr newData,
    forgedClaimRejected_thm oldPcr newData claimedPcr⟩

def safeTpmHashCheckImperative (oldPcr newData claimedPcr : Int) : Bool := Id.run do
  let mut hash : Int := 0
  hash := Int.land (Int.xor oldPcr newData * multiplier + increment) mask32
  return claimedPcr == hash

example : safeTpmHashCheckImperative 0xAAAA 0xBBBB expected0 = true := by
  native_decide

example : safeTpmHashCheckImperative 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide

example : safeTpmHashCheckImperative 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide

example : safeTpmHashCheckImperative 0 0 expectedZero = true := by
  native_decide

#eval safeTpmHashCheckImperative 0xAAAA 0xBBBB expected0
#eval safeTpmHashCheckImperative 0xAAAA 0xBBBB 0xDEAD
#eval safeTpmHashCheckImperative 0xAAAA 0xBBBB 0x1234
#eval safeTpmHashCheckImperative 0 0 expectedZero

theorem functional_eq_imperative (oldPcr newData claimedPcr : Int) :
    safeTpmHashCheck oldPcr newData claimedPcr =
      safeTpmHashCheckImperative oldPcr newData claimedPcr := by
  rfl

end UnsafeTPMHashSafe125

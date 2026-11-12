import Mathlib

namespace SafeTpmHashCheck

/-- Simulated TPM extend: `H(old_pcr || new_data)` modelled as a mixing function,
    truncated to 32 bits (Python: `((old ^ new) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF`). -/
def simulatedHash (oldPcr newData : Nat) : Nat :=
  ((oldPcr ^^^ newData) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

/-- Returns `true` only when `claimedPcr` equals the correctly computed hash. -/
def safeTpmHashCheck (oldPcr newData claimedPcr : Nat) : Bool :=
  claimedPcr == simulatedHash oldPcr newData

/-! ### Concrete tests mirroring `check()` -/

example : safeTpmHashCheck 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true := by native_decide
example : safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safeTpmHashCheck 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safeTpmHashCheck 0 0 (simulatedHash 0 0) = true := by native_decide
example : simulatedHash 0 0 = 1442695040888963407 &&& 0xFFFFFFFF := by native_decide

/-! ### Specification -/

/-- No precondition: the function is total on all naturals. -/
def Pre (_oldPcr _newData _claimedPcr : Nat) : Prop := True

/-- The check succeeds exactly on the correctly computed PCR value. -/
def sound_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData claimedPcr = true ↔ claimedPcr = simulatedHash oldPcr newData

/-- The genuine, correctly-extended PCR value is always accepted. -/
def accepts_correct_prop (oldPcr newData : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData (simulatedHash oldPcr newData) = true

/-- Any claimed PCR that is not the correct hash is rejected (no forgery). -/
def rejects_forgery_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  claimedPcr ≠ simulatedHash oldPcr newData → safeTpmHashCheck oldPcr newData claimedPcr = false

/-- At most one claimed value can be accepted for a given `(oldPcr, newData)`. -/
def unique_accept_prop (oldPcr newData c₁ c₂ : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData c₁ = true → safeTpmHashCheck oldPcr newData c₂ = true → c₁ = c₂

/-- The simulated PCR is a 32-bit value. -/
def bounded_prop (oldPcr newData : Nat) : Prop := simulatedHash oldPcr newData < 2 ^ 32

theorem sound_thm (oldPcr newData claimedPcr : Nat) : sound_prop oldPcr newData claimedPcr := by
  unfold sound_prop safeTpmHashCheck
  exact beq_iff_eq

theorem accepts_correct_thm (oldPcr newData : Nat) : accepts_correct_prop oldPcr newData := by
  unfold accepts_correct_prop safeTpmHashCheck
  exact beq_self_eq_true _

theorem rejects_forgery_thm (oldPcr newData claimedPcr : Nat) :
    rejects_forgery_prop oldPcr newData claimedPcr := by
  unfold rejects_forgery_prop safeTpmHashCheck
  intro h
  first
    | exact beq_eq_false_iff_ne.mpr h
    | simp [h]

theorem unique_accept_thm (oldPcr newData c₁ c₂ : Nat) :
    unique_accept_prop oldPcr newData c₁ c₂ := by
  unfold unique_accept_prop safeTpmHashCheck
  intro h₁ h₂
  have e₁ : c₁ = simulatedHash oldPcr newData := by
    exact beq_iff_eq.mp h₁
  have e₂ : c₂ = simulatedHash oldPcr newData := by
    exact beq_iff_eq.mp h₂
  rw [e₁, e₂]

theorem bounded_thm (oldPcr newData : Nat) : bounded_prop oldPcr newData := by
  unfold bounded_prop simulatedHash
  first
    | exact Nat.and_lt_two_pow _ (by norm_num)
    | exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
    | exact lt_of_le_of_lt (Nat.and_le_right _ _) (by norm_num)

def Post (oldPcr newData claimedPcr : Nat) : Prop :=
  sound_prop oldPcr newData claimedPcr ∧
  accepts_correct_prop oldPcr newData ∧
  rejects_forgery_prop oldPcr newData claimedPcr ∧
  (∀ c₂, unique_accept_prop oldPcr newData claimedPcr c₂) ∧
  bounded_prop oldPcr newData

theorem correctness (oldPcr newData claimedPcr : Nat) :
    Pre oldPcr newData claimedPcr → Post oldPcr newData claimedPcr := by
  intro _
  refine ⟨sound_thm oldPcr newData claimedPcr, accepts_correct_thm oldPcr newData,
    rejects_forgery_thm oldPcr newData claimedPcr, ?_, bounded_thm oldPcr newData⟩
  intro c₂
  exact unique_accept_thm oldPcr newData claimedPcr c₂

end SafeTpmHashCheck
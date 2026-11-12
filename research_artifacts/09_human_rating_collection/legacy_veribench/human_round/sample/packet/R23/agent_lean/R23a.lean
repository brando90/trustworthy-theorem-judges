import Mathlib

/-!
# Safe TPM PCR check

Lean 4 formalization of a Python program that validates a *claimed* TPM PCR value
against the correctly recomputed extend hash.

The Python program simulates the TPM `extend` operation
`H(old_pcr || new_data)` with a 32-bit mixing function

```python
simulated_hash = ((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF
return claimed_pcr == simulated_hash
```

Unlike the vulnerable variant (MIT 6.858 Fall 2011 Quiz 2, where a preimage-vulnerable
hash lets an attacker forge a PCR and extract the disk key), this *safe* version accepts
a claimed PCR **only** when it is bit-for-bit equal to the recomputed value.

The file contains:
* the functional implementation (`simHash`, `safeTpmHashCheck`),
* unit tests mirroring the Python `check()` function,
* a pre-condition, the individual correctness properties with their proofs,
* the post-condition and the `Pre → Post` correctness theorem,
* an imperative (`Id.run do`) implementation with mutable state, and
* the equivalence theorem between the functional and imperative versions.
-/

namespace UnsafeTPMHashSafe

/-! ## Implementation -/

/-- The 64-bit LCG multiplier used by the mixing function. -/
def mult : Nat := 6364136223846793005

/-- The 64-bit LCG increment used by the mixing function. -/
def incr : Nat := 1442695040888963407

/-- The 32-bit mask `0xFFFFFFFF`. -/
def mask : Nat := 0xFFFFFFFF

/-- Simulated TPM extend: `H(old_pcr || new_data)` modelled as XOR + LCG mixing,
truncated to 32 bits. -/
def simHash (oldPcr newData : Nat) : Nat :=
  ((oldPcr ^^^ newData) * mult + incr) &&& mask

/-- Returns `true` only when `claimedPcr` equals the simulated `H(old_pcr || new_data)`. -/
def safeTpmHashCheck (oldPcr newData claimedPcr : Nat) : Bool :=
  claimedPcr == simHash oldPcr newData

/-! ## Unit tests (mirroring the Python `check()` function) -/

#eval simHash 0xAAAA 0xBBBB          -- 4207341644
#eval simHash 0 0                    -- 4150755663
#eval safeTpmHashCheck 0xAAAA 0xBBBB 4207341644
#eval safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD

/-- The correct PCR is accepted. -/
example : safeTpmHashCheck 0xAAAA 0xBBBB (simHash 0xAAAA 0xBBBB) = true := by native_decide

/-- The correct PCR, given by its literal value. -/
example : safeTpmHashCheck 0xAAAA 0xBBBB 4207341644 = true := by native_decide

/-- A forged PCR is rejected. -/
example : safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD = false := by native_decide

/-- An arbitrary PCR is rejected. -/
example : safeTpmHashCheck 0xAAAA 0xBBBB 0x1234 = false := by native_decide

/-- The zero case: the correct PCR is accepted. -/
example : safeTpmHashCheck 0 0 (simHash 0 0) = true := by native_decide

/-- The zero case, given by its literal value. -/
example : safeTpmHashCheck 0 0 4150755663 = true := by native_decide

/-! ## Pre-condition -/

/-- The Python function is total on non-negative machine integers; there is no
restriction on the inputs beyond their being natural numbers. -/
def Pre (_oldPcr _newData _claimedPcr : Nat) : Prop := True

/-! ## Properties -/

/-- **Completeness / no false rejection**: recomputing the hash and offering it as the
claimed PCR always succeeds. -/
def accepts_correct_prop (oldPcr newData : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData (simHash oldPcr newData) = true

theorem accepts_correct_thm (oldPcr newData : Nat) :
    accepts_correct_prop oldPcr newData := by
  simp [accepts_correct_prop, safeTpmHashCheck]

/-- **Soundness / unforgeability**: any claimed PCR different from the recomputed hash
is rejected. -/
def rejects_forged_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  claimedPcr ≠ simHash oldPcr newData → safeTpmHashCheck oldPcr newData claimedPcr = false

theorem rejects_forged_thm (oldPcr newData claimedPcr : Nat) :
    rejects_forged_prop oldPcr newData claimedPcr := by
  intro h
  simp [safeTpmHashCheck, h]

/-- **Characterization**: the check succeeds *exactly* on the recomputed hash. -/
def check_iff_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData claimedPcr = true ↔ claimedPcr = simHash oldPcr newData

theorem check_iff_thm (oldPcr newData claimedPcr : Nat) :
    check_iff_prop oldPcr newData claimedPcr := by
  simp [check_iff_prop, safeTpmHashCheck]

/-- **Uniqueness**: at most one claimed value is accepted for a given `(old, new)` pair. -/
def unique_accept_prop (oldPcr newData c₁ c₂ : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData c₁ = true →
    safeTpmHashCheck oldPcr newData c₂ = true → c₁ = c₂

theorem unique_accept_thm (oldPcr newData c₁ c₂ : Nat) :
    unique_accept_prop oldPcr newData c₁ c₂ := by
  intro h₁ h₂
  simp [safeTpmHashCheck] at h₁ h₂
  omega

/-- **32-bit range**: the simulated hash always fits in 32 bits, because of the mask. -/
def hash_range_prop (oldPcr newData : Nat) : Prop :=
  simHash oldPcr newData < 2 ^ 32

theorem hash_range_thm (oldPcr newData : Nat) : hash_range_prop oldPcr newData := by
  have h : simHash oldPcr newData ≤ mask := Nat.and_le_right
  simp only [mask] at h
  show simHash oldPcr newData < 2 ^ 32
  have h2 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  omega

/-- **Rejection above the 32-bit range**: a claimed PCR that does not fit in 32 bits can
never be accepted. -/
def rejects_out_of_range_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  2 ^ 32 ≤ claimedPcr → safeTpmHashCheck oldPcr newData claimedPcr = false

theorem rejects_out_of_range_thm (oldPcr newData claimedPcr : Nat) :
    rejects_out_of_range_prop oldPcr newData claimedPcr := by
  intro h
  have hlt : simHash oldPcr newData < 2 ^ 32 := hash_range_thm oldPcr newData
  have h2 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hne : claimedPcr ≠ simHash oldPcr newData := by omega
  exact rejects_forged_thm oldPcr newData claimedPcr hne

/-- **Determinism**: the check depends only on its three arguments. -/
def deterministic_prop (o₁ n₁ c₁ o₂ n₂ c₂ : Nat) : Prop :=
  o₁ = o₂ → n₁ = n₂ → c₁ = c₂ →
    safeTpmHashCheck o₁ n₁ c₁ = safeTpmHashCheck o₂ n₂ c₂

theorem deterministic_thm (o₁ n₁ c₁ o₂ n₂ c₂ : Nat) :
    deterministic_prop o₁ n₁ c₁ o₂ n₂ c₂ := by
  intro h₁ h₂ h₃
  subst h₁; subst h₂; subst h₃; rfl

/-- **Symmetry of the mixing input**: the extend simulation mixes `old_pcr` and
`new_data` through XOR, hence swapping them yields the same hash. -/
def hash_comm_prop (oldPcr newData : Nat) : Prop :=
  simHash oldPcr newData = simHash newData oldPcr

theorem hash_comm_thm (oldPcr newData : Nat) : hash_comm_prop oldPcr newData := by
  simp [hash_comm_prop, simHash, Nat.xor_comm]

/-! ## Post-condition -/

/-- The full post-condition: the conjunction of all the specified properties. -/
def Post_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  accepts_correct_prop oldPcr newData ∧
  rejects_forged_prop oldPcr newData claimedPcr ∧
  check_iff_prop oldPcr newData claimedPcr ∧
  hash_range_prop oldPcr newData ∧
  rejects_out_of_range_prop oldPcr newData claimedPcr ∧
  hash_comm_prop oldPcr newData

/-! ## Correctness theorem -/

theorem correctness_thm (oldPcr newData claimedPcr : Nat)
    (_h : Pre oldPcr newData claimedPcr) : Post_prop oldPcr newData claimedPcr :=
  ⟨accepts_correct_thm oldPcr newData,
   rejects_forged_thm oldPcr newData claimedPcr,
   check_iff_thm oldPcr newData claimedPcr,
   hash_range_thm oldPcr newData,
   rejects_out_of_range_thm oldPcr newData claimedPcr,
   hash_comm_thm oldPcr newData⟩

/-! ## Imperative implementation -/

/-- Step-by-step imperative rendering of the mixing function with mutable state. -/
def safeTpmHashCheckImp (oldPcr newData claimedPcr : Nat) : Bool := Id.run do
  let mut acc : Nat := oldPcr ^^^ newData
  acc := acc * mult
  acc := acc + incr
  acc := acc &&& mask
  let mut result : Bool := false
  if claimedPcr == acc then
    result := true
  return result

/-! ## Imperative tests -/

#eval safeTpmHashCheckImp 0xAAAA 0xBBBB 4207341644
#eval safeTpmHashCheckImp 0 0 4150755663

example : safeTpmHashCheckImp 0xAAAA 0xBBBB 4207341644 = true := by native_decide
example : safeTpmHashCheckImp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safeTpmHashCheckImp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safeTpmHashCheckImp 0 0 4150755663 = true := by native_decide

/-! ## Equivalence of the functional and imperative implementations -/

def equiv_prop (oldPcr newData claimedPcr : Nat) : Prop :=
  safeTpmHashCheck oldPcr newData claimedPcr = safeTpmHashCheckImp oldPcr newData claimedPcr

theorem equiv_thm (oldPcr newData claimedPcr : Nat) :
    equiv_prop oldPcr newData claimedPcr := by
  unfold equiv_prop safeTpmHashCheck safeTpmHashCheckImp simHash
  cases hb : (claimedPcr == ((oldPcr ^^^ newData) * mult + incr) &&& mask) <;>
    simp [Id.run, hb] <;> rfl

end UnsafeTPMHashSafe

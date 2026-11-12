import Mathlib

/-!
# Safe TPM PCR check -- Lean 4 formalization

The Python program `safe_tpm_hash_check` simulates a TPM PCR "extend"
operation with a simple mixing function: the old PCR is XORed with the new
data, scrambled by an LCG-style multiply-add, and truncated to 32 bits
(`& 0xFFFFFFFF`).  A claimed PCR value is accepted exactly when it equals
this simulated hash, modelling a collision-resistant hash that prevents
PCR forgery.

We model Python's non-negative arbitrary-precision integers with `Nat`:
Python's `^` on non-negative ints is bitwise XOR (`^^^` on `Nat`), and the
mask `& 0xFFFFFFFF` is reduction modulo `2^32`.
-/

namespace «125_unsafeTPMHash_safe»

/-- The 32-bit mask modulus (`0xFFFFFFFF + 1`). -/
def mask32 : Nat := 4294967296

/-- Simulated extend/hash: `((old ^^^ new) * C + A) mod 2^32`. -/
def simulatedHash (old_pcr new_data : Nat) : Nat :=
  ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) % mask32

/-- Functional implementation: accept iff the claimed PCR equals the
    correctly computed simulated hash. -/
def safeTpmHashCheck (old_pcr new_data claimed_pcr : Nat) : Bool :=
  claimed_pcr == simulatedHash old_pcr new_data

-- ## Unit tests

example : safeTpmHashCheck 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true := by
  native_decide

example : safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide

example : safeTpmHashCheck 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide

example : safeTpmHashCheck 0 0 (simulatedHash 0 0) = true := by
  native_decide

example : safeTpmHashCheck 0 0 0 = false := by
  native_decide

#eval safeTpmHashCheck 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB)
#eval safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD
#eval simulatedHash 0xAAAA 0xBBBB

/-- Precondition: every triple of non-negative integers is admissible
    (Python `int` values are modelled by `Nat`). -/
def Pre (_old_pcr _new_data _claimed_pcr : Nat) : Prop := True

-- ## Properties

/-- A correctly computed PCR is accepted. -/
def acceptsCorrect_prop (old_pcr new_data : Nat) : Prop :=
  safeTpmHashCheck old_pcr new_data (simulatedHash old_pcr new_data) = true

theorem acceptsCorrect_thm (old_pcr new_data : Nat) :
    acceptsCorrect_prop old_pcr new_data :=
  beq_self_eq_true _

/-- A claimed PCR different from the simulated hash is rejected. -/
def rejectsForged_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr ≠ simulatedHash old_pcr new_data →
    safeTpmHashCheck old_pcr new_data claimed_pcr = false

theorem rejectsForged_thm (old_pcr new_data claimed_pcr : Nat) :
    rejectsForged_prop old_pcr new_data claimed_pcr :=
  fun h => beq_eq_false_iff_ne.mpr h

/-- The simulated hash always fits in 32 bits. -/
def hashBounded_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data < mask32

theorem hashBounded_thm (old_pcr new_data : Nat) :
    hashBounded_prop old_pcr new_data :=
  Nat.mod_lt _ (by unfold mask32; decide)

/-- Post-condition: conjunction of the properties. -/
def Post_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  acceptsCorrect_prop old_pcr new_data ∧
  rejectsForged_prop old_pcr new_data claimed_pcr ∧
  hashBounded_prop old_pcr new_data

-- ## Property-based tests

-- Randomized PBT: a correctly computed PCR is always accepted.
#eval Plausible.Testable.check
  (∀ a b : Nat, safeTpmHashCheck a b (simulatedHash a b) = true)

-- Randomized PBT: a claimed PCR different from the hash is always rejected.
#eval Plausible.Testable.check
  (∀ a b c : Nat, c ≠ simulatedHash a b → safeTpmHashCheck a b c = false)

-- Bounded exhaustive PBT: the hash stays below 2^32 on a grid of inputs.
example : (List.range 64).all (fun a => (List.range 64).all (fun b =>
    decide (simulatedHash a b < mask32))) = true := by
  native_decide

/-- Executable Boolean form of the post-condition: the checker agrees with
    the equality test, and the hash is 32-bit bounded. -/
def postCheck (old_pcr new_data claimed_pcr : Nat) : Bool :=
  ((claimed_pcr == simulatedHash old_pcr new_data) ==
    safeTpmHashCheck old_pcr new_data claimed_pcr)
    && decide (simulatedHash old_pcr new_data < mask32)

-- Bounded exhaustive PBT for the post-condition on a small grid.
example : (List.range 16).all (fun a => (List.range 16).all (fun b =>
    (List.range 16).all (fun c => postCheck a b c))) = true := by
  native_decide

-- Randomized PBT for the post-condition.
#eval Plausible.Testable.check
  (∀ a b c : Nat, postCheck a b c = true)

/-- Correctness theorem: the precondition implies the post-condition. -/
theorem correctness (old_pcr new_data claimed_pcr : Nat) :
    Pre old_pcr new_data claimed_pcr → Post_prop old_pcr new_data claimed_pcr :=
  fun _ => ⟨acceptsCorrect_thm old_pcr new_data,
            rejectsForged_thm old_pcr new_data claimed_pcr,
            hashBounded_thm old_pcr new_data⟩

-- ## Imperative implementation

/-- Imperative implementation using `Id.run` with mutable state, mirroring
    the step-by-step mixing of the Python program. -/
def safeTpmHashCheckImp (old_pcr new_data claimed_pcr : Nat) : Bool := Id.run do
  let mut x := old_pcr ^^^ new_data
  x := x * 6364136223846793005
  x := x + 1442695040888963407
  x := x % mask32
  return claimed_pcr == x

-- ## Imperative tests

example : safeTpmHashCheckImp 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true := by
  native_decide

example : safeTpmHashCheckImp 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide

example : safeTpmHashCheckImp 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide

example : safeTpmHashCheckImp 0 0 (simulatedHash 0 0) = true := by
  native_decide

#eval safeTpmHashCheckImp 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB)
#eval safeTpmHashCheckImp 0xAAAA 0xBBBB 0xDEAD

/-- Equivalence theorem: the functional and imperative implementations agree. -/
theorem functional_eq_imperative (old_pcr new_data claimed_pcr : Nat) :
    safeTpmHashCheck old_pcr new_data claimed_pcr
      = safeTpmHashCheckImp old_pcr new_data claimed_pcr := rfl

end «125_unsafeTPMHash_safe»

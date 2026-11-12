import Mathlib

/-!
# Safe TPM PCR hash check

A translation of `safe_tpm_hash_check` and its four Python assertions.
All inputs are unbounded signed `Int`s. Mathlib's `Int.xor` and `Int.land`
use signed, infinite two's-complement bitwise semantics, including negative
inputs. Multiplication and addition are exact; only the final `0xFFFFFFFF`
mask truncates the result. The claimed PCR is compared without truncation.

The proven safety statement is exact validation of this simulated extend
operation, not collision resistance or preimage resistance. This small mixing
function is not a cryptographic hash (and the source contains no actual rotate).
Unit/property tests use native evaluation; named theorem proofs are kernel checked.
-/

namespace «125_unsafeTPMHash_safe»

/-! ## Functional implementation -/

/-- The exact simulated `H(old_pcr || new_data)` expression from Python. -/
def simulated_hash (old_pcr new_data : Int) : Int :=
  Int.land (Int.xor old_pcr new_data * 6364136223846793005 + 1442695040888963407)
    0xFFFFFFFF

/-- Accept exactly the unmodified claimed integer that equals the masked hash. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Int) : Bool :=
  decide (claimed_pcr = simulated_hash old_pcr new_data)

/-! ## Unit tests and the Python `check` -/

def expected_0 : Int :=
  Int.land (Int.xor 0xAAAA 0xBBBB * 6364136223846793005 + 1442695040888963407)
    0xFFFFFFFF

def expected_zero : Int :=
  Int.land (Int.xor 0 0 * 6364136223846793005 + 1442695040888963407) 0xFFFFFFFF

example : safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check 0 0 expected_zero = true := by native_decide

-- Independently computed reference values, including signed and large inputs.
example : expected_0 = 4207341644 := by native_decide
example : expected_zero = 4150755663 := by native_decide
example : simulated_hash (-1) 0 = 2865889826 := by native_decide
example : simulated_hash (-42) 17 = 3927846986 := by native_decide
example : simulated_hash (-42) (-17) = 78697044 := by native_decide
example : simulated_hash (2^100 + 5) (-(2^90)) = 1985150256 := by native_decide
example : safe_tpm_hash_check (-1) 0 2865889826 = true := by native_decide
example : safe_tpm_hash_check 0 0 (-144211633) = false := by native_decide
example : safe_tpm_hash_check 0 0 (expected_zero + 2^32) = false := by native_decide

/-- The conjunction of the four assertions in the Python test driver. -/
def check : Bool :=
  safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 &&
  !safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD &&
  !safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 &&
  safe_tpm_hash_check 0 0 expected_zero

example : check = true := by native_decide
#eval (expected_0, expected_zero)
#eval if check then "All tests passed." else "A test failed."

/-! ## Precondition -/

/-- Python accepts every integer triple, including negative and arbitrarily large inputs. -/
def Pre (_old_pcr _new_data _claimed_pcr : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Soundness and completeness of acceptance for the exact simulated hash. -/
def acceptance_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = simulated_hash old_pcr new_data

theorem acceptance_thm (old_pcr new_data claimed_pcr : Int) :
    acceptance_prop old_pcr new_data claimed_pcr := by
  simp [acceptance_prop, safe_tpm_hash_check]

/-- Rejection happens exactly when the claimed PCR differs from the computed PCR. -/
def rejection_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = false ↔
    claimed_pcr ≠ simulated_hash old_pcr new_data

theorem rejection_thm (old_pcr new_data claimed_pcr : Int) :
    rejection_prop old_pcr new_data claimed_pcr := by
  simp [rejection_prop, safe_tpm_hash_check]

/-- A correctly computed claim is always accepted. -/
def correct_claim_prop (old_pcr new_data : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true

theorem correct_claim_thm (old_pcr new_data : Int) :
    correct_claim_prop old_pcr new_data := by
  simp [correct_claim_prop, safe_tpm_hash_check]

/-- An incorrect claim is never accepted. This is not a cryptographic assumption. -/
def forged_claim_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  claimed_pcr ≠ simulated_hash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem forged_claim_thm (old_pcr new_data claimed_pcr : Int) :
    forged_claim_prop old_pcr new_data claimed_pcr := by
  intro h
  exact (rejection_thm old_pcr new_data claimed_pcr).mpr h

/-- Masking any signed intermediate value gives an unsigned 32-bit result. -/
theorem mask32_bounds (x : Int) :
    0 ≤ Int.land x 0xFFFFFFFF ∧ Int.land x 0xFFFFFFFF < 4294967296 := by
  cases x with
  | ofNat n =>
      change 0 ≤ ((n &&& 4294967295 : Nat) : Int) ∧
        ((n &&& 4294967295 : Nat) : Int) < 4294967296
      have h := Nat.and_le_right (n := n) (m := 4294967295)
      omega
  | negSucc n =>
      change 0 ≤ ((Nat.ldiff 4294967295 n : Nat) : Int) ∧
        ((Nat.ldiff 4294967295 n : Nat) : Int) < 4294967296
      have h : Nat.ldiff 4294967295 n ≤ 4294967295 := by
        apply Nat.le_of_testBit
        intro i hi
        rw [Nat.testBit_ldiff] at hi
        simp only [Bool.and_eq_true] at hi
        exact hi.1
      omega

/-- The computed PCR is in the full unsigned 32-bit range. -/
def hash_range_prop (old_pcr new_data : Int) : Prop :=
  0 ≤ simulated_hash old_pcr new_data ∧ simulated_hash old_pcr new_data < 4294967296

theorem hash_range_thm (old_pcr new_data : Int) :
    hash_range_prop old_pcr new_data := by
  exact mask32_bounds _

/-- Every accepted claim itself, not just its low bits, lies in range. -/
def accepted_range_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true →
    0 ≤ claimed_pcr ∧ claimed_pcr < 4294967296

theorem accepted_range_thm (old_pcr new_data claimed_pcr : Int) :
    accepted_range_prop old_pcr new_data claimed_pcr := by
  intro h
  have heq := (acceptance_thm old_pcr new_data claimed_pcr).mp h
  rw [heq]
  exact hash_range_thm old_pcr new_data

/-- Negative claims and claims at least 2^32 are rejected, rather than wrapped. -/
def out_of_range_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  claimed_pcr < 0 ∨ 4294967296 ≤ claimed_pcr →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem out_of_range_thm (old_pcr new_data claimed_pcr : Int) :
    out_of_range_prop old_pcr new_data claimed_pcr := by
  intro h
  apply forged_claim_thm old_pcr new_data claimed_pcr
  have hr := hash_range_thm old_pcr new_data
  dsimp [hash_range_prop] at hr
  omega

/-! ## Postcondition -/

/-- The complete contract for an unrestricted input triple. -/
def Post_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  acceptance_prop old_pcr new_data claimed_pcr ∧
  rejection_prop old_pcr new_data claimed_pcr ∧
  correct_claim_prop old_pcr new_data ∧
  forged_claim_prop old_pcr new_data claimed_pcr ∧
  hash_range_prop old_pcr new_data ∧
  accepted_range_prop old_pcr new_data claimed_pcr ∧
  out_of_range_prop old_pcr new_data claimed_pcr

/-! ## Bounded property-based tests

Each test checks an executable form of its named property, independently of its
proof. The input grid includes every pair from [-8,8], mixed signs, the supplied
examples, and 100-bit values. Claims include the computed answer and nearby wrong
answers so that acceptance implications are exercised non-vacuously, together
with negative, 32-bit boundary, and large values. No sampler or filtering is needed.
-/

def pbtInputs : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++
    [0xAAAA, 0xBBBB, -0xAAAA, 2^100 + 5, -(2^90)]

def pbtClaims (a b : Int) : List Int :=
  [simulated_hash a b, simulated_hash a b - 1, simulated_hash a b + 1,
   simulated_hash a b + 2^32, 0, -1, 0xFFFFFFFF, 4294967296,
   0xDEAD, 0x1234, 2^100, -(2^100)]

def allPairs (p : Int → Int → Bool) : Bool :=
  pbtInputs.all (fun a => pbtInputs.all (fun b => p a b))

def allTriples (p : Int → Int → Int → Bool) : Bool :=
  allPairs (fun a b => (pbtClaims a b).all (fun c => p a b c))

-- PBT: acceptance_prop.
example : allTriples (fun a b c => decide
    (safe_tpm_hash_check a b c = true ↔ c = simulated_hash a b)) = true := by
  native_decide

-- PBT: rejection_prop.
example : allTriples (fun a b c => decide
    (safe_tpm_hash_check a b c = false ↔ c ≠ simulated_hash a b)) = true := by
  native_decide

-- PBT: correct_claim_prop.
example : allPairs (fun a b => safe_tpm_hash_check a b (simulated_hash a b)) = true := by
  native_decide

-- PBT: forged_claim_prop.
example : allTriples (fun a b c => decide
    (c ≠ simulated_hash a b → safe_tpm_hash_check a b c = false)) = true := by
  native_decide

-- PBT: hash_range_prop.
example : allPairs (fun a b => decide
    (0 ≤ simulated_hash a b ∧ simulated_hash a b < 4294967296)) = true := by
  native_decide

-- PBT: accepted_range_prop.
example : allTriples (fun a b c => decide
    (safe_tpm_hash_check a b c = true → 0 ≤ c ∧ c < 4294967296)) = true := by
  native_decide

-- PBT: out_of_range_prop.
example : allTriples (fun a b c => decide
    (c < 0 ∨ 4294967296 ≤ c → safe_tpm_hash_check a b c = false)) = true := by
  native_decide

-- PBT: Post_prop, the whole conjunction in executable form (Pre is True).
example : allTriples (fun a b c => decide
    ((safe_tpm_hash_check a b c = true ↔ c = simulated_hash a b) ∧
     (safe_tpm_hash_check a b c = false ↔ c ≠ simulated_hash a b) ∧
     safe_tpm_hash_check a b (simulated_hash a b) = true ∧
     (c ≠ simulated_hash a b → safe_tpm_hash_check a b c = false) ∧
     (0 ≤ simulated_hash a b ∧ simulated_hash a b < 4294967296) ∧
     (safe_tpm_hash_check a b c = true → 0 ≤ c ∧ c < 4294967296) ∧
     (c < 0 ∨ 4294967296 ≤ c → safe_tpm_hash_check a b c = false))) = true := by
  native_decide

-- PBT for the general masking helper, including negative intermediate values.
example : pbtInputs.all (fun x => decide
    (0 ≤ Int.land x 0xFFFFFFFF ∧ Int.land x 0xFFFFFFFF < 4294967296)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (old_pcr new_data claimed_pcr : Int) :
    Pre old_pcr new_data claimed_pcr → Post_prop old_pcr new_data claimed_pcr := by
  intro _
  exact ⟨acceptance_thm old_pcr new_data claimed_pcr,
    rejection_thm old_pcr new_data claimed_pcr,
    correct_claim_thm old_pcr new_data,
    forged_claim_thm old_pcr new_data claimed_pcr,
    hash_range_thm old_pcr new_data,
    accepted_range_thm old_pcr new_data claimed_pcr,
    out_of_range_thm old_pcr new_data claimed_pcr⟩

/-! ## Imperative implementation -/

/-- The same expression, evaluated as sequential updates to mutable state. -/
def safe_tpm_hash_check_imperative (old_pcr new_data claimed_pcr : Int) : Bool := Id.run do
  let mut mixed : Int := Int.xor old_pcr new_data
  mixed := mixed * 6364136223846793005
  mixed := mixed + 1442695040888963407
  mixed := Int.land mixed 0xFFFFFFFF
  let mut accepted : Bool := false
  if claimed_pcr = mixed then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_tpm_hash_check_imperative 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check_imperative 0 0 expected_zero = true := by native_decide
example : safe_tpm_hash_check_imperative (-42) 17 3927846986 = true := by native_decide
example : safe_tpm_hash_check_imperative (2^100 + 5) (-(2^90)) 1985150256 = true := by
  native_decide
example : safe_tpm_hash_check_imperative 0 0 (expected_zero + 2^32) = false := by
  native_decide
#eval (safe_tpm_hash_check_imperative 0xAAAA 0xBBBB expected_0,
       safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0xDEAD,
       safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0x1234,
       safe_tpm_hash_check_imperative 0 0 expected_zero)

-- Bounded PBT for functional/imperative equivalence, including accepted claims.
example : allTriples (fun a b c =>
    safe_tpm_hash_check a b c == safe_tpm_hash_check_imperative a b c) = true := by
  native_decide

/-! ## Equivalence -/

theorem functional_eq_imperative (old_pcr new_data claimed_pcr : Int) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check_imperative old_pcr new_data claimed_pcr := by
  by_cases h : claimed_pcr = simulated_hash old_pcr new_data
  all_goals
    simp only [simulated_hash] at h
    simp [safe_tpm_hash_check, safe_tpm_hash_check_imperative, simulated_hash, h]

end «125_unsafeTPMHash_safe»

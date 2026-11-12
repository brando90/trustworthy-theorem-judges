import Mathlib

/-!
# Safe TPM PCR hash check

This file translates `safe_tpm_hash_check` and the four assertions in Python's
`check`. All arguments use `Int`, preserving Python's unbounded signed integers.
`Int.xor` and `Int.land` implement the signed bitwise operations; the multiply and
add are exact, and only the computed hash is masked to 32 bits. The claimed PCR
is compared as an integer without truncation.

The proven guarantee is acceptance exactly when the claim equals this simulated
hash. The mixing function is a test model, with no cryptographic collision or
preimage resistance assumption. Randomized and bounded property tests supplement
the proofs, including negative inputs and values larger than machine integers.
-/

namespace UnsafeTPMHashSafe

/-! ## Functional implementation -/

/-- The Python expression `((old_pcr ^ new_data) * M + A) & 0xFFFFFFFF`. -/
def simulated_hash (old_pcr new_data : Int) : Int :=
  Int.land (Int.xor old_pcr new_data * 6364136223846793005 +
    1442695040888963407) 0xFFFFFFFF

/-- Accept precisely the integer equal to the recomputed PCR. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Int) : Bool :=
  decide (claimed_pcr = simulated_hash old_pcr new_data)

/-! ## Unit tests -/

example : simulated_hash 0xAAAA 0xBBBB = 4207341644 := by native_decide
example : simulated_hash 0 0 = 4150755663 := by native_decide

-- The four assertions from the Python test function.
example : safe_tpm_hash_check 0xAAAA 0xBBBB
    (simulated_hash 0xAAAA 0xBBBB) = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check 0 0 (simulated_hash 0 0) = true := by native_decide

-- Additional values independently evaluated with the Python expression.
example : simulated_hash (-1) 0 = 2865889826 := by native_decide
example : simulated_hash 0 (-1) = 2865889826 := by native_decide
example : simulated_hash (-1) (-1) = 4150755663 := by native_decide
example : simulated_hash (-(2 ^ 80)) (2 ^ 96 + 17) = 223671116 := by native_decide
example : simulated_hash (2 ^ 100 + 0xAAAA) 0xBBBB = 4207341644 := by native_decide
example : safe_tpm_hash_check 0 0 (-1) = false := by native_decide
example : safe_tpm_hash_check 0 0 (4150755663 + 2 ^ 32) = false := by native_decide

#eval do
  let expected_0 := simulated_hash 0xAAAA 0xBBBB
  assert! safe_tpm_hash_check 0xAAAA 0xBBBB expected_0
  assert! !(safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD)
  assert! !(safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234)
  let expected_zero := simulated_hash 0 0
  assert! safe_tpm_hash_check 0 0 expected_zero
  IO.println "All tests passed."

/-! ## Precondition -/

/-- The Python function accepts every triple of integers. -/
def Pre (_old_pcr _new_data _claimed_pcr : Int) : Prop := True

/-! ## Properties and proofs -/

/-- There are neither false acceptances nor false rejections. -/
def acceptance_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = simulated_hash old_pcr new_data

theorem acceptance_thm (old_pcr new_data claimed_pcr : Int) :
    acceptance_prop old_pcr new_data claimed_pcr := by
  simp [acceptance_prop, safe_tpm_hash_check]

/-- A claim is rejected exactly when it differs from the computed value. -/
def rejection_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = false ↔
    claimed_pcr ≠ simulated_hash old_pcr new_data

theorem rejection_thm (old_pcr new_data claimed_pcr : Int) :
    rejection_prop old_pcr new_data claimed_pcr := by
  simp [rejection_prop, safe_tpm_hash_check]

/-- Recomputing the hash always produces an accepted claim. -/
def correct_pcr_prop (old_pcr new_data : Int) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true

theorem correct_pcr_thm (old_pcr new_data : Int) :
    correct_pcr_prop old_pcr new_data := by
  simp [correct_pcr_prop, safe_tpm_hash_check]

private lemma mask_bounds (x : Int) :
    0 ≤ Int.land x 0xFFFFFFFF ∧ Int.land x 0xFFFFFFFF < 4294967296 := by
  cases x with
  | ofNat n =>
    change 0 ≤ (↑(n &&& 4294967295) : Int) ∧
      (↑(n &&& 4294967295) : Int) < 4294967296
    have h : n &&& 4294967295 ≤ 4294967295 := Nat.and_le_right
    omega
  | negSucc n =>
    change 0 ≤ (↑(Nat.ldiff 4294967295 n) : Int) ∧
      (↑(Nat.ldiff 4294967295 n) : Int) < 4294967296
    have h : Nat.ldiff 4294967295 n ≤ 4294967295 := by
      apply Nat.le_of_testBit
      intro i hi
      exact (Bool.and_eq_true_iff.mp (by simpa only [Nat.testBit_ldiff] using hi)).1
    omega

/-- The mask gives an unsigned 32-bit value, even for negative inputs. -/
def hash_range_prop (old_pcr new_data : Int) : Prop :=
  0 ≤ simulated_hash old_pcr new_data ∧ simulated_hash old_pcr new_data < 4294967296

theorem hash_range_thm (old_pcr new_data : Int) :
    hash_range_prop old_pcr new_data := by
  exact mask_bounds _

/-- Claims outside the unsigned 32-bit range are rejected without truncation. -/
def out_of_range_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  (claimed_pcr < 0 ∨ 4294967296 ≤ claimed_pcr) →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem out_of_range_thm (old_pcr new_data claimed_pcr : Int) :
    out_of_range_prop old_pcr new_data claimed_pcr := by
  intro h
  apply (rejection_thm old_pcr new_data claimed_pcr).mpr
  have hr := hash_range_thm old_pcr new_data
  unfold hash_range_prop at hr
  omega

/-! ## Postcondition -/

def Post_prop (old_pcr new_data claimed_pcr : Int) : Prop :=
  acceptance_prop old_pcr new_data claimed_pcr ∧
  rejection_prop old_pcr new_data claimed_pcr ∧
  correct_pcr_prop old_pcr new_data ∧
  hash_range_prop old_pcr new_data ∧
  out_of_range_prop old_pcr new_data claimed_pcr

/-! ## Property-based tests

Each named property has a randomized check of its executable Boolean form.
The implication for out-of-range claims is checked as a Boolean disjunction,
so the sampler does not discard inputs. Bounded tests below also deliberately
exercise matching claims, incorrect claims, and both out-of-range branches.
-/

-- PBT: acceptance_prop.
#eval Plausible.Testable.check (∀ a b c : Int,
  ((safe_tpm_hash_check a b c == true) == (c == simulated_hash a b)) = true)
  { numInst := 300 }

-- PBT: rejection_prop.
#eval Plausible.Testable.check (∀ a b c : Int,
  ((safe_tpm_hash_check a b c == false) == (c != simulated_hash a b)) = true)
  { numInst := 300 }

-- PBT: correct_pcr_prop; these samples always exercise acceptance.
#eval Plausible.Testable.check (∀ a b : Int,
  safe_tpm_hash_check a b (simulated_hash a b) = true)
  { numInst := 300 }

-- PBT: hash_range_prop.
#eval Plausible.Testable.check (∀ a b : Int,
  (decide (0 ≤ simulated_hash a b) && decide (simulated_hash a b < 4294967296)) = true)
  { numInst := 300 }

-- PBT: out_of_range_prop.
#eval Plausible.Testable.check (∀ a b c : Int,
  (!(decide (c < 0 ∨ 4294967296 ≤ c)) || !(safe_tpm_hash_check a b c)) = true)
  { numInst := 300 }

/-- An executable expansion of the entire postcondition. -/
def post_check (a b c : Int) : Bool :=
  let h := simulated_hash a b
  let result := safe_tpm_hash_check a b c
  ((result == true) == (c == h)) &&
  ((result == false) == (c != h)) &&
  safe_tpm_hash_check a b h &&
  (decide (0 ≤ h) && decide (h < 4294967296)) &&
  (!(decide (c < 0 ∨ 4294967296 ≤ c)) || !result)

-- PBT: Post_prop, testing all five conjuncts together.
#eval Plausible.Testable.check (∀ a b c : Int, post_check a b c = true)
  { numInst := 300 }

/-- A signed interval together with mask boundaries and very large integers. -/
def pbt_inputs : List Int :=
  (List.range 25).map (fun n => (n : Int) - 12) ++
  [-4294967297, -4294967296, 0xAAAA, 0xBBBB, 4294967295, 4294967296,
    4294967297, -(2 ^ 80), 2 ^ 96 + 17, 2 ^ 100 + 0xAAAA]

-- Bounded PBT for every conjunct of Post_prop on all pairs in pbt_inputs.
-- In addition to fixed claims, generate the correct value and nearby forgeries.
example : (pbt_inputs.all fun a => pbt_inputs.all fun b =>
    let h := simulated_hash a b
    (pbt_inputs ++ [h, h - 1, h + 1, h - 4294967296, h + 4294967296]).all
      (fun c => post_check a b c)) = true := by native_decide

/-! ## Correctness -/

theorem correctness_thm (old_pcr new_data claimed_pcr : Int) :
    Pre old_pcr new_data claimed_pcr → Post_prop old_pcr new_data claimed_pcr := by
  intro _
  exact ⟨acceptance_thm old_pcr new_data claimed_pcr,
    rejection_thm old_pcr new_data claimed_pcr,
    correct_pcr_thm old_pcr new_data,
    hash_range_thm old_pcr new_data,
    out_of_range_thm old_pcr new_data claimed_pcr⟩

/-! ## Imperative implementation -/

/-- The same computation, with explicit assignments to mutable local state. -/
def safe_tpm_hash_check_imperative (old_pcr new_data claimed_pcr : Int) : Bool := Id.run do
  let mut hash := Int.xor old_pcr new_data
  hash := hash * 6364136223846793005
  hash := hash + 1442695040888963407
  hash := Int.land hash 0xFFFFFFFF
  let mut accepted := false
  if claimed_pcr = hash then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 4207341644 = true := by
  native_decide
example : safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide
example : safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide
example : safe_tpm_hash_check_imperative 0 0 4150755663 = true := by native_decide
example : safe_tpm_hash_check_imperative (-1) 0 2865889826 = true := by native_decide
example : safe_tpm_hash_check_imperative 0 0 (4150755663 + 2 ^ 32) = false := by
  native_decide

#eval safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 4207341644
#eval safe_tpm_hash_check_imperative 0xAAAA 0xBBBB 0xDEAD

-- PBT for functional/imperative equivalence, including generated accepted claims.
example : (pbt_inputs.all fun a => pbt_inputs.all fun b =>
    (pbt_inputs ++ [simulated_hash a b]).all fun c =>
      safe_tpm_hash_check a b c == safe_tpm_hash_check_imperative a b c) = true := by
  native_decide

/-! ## Equivalence -/

theorem functional_eq_imperative_thm (old_pcr new_data claimed_pcr : Int) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check_imperative old_pcr new_data claimed_pcr := by
  by_cases h : claimed_pcr = simulated_hash old_pcr new_data <;>
    simp_all [safe_tpm_hash_check, simulated_hash, safe_tpm_hash_check_imperative]

end UnsafeTPMHashSafe

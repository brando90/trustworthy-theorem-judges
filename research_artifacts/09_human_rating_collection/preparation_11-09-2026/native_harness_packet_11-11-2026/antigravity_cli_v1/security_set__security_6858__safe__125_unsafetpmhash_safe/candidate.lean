import Mathlib

/-!
# Safe TPM PCR Hash Check (`125_unsafeTPMHash_safe`)

Formalization of a safe Trusted Platform Module (TPM) Platform Configuration Register (PCR)
hash verification function in Lean 4.

The function `safe_tpm_hash_check` validates a `claimed_pcr` value against a simulated
hash extension `H(old_pcr || new_data)`, modelled as a bitwise XOR followed by a 64-bit
LCG mixing step (`* 6364136223846793005 + 1442695040888963407`) masked to 32 bits
(`&&& 0xFFFFFFFF`). It returns `true` if and only if `claimed_pcr` equals the computed
simulated hash.
-/

namespace «125_unsafeTPMHash_safe»

/-! ## 1. Functional Implementation -/

/-- Simulated SHA-1 extend operation `H(old_pcr || new_data)`: mixes `old_pcr ^^^ new_data`
with LCG constants and masks the result to 32 bits (`0xFFFFFFFF`). -/
def simulated_hash (old_pcr new_data : Nat) : Nat :=
  ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

/-- Safe TPM PCR check: returns `true` only when `claimed_pcr` equals the simulated
`H(old_pcr || new_data)`. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Nat) : Bool :=
  let simulated_hash := ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF
  claimed_pcr == simulated_hash

/-! ## 2. Unit Tests -/

/-- Expected hash for `(0xAAAA, 0xBBBB)`. -/
def expected_0 : Nat :=
  ((0xAAAA ^^^ 0xBBBB) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

/-- Expected hash for `(0, 0)`. -/
def expected_zero : Nat :=
  ((0 ^^^ 0) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

#eval safe_tpm_hash_check 0xAAAA 0xBBBB expected_0
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check 0 0 expected_zero

example : expected_0 = 4207341644 := by native_decide
example : expected_zero = 4150755663 := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check 0 0 expected_zero = true := by native_decide
example : safe_tpm_hash_check 0 0 0 = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB (0xAAAA ^^^ 0xBBBB) = false := by native_decide

/-! ## 3. Pre-condition -/

/-- Pre-condition for `safe_tpm_hash_check`: all natural numbers `old_pcr`, `new_data`,
and `claimed_pcr` are admissible inputs. -/
def Pre (_old_pcr _new_data _claimed_pcr : Nat) : Prop := True

/-! ## 4. Properties and Theorems -/

/-- Property 1 (Exact Acceptance Specification): `safe_tpm_hash_check` returns `true` if and only if
`claimed_pcr` equals the simulated hash `((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF`. -/
def exact_match_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  (safe_tpm_hash_check old_pcr new_data claimed_pcr = true) ↔
    claimed_pcr = ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

theorem exact_match_thm (old_pcr new_data claimed_pcr : Nat) :
    exact_match_prop old_pcr new_data claimed_pcr := by
  unfold exact_match_prop safe_tpm_hash_check
  simp

/-- Property 2 (Exact Rejection Specification): `safe_tpm_hash_check` returns `false` if and only if
`claimed_pcr` differs from the simulated hash. -/
def exact_mismatch_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  (safe_tpm_hash_check old_pcr new_data claimed_pcr = false) ↔
    claimed_pcr ≠ ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

theorem exact_mismatch_thm (old_pcr new_data claimed_pcr : Nat) :
    exact_mismatch_prop old_pcr new_data claimed_pcr := by
  unfold exact_mismatch_prop safe_tpm_hash_check
  simp

/-- Property 3 (Completeness / Correct PCR Accepted): When `claimed_pcr` is the correctly
computed hash `simulated_hash old_pcr new_data`, `safe_tpm_hash_check` returns `true`. -/
def accepts_valid_pcr_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr = simulated_hash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = true

theorem accepts_valid_pcr_thm (old_pcr new_data claimed_pcr : Nat) :
    accepts_valid_pcr_prop old_pcr new_data claimed_pcr := by
  unfold accepts_valid_pcr_prop safe_tpm_hash_check simulated_hash
  intro h
  simp [h]

/-- Property 4 (Soundness / Forged PCR Rejected): When `claimed_pcr` differs from the
computed hash `simulated_hash old_pcr new_data`, `safe_tpm_hash_check` returns `false`. -/
def rejects_forged_pcr_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr ≠ simulated_hash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem rejects_forged_pcr_thm (old_pcr new_data claimed_pcr : Nat) :
    rejects_forged_pcr_prop old_pcr new_data claimed_pcr := by
  unfold rejects_forged_pcr_prop safe_tpm_hash_check simulated_hash
  intro h
  exact beq_false_of_ne h

/-- Property 5 (Uniqueness of Valid PCR): For a given `(old_pcr, new_data)` pair, at most
one `claimed_pcr` value is accepted. -/
def unique_valid_pcr_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  ∀ other_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr = true →
    safe_tpm_hash_check old_pcr new_data other_pcr = true →
    claimed_pcr = other_pcr

theorem unique_valid_pcr_thm (old_pcr new_data claimed_pcr : Nat) :
    unique_valid_pcr_prop old_pcr new_data claimed_pcr := by
  unfold unique_valid_pcr_prop safe_tpm_hash_check
  intro other_pcr h1 h2
  simp only [beq_iff_eq] at h1 h2
  exact h1.trans h2.symm

/-- Property 6 (Existence and Uniqueness of Canonical PCR): `simulated_hash old_pcr new_data`
is accepted and is the unique accepted PCR value for `(old_pcr, new_data)`. -/
def canonical_valid_pcr_prop (old_pcr new_data _claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true ∧
  ∀ c : Nat, safe_tpm_hash_check old_pcr new_data c = true → c = simulated_hash old_pcr new_data

theorem canonical_valid_pcr_thm (old_pcr new_data claimed_pcr : Nat) :
    canonical_valid_pcr_prop old_pcr new_data claimed_pcr := by
  unfold canonical_valid_pcr_prop safe_tpm_hash_check simulated_hash
  constructor
  · simp
  · intro c hc
    exact beq_iff_eq.mp hc

/-- Property 7 (XOR Symmetry): Because the simulated hash combines `old_pcr` and `new_data`
via bitwise XOR, swapping `old_pcr` and `new_data` preserves the verification result. -/
def xor_symmetry_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    safe_tpm_hash_check new_data old_pcr claimed_pcr

theorem xor_symmetry_thm (old_pcr new_data claimed_pcr : Nat) :
    xor_symmetry_prop old_pcr new_data claimed_pcr := by
  unfold xor_symmetry_prop safe_tpm_hash_check
  rw [Nat.xor_comm]

/-- Property 8 (XOR State Invariance): Any two `(old_pcr, new_data)` pairs with equal
bitwise XOR produce identical verification outcomes for all `claimed_pcr`. -/
def xor_invariance_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  ∀ old_pcr' new_data' : Nat,
    old_pcr ^^^ new_data = old_pcr' ^^^ new_data' →
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check old_pcr' new_data' claimed_pcr

theorem xor_invariance_thm (old_pcr new_data claimed_pcr : Nat) :
    xor_invariance_prop old_pcr new_data claimed_pcr := by
  unfold xor_invariance_prop safe_tpm_hash_check
  intro old_pcr' new_data' h_xor
  rw [h_xor]

/-- Property 9 (Self-Extend Reduction): Extending a PCR value with an identical data value
(`old_pcr ^^^ old_pcr = 0`) produces the same check result as extending `0` with `0`. -/
def self_extend_prop (old_pcr _new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr old_pcr claimed_pcr =
    safe_tpm_hash_check 0 0 claimed_pcr

theorem self_extend_thm (old_pcr new_data claimed_pcr : Nat) :
    self_extend_prop old_pcr new_data claimed_pcr := by
  unfold self_extend_prop safe_tpm_hash_check
  rw [Nat.xor_self]
  rfl

/-- Property 10 (32-bit Mask Bound): Any accepted `claimed_pcr` is bounded above by `0xFFFFFFFF`
(and any `claimed_pcr > 0xFFFFFFFF` is rejected). -/
def bounded_32bit_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  (safe_tpm_hash_check old_pcr new_data claimed_pcr = true → claimed_pcr ≤ 0xFFFFFFFF) ∧
  (claimed_pcr > 0xFFFFFFFF → safe_tpm_hash_check old_pcr new_data claimed_pcr = false)

theorem bounded_32bit_thm (old_pcr new_data claimed_pcr : Nat) :
    bounded_32bit_prop old_pcr new_data claimed_pcr := by
  unfold bounded_32bit_prop safe_tpm_hash_check
  have h_bound :
      (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF) ≤ 0xFFFFFFFF := by
    change _ &&& (2 ^ 32 - 1) ≤ 0xFFFFFFFF
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  constructor
  · intro h
    simp only [beq_iff_eq] at h
    omega
  · intro h_gt
    apply beq_false_of_ne
    omega

/-! ## 5. Post-condition -/

/-- Post-condition combining all specification properties of `safe_tpm_hash_check`. -/
def Post_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  exact_match_prop old_pcr new_data claimed_pcr ∧
  exact_mismatch_prop old_pcr new_data claimed_pcr ∧
  accepts_valid_pcr_prop old_pcr new_data claimed_pcr ∧
  rejects_forged_pcr_prop old_pcr new_data claimed_pcr ∧
  unique_valid_pcr_prop old_pcr new_data claimed_pcr ∧
  canonical_valid_pcr_prop old_pcr new_data claimed_pcr ∧
  xor_symmetry_prop old_pcr new_data claimed_pcr ∧
  xor_invariance_prop old_pcr new_data claimed_pcr ∧
  self_extend_prop old_pcr new_data claimed_pcr ∧
  bounded_32bit_prop old_pcr new_data claimed_pcr

/-! ## 6. Property-Based Tests -/

-- PBT for `exact_match_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data claimed_pcr : Nat,
  safe_tpm_hash_check old_pcr new_data claimed_pcr ==
    (claimed_pcr == (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)))

-- PBT for `exact_mismatch_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data claimed_pcr : Nat,
  (!safe_tpm_hash_check old_pcr new_data claimed_pcr) ==
    (claimed_pcr != (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)))

-- PBT for `accepts_valid_pcr_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data : Nat,
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true)

-- PBT for `rejects_forged_pcr_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data claimed_pcr : Nat,
  claimed_pcr != simulated_hash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false)

-- PBT for `unique_valid_pcr_prop` and `canonical_valid_pcr_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data delta : Nat,
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true ∧
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data + delta + 1) = false)

-- PBT for `xor_symmetry_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data claimed_pcr : Nat,
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    safe_tpm_hash_check new_data old_pcr claimed_pcr)

-- PBT for `xor_invariance_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data mask claimed_pcr : Nat,
  safe_tpm_hash_check (old_pcr ^^^ mask) (new_data ^^^ mask) claimed_pcr =
    safe_tpm_hash_check old_pcr new_data claimed_pcr)

-- PBT for `self_extend_prop`
#eval Plausible.Testable.check (∀ old_pcr claimed_pcr : Nat,
  safe_tpm_hash_check old_pcr old_pcr claimed_pcr =
    safe_tpm_hash_check 0 0 claimed_pcr)

-- PBT for `bounded_32bit_prop`
#eval Plausible.Testable.check (∀ old_pcr new_data extra : Nat,
  simulated_hash old_pcr new_data ≤ 0xFFFFFFFF ∧
    safe_tpm_hash_check old_pcr new_data (0xFFFFFFFF + 1 + extra) = false)

-- PBT for `Post_prop` (combined executable check)
#eval Plausible.Testable.check (∀ old_pcr new_data claimed_pcr : Nat,
  let h := simulated_hash old_pcr new_data
  (safe_tpm_hash_check old_pcr new_data claimed_pcr == (claimed_pcr == h)) &&
  ((!safe_tpm_hash_check old_pcr new_data claimed_pcr) == (claimed_pcr != h)) &&
  safe_tpm_hash_check old_pcr new_data h &&
  !safe_tpm_hash_check old_pcr new_data (h + 1) &&
  (safe_tpm_hash_check old_pcr new_data claimed_pcr == safe_tpm_hash_check new_data old_pcr claimed_pcr) &&
  (safe_tpm_hash_check old_pcr old_pcr claimed_pcr == safe_tpm_hash_check 0 0 claimed_pcr) &&
  decide (h ≤ 0xFFFFFFFF) &&
  !safe_tpm_hash_check old_pcr new_data (0xFFFFFFFF + 1 + claimed_pcr))

-- Bounded exhaustive PBT over small inputs
example : ((List.range 25).all fun old_pcr =>
  (List.range 25).all fun new_data =>
    let h := simulated_hash old_pcr new_data
    safe_tpm_hash_check old_pcr new_data h &&
    !safe_tpm_hash_check old_pcr new_data (h + 1) &&
    (safe_tpm_hash_check old_pcr new_data h == safe_tpm_hash_check new_data old_pcr h) &&
    (safe_tpm_hash_check old_pcr old_pcr h == safe_tpm_hash_check 0 0 h) &&
    decide (h ≤ 0xFFFFFFFF)) = true := by native_decide

/-! ## 7. Correctness Theorem (`Pre -> Post`) -/

/-- Main correctness theorem: under the pre-condition `Pre`, the post-condition `Post_prop` holds. -/
theorem safe_tpm_hash_check_correct (old_pcr new_data claimed_pcr : Nat)
    (_h_pre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr :=
  ⟨exact_match_thm old_pcr new_data claimed_pcr,
   exact_mismatch_thm old_pcr new_data claimed_pcr,
   accepts_valid_pcr_thm old_pcr new_data claimed_pcr,
   rejects_forged_pcr_thm old_pcr new_data claimed_pcr,
   unique_valid_pcr_thm old_pcr new_data claimed_pcr,
   canonical_valid_pcr_thm old_pcr new_data claimed_pcr,
   xor_symmetry_thm old_pcr new_data claimed_pcr,
   xor_invariance_thm old_pcr new_data claimed_pcr,
   self_extend_thm old_pcr new_data claimed_pcr,
   bounded_32bit_thm old_pcr new_data claimed_pcr⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `safe_tpm_hash_check` using `Id.run do` and mutable state. -/
def safe_tpm_hash_check_imp (old_pcr new_data claimed_pcr : Nat) : Bool := Id.run do
  let mut mixed : Nat := old_pcr ^^^ new_data
  mixed := mixed * 6364136223846793005 + 1442695040888963407
  let mut simulated_hash : Nat := mixed &&& 0xFFFFFFFF
  let mut res : Bool := claimed_pcr == simulated_hash
  return res

/-! ## 9. Imperative Tests -/

#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check_imp 0 0 expected_zero

example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check_imp 0 0 expected_zero = true := by native_decide

#eval Plausible.Testable.check (∀ old_pcr new_data claimed_pcr : Nat,
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr)

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

/-- The functional implementation `safe_tpm_hash_check` and imperative implementation
`safe_tpm_hash_check_imp` produce identical results for all inputs. -/
theorem safe_tpm_hash_check_equiv (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check_imp old_pcr new_data claimed_pcr := by
  rfl

end «125_unsafeTPMHash_safe»

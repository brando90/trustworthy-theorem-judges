import Mathlib

/-!
# Safe TPM PCR Hash Check

Formalization of `safe_tpm_hash_check`, which validates a claimed TPM Platform
Configuration Register (PCR) value against the simulated SHA-1 extend operation
`H(old_pcr || new_data)` modelled as the mixing function:
`((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF`.

A collision-resistant mixing function ensures that for a given `old_pcr`,
distinct 32-bit `new_data` inputs produce distinct PCR values and only the
exact simulated hash is accepted.
-/

namespace «125_unsafeTPMHash_safe»

/-! ## Implementation -/

/-- Simulated hash function for TPM PCR extend: `H(old_pcr || new_data)`. -/
def simulated_hash (old_pcr new_data : Nat) : Nat :=
  (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)

/-- Returns `true` only when `claimed_pcr` equals the simulated `H(old_pcr || new_data)`. -/
def safe_tpm_hash_check (old_pcr : Nat) (new_data : Nat) (claimed_pcr : Nat) : Bool :=
  let simulated_hash := (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)
  claimed_pcr == simulated_hash

/-! ## Unit Tests -/

/-- Expected hash for `(0xAAAA, 0xBBBB)` from the Python test suite. -/
def expected_0 : Nat := (((0xAAAA ^^^ 0xBBBB) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)

/-- Expected hash for `(0, 0)` from the Python test suite. -/
def expected_zero : Nat := (((0 ^^^ 0) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)

example : expected_0 = 4207341644 := by native_decide
example : expected_zero = 4150755663 := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check 0 0 expected_zero = true := by native_decide
example : safe_tpm_hash_check 0xBBBB 0xAAAA expected_0 = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xAAAA expected_zero = true := by native_decide
example : safe_tpm_hash_check 0 0 0x100000000 = false := by native_decide

#eval safe_tpm_hash_check 0xAAAA 0xBBBB expected_0
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check 0 0 expected_zero

/-! ## Pre-condition -/

/-- Pre-condition for `safe_tpm_hash_check`: all natural number inputs are admissible. -/
def Pre (_old_pcr _new_data _claimed_pcr : Nat) : Prop := True

/-! ## Helper Lemmas -/

/-- Bitwise masking with `0xFFFFFFFF` equals modulo `2^32` (`4294967296`). -/
theorem mask32_eq_mod (x : Nat) : (x &&& 0xFFFFFFFF) = x % 4294967296 := by
  change x &&& (2 ^ 32 - 1) = x % (2 ^ 32)
  exact Nat.and_two_pow_sub_one_eq_mod x 32

/-- Any value masked with `0xFFFFFFFF` is at most `0xFFFFFFFF`. -/
theorem mask32_le (x : Nat) : (x &&& 0xFFFFFFFF) ≤ 0xFFFFFFFF := by
  have h := mask32_eq_mod x
  omega

/-- `simulated_hash` is bounded by `0xFFFFFFFF`. -/
theorem simulated_hash_le (old_pcr new_data : Nat) :
    simulated_hash old_pcr new_data ≤ 0xFFFFFFFF :=
  mask32_le ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407)

/-- `safe_tpm_hash_check` unfolds to comparing `claimed_pcr` with `simulated_hash`. -/
theorem safe_tpm_hash_check_eq (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      (claimed_pcr == simulated_hash old_pcr new_data) :=
  rfl

/-- Left cancellation for bitwise XOR on `Nat`. -/
theorem xor_cancel_left (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  have h2 := congrArg (fun z => a ^^^ z) h
  simpa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using h2

/-- Right cancellation for bitwise XOR on `Nat`. -/
theorem xor_cancel_right (a b c : Nat) (h : a ^^^ c = b ^^^ c) : a = b := by
  have h2 := congrArg (fun z => z ^^^ c) h
  simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using h2

/-- The affine mixing map modulo `2^32` is injective because `6364136223846793005` is odd
    (with modular inverse `849225893` modulo `2^32`). -/
theorem lcg_left_inv (z : Nat) :
    (((z * 6364136223846793005 + 1442695040888963407) % 4294967296 + 144211633) * 849225893) % 4294967296 =
    z % 4294967296 := by
  omega

theorem lcg_mod32_iff (x y : Nat) :
    ((x * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF) =
    ((y * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF) ↔
    (x &&& 0xFFFFFFFF) = (y &&& 0xFFFFFFFF) := by
  rw [mask32_eq_mod, mask32_eq_mod, mask32_eq_mod, mask32_eq_mod]
  constructor
  · intro h
    have h1 := congrArg (fun w => ((w + 144211633) * 849225893) % 4294967296) h
    dsimp only at h1
    rw [lcg_left_inv, lcg_left_inv] at h1
    exact h1
  · intro h
    rw [Nat.add_mod (x * _), Nat.mul_mod x, h, ← Nat.mul_mod y, ← Nat.add_mod (y * _)]

/-- Two simulated hashes are equal if and only if their XORed inputs agree on the low 32 bits. -/
theorem simulated_hash_eq_iff (old1 new1 old2 new2 : Nat) :
    simulated_hash old1 new1 = simulated_hash old2 new2 ↔
    ((old1 ^^^ new1) &&& 0xFFFFFFFF) = ((old2 ^^^ new2) &&& 0xFFFFFFFF) :=
  lcg_mod32_iff (old1 ^^^ new1) (old2 ^^^ new2)

/-- For a fixed `old_pcr`, `simulated_hash` is injective on 32-bit `new_data` values. -/
theorem simulated_hash_injective_new_data (old_pcr new1 new2 : Nat)
    (h1 : new1 ≤ 0xFFFFFFFF) (h2 : new2 ≤ 0xFFFFFFFF)
    (heq : simulated_hash old_pcr new1 = simulated_hash old_pcr new2) :
    new1 = new2 := by
  have hm := (simulated_hash_eq_iff old_pcr new1 old_pcr new2).mp heq
  rw [Nat.and_xor_distrib_right, Nat.and_xor_distrib_right] at hm
  have hc := xor_cancel_left (old_pcr &&& 0xFFFFFFFF) (new1 &&& 0xFFFFFFFF) (new2 &&& 0xFFFFFFFF) hm
  rw [mask32_eq_mod, mask32_eq_mod] at hc
  omega

/-- For a fixed `new_data`, `simulated_hash` is injective on 32-bit `old_pcr` values. -/
theorem simulated_hash_injective_old_pcr (old1 old2 new_data : Nat)
    (h1 : old1 ≤ 0xFFFFFFFF) (h2 : old2 ≤ 0xFFFFFFFF)
    (heq : simulated_hash old1 new_data = simulated_hash old2 new_data) :
    old1 = old2 := by
  have hm := (simulated_hash_eq_iff old1 new_data old2 new_data).mp heq
  rw [Nat.and_xor_distrib_right, Nat.and_xor_distrib_right] at hm
  have hc := xor_cancel_right (old1 &&& 0xFFFFFFFF) (old2 &&& 0xFFFFFFFF) (new_data &&& 0xFFFFFFFF) hm
  rw [mask32_eq_mod, mask32_eq_mod] at hc
  omega

/-! ## Properties and Theorems -/

/-- Property 1: `safe_tpm_hash_check` returns `true` if and only if `claimed_pcr`
    equals the simulated hash `((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF`. -/
def accepts_iff_hash_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)

theorem accepts_iff_hash_thm (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    accepts_iff_hash_prop old_pcr new_data claimed_pcr := by
  unfold accepts_iff_hash_prop safe_tpm_hash_check
  simp

/-- Property 2: `safe_tpm_hash_check` returns `false` if and only if `claimed_pcr`
    differs from the simulated hash (forgery rejection / soundness). -/
def rejects_forged_pcr_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = false ↔
    claimed_pcr ≠ (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)

theorem rejects_forged_pcr_thm (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    rejects_forged_pcr_prop old_pcr new_data claimed_pcr := by
  unfold rejects_forged_pcr_prop safe_tpm_hash_check
  simp

/-- Property 3: Completeness — passing the correctly computed `simulated_hash` as `claimed_pcr`
    is always accepted. -/
def accepts_correct_pcr_prop (old_pcr new_data : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true

theorem accepts_correct_pcr_thm (old_pcr new_data : Nat) :
    accepts_correct_pcr_prop old_pcr new_data := by
  unfold accepts_correct_pcr_prop safe_tpm_hash_check simulated_hash
  simp

/-- Property 4: Uniqueness of valid `claimed_pcr` — for any `(old_pcr, new_data)`,
    at most one `claimed_pcr` is accepted. -/
def unique_valid_pcr_prop (old_pcr new_data claimed_pcr other_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true →
  safe_tpm_hash_check old_pcr new_data other_pcr = true →
  claimed_pcr = other_pcr

theorem unique_valid_pcr_thm (old_pcr new_data claimed_pcr other_pcr : Nat) :
    unique_valid_pcr_prop old_pcr new_data claimed_pcr other_pcr := by
  unfold unique_valid_pcr_prop safe_tpm_hash_check
  simp only [beq_iff_eq]
  intro h1 h2
  exact h1.trans h2.symm

/-- For every `old_pcr` and `new_data`, there exists a unique `claimed_pcr` accepted by `safe_tpm_hash_check`. -/
theorem existsUnique_valid_pcr_thm (old_pcr new_data : Nat) :
    ∃! claimed_pcr : Nat, safe_tpm_hash_check old_pcr new_data claimed_pcr = true := by
  refine ⟨simulated_hash old_pcr new_data, accepts_correct_pcr_thm old_pcr new_data, ?_⟩
  intro y hy
  exact unique_valid_pcr_thm old_pcr new_data y (simulated_hash old_pcr new_data)
    hy (accepts_correct_pcr_thm old_pcr new_data)

/-- Property 5: 32-bit bound on accepted PCR values — any accepted `claimed_pcr` is at most
    `0xFFFFFFFF`, and any `claimed_pcr > 0xFFFFFFFF` is rejected. -/
def accepted_pcr_bounded_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  (safe_tpm_hash_check old_pcr new_data claimed_pcr = true → claimed_pcr ≤ 0xFFFFFFFF) ∧
  (claimed_pcr > 0xFFFFFFFF → safe_tpm_hash_check old_pcr new_data claimed_pcr = false)

theorem accepted_pcr_bounded_thm (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    accepted_pcr_bounded_prop old_pcr new_data claimed_pcr := by
  unfold accepted_pcr_bounded_prop
  rw [safe_tpm_hash_check_eq]
  have hle := simulated_hash_le old_pcr new_data
  constructor
  · intro h
    rw [beq_iff_eq] at h
    omega
  · intro h
    rw [beq_eq_false_iff_ne]
    omega

/-- Property 6: Symmetry in `(old_pcr, new_data)` due to commutativity of XOR. -/
def xor_symmetry_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    safe_tpm_hash_check new_data old_pcr claimed_pcr

theorem xor_symmetry_thm (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    xor_symmetry_prop old_pcr new_data claimed_pcr := by
  unfold xor_symmetry_prop safe_tpm_hash_check
  rw [Nat.xor_comm]

/-- Property 7: Equal inputs reduce to `(0, 0)` since `pcr ^^^ pcr = 0`. -/
def equal_inputs_zero_xor_prop (pcr claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check pcr pcr claimed_pcr = safe_tpm_hash_check 0 0 claimed_pcr

theorem equal_inputs_zero_xor_thm (pcr claimed_pcr : Nat) :
    equal_inputs_zero_xor_prop pcr claimed_pcr := by
  unfold equal_inputs_zero_xor_prop safe_tpm_hash_check
  rw [Nat.xor_self, Nat.xor_self]

/-- Property 8: XOR mask invariance — XORing both `old_pcr` and `new_data` with the same `mask`
    leaves the verification result unchanged. -/
def xor_mask_invariance_prop (old_pcr new_data claimed_pcr mask : Nat) : Prop :=
  safe_tpm_hash_check (old_pcr ^^^ mask) (new_data ^^^ mask) claimed_pcr =
    safe_tpm_hash_check old_pcr new_data claimed_pcr

theorem xor_mask_invariance_thm (old_pcr new_data claimed_pcr mask : Nat) :
    xor_mask_invariance_prop old_pcr new_data claimed_pcr mask := by
  unfold xor_mask_invariance_prop safe_tpm_hash_check
  have hxor : (old_pcr ^^^ mask) ^^^ (new_data ^^^ mask) = old_pcr ^^^ new_data := by
    calc
      (old_pcr ^^^ mask) ^^^ (new_data ^^^ mask)
          = old_pcr ^^^ (mask ^^^ (mask ^^^ new_data)) := by
            rw [Nat.xor_comm new_data mask, Nat.xor_assoc]
      _ = old_pcr ^^^ ((mask ^^^ mask) ^^^ new_data) := by
            rw [← Nat.xor_assoc mask mask new_data]
      _ = old_pcr ^^^ new_data := by
            rw [Nat.xor_self, Nat.zero_xor]
  rw [hxor]

/-- Property 9: Collision resistance across distinct 32-bit `new_data` inputs —
    if `claimed_pcr` is valid for `(old_pcr, new_data1)`, it is rejected for `(old_pcr, new_data2)`
    whenever `new_data1, new_data2 ≤ 0xFFFFFFFF` and `new_data1 ≠ new_data2`. -/
def collision_resistance_prop (old_pcr new_data1 new_data2 claimed_pcr : Nat) : Prop :=
  new_data1 ≤ 0xFFFFFFFF →
  new_data2 ≤ 0xFFFFFFFF →
  new_data1 ≠ new_data2 →
  safe_tpm_hash_check old_pcr new_data1 claimed_pcr = true →
  safe_tpm_hash_check old_pcr new_data2 claimed_pcr = false

theorem collision_resistance_thm (old_pcr new_data1 new_data2 claimed_pcr : Nat) :
    collision_resistance_prop old_pcr new_data1 new_data2 claimed_pcr := by
  unfold collision_resistance_prop
  rw [safe_tpm_hash_check_eq, safe_tpm_hash_check_eq, beq_iff_eq, beq_eq_false_iff_ne]
  intro h1 h2 hne hclaim heq2
  apply hne
  apply simulated_hash_injective_new_data old_pcr new_data1 new_data2 h1 h2
  exact hclaim.symm.trans heq2

/-- Property 10: Boolean totality / dichotomy — `safe_tpm_hash_check` evaluates to `true` or `false`. -/
def bool_dichotomy_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ∨
  safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem bool_dichotomy_thm (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    bool_dichotomy_prop old_pcr new_data claimed_pcr := by
  unfold bool_dichotomy_prop
  cases safe_tpm_hash_check old_pcr new_data claimed_pcr <;> simp

/-! ## Post-condition -/

/-- Post-condition combining the specification properties of `safe_tpm_hash_check`. -/
def Post_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  accepts_iff_hash_prop old_pcr new_data claimed_pcr ∧
  rejects_forged_pcr_prop old_pcr new_data claimed_pcr ∧
  accepts_correct_pcr_prop old_pcr new_data ∧
  (∀ other_pcr : Nat, unique_valid_pcr_prop old_pcr new_data claimed_pcr other_pcr) ∧
  accepted_pcr_bounded_prop old_pcr new_data claimed_pcr ∧
  xor_symmetry_prop old_pcr new_data claimed_pcr ∧
  equal_inputs_zero_xor_prop old_pcr claimed_pcr ∧
  (∀ mask : Nat, xor_mask_invariance_prop old_pcr new_data claimed_pcr mask) ∧
  (∀ new_data2 : Nat, collision_resistance_prop old_pcr new_data new_data2 claimed_pcr) ∧
  bool_dichotomy_prop old_pcr new_data claimed_pcr

/-! ## Property-Based Tests -/

-- PBT for `accepts_iff_hash_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr ==
      (claimed_pcr == (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)))

-- PBT for `rejects_forged_pcr_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    (!safe_tpm_hash_check old_pcr new_data claimed_pcr) ==
      (claimed_pcr != (((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF)))

-- PBT for `accepts_correct_pcr_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true)

-- PBT for `unique_valid_pcr_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data offset : Nat,
    safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data + offset + 1) = false)

-- PBT for `accepted_pcr_bounded_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data extra : Nat,
    simulated_hash old_pcr new_data ≤ 0xFFFFFFFF ∧
      safe_tpm_hash_check old_pcr new_data (0x100000000 + extra) = false)

-- PBT for `xor_symmetry_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check new_data old_pcr claimed_pcr)

-- PBT for `equal_inputs_zero_xor_prop`
#eval Plausible.Testable.check
  (∀ pcr claimed_pcr : Nat,
    safe_tpm_hash_check pcr pcr claimed_pcr = safe_tpm_hash_check 0 0 claimed_pcr)

-- PBT for `xor_mask_invariance_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr mask : Nat,
    safe_tpm_hash_check (old_pcr ^^^ mask) (new_data ^^^ mask) claimed_pcr =
      safe_tpm_hash_check old_pcr new_data claimed_pcr)

-- PBT for `collision_resistance_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data1 delta : Nat,
    let n1 := new_data1 % 0x10000
    let n2 := n1 + (delta % 0x10000) + 1
    safe_tpm_hash_check old_pcr n2 (simulated_hash old_pcr n1) = false)

-- PBT for `bool_dichotomy_prop`
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr = true ∨
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false)

-- PBT for `Post_prop` (randomized)
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    let h := simulated_hash old_pcr new_data
    (safe_tpm_hash_check old_pcr new_data claimed_pcr == (claimed_pcr == h)) &&
    (safe_tpm_hash_check old_pcr new_data h == true) &&
    (decide (h ≤ 0xFFFFFFFF)) &&
    (safe_tpm_hash_check old_pcr new_data claimed_pcr ==
      safe_tpm_hash_check new_data old_pcr claimed_pcr) &&
    (safe_tpm_hash_check old_pcr old_pcr claimed_pcr ==
      safe_tpm_hash_check 0 0 claimed_pcr))

-- Bounded PBT for `Post_prop` across small exhaustive grid
example :
    (List.range 16).all (fun old_pcr =>
      (List.range 16).all (fun new_data =>
        let h := simulated_hash old_pcr new_data
        safe_tpm_hash_check old_pcr new_data h &&
        !safe_tpm_hash_check old_pcr new_data (h + 1) &&
        decide (h ≤ 0xFFFFFFFF) &&
        (safe_tpm_hash_check old_pcr new_data h == safe_tpm_hash_check new_data old_pcr h) &&
        (safe_tpm_hash_check old_pcr old_pcr expected_zero == true))) = true := by
  native_decide

/-! ## Correctness Theorem -/

/-- Main correctness theorem: under `Pre`, `Post_prop` holds for all inputs. -/
theorem safe_tpm_hash_check_correct (old_pcr new_data claimed_pcr : Nat)
    (hpre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr := by
  refine ⟨accepts_iff_hash_thm old_pcr new_data claimed_pcr hpre,
          rejects_forged_pcr_thm old_pcr new_data claimed_pcr hpre,
          accepts_correct_pcr_thm old_pcr new_data,
          fun other_pcr => unique_valid_pcr_thm old_pcr new_data claimed_pcr other_pcr,
          accepted_pcr_bounded_thm old_pcr new_data claimed_pcr hpre,
          xor_symmetry_thm old_pcr new_data claimed_pcr hpre,
          equal_inputs_zero_xor_thm old_pcr claimed_pcr,
          fun mask => xor_mask_invariance_thm old_pcr new_data claimed_pcr mask,
          fun new_data2 => collision_resistance_thm old_pcr new_data new_data2 claimed_pcr,
          bool_dichotomy_thm old_pcr new_data claimed_pcr hpre⟩

/-! ## Imperative Implementation -/

/-- Imperative implementation of `safe_tpm_hash_check` using `Id.run do` and mutable state. -/
def safe_tpm_hash_check_imp (old_pcr : Nat) (new_data : Nat) (claimed_pcr : Nat) : Bool := Id.run do
  let mut mixed : Nat := old_pcr ^^^ new_data
  mixed := mixed * 6364136223846793005
  mixed := mixed + 1442695040888963407
  let mut simulated_hash : Nat := mixed &&& 0xFFFFFFFF
  let mut result : Bool := claimed_pcr == simulated_hash
  return result

/-! ## Imperative Tests -/

example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check_imp 0 0 expected_zero = true := by native_decide
example : safe_tpm_hash_check_imp 0xBBBB 0xAAAA expected_0 = true := by native_decide

#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check_imp 0 0 expected_zero

#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check_imp old_pcr new_data claimed_pcr)

/-! ## Equivalence Theorem -/

/-- The functional and imperative implementations are equivalent on all inputs. -/
theorem safe_tpm_hash_check_equiv (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check_imp old_pcr new_data claimed_pcr := by
  rfl

end «125_unsafeTPMHash_safe»

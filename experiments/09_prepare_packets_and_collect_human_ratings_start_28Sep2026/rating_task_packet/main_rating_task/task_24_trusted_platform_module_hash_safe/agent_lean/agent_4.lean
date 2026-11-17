import Mathlib

/-!
# Safe TPM PCR hash check

Translation of a Python predicate that returns true only when a claimed TPM PCR
equals the simulated extend of `old_pcr` with `new_data`.

The source does not call SHA-1. It models the extend, for Boolean reasoning, by one
step of the Knuth MMIX linear congruential generator on the XOR of the two words,
truncated to 32 bits:

`(old_pcr XOR new_data) * 6364136223846793005 + 1442695040888963407`,
then masked with `0xFFFFFFFF`.

Python `int` values here are non-negative PCR words (the driver uses `0xAAAA`,
`0xBBBB`, `0xDEAD`, `0x1234`, and `0`). They are modelled as `Nat`, where `^` and `&`
agree with Python bitwise operators and `& 0xFFFFFFFF` is reduction modulo `2^32`.

A passing check means the claimed word is exactly that masked mix. A different word,
including the driver's forgeries `0xDEAD` and `0x1234`, is rejected. The mixer itself
is not injective: distinct pairs with the same XOR share a PCR. Safety is the equality
test against the computed value.
-/

namespace «125_unsafeTPMHash_safe»

/-- MMIX LCG multiplier `6364136223846793005`. -/
def hashMul : Nat := 6364136223846793005

/-- MMIX LCG increment `1442695040888963407`. -/
def hashAdd : Nat := 1442695040888963407

/-- Low 32 bits, Python `0xFFFFFFFF`. -/
def mask32 : Nat := 0xFFFFFFFF

/-- Simulated extend `H(old_pcr || new_data)`.
Python: `((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF`. -/
def simulatedHash (old_pcr new_data : Nat) : Nat :=
  ((old_pcr ^^^ new_data) * hashMul + hashAdd) &&& mask32

/-- Return true only when `claimed_pcr` equals the simulated extend. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Nat) : Bool :=
  let simulated_hash := simulatedHash old_pcr new_data
  claimed_pcr == simulated_hash

/-- Driver from the Python `check`: computed PCR accepted, two forgeries rejected, zero extend accepted. -/
def check : Bool :=
  let expected_0 := ((0xAAAA ^^^ 0xBBBB) * hashMul + hashAdd) &&& mask32
  let expected_zero := ((0 ^^^ 0) * hashMul + hashAdd) &&& mask32
  safe_tpm_hash_check 0xAAAA 0xBBBB expected_0
    && !safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD
    && !safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234
    && safe_tpm_hash_check 0 0 expected_zero

/-- Message printed by the Python driver when every assert holds. -/
def checkMessage : String :=
  if check then "All tests passed." else "check failed"

/-! ## Unit tests -/

/-- correct PCR rejected -/
example : safe_tpm_hash_check 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true := by
  native_decide

/-- forged PCR accepted -/
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide

/-- arbitrary PCR accepted -/
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide

/-- zero correct PCR rejected -/
example : safe_tpm_hash_check 0 0 (simulatedHash 0 0) = true := by
  native_decide

example : simulatedHash 0xAAAA 0xBBBB = 0xFAC6F04C := by
  native_decide

example : simulatedHash 0 0 = 0xF767814F := by
  native_decide

example : check = true := by
  native_decide

#eval safe_tpm_hash_check 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB)
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check 0 0 (simulatedHash 0 0)
#eval simulatedHash 0xAAAA 0xBBBB
#eval simulatedHash 0 0
#eval checkMessage

/-! ## Pre-condition -/

/-- The Python function is unguarded: every triple of PCR words is admissible. -/
def Pre (old_pcr new_data claimed_pcr : Nat) : Prop :=
  -- Names record the Python parameters. The body does not constrain them.
  let _ := (old_pcr, new_data, claimed_pcr)
  True

/-! ## Properties -/

/-- `mask32` is the 32-bit all-ones word. -/
theorem mask32_eq : mask32 = 2 ^ 32 - 1 := rfl

/-- The simulated extend is the LCG step reduced modulo `2^32`. -/
def hash_mod_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data =
    ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32

theorem hash_mod_thm (old_pcr new_data : Nat) : hash_mod_prop old_pcr new_data := by
  unfold hash_mod_prop simulatedHash
  rw [mask32_eq]
  exact Nat.and_two_pow_sub_one_eq_mod ((old_pcr ^^^ new_data) * hashMul + hashAdd) 32

/-- The masked extend always fits in 32 bits. -/
def hash_bounded_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data < 2 ^ 32

theorem hash_bounded_thm (old_pcr new_data : Nat) : hash_bounded_prop old_pcr new_data := by
  unfold hash_bounded_prop
  have hmod : simulatedHash old_pcr new_data =
      ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32 := by
    simpa [hash_mod_prop] using hash_mod_thm old_pcr new_data
  rw [hmod]
  exact Nat.mod_lt _ (by decide : 0 < 2 ^ 32)

/-- Masking the extend again does not change it. -/
def mask_idempotent_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data &&& mask32 = simulatedHash old_pcr new_data

theorem mask_idempotent_thm (old_pcr new_data : Nat) : mask_idempotent_prop old_pcr new_data := by
  unfold mask_idempotent_prop
  have hlt : simulatedHash old_pcr new_data < 2 ^ 32 := by
    simpa [hash_bounded_prop] using hash_bounded_thm old_pcr new_data
  rw [mask32_eq]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow hlt

/-- The check returns true exactly when the claim is the simulated extend. -/
def check_iff_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = simulatedHash old_pcr new_data

theorem check_iff_thm (old_pcr new_data claimed_pcr : Nat) :
    check_iff_prop old_pcr new_data claimed_pcr := by
  unfold check_iff_prop safe_tpm_hash_check
  simp

/-- True iff the claim equals the masked LCG extend, the source arithmetic. -/
def matches_masked_extend_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32

theorem matches_masked_extend_thm (old_pcr new_data claimed_pcr : Nat) :
    matches_masked_extend_prop old_pcr new_data claimed_pcr := by
  unfold matches_masked_extend_prop
  have hmod : simulatedHash old_pcr new_data =
      ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32 := by
    simpa [hash_mod_prop] using hash_mod_thm old_pcr new_data
  have hiff : safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
      claimed_pcr = simulatedHash old_pcr new_data := by
    simpa [check_iff_prop] using check_iff_thm old_pcr new_data claimed_pcr
  rw [hmod] at hiff
  exact hiff

/-- The PCR produced by the extend is accepted. -/
def accepts_computed_prop (old_pcr new_data : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true

theorem accepts_computed_thm (old_pcr new_data : Nat) : accepts_computed_prop old_pcr new_data := by
  unfold accepts_computed_prop safe_tpm_hash_check
  exact beq_self_eq_true (simulatedHash old_pcr new_data)

/-- A claim other than the computed extend is rejected. -/
def rejects_forged_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr ≠ simulatedHash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem rejects_forged_thm (old_pcr new_data claimed_pcr : Nat) :
    rejects_forged_prop old_pcr new_data claimed_pcr := by
  unfold rejects_forged_prop safe_tpm_hash_check
  intro h
  exact (beq_eq_false_iff_ne).mpr h

/-- No integer outside `0 .. 2^32` can match the masked extend. -/
def rejects_wide_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  2 ^ 32 ≤ claimed_pcr → safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem rejects_wide_thm (old_pcr new_data claimed_pcr : Nat) :
    rejects_wide_prop old_pcr new_data claimed_pcr := by
  unfold rejects_wide_prop
  intro hwide
  have hbound : simulatedHash old_pcr new_data < 2 ^ 32 := by
    simpa [hash_bounded_prop] using hash_bounded_thm old_pcr new_data
  have hne : claimed_pcr ≠ simulatedHash old_pcr new_data := by
    intro heq
    have hle : 2 ^ 32 ≤ simulatedHash old_pcr new_data := heq ▸ hwide
    exact Nat.not_le_of_lt hbound hle
  have hrej : claimed_pcr ≠ simulatedHash old_pcr new_data →
      safe_tpm_hash_check old_pcr new_data claimed_pcr = false := by
    simpa [rejects_forged_prop] using rejects_forged_thm old_pcr new_data claimed_pcr
  exact hrej hne

/-- The extend depends on the two words only through their XOR. -/
def xor_determines_hash_prop (a b c d : Nat) : Prop :=
  a ^^^ b = c ^^^ d → simulatedHash a b = simulatedHash c d

theorem xor_determines_hash_thm (a b c d : Nat) : xor_determines_hash_prop a b c d := by
  intro h
  unfold simulatedHash
  rw [h]

/-- Swapping the two extend inputs does not change the simulated PCR. -/
def extend_symm_prop (a b : Nat) : Prop :=
  simulatedHash a b = simulatedHash b a

theorem extend_symm_thm (a b : Nat) : extend_symm_prop a b := by
  have hxor : xor_determines_hash_prop a b b a := xor_determines_hash_thm a b b a
  unfold xor_determines_hash_prop at hxor
  unfold extend_symm_prop
  exact hxor (Nat.xor_comm a b)

/-- The Boolean check is symmetric in the two extend inputs. -/
def check_symm_prop (a b claimed : Nat) : Prop :=
  safe_tpm_hash_check a b claimed = safe_tpm_hash_check b a claimed

theorem check_symm_thm (a b claimed : Nat) : check_symm_prop a b claimed := by
  unfold check_symm_prop safe_tpm_hash_check
  have hsym : simulatedHash a b = simulatedHash b a := by
    simpa [extend_symm_prop] using extend_symm_thm a b
  rw [hsym]

/-- At most one claimed word is accepted for a given extend. -/
def unique_accept_prop (old_pcr new_data c1 c2 : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data c1 = true →
    safe_tpm_hash_check old_pcr new_data c2 = true →
      c1 = c2

theorem unique_accept_thm (old_pcr new_data c1 c2 : Nat) :
    unique_accept_prop old_pcr new_data c1 c2 := by
  unfold unique_accept_prop
  intro h1 h2
  have hiff1 : safe_tpm_hash_check old_pcr new_data c1 = true ↔ c1 = simulatedHash old_pcr new_data := by
    simpa [check_iff_prop] using check_iff_thm old_pcr new_data c1
  have hiff2 : safe_tpm_hash_check old_pcr new_data c2 = true ↔ c2 = simulatedHash old_pcr new_data := by
    simpa [check_iff_prop] using check_iff_thm old_pcr new_data c2
  rw [hiff1.mp h1, hiff2.mp h2]

/-- The zero extend is the masked LCG increment, since `0 XOR 0 = 0`. -/
def zero_extend_prop : Prop :=
  simulatedHash 0 0 = hashAdd % 2 ^ 32

theorem zero_extend_thm : zero_extend_prop := by
  unfold zero_extend_prop
  have hmod : simulatedHash 0 0 = ((0 ^^^ 0) * hashMul + hashAdd) % 2 ^ 32 := by
    simpa [hash_mod_prop] using hash_mod_thm 0 0
  simpa using hmod

/-- Concrete driver obligations, including the digests computed by the source formula. -/
def vector_asserts_prop : Prop :=
  safe_tpm_hash_check 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true ∧
    safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false ∧
      safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false ∧
        safe_tpm_hash_check 0 0 (simulatedHash 0 0) = true ∧
          simulatedHash 0xAAAA 0xBBBB = 0xFAC6F04C ∧
            simulatedHash 0 0 = 0xF767814F

theorem vector_asserts_thm : vector_asserts_prop := by
  unfold vector_asserts_prop
  decide

/-- The Python driver reaches `print("All tests passed.")`. -/
def check_passes_prop : Prop :=
  check = true

theorem check_passes_thm : check_passes_prop := by
  unfold check_passes_prop
  decide

/-- Distinct inputs can share a simulated PCR. The equality check is what rejects a forgery. -/
def mixer_not_injective_prop : Prop :=
  simulatedHash 1 0 = simulatedHash 2 3 ∧ ((1, 0) : Nat × Nat) ≠ (2, 3)

theorem mixer_not_injective_thm : mixer_not_injective_prop := by
  unfold mixer_not_injective_prop
  constructor
  · have hdet : xor_determines_hash_prop 1 0 2 3 := xor_determines_hash_thm 1 0 2 3
    unfold xor_determines_hash_prop at hdet
    exact hdet (by decide)
  · decide

/-! ## Post-condition -/

/-- Contract of one call: the Boolean result is the masked-extend test, the digest is a
32-bit residue of the LCG step, forgeries and out-of-range words are rejected, and the
computed digest is accepted. -/
def Post_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  matches_masked_extend_prop old_pcr new_data claimed_pcr ∧
    hash_bounded_prop old_pcr new_data ∧
      hash_mod_prop old_pcr new_data ∧
        rejects_forged_prop old_pcr new_data claimed_pcr ∧
          accepts_computed_prop old_pcr new_data ∧
            rejects_wide_prop old_pcr new_data claimed_pcr ∧
              extend_symm_prop old_pcr new_data ∧
                mask_idempotent_prop old_pcr new_data

/-! ## Property-based tests

Randomized checks use `Plausible`. Disjunctions are the executable form of rare
antecedents, so a sample is never discarded for failing a guard. Bounded checks cover
small grids exhaustively, including `Post_prop` itself.
-/

-- check_iff_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      (claimed_pcr == simulatedHash old_pcr new_data))

-- matches_masked_extend_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      (claimed_pcr == ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32))

-- rejects_forged_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    claimed_pcr ≠ simulatedHash old_pcr new_data →
      safe_tpm_hash_check old_pcr new_data claimed_pcr = false)

-- accepts_computed_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true)

-- hash_bounded_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat, simulatedHash old_pcr new_data < 2 ^ 32)

-- hash_mod_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    simulatedHash old_pcr new_data =
      ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32)

-- xor_determines_hash_prop (disjunction: equal XORs are sparse under random sampling)
#eval Plausible.Testable.check
  (∀ a b c d : Nat, a ^^^ b ≠ c ^^^ d ∨ simulatedHash a b = simulatedHash c d)

example : ((List.range 8).all fun a =>
    (List.range 8).all fun b =>
      (List.range 8).all fun c =>
        (List.range 8).all fun d =>
          decide (a ^^^ b ≠ c ^^^ d ∨ simulatedHash a b = simulatedHash c d)) = true := by
  native_decide

-- unique_accept_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data c1 c2 : Nat,
    safe_tpm_hash_check old_pcr new_data c1 = false ∨
      safe_tpm_hash_check old_pcr new_data c2 = false ∨
        c1 = c2)

example : ((List.range 6).all fun old_pcr =>
    (List.range 6).all fun new_data =>
      (List.range 10).all fun c1 =>
        (List.range 10).all fun c2 =>
          decide (safe_tpm_hash_check old_pcr new_data c1 = true →
            safe_tpm_hash_check old_pcr new_data c2 = true →
              c1 = c2)) = true := by
  native_decide

-- rejects_wide_prop: every claim `2^32 + k` is outside the mask
#eval Plausible.Testable.check
  (∀ old_pcr new_data k : Nat,
    safe_tpm_hash_check old_pcr new_data (2 ^ 32 + k) = false)

example : ((List.range 12).all fun old_pcr =>
    (List.range 12).all fun new_data =>
      safe_tpm_hash_check old_pcr new_data (2 ^ 32) = false &&
        safe_tpm_hash_check old_pcr new_data (2 ^ 32 + old_pcr + 1) = false) = true := by
  native_decide

-- extend_symm_prop
#eval Plausible.Testable.check
  (∀ a b : Nat, simulatedHash a b = simulatedHash b a)

-- check_symm_prop
#eval Plausible.Testable.check
  (∀ a b claimed : Nat,
    safe_tpm_hash_check a b claimed = safe_tpm_hash_check b a claimed)

-- mask_idempotent_prop
#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    simulatedHash old_pcr new_data &&& mask32 = simulatedHash old_pcr new_data)

-- zero_extend_prop
example : (simulatedHash 0 0 == hashAdd % 2 ^ 32) = true := by
  native_decide

-- vector_asserts_prop
example :
    (safe_tpm_hash_check 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) &&
        !safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD &&
          !safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 &&
            safe_tpm_hash_check 0 0 (simulatedHash 0 0) &&
              (simulatedHash 0xAAAA 0xBBBB == 0xFAC6F04C) &&
                (simulatedHash 0 0 == 0xF767814F)) = true := by
  native_decide

-- check_passes_prop
example : check = true := by
  native_decide

-- mixer_not_injective_prop
example : (simulatedHash 1 0 == simulatedHash 2 3 && (1, 0) != ((2, 3) : Nat × Nat)) = true := by
  native_decide

/-- Executable Boolean form of `Post_prop`. -/
def postBool (old_pcr new_data claimed_pcr : Nat) : Bool :=
  (safe_tpm_hash_check old_pcr new_data claimed_pcr ==
      (claimed_pcr == ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32)) &&
    decide (simulatedHash old_pcr new_data < 2 ^ 32) &&
      (simulatedHash old_pcr new_data ==
          ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32) &&
        (!(claimed_pcr == simulatedHash old_pcr new_data) ||
            safe_tpm_hash_check old_pcr new_data claimed_pcr == false) &&
          (safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) == true) &&
            (decide (claimed_pcr < 2 ^ 32) ||
                safe_tpm_hash_check old_pcr new_data claimed_pcr == false) &&
              (simulatedHash old_pcr new_data == simulatedHash new_data old_pcr) &&
                ((simulatedHash old_pcr new_data &&& mask32) == simulatedHash old_pcr new_data)

-- Post_prop, exhaustive on a small cube
example : ((List.range 5).all fun old_pcr =>
    (List.range 5).all fun new_data =>
      (List.range 5).all fun claimed_pcr =>
        postBool old_pcr new_data claimed_pcr) = true := by
  native_decide

-- Post_prop, randomized executable form (no vacuous guard)
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    (safe_tpm_hash_check old_pcr new_data claimed_pcr =
        (claimed_pcr == ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32)) ∧
      simulatedHash old_pcr new_data < 2 ^ 32 ∧
        simulatedHash old_pcr new_data =
          ((old_pcr ^^^ new_data) * hashMul + hashAdd) % 2 ^ 32 ∧
          (claimed_pcr = simulatedHash old_pcr new_data ∨
            safe_tpm_hash_check old_pcr new_data claimed_pcr = false) ∧
            safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true ∧
              (claimed_pcr < 2 ^ 32 ∨
                safe_tpm_hash_check old_pcr new_data claimed_pcr = false) ∧
                simulatedHash old_pcr new_data = simulatedHash new_data old_pcr ∧
                  simulatedHash old_pcr new_data &&& mask32 = simulatedHash old_pcr new_data)

/-! ## Correctness -/

theorem correctness_thm (old_pcr new_data claimed_pcr : Nat)
    (hPre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr := by
  unfold Pre at hPre
  cases hPre
  unfold Post_prop
  exact ⟨
    matches_masked_extend_thm old_pcr new_data claimed_pcr,
    hash_bounded_thm old_pcr new_data,
    hash_mod_thm old_pcr new_data,
    rejects_forged_thm old_pcr new_data claimed_pcr,
    accepts_computed_thm old_pcr new_data,
    rejects_wide_thm old_pcr new_data claimed_pcr,
    extend_symm_thm old_pcr new_data,
    mask_idempotent_thm old_pcr new_data⟩

/-! ## Imperative implementation -/

/-- Same extend, written with mutable accumulation as in the Python assignment. -/
def safe_tpm_hash_checkImp (old_pcr new_data claimed_pcr : Nat) : Bool :=
  Id.run do
    let mut mixed : Nat := old_pcr ^^^ new_data
    mixed := mixed * hashMul
    mixed := mixed + hashAdd
    let simulated_hash := mixed &&& mask32
    return claimed_pcr == simulated_hash

/-- Imperative driver: mutable flag updated by each source assert. -/
def checkImp : Bool :=
  Id.run do
    let mut ok : Bool := true
    let expected_0 := ((0xAAAA ^^^ 0xBBBB) * hashMul + hashAdd) &&& mask32
    if safe_tpm_hash_checkImp 0xAAAA 0xBBBB expected_0 != true then
      ok := false
    if safe_tpm_hash_checkImp 0xAAAA 0xBBBB 0xDEAD != false then
      ok := false
    if safe_tpm_hash_checkImp 0xAAAA 0xBBBB 0x1234 != false then
      ok := false
    let expected_zero := ((0 ^^^ 0) * hashMul + hashAdd) &&& mask32
    if safe_tpm_hash_checkImp 0 0 expected_zero != true then
      ok := false
    return ok

/-! ## Imperative tests -/

example : safe_tpm_hash_checkImp 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true := by
  native_decide

example : safe_tpm_hash_checkImp 0xAAAA 0xBBBB 0xDEAD = false := by
  native_decide

example : safe_tpm_hash_checkImp 0xAAAA 0xBBBB 0x1234 = false := by
  native_decide

example : safe_tpm_hash_checkImp 0 0 (simulatedHash 0 0) = true := by
  native_decide

example : checkImp = true := by
  native_decide

#eval safe_tpm_hash_checkImp 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB)
#eval safe_tpm_hash_checkImp 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_checkImp 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_checkImp 0 0 (simulatedHash 0 0)
#eval checkImp

/-! ## Equivalence -/

theorem safe_tpm_hash_check_equiv_thm (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_checkImp old_pcr new_data claimed_pcr := by
  rfl

theorem checkImp_passes_thm : checkImp = true := by
  decide

theorem check_equiv_thm : check = checkImp := by
  have hfun : check = true := by simpa [check_passes_prop] using check_passes_thm
  rw [hfun, checkImp_passes_thm]

end «125_unsafeTPMHash_safe»

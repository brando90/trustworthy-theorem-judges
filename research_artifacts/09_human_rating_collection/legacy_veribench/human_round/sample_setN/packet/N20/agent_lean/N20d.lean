import Mathlib

/-!
# Safe TPM PCR check (`125_unsafeTPMHash_safe`)

Lean 4 formalization of the Python program `safe_tpm_hash_check`.

The Python program simulates the TPM *extend* operation
`PCR' = H(old_pcr || new_data)` with a simple mixing function
(XOR followed by a 64-bit LCG step, truncated to 32 bits) and accepts a
claimed PCR value **only** when it equals the correctly recomputed value:

```python
simulated_hash = ((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF
return claimed_pcr == simulated_hash
```

PCR registers, measured data and hash outputs are non-negative bit strings,
so Python `int` is modelled by `Nat`; on non-negative inputs `^`, `*`, `+`,
`&` and `==` on Python ints coincide exactly with `^^^`, `*`, `+`, `&&&`
and `==` on `Nat` (Python ints are unbounded, as are `Nat`).

The file contains
* the functional implementation and ground unit tests,
* a pre-condition (every input is admissible),
* properties with proofs (characterisation of acceptance, completeness,
  soundness against forgeries, uniqueness of the accepted value, 32-bit
  bound of the hash, mask-is-mod, symmetry of the hash, rejection of
  claims that do not fit in 32 bits),
* the post-condition as a conjunction of the properties and the
  correctness theorem `Pre → Post`,
* property-based tests (randomised via `Plausible` and bounded exhaustive),
* an imperative implementation using `Id.run do` with mutable state,
  its tests, and a proof that it agrees with the functional one.
-/

namespace «125_unsafeTPMHash_safe»

/-! ## Implementation -/

/-- LCG multiplier used by the simulated hash (`6364136223846793005`). -/
def hashMultiplier : Nat := 6364136223846793005

/-- LCG increment used by the simulated hash (`1442695040888963407`). -/
def hashIncrement : Nat := 1442695040888963407

/-- 32-bit mask `0xFFFFFFFF`. -/
def mask32 : Nat := 0xFFFFFFFF

/-- Simulated `H(old_pcr || new_data)`: XOR, one LCG step, truncate to 32 bits.
Mirrors the Python expression
`((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF`. -/
def simulatedHash (old_pcr new_data : Nat) : Nat :=
  ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

/-- Returns `true` only when `claimed_pcr` equals the simulated
`H(old_pcr || new_data)`. Mirrors Python `safe_tpm_hash_check`. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Nat) : Bool :=
  claimed_pcr == simulatedHash old_pcr new_data

/-! ## Unit tests (mirroring Python `check()`) -/

/-- `expected_0` from the Python test harness. -/
def expected_0 : Nat :=
  ((0xAAAA ^^^ 0xBBBB) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

/-- `expected_zero` from the Python test harness. -/
def expected_zero : Nat :=
  ((0 ^^^ 0) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

example : expected_0 = 4207341644 := by native_decide
example : expected_zero = 4150755663 := by native_decide
example : simulatedHash 0xAAAA 0xBBBB = 4207341644 := by native_decide

-- correct PCR accepted
example : safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 = true := by native_decide
-- forged PCR rejected
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
-- arbitrary PCR rejected
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
-- zero correct PCR accepted
example : safe_tpm_hash_check 0 0 expected_zero = true := by native_decide
-- a few extra ground checks
example : safe_tpm_hash_check 0 0 0 = false := by native_decide
example : safe_tpm_hash_check 7 7 (simulatedHash 7 7) = true := by native_decide
example : safe_tpm_hash_check 7 7 (simulatedHash 7 7 + 2 ^ 32) = false := by native_decide

#eval simulatedHash 0xAAAA 0xBBBB                      -- 4207341644
#eval safe_tpm_hash_check 0xAAAA 0xBBBB expected_0     -- true
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD         -- false
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234         -- false
#eval safe_tpm_hash_check 0 0 expected_zero            -- true

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- Pre-condition: the Python function accepts any three integers (modelled as
non-negative PCR / data / claim values); there is no further restriction. -/
def Pre (old_pcr new_data claimed_pcr : Nat) : Prop := True

/-! ## Properties -/

/-- The check succeeds **exactly** when the claimed PCR equals the correctly
recomputed hash. -/
def check_iff_hash_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = simulatedHash old_pcr new_data

theorem check_iff_hash_thm (old_pcr new_data claimed_pcr : Nat) :
    check_iff_hash_prop old_pcr new_data claimed_pcr := by
  unfold check_iff_hash_prop safe_tpm_hash_check
  simp

/-- Completeness: the correctly computed PCR is never rejected. -/
def correct_accepted_prop (old_pcr new_data : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true

theorem correct_accepted_thm (old_pcr new_data : Nat) :
    correct_accepted_prop old_pcr new_data := by
  unfold correct_accepted_prop safe_tpm_hash_check
  simp

/-- Soundness: every forged PCR (any value other than the hash) is rejected. -/
def forged_rejected_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr ≠ simulatedHash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem forged_rejected_thm (old_pcr new_data claimed_pcr : Nat) :
    forged_rejected_prop old_pcr new_data claimed_pcr := by
  unfold forged_rejected_prop safe_tpm_hash_check
  intro h
  simpa using h

/-- Uniqueness: for fixed `old_pcr` / `new_data`, at most one claimed value
is accepted, i.e. two accepted claims are equal. -/
def unique_accepted_prop (old_pcr new_data c₁ c₂ : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data c₁ = true →
    safe_tpm_hash_check old_pcr new_data c₂ = true → c₁ = c₂

theorem unique_accepted_thm (old_pcr new_data c₁ c₂ : Nat) :
    unique_accepted_prop old_pcr new_data c₁ c₂ := by
  unfold unique_accepted_prop safe_tpm_hash_check
  intro h₁ h₂
  have e₁ : c₁ = simulatedHash old_pcr new_data := by simpa using h₁
  have e₂ : c₂ = simulatedHash old_pcr new_data := by simpa using h₂
  rw [e₁, e₂]

/-- The 32-bit mask makes the simulated hash equal to the LCG value modulo `2^32`. -/
def hash_eq_mod_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data =
    ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32

theorem hash_eq_mod_thm (old_pcr new_data : Nat) : hash_eq_mod_prop old_pcr new_data := by
  unfold hash_eq_mod_prop simulatedHash
  have hm : (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 := by norm_num
  rw [hm, Nat.and_two_pow_sub_one_eq_mod]

/-- The simulated hash always fits in 32 bits. -/
def hash_lt_two_pow_32_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data < 2 ^ 32

theorem hash_lt_two_pow_32_thm (old_pcr new_data : Nat) :
    hash_lt_two_pow_32_prop old_pcr new_data := by
  unfold hash_lt_two_pow_32_prop
  rw [hash_eq_mod_thm old_pcr new_data]
  exact Nat.mod_lt _ (by norm_num)

/-- The simulated hash is symmetric in `old_pcr` and `new_data`
(XOR is commutative). -/
def hash_comm_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data = simulatedHash new_data old_pcr

theorem hash_comm_thm (old_pcr new_data : Nat) : hash_comm_prop old_pcr new_data := by
  unfold hash_comm_prop simulatedHash
  rw [Nat.xor_comm]

/-- A claimed PCR that does not fit in 32 bits is always rejected. -/
def large_claim_rejected_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  2 ^ 32 ≤ claimed_pcr → safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem large_claim_rejected_thm (old_pcr new_data claimed_pcr : Nat) :
    large_claim_rejected_prop old_pcr new_data claimed_pcr := by
  unfold large_claim_rejected_prop
  intro hc
  apply forged_rejected_thm
  intro heq
  have hlt := hash_lt_two_pow_32_thm old_pcr new_data
  unfold hash_lt_two_pow_32_prop at hlt
  omega

/-- Determinism: the check depends only on its three arguments (re-running it
yields the same verdict). -/
def deterministic_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    safe_tpm_hash_check old_pcr new_data claimed_pcr

theorem deterministic_thm (old_pcr new_data claimed_pcr : Nat) :
    deterministic_prop old_pcr new_data claimed_pcr := by
  unfold deterministic_prop
  rfl

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above, stated for the
result `result = safe_tpm_hash_check old_pcr new_data claimed_pcr`. -/
def Post_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  result = safe_tpm_hash_check old_pcr new_data claimed_pcr ∧
  (result = true ↔ claimed_pcr = simulatedHash old_pcr new_data) ∧
  check_iff_hash_prop old_pcr new_data claimed_pcr ∧
  correct_accepted_prop old_pcr new_data ∧
  forged_rejected_prop old_pcr new_data claimed_pcr ∧
  (∀ c₁ c₂, unique_accepted_prop old_pcr new_data c₁ c₂) ∧
  hash_eq_mod_prop old_pcr new_data ∧
  hash_lt_two_pow_32_prop old_pcr new_data ∧
  hash_comm_prop old_pcr new_data ∧
  large_claim_rejected_prop old_pcr new_data claimed_pcr ∧
  deterministic_prop old_pcr new_data claimed_pcr

/-! ## Property-based tests -/

-- check_iff_hash_prop
#eval Plausible.Testable.check
  (∀ o n c : Nat, safe_tpm_hash_check o n c = (c == simulatedHash o n))
-- correct_accepted_prop
#eval Plausible.Testable.check
  (∀ o n : Nat, safe_tpm_hash_check o n (simulatedHash o n) = true)
-- forged_rejected_prop
#eval Plausible.Testable.check
  (∀ o n c : Nat, c ≠ simulatedHash o n → safe_tpm_hash_check o n c = false)
-- unique_accepted_prop (premise-free Boolean form: two accepted claims are equal)
#eval Plausible.Testable.check
  (∀ o n c₁ c₂ : Nat,
    (!(safe_tpm_hash_check o n c₁ && safe_tpm_hash_check o n c₂) || (c₁ == c₂)) = true)
#eval Plausible.Testable.check
  (∀ o n d : Nat, safe_tpm_hash_check o n (simulatedHash o n + d) = (d == 0))
-- hash_eq_mod_prop
#eval Plausible.Testable.check
  (∀ o n : Nat, simulatedHash o n =
    ((o ^^^ n) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32)
-- hash_lt_two_pow_32_prop
#eval Plausible.Testable.check (∀ o n : Nat, simulatedHash o n < 2 ^ 32)
-- hash_comm_prop
#eval Plausible.Testable.check (∀ o n : Nat, simulatedHash o n = simulatedHash n o)
-- large_claim_rejected_prop (shifted so that every sample satisfies the premise)
#eval Plausible.Testable.check
  (∀ o n c : Nat, safe_tpm_hash_check o n (c + 2 ^ 32) = false)
-- deterministic_prop
#eval Plausible.Testable.check
  (∀ o n c : Nat, safe_tpm_hash_check o n c = safe_tpm_hash_check o n c)
-- Post_prop (executable Boolean form of every conjunct)
#eval Plausible.Testable.check
  (∀ o n c : Nat,
    (safe_tpm_hash_check o n c = (c == simulatedHash o n)) ∧
    safe_tpm_hash_check o n (simulatedHash o n) = true ∧
    (c ≠ simulatedHash o n → safe_tpm_hash_check o n c = false) ∧
    simulatedHash o n =
      ((o ^^^ n) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32 ∧
    simulatedHash o n < 2 ^ 32 ∧
    simulatedHash o n = simulatedHash n o ∧
    safe_tpm_hash_check o n (c + 2 ^ 32) = false)

/-- Bounded exhaustive PBT over small inputs (all properties and the
post-condition in Boolean form). -/
example :
    (List.range 24).all (fun o => (List.range 24).all (fun n => (List.range 40).all (fun c =>
      (safe_tpm_hash_check o n c == (c == simulatedHash o n)) &&
      safe_tpm_hash_check o n (simulatedHash o n) &&
      (c == simulatedHash o n || !safe_tpm_hash_check o n c) &&
      (simulatedHash o n ==
        ((o ^^^ n) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32) &&
      decide (simulatedHash o n < 2 ^ 32) &&
      (simulatedHash o n == simulatedHash n o) &&
      !safe_tpm_hash_check o n (c + 2 ^ 32) &&
      !safe_tpm_hash_check o n (simulatedHash o n + 1) &&
      (safe_tpm_hash_check o n c == safe_tpm_hash_check o n c)))) = true := by
  native_decide

/-- Bounded PBT for uniqueness over small claimed values. -/
example :
    (List.range 12).all (fun o => (List.range 12).all (fun n =>
      (List.range 16).all (fun c₁ => (List.range 16).all (fun c₂ =>
        !(safe_tpm_hash_check o n c₁ && safe_tpm_hash_check o n c₂) || (c₁ == c₂))))) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem safe_tpm_hash_check_correct (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr (safe_tpm_hash_check old_pcr new_data claimed_pcr) := by
  refine ⟨rfl, ?_, check_iff_hash_thm _ _ _, correct_accepted_thm _ _, forged_rejected_thm _ _ _,
    fun c₁ c₂ => unique_accepted_thm _ _ c₁ c₂, hash_eq_mod_thm _ _, hash_lt_two_pow_32_thm _ _,
    hash_comm_thm _ _, large_claim_rejected_thm _ _ _, deterministic_thm _ _ _⟩
  exact check_iff_hash_thm old_pcr new_data claimed_pcr

/-! ## Imperative implementation -/

/-- Imperative version of `safe_tpm_hash_check`, following the Python statements
step by step with mutable state. -/
def safe_tpm_hash_check_imp (old_pcr new_data claimed_pcr : Nat) : Bool := Id.run do
  -- simulated_hash = ((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF
  let mut simulated_hash : Nat := old_pcr ^^^ new_data
  simulated_hash := simulated_hash * 6364136223846793005
  simulated_hash := simulated_hash + 1442695040888963407
  simulated_hash := simulated_hash &&& 0xFFFFFFFF
  -- return claimed_pcr == simulated_hash
  let mut result : Bool := false
  if claimed_pcr == simulated_hash then
    result := true
  return result

/-! ## Imperative tests -/

example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check_imp 0 0 expected_zero = true := by native_decide
example : safe_tpm_hash_check_imp 0 0 0 = false := by native_decide

#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0   -- true
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD       -- false
#eval safe_tpm_hash_check_imp 0 0 expected_zero          -- true

-- PBT: imperative agrees with functional
#eval Plausible.Testable.check
  (∀ o n c : Nat, safe_tpm_hash_check_imp o n c = safe_tpm_hash_check o n c)
#eval Plausible.Testable.check
  (∀ o n : Nat, safe_tpm_hash_check_imp o n (simulatedHash o n) = true)

example :
    (List.range 24).all (fun o => (List.range 24).all (fun n => (List.range 40).all (fun c =>
      (safe_tpm_hash_check_imp o n c == safe_tpm_hash_check o n c) &&
      safe_tpm_hash_check_imp o n (simulatedHash o n)))) = true := by
  native_decide

/-! ## Equivalence theorem -/

theorem safe_tpm_hash_check_imp_eq (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr =
      safe_tpm_hash_check old_pcr new_data claimed_pcr := by
  unfold safe_tpm_hash_check_imp safe_tpm_hash_check simulatedHash
  simp only [Id.run, bind, pure]
  split <;> simp_all

/-- The imperative version therefore satisfies the same post-condition. -/
theorem safe_tpm_hash_check_imp_correct (old_pcr new_data claimed_pcr : Nat)
    (hpre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr (safe_tpm_hash_check_imp old_pcr new_data claimed_pcr) := by
  rw [safe_tpm_hash_check_imp_eq]
  exact safe_tpm_hash_check_correct old_pcr new_data claimed_pcr hpre

end «125_unsafeTPMHash_safe»

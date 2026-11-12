import Mathlib

/-!
# Safe TPM PCR check (`125_unsafeTPMHash_safe`)

Lean 4 formalization of the Python program `safe_tpm_hash_check`.

A TPM Platform Configuration Register (PCR) is *extended* with new data by
replacing its value with `H(old_pcr || new_data)`.  A verifier must only accept
a claimed PCR value when it equals the correctly computed extension; a hash
that is vulnerable to preimage attacks would let an attacker forge the PCR and
extract the disk key (MIT 6.858 Fall 2011 Quiz 2).

The Python program simulates the SHA-1 extend operation with a simple mixing
function (an LCG step on the XOR of the inputs, truncated to 32 bits):

```python
simulated_hash = ((old_pcr ^ new_data) * 6364136223846793005
                  + 1442695040888963407) & 0xFFFFFFFF
return claimed_pcr == simulated_hash
```

PCR values and extension data are non-negative bit strings, so all three Python
`int` arguments are modelled as `Nat`.  The bitwise operators of the Python
source (`^` and `& 0xFFFFFFFF`) are kept as `^^^` and `&&& 0xFFFFFFFF` on `Nat`.

Contents:
* functional implementation `simulatedHash` / `safeTpmHashCheck`;
* unit tests mirroring the Python `check()` function;
* pre-condition `Pre`, properties (`*_prop` / `*_thm`), post-condition
  `Post_prop`, property-based tests and the correctness theorem;
* imperative implementation `safeTpmHashCheckImp` (`Id.run do` with mutable
  state), its tests and the functional/imperative equivalence theorem.
-/

namespace «125_unsafeTPMHash_safe»

/-! ## Functional implementation -/

/-- LCG multiplier used by the simulated hash (Knuth's MMIX constant). -/
def lcgMultiplier : Nat := 6364136223846793005

/-- LCG increment used by the simulated hash (Knuth's MMIX constant). -/
def lcgIncrement : Nat := 1442695040888963407

/-- 32-bit mask `0xFFFFFFFF`. -/
def mask32 : Nat := 0xFFFFFFFF

/-- Simulated SHA-1 extend `H(old_pcr || new_data)`:
`((old_pcr ^ new_data) * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFF`. -/
def simulatedHash (old_pcr new_data : Nat) : Nat :=
  ((old_pcr ^^^ new_data) * lcgMultiplier + lcgIncrement) &&& mask32

/-- `safe_tpm_hash_check`: returns `true` only when `claimed_pcr` equals the
simulated `H(old_pcr || new_data)`. -/
def safeTpmHashCheck (old_pcr new_data claimed_pcr : Nat) : Bool :=
  claimed_pcr == simulatedHash old_pcr new_data

/-! ## Unit tests (mirroring the Python `check()` function) -/

/-- `expected_0` of the Python test. -/
def expected_0 : Nat :=
  ((0xAAAA ^^^ 0xBBBB) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

/-- `expected_zero` of the Python test. -/
def expected_zero : Nat :=
  ((0 ^^^ 0) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF

#eval expected_0          -- 4207341644
#eval expected_zero       -- 4150755663
#eval simulatedHash 0xAAAA 0xBBBB
#eval safeTpmHashCheck 0xAAAA 0xBBBB expected_0   -- true
#eval safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD       -- false
#eval safeTpmHashCheck 0xAAAA 0xBBBB 0x1234       -- false
#eval safeTpmHashCheck 0 0 expected_zero          -- true

example : expected_0 = 4207341644 := by native_decide
example : expected_zero = 4150755663 := by native_decide
-- "correct PCR rejected"
example : safeTpmHashCheck 0xAAAA 0xBBBB expected_0 = true := by native_decide
-- "forged PCR accepted"
example : safeTpmHashCheck 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
-- "arbitrary PCR accepted"
example : safeTpmHashCheck 0xAAAA 0xBBBB 0x1234 = false := by native_decide
-- "zero correct PCR rejected"
example : safeTpmHashCheck 0 0 expected_zero = true := by native_decide
-- a few extra ground checks
example : safeTpmHashCheck 0xAAAA 0xBBBB 4207341644 = true := by native_decide
example : safeTpmHashCheck 0xBBBB 0xAAAA 4207341644 = true := by native_decide
example : safeTpmHashCheck 0 0 4150755663 = true := by native_decide
example : safeTpmHashCheck 0 0 0 = false := by native_decide
example : safeTpmHashCheck 1 2 (simulatedHash 1 2) = true := by native_decide

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- Pre-condition: the Python function is total on its (non-negative integer)
inputs, so every triple of natural numbers is admissible. -/
def Pre (old_pcr new_data claimed_pcr : Nat) : Prop := True

/-! ## Properties and theorems -/

/-- The mask `0xFFFFFFFF` is `2^32 - 1`, hence masking is reduction modulo `2^32`. -/
theorem simulatedHash_eq_mod (old_pcr new_data : Nat) :
    simulatedHash old_pcr new_data =
      ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32 := by
  unfold simulatedHash lcgMultiplier lcgIncrement mask32
  have h : (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 := by norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

/-- Property 1 (soundness and completeness of the check): the check succeeds
exactly when the claimed PCR equals the simulated `H(old_pcr || new_data)`. -/
def check_iff_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  result = true ↔ claimed_pcr = simulatedHash old_pcr new_data

theorem check_iff_thm (old_pcr new_data claimed_pcr : Nat) :
    check_iff_prop old_pcr new_data claimed_pcr (safeTpmHashCheck old_pcr new_data claimed_pcr) := by
  unfold check_iff_prop safeTpmHashCheck
  exact beq_iff_eq

/-- Property 2 ("correct PCR rejected" must not happen): the correctly computed
PCR is always accepted. -/
def accepts_correct_prop (old_pcr new_data : Nat) : Prop :=
  safeTpmHashCheck old_pcr new_data (simulatedHash old_pcr new_data) = true

theorem accepts_correct_thm (old_pcr new_data : Nat) :
    accepts_correct_prop old_pcr new_data := by
  unfold accepts_correct_prop safeTpmHashCheck
  exact beq_self_eq_true _

/-- Property 3 ("forged PCR accepted" must not happen): any claimed value that
differs from the simulated hash is rejected. -/
def rejects_forged_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  claimed_pcr ≠ simulatedHash old_pcr new_data → result = false

theorem rejects_forged_thm (old_pcr new_data claimed_pcr : Nat) :
    rejects_forged_prop old_pcr new_data claimed_pcr
      (safeTpmHashCheck old_pcr new_data claimed_pcr) := by
  unfold rejects_forged_prop safeTpmHashCheck
  intro h
  exact beq_eq_false_iff_ne.mpr h

/-- Property 4: the simulated hash is a 32-bit value. -/
def hash_bounded_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data < 2 ^ 32

theorem hash_bounded_thm (old_pcr new_data : Nat) : hash_bounded_prop old_pcr new_data := by
  unfold hash_bounded_prop
  rw [simulatedHash_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

/-- Property 5: masking with `0xFFFFFFFF` is reduction modulo `2^32`
(the mixing function is an LCG step modulo `2^32`). -/
def hash_eq_mod_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data =
    ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32

theorem hash_eq_mod_thm (old_pcr new_data : Nat) : hash_eq_mod_prop old_pcr new_data :=
  simulatedHash_eq_mod old_pcr new_data

set_option linter.unusedVariables false in
/-- Property 6: an accepted claim is necessarily a 32-bit value. -/
def accepted_bounded_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  result = true → claimed_pcr < 2 ^ 32

theorem accepted_bounded_thm (old_pcr new_data claimed_pcr : Nat) :
    accepted_bounded_prop old_pcr new_data claimed_pcr
      (safeTpmHashCheck old_pcr new_data claimed_pcr) := by
  unfold accepted_bounded_prop
  intro h
  rw [(check_iff_thm old_pcr new_data claimed_pcr).mp h]
  exact hash_bounded_thm old_pcr new_data

set_option linter.unusedVariables false in
/-- Property 7: any claim of `2^32` or more is rejected. -/
def rejects_large_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  2 ^ 32 ≤ claimed_pcr → result = false

theorem rejects_large_thm (old_pcr new_data claimed_pcr : Nat) :
    rejects_large_prop old_pcr new_data claimed_pcr
      (safeTpmHashCheck old_pcr new_data claimed_pcr) := by
  unfold rejects_large_prop
  intro h
  apply rejects_forged_thm old_pcr new_data claimed_pcr
  intro heq
  have hb := hash_bounded_thm old_pcr new_data
  unfold hash_bounded_prop at hb
  omega

/-- Property 8 (no forgery): two accepted claims for the same extension are equal. -/
def unique_accepted_prop (old_pcr new_data c₁ c₂ : Nat) : Prop :=
  safeTpmHashCheck old_pcr new_data c₁ = true →
    safeTpmHashCheck old_pcr new_data c₂ = true → c₁ = c₂

theorem unique_accepted_thm (old_pcr new_data c₁ c₂ : Nat) :
    unique_accepted_prop old_pcr new_data c₁ c₂ := by
  unfold unique_accepted_prop
  intro h₁ h₂
  rw [(check_iff_thm old_pcr new_data c₁).mp h₁, (check_iff_thm old_pcr new_data c₂).mp h₂]

/-- Property 9: for every extension there is exactly one accepted claimed PCR. -/
def exists_unique_accepted_prop (old_pcr new_data : Nat) : Prop :=
  ∃! c : Nat, safeTpmHashCheck old_pcr new_data c = true

theorem exists_unique_accepted_thm (old_pcr new_data : Nat) :
    exists_unique_accepted_prop old_pcr new_data := by
  unfold exists_unique_accepted_prop
  refine ⟨simulatedHash old_pcr new_data, accepts_correct_thm old_pcr new_data, ?_⟩
  intro c hc
  exact (check_iff_thm old_pcr new_data c).mp hc

/-- Property 10: the simulated extend only depends on `old_pcr ^ new_data`, so
the check is symmetric in `old_pcr` and `new_data`. -/
def symm_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  result = safeTpmHashCheck new_data old_pcr claimed_pcr

theorem symm_thm (old_pcr new_data claimed_pcr : Nat) :
    symm_prop old_pcr new_data claimed_pcr (safeTpmHashCheck old_pcr new_data claimed_pcr) := by
  unfold symm_prop safeTpmHashCheck simulatedHash
  rw [Nat.xor_comm]

/-- Property 11 (collision structure of the simulated hash): since the LCG
multiplier is odd, two extensions collide exactly when their XORs agree
modulo `2^32`. -/
def collision_iff_prop (o₁ n₁ o₂ n₂ : Nat) : Prop :=
  simulatedHash o₁ n₁ = simulatedHash o₂ n₂ ↔ (o₁ ^^^ n₁) % 2 ^ 32 = (o₂ ^^^ n₂) % 2 ^ 32

theorem collision_iff_thm (o₁ n₁ o₂ n₂ : Nat) : collision_iff_prop o₁ n₁ o₂ n₂ := by
  unfold collision_iff_prop
  rw [simulatedHash_eq_mod, simulatedHash_eq_mod]
  have hcop : Nat.gcd (2 ^ 32) 6364136223846793005 = 1 := by norm_num
  constructor
  · intro h
    have h' : (o₁ ^^^ n₁) * 6364136223846793005 + 1442695040888963407 ≡
        (o₂ ^^^ n₂) * 6364136223846793005 + 1442695040888963407 [MOD 2 ^ 32] := h
    exact Nat.ModEq.cancel_right_of_coprime hcop (Nat.ModEq.add_right_cancel' _ h')
  · intro h
    have h' : o₁ ^^^ n₁ ≡ o₂ ^^^ n₂ [MOD 2 ^ 32] := h
    exact (h'.mul_right _).add_right _

/-! ## Post-condition -/

/-- Post-condition: conjunction of the result-related properties. -/
def Post_prop (old_pcr new_data claimed_pcr : Nat) (result : Bool) : Prop :=
  check_iff_prop old_pcr new_data claimed_pcr result ∧
  rejects_forged_prop old_pcr new_data claimed_pcr result ∧
  accepted_bounded_prop old_pcr new_data claimed_pcr result ∧
  rejects_large_prop old_pcr new_data claimed_pcr result ∧
  symm_prop old_pcr new_data claimed_pcr result ∧
  hash_bounded_prop old_pcr new_data ∧
  hash_eq_mod_prop old_pcr new_data ∧
  accepts_correct_prop old_pcr new_data

/-! ## Property-based tests -/

/-- `Post_prop` is a conjunction of decidable statements, so it can be tested directly. -/
instance instDecidablePost (old_pcr new_data claimed_pcr : Nat) (result : Bool) :
    Decidable (Post_prop old_pcr new_data claimed_pcr result) := by
  unfold Post_prop check_iff_prop rejects_forged_prop accepted_bounded_prop rejects_large_prop
    symm_prop hash_bounded_prop hash_eq_mod_prop accepts_correct_prop
  infer_instance

/-- Candidate claimed PCRs used by the exhaustive tests: small values together with the
one value that is actually accepted, so that the preconditions are not vacuous. -/
def candidates (old_pcr new_data : Nat) (k : Nat) : List Nat :=
  List.range k ++ [simulatedHash old_pcr new_data, simulatedHash old_pcr new_data + 1,
    simulatedHash old_pcr new_data + 2 ^ 32]

-- check_iff_prop
#eval Plausible.Testable.check
  (∀ o n c : Nat, (safeTpmHashCheck o n c = true ↔ c = simulatedHash o n))
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    (candidates o n 32).all (fun c =>
      safeTpmHashCheck o n c == (c == simulatedHash o n)))) = true := by native_decide
-- accepts_correct_prop
#eval Plausible.Testable.check
  (∀ o n : Nat, safeTpmHashCheck o n (simulatedHash o n) = true)
example : (List.range 64).all (fun o => (List.range 64).all (fun n =>
    safeTpmHashCheck o n (simulatedHash o n))) = true := by native_decide
-- rejects_forged_prop
#eval Plausible.Testable.check
  (∀ o n c : Nat, c ≠ simulatedHash o n → safeTpmHashCheck o n c = false)
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    (candidates o n 32).all (fun c =>
      (c == simulatedHash o n) || (safeTpmHashCheck o n c == false)))) = true := by native_decide
-- hash_bounded_prop
#eval Plausible.Testable.check
  (∀ o n : Nat, simulatedHash o n < 2 ^ 32)
example : (List.range 64).all (fun o => (List.range 64).all (fun n =>
    decide (simulatedHash o n < 2 ^ 32))) = true := by native_decide
-- hash_eq_mod_prop
#eval Plausible.Testable.check
  (∀ o n : Nat, simulatedHash o n =
    ((o ^^^ n) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32)
example : (List.range 64).all (fun o => (List.range 64).all (fun n =>
    simulatedHash o n ==
      ((o ^^^ n) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32)) = true := by native_decide
-- accepted_bounded_prop (Boolean form `¬ result ∨ claimed < 2^32`; the exhaustive test
-- includes the accepted claim, so the premise is exercised)
#eval Plausible.Testable.check
  (∀ o n c : Nat, (!(safeTpmHashCheck o n c) || decide (c < 2 ^ 32)) = true)
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    (candidates o n 32).all (fun c =>
      !(safeTpmHashCheck o n c) || decide (c < 2 ^ 32)))) = true := by native_decide
-- rejects_large_prop (sampled as `c + 2^32`, which always satisfies the premise)
#eval Plausible.Testable.check
  (∀ o n c : Nat, safeTpmHashCheck o n (c + 2 ^ 32) = false)
#eval Plausible.Testable.check
  (∀ o n c : Nat, (!(decide (2 ^ 32 ≤ c)) || (safeTpmHashCheck o n c == false)) = true)
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    (candidates o n 32).all (fun c =>
      !(decide (2 ^ 32 ≤ c)) || (safeTpmHashCheck o n c == false)))) = true := by native_decide
-- unique_accepted_prop (Boolean form; the exhaustive test includes the accepted claim)
#eval Plausible.Testable.check
  (∀ o n c₁ c₂ : Nat,
    (!(safeTpmHashCheck o n c₁) || !(safeTpmHashCheck o n c₂) || (c₁ == c₂)) = true)
example : (List.range 16).all (fun o => (List.range 16).all (fun n =>
    (candidates o n 16).all (fun c₁ => (candidates o n 16).all (fun c₂ =>
      !(safeTpmHashCheck o n c₁) || !(safeTpmHashCheck o n c₂) || (c₁ == c₂))))) = true := by
  native_decide
-- exists_unique_accepted_prop (executable counterpart: the witness `simulatedHash o n` is
-- accepted and every accepted claim equals the witness)
#eval Plausible.Testable.check
  (∀ o n c : Nat, (safeTpmHashCheck o n (simulatedHash o n) &&
    (!(safeTpmHashCheck o n c) || (c == simulatedHash o n))) = true)
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    safeTpmHashCheck o n (simulatedHash o n) &&
    (candidates o n 32).all (fun c =>
      !(safeTpmHashCheck o n c) || (c == simulatedHash o n)))) = true := by native_decide
-- symm_prop
#eval Plausible.Testable.check
  (∀ o n c : Nat, safeTpmHashCheck o n c = safeTpmHashCheck n o c)
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    (candidates o n 32).all (fun c =>
      safeTpmHashCheck o n c == safeTpmHashCheck n o c))) = true := by native_decide
-- collision_iff_prop
#eval Plausible.Testable.check
  (∀ o₁ n₁ o₂ n₂ : Nat,
    (simulatedHash o₁ n₁ = simulatedHash o₂ n₂ ↔ (o₁ ^^^ n₁) % 2 ^ 32 = (o₂ ^^^ n₂) % 2 ^ 32))
example : (List.range 24).all (fun o₁ => (List.range 24).all (fun n₁ =>
    (List.range 24).all (fun o₂ => (List.range 24).all (fun n₂ =>
      (simulatedHash o₁ n₁ == simulatedHash o₂ n₂) ==
        ((o₁ ^^^ n₁) % 2 ^ 32 == (o₂ ^^^ n₂) % 2 ^ 32))))) = true := by native_decide
-- Post_prop (tested directly through its `Decidable` instance)
#eval Plausible.Testable.check
  (∀ o n c : Nat, Post_prop o n c (safeTpmHashCheck o n c))
example : (List.range 32).all (fun o => (List.range 32).all (fun n =>
    (candidates o n 32).all (fun c =>
      decide (Post_prop o n c (safeTpmHashCheck o n c))))) = true := by native_decide

/-! ## Correctness theorem -/

theorem correctness (old_pcr new_data claimed_pcr : Nat)
    (_hpre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr (safeTpmHashCheck old_pcr new_data claimed_pcr) :=
  ⟨check_iff_thm old_pcr new_data claimed_pcr,
   rejects_forged_thm old_pcr new_data claimed_pcr,
   accepted_bounded_thm old_pcr new_data claimed_pcr,
   rejects_large_thm old_pcr new_data claimed_pcr,
   symm_thm old_pcr new_data claimed_pcr,
   hash_bounded_thm old_pcr new_data,
   hash_eq_mod_thm old_pcr new_data,
   accepts_correct_thm old_pcr new_data⟩

/-! ## Imperative implementation -/

/-- Imperative version of `safe_tpm_hash_check`: the simulated extend is
computed step by step in a mutable accumulator, then compared with the claim. -/
def safeTpmHashCheckImp (old_pcr new_data claimed_pcr : Nat) : Bool := Id.run do
  let mut acc : Nat := old_pcr ^^^ new_data
  acc := acc * 6364136223846793005
  acc := acc + 1442695040888963407
  acc := acc &&& 0xFFFFFFFF
  let mut ok : Bool := false
  if claimed_pcr == acc then
    ok := true
  return ok

/-! ## Imperative tests -/

#eval safeTpmHashCheckImp 0xAAAA 0xBBBB expected_0   -- true
#eval safeTpmHashCheckImp 0xAAAA 0xBBBB 0xDEAD       -- false
#eval safeTpmHashCheckImp 0xAAAA 0xBBBB 0x1234       -- false
#eval safeTpmHashCheckImp 0 0 expected_zero          -- true

example : safeTpmHashCheckImp 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safeTpmHashCheckImp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safeTpmHashCheckImp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safeTpmHashCheckImp 0 0 expected_zero = true := by native_decide
example : safeTpmHashCheckImp 0 0 0 = false := by native_decide
example : (List.range 40).all (fun o => (List.range 40).all (fun n =>
    (List.range 40).all (fun c =>
      safeTpmHashCheckImp o n c == safeTpmHashCheck o n c))) = true := by native_decide
#eval Plausible.Testable.check
  (∀ o n c : Nat, safeTpmHashCheckImp o n c = safeTpmHashCheck o n c)

/-! ## Equivalence theorem -/

theorem imp_equiv (old_pcr new_data claimed_pcr : Nat) :
    safeTpmHashCheck old_pcr new_data claimed_pcr =
      safeTpmHashCheckImp old_pcr new_data claimed_pcr := by
  unfold safeTpmHashCheckImp safeTpmHashCheck simulatedHash lcgMultiplier lcgIncrement mask32
  simp only [Id.run, bind, pure]
  split <;> simp_all

/-- The imperative implementation satisfies the same post-condition. -/
theorem imp_correctness (old_pcr new_data claimed_pcr : Nat)
    (hpre : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr (safeTpmHashCheckImp old_pcr new_data claimed_pcr) := by
  rw [← imp_equiv]
  exact correctness old_pcr new_data claimed_pcr hpre

end «125_unsafeTPMHash_safe»

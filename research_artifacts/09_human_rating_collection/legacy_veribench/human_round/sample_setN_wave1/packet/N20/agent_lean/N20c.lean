import Mathlib

/-!
# 125_unsafeTPMHash_safe — Safe TPM PCR extend-and-verify

Lean 4 formalization of the Python program `safe_tpm_hash_check`, which validates a
*claimed* TPM PCR value against the correctly computed simulated extend hash
`H(old_pcr || new_data)`.

The Python semantics being modelled:

    simulated_hash = ((old_pcr ^ new_data) * 6364136223846793005
                        + 1442695040888963407) & 0xFFFFFFFF
    return claimed_pcr == simulated_hash

## Modelling notes

* PCR values, extend data and hash outputs are non-negative machine words, modelled by
  `Nat`; `^^^` is `Nat.xor`, the model of Python's `^`.
* On non-negative Python integers `x & 0xFFFFFFFF` is exactly `x % 2^32`, so the mask is
  implemented as `% word32_mod` with `word32_mod = 4294967296 = 2^32`. The theorems
  `mask32_add_one`, `mask32_eq_two_pow_sub` and `word32_eq_two_pow` tie this back to the
  source literal `0xFFFFFFFF`, and `simulated_hash_eq_python` / `mix32_eq_python` restate
  the definitions in the exact shape of the Python expression.
* The security content (MIT 6.858 Fall 2011 Quiz 2: a preimage-vulnerable hash lets an
  attacker forge a PCR value and extract the disk key) is captured by `accept_prop` (the
  correctly extended PCR is accepted), `reject_prop` (every other claim is rejected) and
  `sound_prop` (acceptance implies the claim equals the computed hash): the verdict cannot
  be forged.
* No floating point occurs in the source, so the exact discrete layer `Nat` is used
  throughout; there is no `Real`/`Float` obligation to model.
-/

namespace «125_unsafeTPMHash_safe»

/-! ## Constants of the simulated extend hash -/

/-- Python's multiplier `6364136223846793005`. -/
def lcg_mul : Nat := 6364136223846793005

/-- Python's increment `1442695040888963407`. -/
def lcg_inc : Nat := 1442695040888963407

/-- Python's mask literal `0xFFFFFFFF`. -/
def mask32 : Nat := 0xFFFFFFFF

/-- `2^32 = 0xFFFFFFFF + 1`: masking with `mask32` is reduction modulo this number. -/
def word32_mod : Nat := 4294967296

theorem mask32_add_one : mask32 + 1 = word32_mod := by decide

theorem mask32_eq_two_pow_sub : mask32 = 2 ^ 32 - 1 := by decide

theorem word32_eq_two_pow : word32_mod = 2 ^ 32 := by decide

theorem word32_pos : 0 < word32_mod := by decide

/-! ## Functional implementation -/

/-- One mixing step of the simulated hash: `(x * lcg_mul + lcg_inc) & 0xFFFFFFFF`. -/
def mix32 (x : Nat) : Nat := (x * lcg_mul + lcg_inc) % word32_mod

/-- Simulated `H(old_pcr || new_data)`: the SHA-1 extend modelled as XOR + mixing. -/
def simulated_hash (old_pcr new_data : Nat) : Nat := mix32 (old_pcr ^^^ new_data)

/-- `safe_tpm_hash_check`: returns `true` only when `claimed_pcr` equals the simulated
`H(old_pcr || new_data)`. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Nat) : Bool :=
  claimed_pcr == simulated_hash old_pcr new_data

/-- The mixing step written exactly in the shape of the Python expression. -/
theorem mix32_eq_python (x : Nat) :
    mix32 x = (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 32 := rfl

/-- The simulated extend written exactly in the shape of the Python expression. -/
theorem simulated_hash_eq_python (old_pcr new_data : Nat) :
    simulated_hash old_pcr new_data =
      ((old_pcr ^^^ new_data) * 6364136223846793005 + 1442695040888963407) % 2 ^ 32 := rfl

/-- `expected_0` of the Python `check()` driver. -/
def expected_0 : Nat := simulated_hash 0xAAAA 0xBBBB

/-- `expected_zero` of the Python `check()` driver. -/
def expected_zero : Nat := simulated_hash 0 0

/-- The four assertions of the Python `check()` driver, conjoined. -/
def python_check : Bool :=
  safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 &&
    !safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD &&
    !safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 &&
    safe_tpm_hash_check 0 0 expected_zero

/-! ## Unit tests -/

example : expected_0 = 4207341644 := by native_decide
example : expected_0 = 0xfac6f04c := by native_decide
example : expected_zero = 4150755663 := by native_decide
example : expected_zero = 0xf767814f := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check 0 0 expected_zero = true := by native_decide
example : python_check = true := by native_decide

#eval expected_0
#eval expected_zero
#eval safe_tpm_hash_check 0xAAAA 0xBBBB expected_0
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check 0 0 expected_zero
#eval if python_check then "All tests passed." else "TEST FAILURE"

/-- Kernel-checked counterparts of the ground unit tests (`native_decide` is only used in
the `example` tests above, never inside a theorem). -/
theorem expected_0_val : expected_0 = 4207341644 := by decide

theorem expected_zero_val : expected_zero = 4150755663 := by decide

theorem python_check_thm : python_check = true := by decide

/-! ## Pre-condition -/

/-- The Python function is total on PCR values: every argument is a non-negative machine
integer (modelled by `Nat`) and the 32-bit mask keeps the result in range, so the source
imposes no side condition. `Pre` is therefore the trivial predicate on the whole input
domain `Nat × Nat × Nat`; it is not narrowed anywhere below. -/
@[reducible] def Pre (_old_pcr _new_data _claimed_pcr : Nat) : Prop := True

theorem Pre_holds (old_pcr new_data claimed_pcr : Nat) :
    Pre old_pcr new_data claimed_pcr := trivial

/-! ## Properties of the safe PCR check -/

/-- The correctly extended PCR is accepted. -/
@[reducible] def accept_prop (old_pcr new_data : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true

/-- Every claim different from the computed extend hash is rejected: the PCR cannot be
forged. -/
@[reducible] def reject_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr ≠ simulated_hash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

/-- Acceptance implies the claim is exactly the computed hash (soundness of the check). -/
@[reducible] def sound_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true →
    claimed_pcr = simulated_hash old_pcr new_data

/-- The verdict is `true` exactly for the correctly computed extend hash: this is the
exact claim of the Python docstring "Returns True only when claimed_pcr equals the
simulated H(old_pcr || new_data)". -/
@[reducible] def iff_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  (safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = simulated_hash old_pcr new_data)

/-- The verdict is the decision procedure for the claimed equality. -/
@[reducible] def decide_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    decide (claimed_pcr = simulated_hash old_pcr new_data)

/-- The simulated extend hash is a 32-bit word. -/
@[reducible] def range_prop (old_pcr new_data : Nat) : Prop :=
  simulated_hash old_pcr new_data < 2 ^ 32

/-- The extend hash depends on its arguments only through `old_pcr ^^^ new_data`. -/
@[reducible] def xor_dep_prop (old_pcr new_data : Nat) : Prop :=
  simulated_hash old_pcr new_data = mix32 (old_pcr ^^^ new_data)

/-- The simulated extend is symmetric in its two arguments (XOR is commutative). -/
@[reducible] def symm_prop (old_pcr new_data : Nat) : Prop :=
  simulated_hash old_pcr new_data = simulated_hash new_data old_pcr

/-- Hence the verdict does not depend on the order of `old_pcr` and `new_data`. -/
@[reducible] def check_symm_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr =
    safe_tpm_hash_check new_data old_pcr claimed_pcr

/-- Extending a PCR with itself mixes `0`, since `a ^^^ a = 0`. -/
@[reducible] def self_extend_prop (old_pcr : Nat) : Prop :=
  simulated_hash old_pcr old_pcr = mix32 0

/-- Extending `0` with `0` yields the increment reduced to 32 bits (`expected_zero`). -/
@[reducible] def zero_extend_prop : Prop := simulated_hash 0 0 = lcg_inc % word32_mod

/-- The check is not vacuous: the honest claim is accepted while the very next value is
rejected, so the verdict really discriminates PCR values. -/
@[reducible] def discriminating_prop (old_pcr new_data : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data) = true ∧
    safe_tpm_hash_check old_pcr new_data (simulated_hash old_pcr new_data + 1) = false

theorem accept_thm (old_pcr new_data : Nat) : accept_prop old_pcr new_data := by
  simp [accept_prop, safe_tpm_hash_check]

theorem reject_thm (old_pcr new_data claimed_pcr : Nat) :
    reject_prop old_pcr new_data claimed_pcr :=
  fun h => by simp [safe_tpm_hash_check, h]

theorem decide_thm (old_pcr new_data claimed_pcr : Nat) :
    decide_prop old_pcr new_data claimed_pcr := by
  by_cases h : claimed_pcr = simulated_hash old_pcr new_data
  · simp [decide_prop, safe_tpm_hash_check, h]
  · simp [decide_prop, safe_tpm_hash_check, h]

theorem sound_thm (old_pcr new_data claimed_pcr : Nat) :
    sound_prop old_pcr new_data claimed_pcr := by
  intro h
  rw [decide_thm old_pcr new_data claimed_pcr] at h
  exact of_decide_eq_true h

theorem iff_thm (old_pcr new_data claimed_pcr : Nat) :
    iff_prop old_pcr new_data claimed_pcr :=
  ⟨sound_thm old_pcr new_data claimed_pcr,
    fun heq => by rw [heq]; exact accept_thm old_pcr new_data⟩

theorem range_thm (old_pcr new_data : Nat) : range_prop old_pcr new_data :=
  Nat.mod_lt _ word32_pos

theorem xor_dep_thm (old_pcr new_data : Nat) : xor_dep_prop old_pcr new_data := rfl

theorem symm_thm (old_pcr new_data : Nat) : symm_prop old_pcr new_data := by
  simp [symm_prop, simulated_hash, Nat.xor_comm]

theorem check_symm_thm (old_pcr new_data claimed_pcr : Nat) :
    check_symm_prop old_pcr new_data claimed_pcr := by
  simp [check_symm_prop, safe_tpm_hash_check, simulated_hash, Nat.xor_comm]

theorem self_extend_thm (old_pcr : Nat) : self_extend_prop old_pcr := by
  simp [self_extend_prop, simulated_hash]

theorem zero_extend_thm : zero_extend_prop := by
  simp [zero_extend_prop, simulated_hash, mix32]

theorem discriminating_thm (old_pcr new_data : Nat) :
    discriminating_prop old_pcr new_data :=
  ⟨accept_thm old_pcr new_data,
    reject_thm old_pcr new_data (simulated_hash old_pcr new_data + 1) (by omega)⟩

/-! ## Post-condition -/

/-- The conjunction of every property established above: the check accepts exactly the
correctly computed extend hash, rejects (and hence cannot be tricked by) any forged or
arbitrary claim, and the hash itself is a well-formed 32-bit word. -/
@[reducible] def Post_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  accept_prop old_pcr new_data ∧
    reject_prop old_pcr new_data claimed_pcr ∧
    sound_prop old_pcr new_data claimed_pcr ∧
    iff_prop old_pcr new_data claimed_pcr ∧
    decide_prop old_pcr new_data claimed_pcr ∧
    range_prop old_pcr new_data ∧
    xor_dep_prop old_pcr new_data ∧
    symm_prop old_pcr new_data ∧
    check_symm_prop old_pcr new_data claimed_pcr ∧
    discriminating_prop old_pcr new_data

/-! ## Property-based tests

Randomized tests (Plausible) plus exhaustive bounded tests over small input grids. Each
executable property stated above, and the post-condition, is tested here in its Boolean
form. -/

#eval Plausible.Testable.check (∀ a b : Nat, decide (accept_prop a b) = true)
#eval Plausible.Testable.check (∀ a b c : Nat, decide (reject_prop a b c) = true)
#eval Plausible.Testable.check (∀ a b c : Nat, decide (sound_prop a b c) = true)
#eval Plausible.Testable.check (∀ a b c : Nat, decide (iff_prop a b c) = true)
#eval Plausible.Testable.check (∀ a b c : Nat, decide (decide_prop a b c) = true)
#eval Plausible.Testable.check (∀ a b : Nat, decide (range_prop a b) = true)
#eval Plausible.Testable.check (∀ a b : Nat, decide (xor_dep_prop a b) = true)
#eval Plausible.Testable.check (∀ a b : Nat, decide (symm_prop a b) = true)
#eval Plausible.Testable.check (∀ a b c : Nat, decide (check_symm_prop a b c) = true)
#eval Plausible.Testable.check (∀ a : Nat, decide (self_extend_prop a) = true)
#eval Plausible.Testable.check (∀ a b : Nat, decide (discriminating_prop a b) = true)
#eval Plausible.Testable.check (∀ a b c : Nat, decide (Pre a b c → Post_prop a b c) = true)

example : decide zero_extend_prop = true := by native_decide

-- bounded PBT: the honest PCR is always accepted
example : (List.range 64).all
    (fun n => safe_tpm_hash_check n (n * 7 + 3) (simulated_hash n (n * 7 + 3))) = true := by
  native_decide

-- bounded PBT: the hash always stays inside the 32-bit word
example : (List.range 64).all (fun n => simulated_hash n (n * n + 1) < 2 ^ 32) = true := by
  native_decide

-- bounded PBT: the forged value `0xDEAD` of the Python driver is always rejected
example : (List.range 64).all (fun n => safe_tpm_hash_check n (n + 5) 0xDEAD = false) = true := by
  native_decide

-- bounded PBT: symmetry / xor-dependence / self-extend over a grid
example : (List.range 24).all (fun a => (List.range 24).all (fun b =>
    decide (symm_prop a b) && decide (xor_dep_prop a b) && decide (self_extend_prop a))) = true := by
  native_decide

-- bounded PBT: every claim different from the computed hash is rejected
example : (List.range 16).all (fun a => (List.range 16).all (fun b => (List.range 16).all (fun c =>
    decide (reject_prop a b (simulated_hash a b + c + 1))))) = true := by
  native_decide

-- bounded PBT: the verdict is `true` exactly on the computed hash
example : (List.range 16).all (fun a => (List.range 16).all (fun b => (List.range 16).all (fun c =>
    decide (iff_prop a b (simulated_hash a b + c))))) = true := by
  native_decide

-- bounded PBT: the full post-condition over a grid of admissible inputs
example : (List.range 12).all (fun a => (List.range 12).all (fun b => (List.range 12).all (fun c =>
    decide (Post_prop a b c)))) = true := by
  native_decide

/-- Edge-case inputs: the mask boundary, the constants of the Python driver and values far
beyond a single 32-bit word (the Python function is total on all non-negative integers). -/
def edge_inputs : List Nat :=
  [0, 1, 2, 0xDEAD, 0x1234, 0xAAAA, 0xBBBB, 0xFFFFFFFF, 4294967296, 4294967297,
    6364136223846793005, 1442695040888963407, 18446744073709551616, 12345678901234567890]

-- bounded PBT over edge-case inputs: the full post-condition holds
example : edge_inputs.all (fun a => edge_inputs.all (fun b => edge_inputs.all (fun c =>
    decide (Post_prop a b c)))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (old_pcr new_data claimed_pcr : Nat)
    (_h : Pre old_pcr new_data claimed_pcr) :
    Post_prop old_pcr new_data claimed_pcr :=
  ⟨accept_thm old_pcr new_data,
    reject_thm old_pcr new_data claimed_pcr,
    sound_thm old_pcr new_data claimed_pcr,
    iff_thm old_pcr new_data claimed_pcr,
    decide_thm old_pcr new_data claimed_pcr,
    range_thm old_pcr new_data,
    xor_dep_thm old_pcr new_data,
    symm_thm old_pcr new_data,
    check_symm_thm old_pcr new_data claimed_pcr,
    discriminating_thm old_pcr new_data⟩

/-! ## Imperative implementation -/

/-- Imperative transcription of the Python function: a mutable PCR register is extended
step by step inside the `Id` monad (XOR with the new data, LCG mixing, 32-bit mask) and a
mutable verdict flag is then set by comparing the register with the claimed PCR. -/
def safe_tpm_hash_check_imp (old_pcr new_data claimed_pcr : Nat) : Bool := Id.run do
  let mut pcr := old_pcr
  -- extend: pcr <- H(pcr || new_data), simulated as XOR + mixing + 32-bit mask
  pcr := pcr ^^^ new_data
  pcr := pcr * lcg_mul
  pcr := pcr + lcg_inc
  pcr := pcr % word32_mod
  let mut verdict := false
  if claimed_pcr == pcr then
    verdict := true
  return verdict

/-- Imperative transcription of the Python `check()` driver. -/
def python_check_imp : Bool :=
  safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0 &&
    !safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD &&
    !safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 &&
    safe_tpm_hash_check_imp 0 0 expected_zero

/-! ## Imperative tests -/

example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0 = true := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check_imp 0 0 expected_zero = true := by native_decide
example : python_check_imp = true := by native_decide

example : (List.range 40).all
    (fun n => safe_tpm_hash_check_imp n (2 * n + 1) (simulated_hash n (2 * n + 1))) = true := by
  native_decide

example : (List.range 40).all (fun n => safe_tpm_hash_check_imp n (n + 3) 0xDEAD = false) = true := by
  native_decide

-- bounded PBT over edge-case inputs: imperative and functional verdicts agree
example : edge_inputs.all (fun a => edge_inputs.all (fun b => edge_inputs.all (fun c =>
    safe_tpm_hash_check_imp a b c == safe_tpm_hash_check a b c))) = true := by
  native_decide

#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check_imp 0 0 expected_zero
#eval if python_check_imp then "All tests passed." else "TEST FAILURE"

theorem imp_expected_0_thm : safe_tpm_hash_check_imp 0xAAAA 0xBBBB expected_0 = true := by decide

theorem imp_forged_thm : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD = false := by decide

theorem imp_arbitrary_thm : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 = false := by decide

theorem imp_expected_zero_thm : safe_tpm_hash_check_imp 0 0 expected_zero = true := by decide

theorem imp_python_check_thm : python_check_imp = true := by decide

/-! ## Equivalence of the functional and the imperative implementations -/

theorem equivalence_thm (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr =
      safe_tpm_hash_check old_pcr new_data claimed_pcr := by
  simp only [safe_tpm_hash_check_imp, safe_tpm_hash_check, simulated_hash, mix32]
  split <;> simp [*]

theorem imp_accept_thm (old_pcr new_data : Nat) :
    safe_tpm_hash_check_imp old_pcr new_data (simulated_hash old_pcr new_data) = true := by
  rw [equivalence_thm]
  exact accept_thm old_pcr new_data

theorem imp_reject_thm (old_pcr new_data claimed_pcr : Nat) :
    claimed_pcr ≠ simulated_hash old_pcr new_data →
      safe_tpm_hash_check_imp old_pcr new_data claimed_pcr = false :=
  fun h => by
    rw [equivalence_thm]
    exact reject_thm old_pcr new_data claimed_pcr h

theorem imp_sound_thm (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr = true →
      claimed_pcr = simulated_hash old_pcr new_data :=
  fun h => by
    rw [equivalence_thm] at h
    exact sound_thm old_pcr new_data claimed_pcr h

theorem imp_decide_thm (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr =
      decide (claimed_pcr = simulated_hash old_pcr new_data) := by
  rw [equivalence_thm]
  exact decide_thm old_pcr new_data claimed_pcr

/-- The imperative implementation satisfies the same post-condition as the functional one. -/
theorem imp_post_thm (old_pcr new_data claimed_pcr : Nat)
    (_h : Pre old_pcr new_data claimed_pcr) :
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr =
        safe_tpm_hash_check old_pcr new_data claimed_pcr ∧
      (safe_tpm_hash_check_imp old_pcr new_data claimed_pcr = true ↔
        claimed_pcr = simulated_hash old_pcr new_data) := by
  refine ⟨equivalence_thm old_pcr new_data claimed_pcr, ?_⟩
  rw [equivalence_thm]
  exact iff_thm old_pcr new_data claimed_pcr

end «125_unsafeTPMHash_safe»

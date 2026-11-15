import Mathlib
import Plausible

/-!
# Safe TPM PCR hash check

Lean 4 formalization of a safe TPM PCR extend check. The Python program returns
true only when the claimed PCR equals a simulated extend

`H(old_pcr || new_data) = ((old_pcr XOR new_data) * mulConst + addConst) & 0xFFFFFFFF`.

Non-negative Python ints are modelled as Nat. For those inputs,
`& 0xFFFFFFFF` is exactly reduction modulo `2^32`. Negative Python integers are
outside this model; PCR values and the masked hash are non-negative, and every
Python test in the source uses non-negative inputs.

The checker itself is exact: a claim is accepted if and only if it equals that
simulated hash. The mixing function is still XOR-based, so distinct extension
pairs that share an XOR collide. That is a property of the simulated hash, not
a failure of the equality check.
-/

namespace «125_unsafeTPMHash_safe»

/-- LCG multiplier used by the Python simulated extend. -/
def mulConst : Nat := 6364136223846793005

/-- LCG increment used by the Python simulated extend. -/
def addConst : Nat := 1442695040888963407

/-- 32-bit mask `0xFFFFFFFF`, matching Python `& 0xFFFFFFFF`. -/
def mask32 : Nat := 0xFFFFFFFF

theorem mask32_eq : mask32 = 2 ^ 32 - 1 := by
  decide

/-- Simulated TPM extend from the Python source. -/
def simulatedHash (old_pcr new_data : Nat) : Nat :=
  ((old_pcr ^^^ new_data) * mulConst + addConst) &&& mask32

/-- Returns true only when claimed_pcr equals the simulated extend. -/
def safe_tpm_hash_check (old_pcr new_data claimed_pcr : Nat) : Bool :=
  claimed_pcr == simulatedHash old_pcr new_data

/-- The definition is the Python arithmetic expression, not a rewritten form. -/
theorem simulatedHash_eq_python_formula (old_pcr new_data : Nat) :
    simulatedHash old_pcr new_data =
      ((old_pcr ^^^ new_data) * 6364136223846793005 +
        1442695040888963407) &&& 0xFFFFFFFF := by
  unfold simulatedHash mulConst addConst mask32
  rfl

/-- Python bitwise-and with 0xFFFFFFFF on this non-negative expression is mod 2^32. -/
theorem simulatedHash_eq_mod (old_pcr new_data : Nat) :
    simulatedHash old_pcr new_data =
      ((old_pcr ^^^ new_data) * mulConst + addConst) % 2 ^ 32 := by
  unfold simulatedHash
  rw [mask32_eq, Nat.and_two_pow_sub_one_eq_mod]

/-- If two naturals agree modulo n, so do x * m + c and y * m + c. -/
theorem mul_add_mod_eq_of_mod_eq {n x y m c : Nat} (h : x % n = y % n) :
    (x * m + c) % n = (y * m + c) % n := by
  simp [Nat.add_mod, Nat.mul_mod, h]

/-! ## Unit tests -/

theorem expected_hash_aaaa_bbbb : simulatedHash 0xAAAA 0xBBBB = 4207341644 := by
  decide

theorem expected_hash_zero : simulatedHash 0 0 = 4150755663 := by
  decide

example : safe_tpm_hash_check 0xAAAA 0xBBBB 4207341644 = true := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check 0 0 4150755663 = true := by native_decide
example : simulatedHash 0xAAAA 0xBBBB = 0xFAC6F04C := by native_decide
example : simulatedHash 0 0 = 0xF767814F := by native_decide

#eval safe_tpm_hash_check 0xAAAA 0xBBBB 4207341644
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234
#eval safe_tpm_hash_check 0 0 4150755663
#eval simulatedHash 0xAAAA 0xBBBB
#eval simulatedHash 0 0

def pythonChecksPass : Bool :=
  let expected_0 :=
    ((0xAAAA ^^^ 0xBBBB) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF
  let expected_zero :=
    ((0 ^^^ 0) * 6364136223846793005 + 1442695040888963407) &&& 0xFFFFFFFF
  safe_tpm_hash_check 0xAAAA 0xBBBB expected_0 &&
    !safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD &&
    !safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 &&
    safe_tpm_hash_check 0 0 expected_zero

theorem pythonChecksPass_thm : pythonChecksPass = true := by
  decide

/-! ## Pre-condition -/

/-- Every Nat triple is admissible in this non-negative model of the Python ints. -/
def Pre (old_pcr new_data claimed_pcr : Nat) : Prop :=
  old_pcr + new_data + claimed_pcr ≥ 0

/-! ## Properties -/

def returns_true_iff_hash_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true ↔
    claimed_pcr = simulatedHash old_pcr new_data

theorem returns_true_iff_hash_thm (old_pcr new_data claimed_pcr : Nat) :
    returns_true_iff_hash_prop old_pcr new_data claimed_pcr := by
  unfold returns_true_iff_hash_prop safe_tpm_hash_check
  simp [beq_iff_eq]

def hash_in_range_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data < 2 ^ 32

theorem hash_in_range_thm (old_pcr new_data : Nat) :
    hash_in_range_prop old_pcr new_data := by
  unfold hash_in_range_prop simulatedHash
  rw [mask32_eq]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos 32) Nat.zero_lt_one)

def forgery_rejected_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  claimed_pcr ≠ simulatedHash old_pcr new_data →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem forgery_rejected_thm (old_pcr new_data claimed_pcr : Nat) :
    forgery_rejected_prop old_pcr new_data claimed_pcr := by
  unfold forgery_rejected_prop safe_tpm_hash_check
  intro hne
  simpa [beq_eq_false_iff_ne] using hne

def correct_accepted_prop (old_pcr new_data : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true

theorem correct_accepted_thm (old_pcr new_data : Nat) :
    correct_accepted_prop old_pcr new_data := by
  unfold correct_accepted_prop safe_tpm_hash_check
  simp

def accepted_implies_in_range_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  safe_tpm_hash_check old_pcr new_data claimed_pcr = true →
    claimed_pcr < 2 ^ 32

theorem accepted_implies_in_range_thm (old_pcr new_data claimed_pcr : Nat) :
    accepted_implies_in_range_prop old_pcr new_data claimed_pcr := by
  intro h
  have heq : claimed_pcr = simulatedHash old_pcr new_data :=
    (returns_true_iff_hash_thm old_pcr new_data claimed_pcr).mp h
  rw [heq]
  exact hash_in_range_thm old_pcr new_data

def large_claim_rejected_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  2 ^ 32 ≤ claimed_pcr →
    safe_tpm_hash_check old_pcr new_data claimed_pcr = false

theorem large_claim_rejected_thm (old_pcr new_data claimed_pcr : Nat) :
    large_claim_rejected_prop old_pcr new_data claimed_pcr := by
  intro hge
  apply forgery_rejected_thm old_pcr new_data claimed_pcr
  intro heq
  have hlt : claimed_pcr < 2 ^ 32 := by
    rw [heq]
    exact hash_in_range_thm old_pcr new_data
  omega

def unique_accepted_prop (old_pcr new_data : Nat) : Prop :=
  ∃! claimed_pcr : Nat, safe_tpm_hash_check old_pcr new_data claimed_pcr = true

theorem unique_accepted_thm (old_pcr new_data : Nat) :
    unique_accepted_prop old_pcr new_data := by
  unfold unique_accepted_prop
  refine ExistsUnique.intro (simulatedHash old_pcr new_data)
    (correct_accepted_thm old_pcr new_data) ?_
  intro c hc
  exact (returns_true_iff_hash_thm old_pcr new_data c).mp hc

def hash_depends_on_xor_prop (a b c d : Nat) : Prop :=
  a ^^^ b = c ^^^ d → simulatedHash a b = simulatedHash c d

theorem hash_depends_on_xor_thm (a b c d : Nat) :
    hash_depends_on_xor_prop a b c d := by
  intro h
  unfold simulatedHash
  rw [h]

def xor_symmetric_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data = simulatedHash new_data old_pcr

theorem xor_symmetric_thm (old_pcr new_data : Nat) :
    xor_symmetric_prop old_pcr new_data := by
  unfold xor_symmetric_prop simulatedHash
  rw [Nat.xor_comm]

def low32_inputs_prop (old_pcr new_data : Nat) : Prop :=
  simulatedHash old_pcr new_data =
    simulatedHash (old_pcr &&& mask32) (new_data &&& mask32)

theorem low32_inputs_thm (old_pcr new_data : Nat) :
    low32_inputs_prop old_pcr new_data := by
  unfold low32_inputs_prop
  simp only [simulatedHash, mask32_eq, Nat.and_two_pow_sub_one_eq_mod]
  apply mul_add_mod_eq_of_mod_eq
  rw [Nat.xor_mod_two_pow]
  symm
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow
  · exact Nat.mod_lt _ (Nat.two_pow_pos 32)
  · exact Nat.mod_lt _ (Nat.two_pow_pos 32)

theorem xor_collision_accepted_thm (a b c d : Nat) (h : a ^^^ b = c ^^^ d) :
    safe_tpm_hash_check a b (simulatedHash c d) = true := by
  have hh : simulatedHash a b = simulatedHash c d := hash_depends_on_xor_thm a b c d h
  rw [← hh]
  exact correct_accepted_thm a b

theorem python_assert_correct_accepted :
    safe_tpm_hash_check 0xAAAA 0xBBBB (simulatedHash 0xAAAA 0xBBBB) = true :=
  correct_accepted_thm 0xAAAA 0xBBBB

theorem python_assert_dead_rejected :
    safe_tpm_hash_check 0xAAAA 0xBBBB 0xDEAD = false := by
  decide

theorem python_assert_arbitrary_rejected :
    safe_tpm_hash_check 0xAAAA 0xBBBB 0x1234 = false := by
  decide

theorem python_assert_zero_accepted :
    safe_tpm_hash_check 0 0 (simulatedHash 0 0) = true :=
  correct_accepted_thm 0 0

/-! ## Post-condition -/

def Post_prop (old_pcr new_data claimed_pcr : Nat) : Prop :=
  returns_true_iff_hash_prop old_pcr new_data claimed_pcr ∧
    hash_in_range_prop old_pcr new_data ∧
    forgery_rejected_prop old_pcr new_data claimed_pcr ∧
    correct_accepted_prop old_pcr new_data ∧
    accepted_implies_in_range_prop old_pcr new_data claimed_pcr ∧
    large_claim_rejected_prop old_pcr new_data claimed_pcr

/-! ## Property-based tests -/

#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      (claimed_pcr == simulatedHash old_pcr new_data))

#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat, simulatedHash old_pcr new_data < 2 ^ 32)

#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr : Nat,
    claimed_pcr ≠ simulatedHash old_pcr new_data →
      safe_tpm_hash_check old_pcr new_data claimed_pcr = false)

#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true)

-- accepted_implies_in_range_prop: the only accepted claim is the hash, so test that case directly.
#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true ∧
      simulatedHash old_pcr new_data < 2 ^ 32)

-- large_claim_rejected_prop, sampled on every k via claimed = 2^32 + k.
#eval Plausible.Testable.check
  (∀ old_pcr new_data k : Nat,
    safe_tpm_hash_check old_pcr new_data (2 ^ 32 + k) = false)

-- hash_depends_on_xor_prop. Every colliding c is a ^^^ b ^^^ d for c ^^^ d = a ^^^ b.
#eval Plausible.Testable.check
  (∀ a b d : Nat, simulatedHash a b = simulatedHash (a ^^^ b ^^^ d) d)

#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    simulatedHash old_pcr new_data = simulatedHash new_data old_pcr)

#eval Plausible.Testable.check
  (∀ old_pcr new_data : Nat,
    simulatedHash old_pcr new_data =
      simulatedHash (old_pcr &&& mask32) (new_data &&& mask32))

-- Executable form of Post_prop. Oversized claims are sampled as 2^32 + k so the
-- guard 2^32 ≤ claimed does not make Plausible give up.
#eval Plausible.Testable.check
  (∀ old_pcr new_data claimed_pcr k : Nat,
    (safe_tpm_hash_check old_pcr new_data claimed_pcr =
        (claimed_pcr == simulatedHash old_pcr new_data)) ∧
      simulatedHash old_pcr new_data < 2 ^ 32 ∧
      (claimed_pcr ≠ simulatedHash old_pcr new_data →
        safe_tpm_hash_check old_pcr new_data claimed_pcr = false) ∧
      safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true ∧
      (safe_tpm_hash_check old_pcr new_data (simulatedHash old_pcr new_data) = true →
        simulatedHash old_pcr new_data < 2 ^ 32) ∧
      safe_tpm_hash_check old_pcr new_data (2 ^ 32 + k) = false)

example : (List.range 12).all (fun old =>
    (List.range 12).all (fun new =>
      (List.range 12).all (fun claimed =>
        safe_tpm_hash_check old new claimed ==
          (claimed == simulatedHash old new)))) = true := by
  native_decide

example : (List.range 40).all (fun n =>
    simulatedHash n (n * 3 + 7) < 2 ^ 32) = true := by
  native_decide

example : (List.range 20).all (fun n =>
    safe_tpm_hash_check n (n + 1) 0 = false ∨ simulatedHash n (n + 1) = 0) = true := by
  native_decide

example : (List.range 30).all (fun n =>
    safe_tpm_hash_check n (2 * n + 5) (simulatedHash n (2 * n + 5)) = true) = true := by
  native_decide

example : (List.range 16).all (fun n =>
    safe_tpm_hash_check n (n + 3) (2 ^ 32 + n) = false) = true := by
  native_decide

example : (List.range 24).all (fun n =>
    simulatedHash (n + 2 ^ 32) (n + 7) =
      simulatedHash ((n + 2 ^ 32) &&& mask32) ((n + 7) &&& mask32)) = true := by
  native_decide

example : (List.range 25).all (fun n =>
    simulatedHash n (40 - n) = simulatedHash (40 - n) n) = true := by
  native_decide

-- Bounded PBT for unique_accepted_prop: on a finite window there is exactly one hit,
-- namely the simulated hash when it lies in that window. The unrestricted
-- ExistsUnique quantifier is not exhaustively executable over Nat.
example : (List.range 8).all (fun old =>
    (List.range 8).all (fun new =>
      ((List.range 64).filter (fun claimed =>
        safe_tpm_hash_check old new claimed)).length ≤ 1)) = true := by
  native_decide

example : (List.range 10).all (fun a =>
    (List.range 10).all (fun b =>
      (List.range 10).all (fun c =>
        (List.range 10).all (fun d =>
          a ^^^ b != c ^^^ d || simulatedHash a b == simulatedHash c d)))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (old_pcr new_data claimed_pcr : Nat) :
    Pre old_pcr new_data claimed_pcr →
      Post_prop old_pcr new_data claimed_pcr := by
  intro _hPre
  exact ⟨returns_true_iff_hash_thm old_pcr new_data claimed_pcr,
    hash_in_range_thm old_pcr new_data,
    forgery_rejected_thm old_pcr new_data claimed_pcr,
    correct_accepted_thm old_pcr new_data,
    accepted_implies_in_range_thm old_pcr new_data claimed_pcr,
    large_claim_rejected_thm old_pcr new_data claimed_pcr⟩

/-! ## Imperative implementation -/

def safe_tpm_hash_check_imp (old_pcr new_data claimed_pcr : Nat) : Bool :=
  Id.run do
    let mut old : Nat := old_pcr
    let mut data : Nat := new_data
    let mut mixed : Nat := old ^^^ data
    mixed := mixed * mulConst
    mixed := mixed + addConst
    mixed := mixed &&& mask32
    let mut accepted : Bool := claimed_pcr == mixed
    return accepted

/-! ## Imperative tests -/

example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 4207341644 = true := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD = false := by native_decide
example : safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0x1234 = false := by native_decide
example : safe_tpm_hash_check_imp 0 0 4150755663 = true := by native_decide

#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 4207341644
#eval safe_tpm_hash_check_imp 0xAAAA 0xBBBB 0xDEAD
#eval safe_tpm_hash_check_imp 0 0 4150755663

/-! ## Equivalence -/

theorem functional_eq_imperative_thm (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check old_pcr new_data claimed_pcr =
      safe_tpm_hash_check_imp old_pcr new_data claimed_pcr := by
  delta safe_tpm_hash_check_imp safe_tpm_hash_check simulatedHash
  simp only [Id.run_pure]

theorem imp_returns_true_iff_hash_thm (old_pcr new_data claimed_pcr : Nat) :
    safe_tpm_hash_check_imp old_pcr new_data claimed_pcr = true ↔
      claimed_pcr = simulatedHash old_pcr new_data := by
  rw [← functional_eq_imperative_thm]
  exact returns_true_iff_hash_thm old_pcr new_data claimed_pcr

end «125_unsafeTPMHash_safe»

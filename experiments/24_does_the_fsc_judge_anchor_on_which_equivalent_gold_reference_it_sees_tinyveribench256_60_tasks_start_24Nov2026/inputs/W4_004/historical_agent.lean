import Mathlib
namespace Agent

/-!
# Safe certificate-chain validation

Translation of the Python `safe_cert_chain` and its three-assertion test harness.
Python's unbounded signed integers are modeled by `Int`. The executable condition
is strictly positive, not merely nonzero: negative signatures are rejected too.
A positive integer represents a valid CA endorsement in this simplified model;
no cryptographic verification beyond the source program's test is asserted.

The Boolean `check` records whether all three Python assertions succeed.
The specification covers every integer, without a positivity precondition.
-/

namespace UnsafeCertChainSafe

/-! ## Functional implementation -/

def safe_cert_chain (ca_signature : Int) : Bool :=
  decide (0 < ca_signature)

/-- Boolean form of the assertions in Python's `check`. -/
def check (candidate : Int → Bool) : Bool :=
  candidate 12345 && !(candidate 0) && candidate 1

/-! ## Unit tests -/

example : safe_cert_chain 12345 = true := by native_decide
example : safe_cert_chain 0 = false := by native_decide
example : safe_cert_chain 1 = true := by native_decide
example : safe_cert_chain (-1) = false := by native_decide
example : safe_cert_chain (-12345) = false := by native_decide
example : check safe_cert_chain = true := by native_decide

#eval safe_cert_chain 12345
#eval safe_cert_chain 0
#eval safe_cert_chain 1
#eval safe_cert_chain (-1)
#eval check safe_cert_chain
#eval if check safe_cert_chain then "All tests passed." else "Candidate failed tests"

/-! ## Precondition -/

/-- The Python function is defined for every integer. -/
def Pre (_ca_signature : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Acceptance is exactly strict positivity, including both directions. -/
def acceptance_prop (ca_signature : Int) : Prop :=
  safe_cert_chain ca_signature = true ↔ 0 < ca_signature

theorem acceptance_thm (ca_signature : Int) : acceptance_prop ca_signature := by
  simp [acceptance_prop, safe_cert_chain]

/-- Zero and every negative signature are rejected, and only those are rejected. -/
def rejection_prop (ca_signature : Int) : Prop :=
  safe_cert_chain ca_signature = false ↔ ca_signature ≤ 0

theorem rejection_thm (ca_signature : Int) : rejection_prop ca_signature := by
  simp [rejection_prop, safe_cert_chain, not_lt]

/-- Acceptance requires an endorsement; a zero signature can never suffice. -/
def endorsement_prop (ca_signature : Int) : Prop :=
  safe_cert_chain ca_signature = true → ca_signature ≠ 0

theorem endorsement_thm (ca_signature : Int) : endorsement_prop ca_signature := by
  intro h
  have hpositive : 0 < ca_signature := (acceptance_thm ca_signature).mp h
  omega

/-- Every valid (positive) signature is accepted. -/
theorem positive_signature_accepted_thm (ca_signature : Int)
    (h : 0 < ca_signature) : safe_cert_chain ca_signature = true := by
  exact (acceptance_thm ca_signature).mpr h

/-- The missing-endorsement case that the Python fix specifically addresses. -/
theorem zero_signature_rejected_thm : safe_cert_chain 0 = false := by
  exact (rejection_thm 0).mpr (le_refl 0)

/-- The source program's assertions also hold by kernel computation. -/
theorem check_safe_cert_chain_thm : check safe_cert_chain = true := by
  decide

/-! ## Postcondition -/

def Post_prop (ca_signature : Int) : Prop :=
  acceptance_prop ca_signature ∧
  rejection_prop ca_signature ∧
  endorsement_prop ca_signature

/-! ## Property-based tests

Each executable property, including the conjunction in `Post_prop`, is tested
on all 201 integers from -100 through 100. These tests use Boolean counterparts
of the propositions and are evidence only, not dependencies of any theorem.
-/

def pbtSignatures : List Int :=
  (List.range 201).map (fun n => (n : Int) - 100)

-- PBT for acceptance_prop: acceptance iff strictly positive.
example : pbtSignatures.all (fun s =>
    safe_cert_chain s == decide (0 < s)) = true := by
  native_decide

-- PBT for rejection_prop: rejection iff nonpositive.
example : pbtSignatures.all (fun s =>
    (!safe_cert_chain s) == decide (s ≤ 0)) = true := by
  native_decide

-- PBT for endorsement_prop: acceptance implies a nonzero endorsement.
example : pbtSignatures.all (fun s =>
    (!safe_cert_chain s) || decide (s ≠ 0)) = true := by
  native_decide

-- PBT for Post_prop: the complete conjunction of the three Boolean properties.
example : pbtSignatures.all (fun s =>
    (safe_cert_chain s == decide (0 < s)) &&
    ((!safe_cert_chain s) == decide (s ≤ 0)) &&
    ((!safe_cert_chain s) || decide (s ≠ 0))) = true := by
  native_decide

#eval pbtSignatures.all (fun s =>
  (safe_cert_chain s == decide (0 < s)) &&
  ((!safe_cert_chain s) == decide (s ≤ 0)) &&
  ((!safe_cert_chain s) || decide (s ≠ 0)))

/-! ## Correctness -/

theorem safe_cert_chain_correct (ca_signature : Int) :
    Pre ca_signature → Post_prop ca_signature := by
  intro _
  exact ⟨acceptance_thm ca_signature, rejection_thm ca_signature,
    endorsement_thm ca_signature⟩

/-! ## Imperative implementation -/

def safe_cert_chain_imperative (ca_signature : Int) : Bool := Id.run do
  let mut accepted := false
  if 0 < ca_signature then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_cert_chain_imperative 12345 = true := by native_decide
example : safe_cert_chain_imperative 0 = false := by native_decide
example : safe_cert_chain_imperative 1 = true := by native_decide
example : safe_cert_chain_imperative (-1) = false := by native_decide
example : safe_cert_chain_imperative (-12345) = false := by native_decide
example : check safe_cert_chain_imperative = true := by native_decide

#eval safe_cert_chain_imperative 12345
#eval safe_cert_chain_imperative 0
#eval safe_cert_chain_imperative 1
#eval safe_cert_chain_imperative (-1)
#eval check safe_cert_chain_imperative

-- Additional bounded test of functional/imperative agreement.
example : pbtSignatures.all (fun s =>
    safe_cert_chain s == safe_cert_chain_imperative s) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_eq_imperative (ca_signature : Int) :
    safe_cert_chain ca_signature = safe_cert_chain_imperative ca_signature := by
  by_cases h : 0 < ca_signature <;>
    simp [safe_cert_chain, safe_cert_chain_imperative, h]

end UnsafeCertChainSafe
end Agent

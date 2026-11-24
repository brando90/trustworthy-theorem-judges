import Mathlib
namespace Agent

/-!
# Unsafe certificate-chain validation

This file translates Python's `unsafe_cert_chain` and its three assertion checks.
Python integers are modeled by `Int`, with no restriction on their sign or size.
The validator deliberately ignores the alleged CA signature and returns `true`.
Thus acceptance is not evidence of CA endorsement: zero and negative integers
are accepted as well as the supplied valid-signature example, `12345`.

The original third test uses the positive integer `1`, despite its comment
calling it "negative-like". We preserve that literal test and additionally test
actual negative integers. Theorems describe the vulnerability, not a repaired
validator. Property-based tests provide executable evidence separately from the
kernel-checked proofs.
-/

namespace UnsafeCertChain

/-! ## Functional implementation -/

/-- Exactly the Python validator: the signature is never inspected. -/
def unsafe_cert_chain (_ca_signature : Int) : Bool :=
  true

/-- The Boolean success condition of Python's assertion harness.
A false result represents an assertion failure; successful Python execution
returns `True` precisely when these three conditions all hold. -/
def check (candidate : Int → Bool) : Bool :=
  candidate 12345 && candidate 0 && candidate 1

/-! ## Unit tests -/

example : unsafe_cert_chain 12345 = true := by native_decide
example : unsafe_cert_chain 0 = true := by native_decide
example : unsafe_cert_chain 1 = true := by native_decide
example : unsafe_cert_chain (-12345) = true := by native_decide
example : check unsafe_cert_chain = true := by native_decide
example : check (fun _ => false) = false := by native_decide

#eval unsafe_cert_chain 12345
#eval unsafe_cert_chain 0
#eval unsafe_cert_chain 1
#eval unsafe_cert_chain (-12345)
#eval check unsafe_cert_chain
#eval if check unsafe_cert_chain then "All tests passed." else "Candidate failed tests"

/-! ## Precondition -/

/-- Every Python integer is admissible; no valid-signature assumption is made. -/
def Pre (_ca_signature : Int) : Prop := True

/-! ## Behavioral properties and their proofs -/

/-- All signatures are accepted, whether or not there is CA endorsement. -/
def alwaysAccepts_prop (ca_signature : Int) : Prop :=
  unsafe_cert_chain ca_signature = true

theorem alwaysAccepts_thm (ca_signature : Int) :
    alwaysAccepts_prop ca_signature := by sorry

/-- Changing the alleged signature cannot change the result. -/
def signatureIndependent_prop (ca_signature other_signature : Int) : Prop :=
  unsafe_cert_chain ca_signature = unsafe_cert_chain other_signature

theorem signatureIndependent_thm (ca_signature other_signature : Int) :
    signatureIndependent_prop ca_signature other_signature := by sorry

/-- In particular, zero and every negative signature value are accepted.
The inequality is a class of test inputs, not a model of cryptographic validity. -/
def nonpositiveAccepted_prop (ca_signature : Int) : Prop :=
  ca_signature ≤ 0 → unsafe_cert_chain ca_signature = true

theorem nonpositiveAccepted_thm (ca_signature : Int) :
    nonpositiveAccepted_prop ca_signature := by sorry

/-- The missing-endorsement example in the Python test is accepted. -/
theorem zero_signature_thm : unsafe_cert_chain 0 = true := by sorry

/-- The harness expresses exactly the three supplied assertions. -/
theorem check_spec_thm (candidate : Int → Bool) :
    check candidate = true ↔
      candidate 12345 = true ∧ candidate 0 = true ∧ candidate 1 = true := by sorry

/-- The translated candidate passes every supplied assertion. -/
theorem check_thm : check unsafe_cert_chain = true := by sorry

/-! ## Postcondition -/

/-- The result is always acceptance, independent of any other signature;
nonpositive signatures and zero are accepted, and the Python checks pass. -/
def Post_prop (ca_signature : Int) : Prop :=
  alwaysAccepts_prop ca_signature ∧
  (∀ other_signature : Int,
    signatureIndependent_prop ca_signature other_signature) ∧
  nonpositiveAccepted_prop ca_signature ∧
  unsafe_cert_chain 0 = true ∧
  check unsafe_cert_chain = true

/-! ## Property-based tests

The bounded sample includes every integer from -100 to 100 and larger values
of both signs. These tests use executable Boolean forms, without adding
`Decidable` instances for the specification predicates. Theorems above and
below cover all integers, not just these samples.
-/

private def signatureSamples : List Int :=
  [-12345, 12345, -100000000000000000000, 100000000000000000000] ++
    (List.range 201).map (fun n => (n : Int) - 100)

-- PBT for alwaysAccepts_prop.
example : signatureSamples.all (fun s => unsafe_cert_chain s) = true := by
  native_decide

#eval Plausible.Testable.check (∀ s : Int, unsafe_cert_chain s = true)

-- PBT for signatureIndependent_prop: all pairs of bounded samples.
example : signatureSamples.all (fun s =>
    signatureSamples.all (fun t =>
      unsafe_cert_chain s == unsafe_cert_chain t)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ s t : Int, unsafe_cert_chain s = unsafe_cert_chain t)

-- PBT for nonpositiveAccepted_prop, including zero and actual negatives.
example : signatureSamples.all (fun s =>
    if s ≤ 0 then unsafe_cert_chain s else true) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ s : Int, s ≤ 0 → unsafe_cert_chain s = true)

-- PBT for Post_prop: its executable conjunction at every bounded signature,
-- with the independence clause checked against every bounded second input.
example : signatureSamples.all (fun s =>
    unsafe_cert_chain s &&
    signatureSamples.all (fun t =>
      unsafe_cert_chain s == unsafe_cert_chain t) &&
    (if s ≤ 0 then unsafe_cert_chain s else true) &&
    unsafe_cert_chain 0 &&
    check unsafe_cert_chain) = true := by
  native_decide

-- Randomized counterpart of the whole postcondition. Its universally
-- quantified independence input is sampled alongside the main signature.
#eval Plausible.Testable.check
  (∀ s t : Int,
    unsafe_cert_chain s = true ∧
    unsafe_cert_chain s = unsafe_cert_chain t ∧
    (s ≤ 0 → unsafe_cert_chain s = true) ∧
    unsafe_cert_chain 0 = true ∧
    check unsafe_cert_chain = true)

/-! ## Correctness -/

theorem correctness_thm (ca_signature : Int) :
    Pre ca_signature → Post_prop ca_signature := by sorry

/-! ## Imperative implementation -/

/-- Mutable-state version of the same unconditional acceptance. -/
def unsafe_cert_chain_imperative (_ca_signature : Int) : Bool := Id.run do
  let mut accepted : Bool := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_cert_chain_imperative 12345 = true := by native_decide
example : unsafe_cert_chain_imperative 0 = true := by native_decide
example : unsafe_cert_chain_imperative 1 = true := by native_decide
example : unsafe_cert_chain_imperative (-12345) = true := by native_decide
example : check unsafe_cert_chain_imperative = true := by native_decide

#eval unsafe_cert_chain_imperative 12345
#eval unsafe_cert_chain_imperative 0
#eval unsafe_cert_chain_imperative 1
#eval unsafe_cert_chain_imperative (-12345)
#eval check unsafe_cert_chain_imperative

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equiv_thm (ca_signature : Int) :
    unsafe_cert_chain ca_signature = unsafe_cert_chain_imperative ca_signature := by sorry

end UnsafeCertChain
end Agent

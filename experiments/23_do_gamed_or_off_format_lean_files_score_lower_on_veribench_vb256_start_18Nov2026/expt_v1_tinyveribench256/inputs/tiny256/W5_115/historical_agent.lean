import Mathlib
namespace Agent

/-!
# Unsafe U2F origin verification

Translation of the vulnerable U2F verifier in MIT 6.858 Quiz 1 (Spring 2020),
Question 5. Both origins are arbitrary strings and are deliberately ignored:
only a valid signature and an exactly matching challenge are required. Thus a
phishing origin can relay a challenge and obtain acceptance. We model the
signature-validity flag supplied to the Python function, not cryptography or
origin hashing themselves.

The Boolean `check` is the success/failure interpretation of the Python assertion
harness. Named theorems are kernel-proved; `native_decide` is used only for tests.
Bounded property-based tests exercise empty strings, distinct origins, exact and
near-matching challenges, Unicode, and both signature-validity flags.
-/

namespace UnsafeU2FOrigin

abbrev Verifier := String → String → String → String → Bool → Bool

/-- The origin check is intentionally absent, exactly as in the Python source. -/
def unsafe_u2f_verify
    (_expected_origin _signed_origin challenge signed_challenge : String)
    (signature_valid : Bool) : Bool :=
  signature_valid && (challenge == signed_challenge)

/-- Boolean rendition of the five Python assertions, in their original order. -/
def check (candidate : Verifier) : Bool :=
  candidate "hash(bank.com)" "hash(bank.com)" "abc123" "abc123" true &&
  candidate "hash(bank.com)" "hash(banc.com)" "abc123" "abc123" true &&
  !(candidate "hash(bank.com)" "hash(bank.com)" "abc123" "xyz999" true) &&
  !(candidate "hash(bank.com)" "hash(bank.com)" "abc123" "abc123" false) &&
  !(candidate "hash(bank.com)" "hash(evil.com)" "abc123" "xyz999" true)

-- 1. Normal operation.
example : unsafe_u2f_verify "hash(bank.com)" "hash(bank.com)"
    "abc123" "abc123" true = true := by native_decide

-- 2. The phishing origin is accepted: this is the vulnerability, not a fix.
example : unsafe_u2f_verify "hash(bank.com)" "hash(banc.com)"
    "abc123" "abc123" true = true := by native_decide

-- 3. A challenge mismatch is rejected.
example : unsafe_u2f_verify "hash(bank.com)" "hash(bank.com)"
    "abc123" "xyz999" true = false := by native_decide

-- 4. An invalid signature is rejected.
example : unsafe_u2f_verify "hash(bank.com)" "hash(bank.com)"
    "abc123" "abc123" false = false := by native_decide

-- 5. Both the origin and the challenge differ; the challenge causes rejection.
example : unsafe_u2f_verify "hash(bank.com)" "hash(evil.com)"
    "abc123" "xyz999" true = false := by native_decide

example : check unsafe_u2f_verify = true := by native_decide
#eval check unsafe_u2f_verify
#eval if check unsafe_u2f_verify then "All tests passed."
      else "Candidate failed U2F origin check tests"

/-- Every tuple of strings and a Boolean is admissible; even empty strings are allowed. -/
def Pre (_expected_origin _signed_origin _challenge _signed_challenge : String)
    (_signature_valid : Bool) : Prop := True

section Specifications

variable (expected_origin signed_origin challenge signed_challenge : String)
variable (signature_valid : Bool)

/-- Exact necessary and sufficient conditions for acceptance. -/
def acceptance_prop : Prop :=
  unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = true ↔
    signature_valid = true ∧ challenge = signed_challenge

theorem acceptance_thm :
    acceptance_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  cases signature_valid <;> simp [acceptance_prop, unsafe_u2f_verify]

/-- Exact necessary and sufficient conditions for rejection. -/
def rejection_prop : Prop :=
  unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = false ↔
    signature_valid = false ∨ challenge ≠ signed_challenge

theorem rejection_thm :
    rejection_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  cases signature_valid <;> simp [rejection_prop, unsafe_u2f_verify]

/-- Replacing both origins by a fixed canonical pair leaves the answer unchanged.
Since the original pair is arbitrary, the answer is independent of both origins. -/
def origin_independence_prop : Prop :=
  unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid =
    unsafe_u2f_verify "" "" challenge signed_challenge signature_valid

theorem origin_independence_thm :
    origin_independence_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  rfl

/-- Matching challenges with a valid signature succeed, including normal operation. -/
def matching_challenge_acceptance_prop : Prop :=
  signature_valid = true → challenge = signed_challenge →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = true

theorem matching_challenge_acceptance_thm :
    matching_challenge_acceptance_prop expected_origin signed_origin challenge signed_challenge
      signature_valid := by
  intro hsig hchallenge
  simp [unsafe_u2f_verify, hsig, hchallenge]

/-- A different, potentially phishing origin is still accepted when the relay
preserves the challenge and the signature is valid. No origin equality is assumed. -/
def mitm_acceptance_prop : Prop :=
  expected_origin ≠ signed_origin → signature_valid = true → challenge = signed_challenge →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = true

theorem mitm_acceptance_thm :
    mitm_acceptance_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  intro _ hsig hchallenge
  simp [unsafe_u2f_verify, hsig, hchallenge]

/-- A challenge mismatch is rejected regardless of either origin or the signature flag. -/
def challenge_mismatch_prop : Prop :=
  challenge ≠ signed_challenge →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = false

theorem challenge_mismatch_thm :
    challenge_mismatch_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  intro hchallenge
  simp [unsafe_u2f_verify, hchallenge]

/-- An invalid signature is rejected regardless of all strings. -/
def invalid_signature_prop : Prop :=
  signature_valid = false →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = false

theorem invalid_signature_thm :
    invalid_signature_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  intro hsig
  simp [unsafe_u2f_verify, hsig]

/-- Full specification, intentionally documenting rather than repairing the vulnerability. -/
def Post_prop : Prop :=
  acceptance_prop expected_origin signed_origin challenge signed_challenge signature_valid ∧
  rejection_prop expected_origin signed_origin challenge signed_challenge signature_valid ∧
  origin_independence_prop expected_origin signed_origin challenge signed_challenge signature_valid ∧
  matching_challenge_acceptance_prop expected_origin signed_origin challenge signed_challenge signature_valid ∧
  mitm_acceptance_prop expected_origin signed_origin challenge signed_challenge signature_valid ∧
  challenge_mismatch_prop expected_origin signed_origin challenge signed_challenge signature_valid ∧
  invalid_signature_prop expected_origin signed_origin challenge signed_challenge signature_valid

-- Executable Boolean counterparts of every property. These spell out the
-- propositions and do not require Decidable instances for the named Prop definitions.
def acceptance_test : Bool :=
  decide (unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = true ↔
    signature_valid = true ∧ challenge = signed_challenge)

def rejection_test : Bool :=
  decide (unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = false ↔
    signature_valid = false ∨ challenge ≠ signed_challenge)

def origin_independence_test : Bool :=
  decide (unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid =
    unsafe_u2f_verify "" "" challenge signed_challenge signature_valid)

def matching_challenge_acceptance_test : Bool :=
  decide (signature_valid = true → challenge = signed_challenge →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = true)

def mitm_acceptance_test : Bool :=
  decide (expected_origin ≠ signed_origin → signature_valid = true → challenge = signed_challenge →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = true)

def challenge_mismatch_test : Bool :=
  decide (challenge ≠ signed_challenge →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = false)

def invalid_signature_test : Bool :=
  decide (signature_valid = false →
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid = false)

/-- Executable counterpart of the entire conjunctive postcondition. -/
def post_test : Bool :=
  acceptance_test expected_origin signed_origin challenge signed_challenge signature_valid &&
  rejection_test expected_origin signed_origin challenge signed_challenge signature_valid &&
  origin_independence_test expected_origin signed_origin challenge signed_challenge signature_valid &&
  matching_challenge_acceptance_test expected_origin signed_origin challenge signed_challenge signature_valid &&
  mitm_acceptance_test expected_origin signed_origin challenge signed_challenge signature_valid &&
  challenge_mismatch_test expected_origin signed_origin challenge signed_challenge signature_valid &&
  invalid_signature_test expected_origin signed_origin challenge signed_challenge signature_valid

end Specifications

-- Bounded PBT: exhaustive products, not a restriction on any theorem's domain.
def sampleOrigins : List String :=
  ["", "hash(bank.com)", "hash(banc.com)", "hash(evil.com)",
   "https://bank.com:443", "銀行.example", "abc123"]

def sampleChallenges : List String :=
  ["", "abc123", "xyz999", "ABC123", "abc123 ", "0", "hash(bank.com)", "挑戦🔐"]

/-- Check all 7 × 7 × 8 × 8 × 2 = 6,272 combinations, including both matching
and mismatching challenges/origins. Implication checks therefore are nonvacuous. -/
def allSampleInputs (property : Verifier) : Bool :=
  sampleOrigins.all fun expected =>
    sampleOrigins.all fun signed =>
      sampleChallenges.all fun challenge =>
        sampleChallenges.all fun signedChallenge =>
          [false, true].all fun valid =>
            property expected signed challenge signedChallenge valid

-- PBT for acceptance_prop.
example : allSampleInputs acceptance_test = true := by native_decide
-- PBT for rejection_prop.
example : allSampleInputs rejection_test = true := by native_decide
-- PBT for origin_independence_prop.
example : allSampleInputs origin_independence_test = true := by native_decide
-- PBT for matching_challenge_acceptance_prop.
example : allSampleInputs matching_challenge_acceptance_test = true := by native_decide
-- PBT for mitm_acceptance_prop.
example : allSampleInputs mitm_acceptance_test = true := by native_decide
-- PBT for challenge_mismatch_prop.
example : allSampleInputs challenge_mismatch_test = true := by native_decide
-- PBT for invalid_signature_prop.
example : allSampleInputs invalid_signature_test = true := by native_decide
-- PBT for Post_prop, using the conjunction of all seven executable properties.
example : allSampleInputs post_test = true := by native_decide

#eval [("acceptance", allSampleInputs acceptance_test),
       ("rejection", allSampleInputs rejection_test),
       ("origin independence", allSampleInputs origin_independence_test),
       ("matching challenge", allSampleInputs matching_challenge_acceptance_test),
       ("phishing acceptance", allSampleInputs mitm_acceptance_test),
       ("challenge mismatch", allSampleInputs challenge_mismatch_test),
       ("invalid signature", allSampleInputs invalid_signature_test),
       ("postcondition", allSampleInputs post_test)]

/-- Correctness holds on the entire Python input domain, without any origin restriction. -/
theorem correctness_thm
    (expected_origin signed_origin challenge signed_challenge : String)
    (signature_valid : Bool) :
    Pre expected_origin signed_origin challenge signed_challenge signature_valid →
      Post_prop expected_origin signed_origin challenge signed_challenge signature_valid := by
  intro _
  exact ⟨acceptance_thm expected_origin signed_origin challenge signed_challenge signature_valid,
    rejection_thm expected_origin signed_origin challenge signed_challenge signature_valid,
    origin_independence_thm expected_origin signed_origin challenge signed_challenge signature_valid,
    matching_challenge_acceptance_thm expected_origin signed_origin challenge signed_challenge signature_valid,
    mitm_acceptance_thm expected_origin signed_origin challenge signed_challenge signature_valid,
    challenge_mismatch_thm expected_origin signed_origin challenge signed_challenge signature_valid,
    invalid_signature_thm expected_origin signed_origin challenge signed_challenge signature_valid⟩

/-- Imperative translation: start rejected, test the signature first, then the
challenge, and mutate the result on success. Neither origin is inspected. -/
def unsafe_u2f_verify_imperative
    (_expected_origin _signed_origin challenge signed_challenge : String)
    (signature_valid : Bool) : Bool := Id.run do
  let mut accepted := false
  if signature_valid then
    if challenge == signed_challenge then
      accepted := true
  return accepted

-- The same five Python cases for the imperative version.
example : unsafe_u2f_verify_imperative "hash(bank.com)" "hash(bank.com)"
    "abc123" "abc123" true = true := by native_decide
example : unsafe_u2f_verify_imperative "hash(bank.com)" "hash(banc.com)"
    "abc123" "abc123" true = true := by native_decide
example : unsafe_u2f_verify_imperative "hash(bank.com)" "hash(bank.com)"
    "abc123" "xyz999" true = false := by native_decide
example : unsafe_u2f_verify_imperative "hash(bank.com)" "hash(bank.com)"
    "abc123" "abc123" false = false := by native_decide
example : unsafe_u2f_verify_imperative "hash(bank.com)" "hash(evil.com)"
    "abc123" "xyz999" true = false := by native_decide
example : check unsafe_u2f_verify_imperative = true := by native_decide
#eval check unsafe_u2f_verify_imperative

-- Bounded equivalence test in addition to the universal kernel proof below.
example : allSampleInputs (fun e o c sc valid =>
    unsafe_u2f_verify e o c sc valid == unsafe_u2f_verify_imperative e o c sc valid) = true := by
  native_decide
#eval allSampleInputs (fun e o c sc valid =>
  unsafe_u2f_verify e o c sc valid == unsafe_u2f_verify_imperative e o c sc valid)

/-- Functional and mutable implementations agree for every input, not only samples. -/
theorem functional_imperative_equiv
    (expected_origin signed_origin challenge signed_challenge : String)
    (signature_valid : Bool) :
    unsafe_u2f_verify expected_origin signed_origin challenge signed_challenge signature_valid =
      unsafe_u2f_verify_imperative expected_origin signed_origin challenge signed_challenge signature_valid := by
  cases signature_valid <;> cases h : (challenge == signed_challenge) <;>
    simp [unsafe_u2f_verify, unsafe_u2f_verify_imperative, h]

end UnsafeU2FOrigin
end Agent

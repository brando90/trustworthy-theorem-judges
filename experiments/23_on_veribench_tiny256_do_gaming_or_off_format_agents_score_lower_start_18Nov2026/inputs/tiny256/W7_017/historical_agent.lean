import Mathlib
namespace Agent

/-!
# Unsafe certificate hostname validation

Translation of the Python `unsafe_cert_hostname` function and its test harness.
A certificate is accepted exactly when its validity and non-expiry flags are true.
Neither the requested hostname nor the certificate SAN is examined: in particular,
a valid, unexpired certificate for an attacker-controlled hostname is accepted.
This file models that vulnerability, not RFC 6125-compliant hostname verification.

Strings and Boolean flags have no additional input restrictions. Kernel-checked
proofs cover all inputs; the finite executable tests are supplementary evidence.
-/

namespace UnsafeCertHostname

/-- Deliberately unsafe: the two hostname arguments are ignored. -/
def unsafe_cert_hostname (_requested_host _cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  cert_valid && cert_not_expired

/-- Boolean version of all eight assertions in the Python `check` function. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  candidate "bank.com" "bank.com" true true &&
  candidate "bank.com" "evil.com" true true &&
  candidate "secure.example.com" "attacker.com" true true &&
  !(candidate "bank.com" "bank.com" false true) &&
  !(candidate "bank.com" "bank.com" true false) &&
  candidate "bank.com" "*.evil.com" true true &&
  candidate "" "evil.com" true true &&
  !(candidate "bank.com" "bank.com" false false)

-- Unit tests: exactly the eight assertions of the source program.
example : unsafe_cert_hostname "bank.com" "bank.com" true true = true := by
  native_decide
example : unsafe_cert_hostname "bank.com" "evil.com" true true = true := by
  native_decide
example : unsafe_cert_hostname "secure.example.com" "attacker.com" true true = true := by
  native_decide
example : unsafe_cert_hostname "bank.com" "bank.com" false true = false := by
  native_decide
example : unsafe_cert_hostname "bank.com" "bank.com" true false = false := by
  native_decide
example : unsafe_cert_hostname "bank.com" "*.evil.com" true true = true := by
  native_decide
example : unsafe_cert_hostname "" "evil.com" true true = true := by
  native_decide
example : unsafe_cert_hostname "bank.com" "bank.com" false false = false := by
  native_decide
example : check unsafe_cert_hostname = true := by native_decide

#eval check unsafe_cert_hostname
#eval if check unsafe_cert_hostname then "All tests passed." else "Candidate failed tests"

/-- All strings (including empty ones) and all Boolean flag combinations are allowed. -/
def Pre (_requested_host _cert_san : String)
    (_cert_valid _cert_not_expired : Bool) : Prop := True

/-- Acceptance has exactly the two certificate-flag requirements, and no others. -/
def acceptance_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true ↔
    cert_valid = true ∧ cert_not_expired = true

theorem acceptance_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    acceptance_prop requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;>
    simp [acceptance_prop, unsafe_cert_hostname]

/-- Rejection occurs exactly when at least one certificate check fails. -/
def rejection_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false ↔
    cert_valid = false ∨ cert_not_expired = false

theorem rejection_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    rejection_prop requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;>
    simp [rejection_prop, unsafe_cert_hostname]

/-- Changing either or both hostname strings cannot change the decision. -/
def hostname_independence_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  ∀ other_requested_host other_cert_san : String,
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname other_requested_host other_cert_san cert_valid cert_not_expired

theorem hostname_independence_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    hostname_independence_prop requested_host cert_san cert_valid cert_not_expired := by
  intro other_requested_host other_cert_san
  rfl

/-- The vulnerability: a hostname mismatch is accepted if both flags pass. -/
def mismatch_accepted_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  requested_host ≠ cert_san → cert_valid = true → cert_not_expired = true →
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem mismatch_accepted_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    mismatch_accepted_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _hMismatch hValid hNotExpired
  simp [unsafe_cert_hostname, hValid, hNotExpired]

/-- An invalid certificate is rejected regardless of the expiry flag or hostnames. -/
def invalid_rejected_prop (requested_host cert_san : String)
    (cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san false cert_not_expired = false

theorem invalid_rejected_thm (requested_host cert_san : String)
    (cert_not_expired : Bool) :
    invalid_rejected_prop requested_host cert_san cert_not_expired := by
  simp [invalid_rejected_prop, unsafe_cert_hostname]

/-- An expired certificate is rejected regardless of the validity flag or hostnames. -/
def expired_rejected_prop (requested_host cert_san : String)
    (cert_valid : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid false = false

theorem expired_rejected_thm (requested_host cert_san : String)
    (cert_valid : Bool) :
    expired_rejected_prop requested_host cert_san cert_valid := by
  cases cert_valid <;> rfl

/-- Combined contract, describing the unsafe behavior rather than repairing it. -/
def Post_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  acceptance_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejection_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_independence_prop requested_host cert_san cert_valid cert_not_expired ∧
  mismatch_accepted_prop requested_host cert_san cert_valid cert_not_expired ∧
  invalid_rejected_prop requested_host cert_san cert_not_expired ∧
  expired_rejected_prop requested_host cert_san cert_valid

/-!
## Bounded property-based tests

Exhaustively test the Cartesian product of this hostname corpus and both Boolean
flags. The corpus includes matching and mismatching names, wildcard strings,
empty names, case differences, trailing dots, and a non-ASCII name. Independence
also varies both replacement strings independently. These finite checks do not
restrict the domains of any of the theorems above.
-/

private def hostnameSamples : List String :=
  ["", "bank.com", "evil.com", "secure.example.com", "attacker.com", "*.evil.com",
   "*.bank.com", "BANK.COM", "bank.com.", "localhost", "127.0.0.1", "例え.jp"]

private def boolSamples : List Bool := [false, true]

private def allInputs (p : String → String → Bool → Bool → Bool) : Bool :=
  hostnameSamples.all fun requested_host =>
    hostnameSamples.all fun cert_san =>
      boolSamples.all fun cert_valid =>
        boolSamples.all fun cert_not_expired =>
          p requested_host cert_san cert_valid cert_not_expired

-- Executable Boolean counterpart of acceptance_prop.
private def acceptanceCheck (h s : String) (v e : Bool) : Bool :=
  (unsafe_cert_hostname h s v e == true) == (v && e)

-- Executable Boolean counterpart of rejection_prop.
private def rejectionCheck (h s : String) (v e : Bool) : Bool :=
  (unsafe_cert_hostname h s v e == false) == (!v || !e)

-- Bounded executable counterpart of the universally quantified hostname property.
private def hostnameIndependenceCheck (h s : String) (v e : Bool) : Bool :=
  hostnameSamples.all fun other_host =>
    hostnameSamples.all fun other_san =>
      unsafe_cert_hostname h s v e == unsafe_cert_hostname other_host other_san v e

-- Boolean implication: (different names AND passing flags) implies acceptance.
private def mismatchAcceptedCheck (h s : String) (v e : Bool) : Bool :=
  !(h != s && v && e) || (unsafe_cert_hostname h s v e == true)

private def invalidRejectedCheck (h s : String) (_v e : Bool) : Bool :=
  unsafe_cert_hostname h s false e == false

private def expiredRejectedCheck (h s : String) (v _e : Bool) : Bool :=
  unsafe_cert_hostname h s v false == false

-- Executable counterpart of every conjunct of Post_prop.
private def postCheck (h s : String) (v e : Bool) : Bool :=
  acceptanceCheck h s v e && rejectionCheck h s v e &&
  hostnameIndependenceCheck h s v e && mismatchAcceptedCheck h s v e &&
  invalidRejectedCheck h s v e && expiredRejectedCheck h s v e

-- One independently checked PBT for each property, plus the combined postcondition.
example : allInputs acceptanceCheck = true := by native_decide
example : allInputs rejectionCheck = true := by native_decide
example : allInputs hostnameIndependenceCheck = true := by native_decide
example : allInputs mismatchAcceptedCheck = true := by native_decide
example : allInputs invalidRejectedCheck = true := by native_decide
example : allInputs expiredRejectedCheck = true := by native_decide
example : allInputs postCheck = true := by native_decide

#eval [("acceptance", allInputs acceptanceCheck),
       ("rejection", allInputs rejectionCheck),
       ("hostname independence", allInputs hostnameIndependenceCheck),
       ("mismatch accepted", allInputs mismatchAcceptedCheck),
       ("invalid rejected", allInputs invalidRejectedCheck),
       ("expired rejected", allInputs expiredRejectedCheck),
       ("postcondition", allInputs postCheck)]

/-- Total correctness of the functional implementation under the unrestricted Pre. -/
theorem correctness_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    Pre requested_host cert_san cert_valid cert_not_expired →
      Post_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _hPre
  exact ⟨acceptance_thm requested_host cert_san cert_valid cert_not_expired,
    rejection_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_independence_thm requested_host cert_san cert_valid cert_not_expired,
    mismatch_accepted_thm requested_host cert_san cert_valid cert_not_expired,
    invalid_rejected_thm requested_host cert_san cert_not_expired,
    expired_rejected_thm requested_host cert_san cert_valid⟩

/-- Stateful spelling of the same two Boolean checks; hostnames are still ignored. -/
def unsafe_cert_hostname_imperative (_requested_host _cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool := Id.run do
  let mut accepted := false
  if cert_valid then
    if cert_not_expired then
      accepted := true
  return accepted

-- The same eight source assertions exercise the imperative implementation.
example : check unsafe_cert_hostname_imperative = true := by native_decide
example : unsafe_cert_hostname_imperative "bank.com" "evil.com" true true = true := by
  native_decide
example : unsafe_cert_hostname_imperative "bank.com" "bank.com" false true = false := by
  native_decide
example : unsafe_cert_hostname_imperative "bank.com" "bank.com" true false = false := by
  native_decide
#eval check unsafe_cert_hostname_imperative

-- A bounded cross-implementation test is evidence separate from the following proof.
example : allInputs (fun h s v e =>
    unsafe_cert_hostname h s v e == unsafe_cert_hostname_imperative h s v e) = true := by
  native_decide

/-- Functional and imperative results agree for every input, with no precondition. -/
theorem functional_imperative_equivalence_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname_imperative requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;> rfl

end UnsafeCertHostname
end Agent

import Mathlib

/-!
# Unsafe certificate hostname validation

This file translates the Python `unsafe_cert_hostname` function. It accepts a
certificate exactly when its validity and non-expiry flags are both true, and
never examines the requested hostname or certificate Subject Alternative Name.
In particular, a valid, unexpired certificate for `evil.com` is accepted for
`bank.com`: the missing hostname verification vulnerability is preserved.

All strings (including empty strings and wildcard names) and both Boolean values
are admissible. The properties below describe this unsafe behavior, not the
hostname verification required by RFC 6125. Bounded property-based tests accompany
the universal proofs, and a mutable implementation is proved equivalent.
-/

namespace UnsafeCertHostname

/- Functional implementation. -/

def unsafe_cert_hostname (_requested_host _cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  cert_valid && cert_not_expired

/- Unit tests: all eight assertions from the Python source. -/

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

/-- The Python `check` harness, expressed as a Boolean conjunction. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  candidate "bank.com" "bank.com" true true &&
  candidate "bank.com" "evil.com" true true &&
  candidate "secure.example.com" "attacker.com" true true &&
  !(candidate "bank.com" "bank.com" false true) &&
  !(candidate "bank.com" "bank.com" true false) &&
  candidate "bank.com" "*.evil.com" true true &&
  candidate "" "evil.com" true true &&
  !(candidate "bank.com" "bank.com" false false)

#eval check unsafe_cert_hostname

/- Precondition: the Python function imposes no restrictions on its typed inputs. -/

def Pre (_requested_host _cert_san : String)
    (_cert_valid _cert_not_expired : Bool) : Prop :=
  True

/- Properties and their universal proofs. -/

/-- Acceptance is equivalent to both certificate flags being true. -/
def acceptance_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true ↔
    cert_valid = true ∧ cert_not_expired = true

theorem acceptance_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    acceptance_prop requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;>
    simp [acceptance_prop, unsafe_cert_hostname]

/-- Changing either or both hostname strings has no effect on the result. -/
def hostname_independence_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  ∀ other_host other_san : String,
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname other_host other_san cert_valid cert_not_expired

theorem hostname_independence_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    hostname_independence_prop requested_host cert_san cert_valid cert_not_expired := by
  intro other_host other_san
  rfl

/-- A hostname mismatch cannot prevent acceptance of a valid, unexpired cert. -/
def hostname_mismatch_accepted_prop (requested_host cert_san : String) : Prop :=
  requested_host ≠ cert_san →
    unsafe_cert_hostname requested_host cert_san true true = true

theorem hostname_mismatch_accepted_thm (requested_host cert_san : String) :
    hostname_mismatch_accepted_prop requested_host cert_san := by
  intro _
  rfl

/-- An invalid certificate is rejected for either expiry flag and any names. -/
def invalid_cert_rejected_prop (requested_host cert_san : String)
    (cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san false cert_not_expired = false

theorem invalid_cert_rejected_thm (requested_host cert_san : String)
    (cert_not_expired : Bool) :
    invalid_cert_rejected_prop requested_host cert_san cert_not_expired := by
  rfl

/-- An expired certificate is rejected for either validity flag and any names. -/
def expired_cert_rejected_prop (requested_host cert_san : String)
    (cert_valid : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid false = false

theorem expired_cert_rejected_thm (requested_host cert_san : String)
    (cert_valid : Bool) :
    expired_cert_rejected_prop requested_host cert_san cert_valid := by
  cases cert_valid <;> rfl

/- Postcondition. -/

def Post_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  acceptance_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_independence_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_mismatch_accepted_prop requested_host cert_san ∧
  invalid_cert_rejected_prop requested_host cert_san cert_not_expired ∧
  expired_cert_rejected_prop requested_host cert_san cert_valid

/- Property-based tests.

The bounded domain contains 12 representative strings and every Boolean value.
Each test checks all 576 input tuples. The independence test additionally checks
all 144 replacement hostname pairs per tuple (82,944 comparisons). The proofs
above still quantify over all strings; only these executable tests are bounded.
-/

def hostnameSamples : List String :=
  ["", "bank.com", "evil.com", "secure.example.com", "attacker.com", "*.evil.com",
   "*.bank.com", "BANK.COM", "bank.com.", "localhost", "127.0.0.1", "bücher.example"]

def boolSamples : List Bool := [false, true]

def allInputs (p : String → String → Bool → Bool → Bool) : Bool :=
  hostnameSamples.all fun requested_host =>
    hostnameSamples.all fun cert_san =>
      boolSamples.all fun cert_valid =>
        boolSamples.all fun cert_not_expired =>
          p requested_host cert_san cert_valid cert_not_expired

/-- Executable form of `acceptance_prop` (Boolean equality expresses iff). -/
def acceptanceCheck (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  (unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired == true) ==
    ((cert_valid == true) && (cert_not_expired == true))

/-- Bounded executable form of `hostname_independence_prop`. -/
def hostnameIndependenceCheck (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  hostnameSamples.all fun other_host =>
    hostnameSamples.all fun other_san =>
      unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired ==
        unsafe_cert_hostname other_host other_san cert_valid cert_not_expired

/-- Executable implication for `hostname_mismatch_accepted_prop`. -/
def hostnameMismatchCheck (requested_host cert_san : String) : Bool :=
  (requested_host == cert_san) ||
    (unsafe_cert_hostname requested_host cert_san true true == true)

/-- Executable form of `invalid_cert_rejected_prop`. -/
def invalidCertCheck (requested_host cert_san : String) (cert_not_expired : Bool) : Bool :=
  unsafe_cert_hostname requested_host cert_san false cert_not_expired == false

/-- Executable form of `expired_cert_rejected_prop`. -/
def expiredCertCheck (requested_host cert_san : String) (cert_valid : Bool) : Bool :=
  unsafe_cert_hostname requested_host cert_san cert_valid false == false

/-- Executable conjunction for `Post_prop`, with bounded hostname replacements. -/
def postCheck (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  acceptanceCheck requested_host cert_san cert_valid cert_not_expired &&
  hostnameIndependenceCheck requested_host cert_san cert_valid cert_not_expired &&
  hostnameMismatchCheck requested_host cert_san &&
  invalidCertCheck requested_host cert_san cert_not_expired &&
  expiredCertCheck requested_host cert_san cert_valid

-- PBT for acceptance_prop.
example : allInputs acceptanceCheck = true := by native_decide
#eval allInputs acceptanceCheck

-- PBT for hostname_independence_prop.
example : allInputs hostnameIndependenceCheck = true := by native_decide
#eval allInputs hostnameIndependenceCheck

-- PBT for hostname_mismatch_accepted_prop; unequal pairs are included extensively.
example : allInputs (fun h s _ _ => hostnameMismatchCheck h s) = true := by native_decide
#eval allInputs (fun h s _ _ => hostnameMismatchCheck h s)

-- PBT for invalid_cert_rejected_prop.
example : allInputs (fun h s _ n => invalidCertCheck h s n) = true := by native_decide
#eval allInputs (fun h s _ n => invalidCertCheck h s n)

-- PBT for expired_cert_rejected_prop.
example : allInputs (fun h s v _ => expiredCertCheck h s v) = true := by native_decide
#eval allInputs (fun h s v _ => expiredCertCheck h s v)

-- PBT for the complete Post_prop conjunction.
example : allInputs postCheck = true := by native_decide
#eval allInputs postCheck

/- Correctness for every admissible input. -/

theorem correctness_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    Pre requested_host cert_san cert_valid cert_not_expired →
      Post_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _
  exact ⟨acceptance_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_independence_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_mismatch_accepted_thm requested_host cert_san,
    invalid_cert_rejected_thm requested_host cert_san cert_not_expired,
    expired_cert_rejected_thm requested_host cert_san cert_valid⟩

/- Imperative implementation, preserving the short-circuit Boolean decision. -/

def unsafe_cert_hostname_imperative (_requested_host _cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool := Id.run do
  let mut accepted := false
  if cert_valid then
    accepted := cert_not_expired
  return accepted

/- Imperative tests: the same eight Python assertions and bounded equivalence. -/

example : check unsafe_cert_hostname_imperative = true := by native_decide
#eval check unsafe_cert_hostname_imperative

example : allInputs (fun h s v n =>
    unsafe_cert_hostname h s v n == unsafe_cert_hostname_imperative h s v n) = true := by
  native_decide

#eval allInputs (fun h s v n =>
  unsafe_cert_hostname h s v n == unsafe_cert_hostname_imperative h s v n)

/- Equivalence for arbitrary strings and certificate flags. -/

theorem functional_imperative_equivalence_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname_imperative requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> rfl

end UnsafeCertHostname

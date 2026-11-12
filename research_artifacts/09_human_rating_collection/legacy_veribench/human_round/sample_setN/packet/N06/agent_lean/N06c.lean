import Mathlib

/-!
# Unsafe certificate hostname validation

A direct translation of the Python `unsafe_cert_hostname` program. A certificate
is accepted exactly when it is valid and not expired. Neither the requested
hostname nor the certificate's Subject Alternative Name (SAN) is inspected.
This intentionally preserves the vulnerability: a valid, unexpired certificate
for `evil.com` is accepted when connecting to `bank.com`.

The specification covers every String and Bool input, including empty strings
and wildcard SANs. It describes the unsafe behavior, not RFC 6125 hostname
verification. Bounded property-based tests supplement, but do not replace, the
universally quantified kernel-checked proofs.
-/

namespace UnsafeCertHostname

/-! ## Functional implementation -/

/-- Python's Boolean `cert_valid and cert_not_expired`; both names are ignored. -/
def unsafe_cert_hostname (_requested_host _cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  cert_valid && cert_not_expired

/-- Executable conjunction of the eight assertions in Python's `check`. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  candidate "bank.com" "bank.com" true true &&
  candidate "bank.com" "evil.com" true true &&
  candidate "secure.example.com" "attacker.com" true true &&
  !(candidate "bank.com" "bank.com" false true) &&
  !(candidate "bank.com" "bank.com" true false) &&
  candidate "bank.com" "*.evil.com" true true &&
  candidate "" "evil.com" true true &&
  !(candidate "bank.com" "bank.com" false false)

/-! ## Unit tests: all eight Python assertions -/

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
example : check unsafe_cert_hostname = true := by
  native_decide

#eval check unsafe_cert_hostname
#eval if check unsafe_cert_hostname then "All tests passed." else "Candidate failed tests"

/-! ## Precondition -/

/-- The Python function imposes no restrictions on its typed inputs. -/
def Pre (_requested_host _cert_san : String)
    (_cert_valid _cert_not_expired : Bool) : Prop :=
  True

/-! ## Semantic properties and proofs -/

/-- Acceptance depends exactly on the two certificate status flags. -/
def acceptance_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true ↔
    cert_valid = true ∧ cert_not_expired = true

theorem acceptance_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    acceptance_prop requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;>
    simp [acceptance_prop, unsafe_cert_hostname]

/-- The only reasons for rejection are invalidity or expiration. -/
def rejection_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false ↔
    cert_valid = false ∨ cert_not_expired = false

theorem rejection_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    rejection_prop requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;>
    simp [rejection_prop, unsafe_cert_hostname]

/-- Changing either or both hostnames cannot change the decision. -/
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

/-- Normal operation: a matching, valid, unexpired certificate is accepted. -/
def matching_hostname_prop (host : String) : Prop :=
  unsafe_cert_hostname host host true true = true

theorem matching_hostname_thm (host : String) : matching_hostname_prop host := by
  rfl

/-- Vulnerability: even a different SAN is accepted when both status flags pass. -/
def hostname_mismatch_prop (requested_host cert_san : String) : Prop :=
  requested_host ≠ cert_san →
    unsafe_cert_hostname requested_host cert_san true true = true

theorem hostname_mismatch_thm (requested_host cert_san : String) :
    hostname_mismatch_prop requested_host cert_san := by
  intro _mismatch
  rfl

/-- Invalid certificates are rejected regardless of expiry and hostnames. -/
def invalid_rejected_prop (requested_host cert_san : String)
    (cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san false cert_not_expired = false

theorem invalid_rejected_thm (requested_host cert_san : String)
    (cert_not_expired : Bool) :
    invalid_rejected_prop requested_host cert_san cert_not_expired := by
  rfl

/-- Expired certificates are rejected regardless of validity and hostnames. -/
def expired_rejected_prop (requested_host cert_san : String)
    (cert_valid : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid false = false

theorem expired_rejected_thm (requested_host cert_san : String)
    (cert_valid : Bool) :
    expired_rejected_prop requested_host cert_san cert_valid := by
  cases cert_valid <;> rfl

/-! ## Postcondition -/

/-- Full behavior, including normal operation and the hostname-check omission. -/
def Post_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  acceptance_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejection_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_independence_prop requested_host cert_san cert_valid cert_not_expired ∧
  matching_hostname_prop requested_host ∧
  hostname_mismatch_prop requested_host cert_san ∧
  invalid_rejected_prop requested_host cert_san cert_not_expired ∧
  expired_rejected_prop requested_host cert_san cert_valid

/-! ## Bounded property-based tests

Each property below is checked in executable Boolean form. We exhaust every
combination of the two Bool flags and all pairs from ten representative strings.
The string domain includes the original examples, empty names, wildcards,
case differences, trailing dots, and a Unicode name. Independence also varies
both replacement hostnames over the same domain (40,000 total input tuples).
These finite tests do not restrict the domains of the theorems above.
-/

def hostSamples : List String :=
  ["", "bank.com", "evil.com", "secure.example.com", "attacker.com",
   "*.evil.com", "*.bank.com", "BANK.COM", "bank.com.", "例え.テスト"]

def boolSamples : List Bool := [false, true]

def allHosts (p : String → String → Bool) : Bool :=
  hostSamples.all fun requested_host =>
    hostSamples.all fun cert_san => p requested_host cert_san

def allInputs (p : String → String → Bool → Bool → Bool) : Bool :=
  allHosts fun requested_host cert_san =>
    boolSamples.all fun cert_valid =>
      boolSamples.all fun cert_not_expired =>
        p requested_host cert_san cert_valid cert_not_expired

/-- Boolean form of `acceptance_prop`. -/
def acceptanceCheck (h s : String) (v n : Bool) : Bool :=
  unsafe_cert_hostname h s v n == (v && n)

/-- Boolean form of `rejection_prop`. -/
def rejectionCheck (h s : String) (v n : Bool) : Bool :=
  (!(unsafe_cert_hostname h s v n)) == ((!v) || (!n))

/-- Bounded Boolean form of the universal hostname-independence property. -/
def independenceCheck (h s : String) (v n : Bool) : Bool :=
  allHosts fun other_h other_s =>
    unsafe_cert_hostname h s v n == unsafe_cert_hostname other_h other_s v n

/-- Boolean form of `matching_hostname_prop`. -/
def matchingCheck (h : String) : Bool :=
  unsafe_cert_hostname h h true true

/-- `h ≠ s → accepted` is executable as `h == s || accepted`. -/
def mismatchCheck (h s : String) : Bool :=
  (h == s) || unsafe_cert_hostname h s true true

/-- Boolean form of `invalid_rejected_prop`. -/
def invalidCheck (h s : String) (n : Bool) : Bool :=
  !(unsafe_cert_hostname h s false n)

/-- Boolean form of `expired_rejected_prop`. -/
def expiredCheck (h s : String) (v : Bool) : Bool :=
  !(unsafe_cert_hostname h s v false)

-- PBT for acceptance_prop: 400 combinations.
example : allInputs acceptanceCheck = true := by native_decide

-- PBT for rejection_prop: 400 combinations.
example : allInputs rejectionCheck = true := by native_decide

-- PBT for hostname_independence_prop: 40,000 combinations.
example : allInputs independenceCheck = true := by native_decide

-- PBT for matching_hostname_prop: every sampled name, including the empty name.
example : hostSamples.all matchingCheck = true := by native_decide

-- PBT for hostname_mismatch_prop: both matching and nonmatching name pairs.
example : allHosts mismatchCheck = true := by native_decide

-- PBT for invalid_rejected_prop: every name pair and both expiry flags.
example : allHosts (fun h s => boolSamples.all (invalidCheck h s)) = true := by
  native_decide

-- PBT for expired_rejected_prop: every name pair and both validity flags.
example : allHosts (fun h s => boolSamples.all (expiredCheck h s)) = true := by
  native_decide

/-- Executable bounded conjunction of all seven clauses of `Post_prop`. -/
def postCheck (h s : String) (v n : Bool) : Bool :=
  acceptanceCheck h s v n &&
  rejectionCheck h s v n &&
  independenceCheck h s v n &&
  matchingCheck h &&
  mismatchCheck h s &&
  invalidCheck h s n &&
  expiredCheck h s v

-- PBT for Post_prop; Pre is True, so no inputs need to be filtered out.
example : allInputs postCheck = true := by native_decide
#eval allInputs postCheck

/-! ## Correctness: unrestricted precondition implies the full postcondition -/

theorem correctness_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    Pre requested_host cert_san cert_valid cert_not_expired →
      Post_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _pre
  exact ⟨acceptance_thm requested_host cert_san cert_valid cert_not_expired,
    rejection_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_independence_thm requested_host cert_san cert_valid cert_not_expired,
    matching_hostname_thm requested_host,
    hostname_mismatch_thm requested_host cert_san,
    invalid_rejected_thm requested_host cert_san cert_not_expired,
    expired_rejected_thm requested_host cert_san cert_valid⟩

/-! ## Imperative implementation -/

/-- Mutable-state version of Python's short-circuit Boolean conjunction. -/
def unsafe_cert_hostname_imperative (_requested_host _cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool := Id.run do
  let mut accepted := false
  if cert_valid then
    accepted := cert_not_expired
  return accepted

/-! ## Imperative tests -/

-- Re-run exactly the eight original assertions against the imperative version.
example : check unsafe_cert_hostname_imperative = true := by native_decide
#eval check unsafe_cert_hostname_imperative

-- Bounded cross-implementation test for all sampled names and status flags.
example : allInputs (fun h s v n =>
    unsafe_cert_hostname h s v n == unsafe_cert_hostname_imperative h s v n) = true := by
  native_decide
#eval allInputs (fun h s v n =>
  unsafe_cert_hostname h s v n == unsafe_cert_hostname_imperative h s v n)

/-! ## Functional-imperative equivalence -/

theorem equivalence_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname_imperative requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;> rfl

end UnsafeCertHostname

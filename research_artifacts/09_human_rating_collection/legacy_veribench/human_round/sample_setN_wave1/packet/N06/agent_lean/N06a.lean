import Mathlib
import Plausible

/-!
# Unsafe Certificate Hostname Validation

Formalization of the Python program `unsafe_cert_hostname` from MIT 6.858 Lecture 15
(Certificates, RFC 6125 hostname verification).

Vulnerability: A client connects to `requested_host` (e.g., `bank.com`), the server
presents a valid, non-expired certificate for `cert_san` (e.g., `evil.com`), and the
client accepts it without checking Subject Alternative Name (SAN) or Common Name (CN).
This enables Man-in-the-Middle (MITM) attacks even with valid certificates.
-/

namespace «75_unsafeCertHostname»

set_option linter.unusedVariables false

/-! ## 1. Functional Implementation -/

/-- Returns `true` if `cert_valid` and `cert_not_expired` both hold — `requested_host`
and `cert_san` are never checked. -/
def unsafe_cert_hostname (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Bool :=
  cert_valid && cert_not_expired

/-- Reference safe hostname verification (checks exact SAN match in addition to validity
and non-expiration) to contrast with `unsafe_cert_hostname`. -/
def safe_cert_hostname (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Bool :=
  (requested_host == cert_san) && cert_valid && cert_not_expired

/-- Test suite translated from the Python `check` function. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  -- 1) Normal operation - exact hostname match accepted
  (candidate "bank.com" "bank.com" true true == true) &&
  -- 2) Vulnerability: hostname mismatch accepted (MITM attack succeeds)
  (candidate "bank.com" "evil.com" true true == true) &&
  (candidate "secure.example.com" "attacker.com" true true == true) &&
  -- 3) Still rejects invalid/expired certs
  (candidate "bank.com" "bank.com" false true == false) &&
  (candidate "bank.com" "bank.com" true false == false) &&
  -- 4) Edge cases
  (candidate "bank.com" "*.evil.com" true true == true) &&
  (candidate "" "evil.com" true true == true) &&
  (candidate "bank.com" "bank.com" false false == false)

/-! ## 2. Unit Tests -/

-- 1) Normal operation - exact hostname match accepted
example : unsafe_cert_hostname "bank.com" "bank.com" true true = true := by native_decide

-- 2) Vulnerability: hostname mismatch accepted (MITM attack succeeds)
example : unsafe_cert_hostname "bank.com" "evil.com" true true = true := by native_decide
example : unsafe_cert_hostname "secure.example.com" "attacker.com" true true = true := by native_decide

-- 3) Still rejects invalid/expired certs
example : unsafe_cert_hostname "bank.com" "bank.com" false true = false := by native_decide
example : unsafe_cert_hostname "bank.com" "bank.com" true false = false := by native_decide

-- 4) Edge cases
example : unsafe_cert_hostname "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafe_cert_hostname "" "evil.com" true true = true := by native_decide
example : unsafe_cert_hostname "bank.com" "bank.com" false false = false := by native_decide

-- Candidate check suite
example : check unsafe_cert_hostname = true := by native_decide

#eval unsafe_cert_hostname "bank.com" "bank.com" true true
#eval unsafe_cert_hostname "bank.com" "evil.com" true true
#eval unsafe_cert_hostname "secure.example.com" "attacker.com" true true
#eval unsafe_cert_hostname "bank.com" "bank.com" false true
#eval unsafe_cert_hostname "bank.com" "bank.com" true false
#eval unsafe_cert_hostname "bank.com" "*.evil.com" true true
#eval unsafe_cert_hostname "" "evil.com" true true
#eval unsafe_cert_hostname "bank.com" "bank.com" false false
#eval check unsafe_cert_hostname

/-! ## 3. Pre-condition -/

/-- All `(requested_host, cert_san, cert_valid, cert_not_expired)` inputs are admissible. -/
def Pre (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  True

/-! ## 4. Properties and Theorems -/

/-- Exact Boolean specification: `unsafe_cert_hostname` equals `cert_valid && cert_not_expired`. -/
def exact_spec_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
    (cert_valid && cert_not_expired)

theorem exact_spec_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    exact_spec_prop requested_host cert_san cert_valid cert_not_expired := by
  rfl

/-- Acceptance iff both `cert_valid = true` and `cert_not_expired = true`. -/
def accepts_iff_valid_and_not_expired_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true ↔
    (cert_valid = true ∧ cert_not_expired = true)

theorem accepts_iff_valid_and_not_expired_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    accepts_iff_valid_and_not_expired_prop requested_host cert_san cert_valid cert_not_expired := by
  unfold accepts_iff_valid_and_not_expired_prop unsafe_cert_hostname
  simp

/-- Rejection iff `cert_valid = false` or `cert_not_expired = false`. -/
def rejects_iff_invalid_or_expired_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false ↔
    (cert_valid = false ∨ cert_not_expired = false)

theorem rejects_iff_invalid_or_expired_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    rejects_iff_invalid_or_expired_prop requested_host cert_san cert_valid cert_not_expired := by
  unfold rejects_iff_invalid_or_expired_prop unsafe_cert_hostname
  exact Bool.and_eq_false_iff

/-- Normal operation: a valid, non-expired certificate with matching hostname is accepted. -/
def normal_match_accepted_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  requested_host = cert_san → cert_valid = true → cert_not_expired = true →
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem normal_match_accepted_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    normal_match_accepted_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _ h_valid h_unexpired
  unfold unsafe_cert_hostname
  simp [h_valid, h_unexpired]

/-- MITM vulnerability: a valid, non-expired certificate is accepted even when
`requested_host ≠ cert_san`. -/
def mitm_mismatch_accepted_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  requested_host ≠ cert_san → cert_valid = true → cert_not_expired = true →
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem mitm_mismatch_accepted_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    mitm_mismatch_accepted_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _ h_valid h_unexpired
  unfold unsafe_cert_hostname
  simp [h_valid, h_unexpired]

/-- Hostname independence: the result is invariant under replacing `requested_host` and
`cert_san` with any other strings `other_host` and `other_san`. -/
def hostname_ignored_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  ∀ (other_host other_san : String),
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname other_host other_san cert_valid cert_not_expired

theorem hostname_ignored_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    hostname_ignored_prop requested_host cert_san cert_valid cert_not_expired := by
  intro other_host other_san
  rfl

/-- Invalid certificates (`cert_valid = false`) are always rejected regardless of
hostname or expiration status. -/
def rejects_invalid_cert_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  cert_valid = false →
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false

theorem rejects_invalid_cert_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    rejects_invalid_cert_prop requested_host cert_san cert_valid cert_not_expired := by
  intro h_invalid
  unfold unsafe_cert_hostname
  simp [h_invalid]

/-- Expired certificates (`cert_not_expired = false`) are always rejected regardless of
hostname or signature validity. -/
def rejects_expired_cert_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  cert_not_expired = false →
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false

theorem rejects_expired_cert_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    rejects_expired_cert_prop requested_host cert_san cert_valid cert_not_expired := by
  intro h_expired
  unfold unsafe_cert_hostname
  simp [h_expired]

/-- Edge cases: an empty `requested_host` or wildcard `cert_san` is still accepted whenever
`cert_valid = true` and `cert_not_expired = true`. -/
def edge_cases_accepted_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  (requested_host = "" ∨ cert_san.startsWith "*." = true) →
    cert_valid = true → cert_not_expired = true →
      unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem edge_cases_accepted_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    edge_cases_accepted_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _ h_valid h_unexpired
  unfold unsafe_cert_hostname
  simp [h_valid, h_unexpired]

/-- Safe validation implies unsafe validation, but unsafe validation strictly over-accepts
whenever `requested_host ≠ cert_san` and the certificate is valid and not expired. -/
def safe_implies_unsafe_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  (safe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true →
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true) ∧
  (requested_host ≠ cert_san → cert_valid = true → cert_not_expired = true →
    safe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false ∧
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true)

theorem safe_implies_unsafe_thm (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    safe_implies_unsafe_prop requested_host cert_san cert_valid cert_not_expired := by
  unfold safe_implies_unsafe_prop safe_cert_hostname unsafe_cert_hostname
  constructor
  · intro h
    cases cert_valid <;> cases cert_not_expired <;> simp_all
  · intro h_ne h_valid h_unexpired
    refine ⟨?_, by simp [h_valid, h_unexpired]⟩
    have h_beq : (requested_host == cert_san) = false := beq_false_of_ne h_ne
    simp [h_beq]

/-! ## 5. Post-condition -/

/-- Post-condition combining all behavioral and vulnerability properties of
`unsafe_cert_hostname`. -/
def Post_prop (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Prop :=
  exact_spec_prop requested_host cert_san cert_valid cert_not_expired ∧
  accepts_iff_valid_and_not_expired_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejects_iff_invalid_or_expired_prop requested_host cert_san cert_valid cert_not_expired ∧
  normal_match_accepted_prop requested_host cert_san cert_valid cert_not_expired ∧
  mitm_mismatch_accepted_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_ignored_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejects_invalid_cert_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejects_expired_cert_prop requested_host cert_san cert_valid cert_not_expired ∧
  edge_cases_accepted_prop requested_host cert_san cert_valid cert_not_expired ∧
  safe_implies_unsafe_prop requested_host cert_san cert_valid cert_not_expired

/-! ## 6. Property-Based Tests -/

/-- Sample hostnames for bounded exhaustive property-based testing. -/
def sampleHosts : List String :=
  ["", "bank.com", "evil.com", "secure.example.com", "attacker.com", "*.evil.com"]

def sampleBools : List Bool := [false, true]

-- PBT for exact_spec_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired ==
    (cert_valid && cert_not_expired))

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v => sampleBools.all (fun e =>
  unsafe_cert_hostname h s v e == (v && e))))) = true := by native_decide

-- PBT for accepts_iff_valid_and_not_expired_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
  (unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired == true) ==
    (cert_valid == true && cert_not_expired == true))

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v => sampleBools.all (fun e =>
  (unsafe_cert_hostname h s v e == true) == (v == true && e == true))))) = true := by native_decide

-- PBT for rejects_iff_invalid_or_expired_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
  (unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired == false) ==
    (cert_valid == false || cert_not_expired == false))

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v => sampleBools.all (fun e =>
  (unsafe_cert_hostname h s v e == false) == (v == false || e == false))))) = true := by native_decide

-- PBT for normal_match_accepted_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host : String),
  unsafe_cert_hostname requested_host requested_host true true == true)

example : sampleHosts.all (fun h =>
  unsafe_cert_hostname h h true true == true) = true := by native_decide

-- PBT for mitm_mismatch_accepted_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String),
  !(requested_host != cert_san) ||
    (unsafe_cert_hostname requested_host cert_san true true == true))

example : sampleHosts.all (fun h => sampleHosts.all (fun s =>
  !(h != s) || unsafe_cert_hostname h s true true == true)) = true := by native_decide

-- PBT for hostname_ignored_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (h1 s1 h2 s2 : String) (cert_valid cert_not_expired : Bool),
  unsafe_cert_hostname h1 s1 cert_valid cert_not_expired ==
    unsafe_cert_hostname h2 s2 cert_valid cert_not_expired)

example : sampleHosts.all (fun h1 => sampleHosts.all (fun s1 => sampleHosts.all (fun h2 => sampleHosts.all (fun s2 =>
  sampleBools.all (fun v => sampleBools.all (fun e =>
    unsafe_cert_hostname h1 s1 v e == unsafe_cert_hostname h2 s2 v e)))))) = true := by native_decide

-- PBT for rejects_invalid_cert_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_not_expired : Bool),
  unsafe_cert_hostname requested_host cert_san false cert_not_expired == false)

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun e =>
  unsafe_cert_hostname h s false e == false))) = true := by native_decide

-- PBT for rejects_expired_cert_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid : Bool),
  unsafe_cert_hostname requested_host cert_san cert_valid false == false)

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v =>
  unsafe_cert_hostname h s v false == false))) = true := by native_decide

-- PBT for edge_cases_accepted_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String),
  unsafe_cert_hostname "" cert_san true true == true &&
  unsafe_cert_hostname requested_host ("*." ++ cert_san) true true == true)

example : sampleHosts.all (fun h => sampleHosts.all (fun s =>
  !((h == "" || s.startsWith "*.")) || unsafe_cert_hostname h s true true == true)) = true := by native_decide

-- PBT for safe_implies_unsafe_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
  (!(safe_cert_hostname requested_host cert_san cert_valid cert_not_expired) ||
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired) &&
  (!(requested_host != cert_san && cert_valid && cert_not_expired) ||
    (!safe_cert_hostname requested_host cert_san cert_valid cert_not_expired &&
      unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired)))

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v => sampleBools.all (fun e =>
  (!(safe_cert_hostname h s v e) || unsafe_cert_hostname h s v e) &&
  (!(h != s && v && e) || (!safe_cert_hostname h s v e && unsafe_cert_hostname h s v e)))))) = true := by native_decide

-- PBT for Post_prop (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
  (unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired == (cert_valid && cert_not_expired)) &&
  ((unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired == true) == (cert_valid && cert_not_expired)) &&
  ((unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired == false) == (!cert_valid || !cert_not_expired)) &&
  (unsafe_cert_hostname requested_host requested_host true true == true) &&
  (unsafe_cert_hostname requested_host cert_san true true == true) &&
  (unsafe_cert_hostname requested_host cert_san false cert_not_expired == false) &&
  (unsafe_cert_hostname requested_host cert_san cert_valid false == false) &&
  (unsafe_cert_hostname "" cert_san true true == true))

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v => sampleBools.all (fun e =>
  (unsafe_cert_hostname h s v e == (v && e)) &&
  ((unsafe_cert_hostname h s v e == true) == (v && e)) &&
  ((unsafe_cert_hostname h s v e == false) == (!v || !e)) &&
  (unsafe_cert_hostname h h true true == true) &&
  (unsafe_cert_hostname h s true true == true) &&
  (unsafe_cert_hostname h s false e == false) &&
  (unsafe_cert_hostname h s v false == false))))) = true := by native_decide

/-! ## 7. Correctness Theorem -/

theorem unsafe_cert_hostname_correct (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool)
    (h_pre : Pre requested_host cert_san cert_valid cert_not_expired) :
    Post_prop requested_host cert_san cert_valid cert_not_expired := by
  unfold Post_prop
  refine ⟨exact_spec_thm requested_host cert_san cert_valid cert_not_expired,
    accepts_iff_valid_and_not_expired_thm requested_host cert_san cert_valid cert_not_expired,
    rejects_iff_invalid_or_expired_thm requested_host cert_san cert_valid cert_not_expired,
    normal_match_accepted_thm requested_host cert_san cert_valid cert_not_expired,
    mitm_mismatch_accepted_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_ignored_thm requested_host cert_san cert_valid cert_not_expired,
    rejects_invalid_cert_thm requested_host cert_san cert_valid cert_not_expired,
    rejects_expired_cert_thm requested_host cert_san cert_valid cert_not_expired,
    edge_cases_accepted_thm requested_host cert_san cert_valid cert_not_expired,
    safe_implies_unsafe_thm requested_host cert_san cert_valid cert_not_expired⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `unsafe_cert_hostname` using `Id.run do` and mutable state. -/
def unsafe_cert_hostname_imp (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Bool := Id.run do
  let mut result : Bool := false
  if cert_valid then
    if cert_not_expired then
      result := true
  return result

/-! ## 9. Imperative Tests -/

-- 1) Normal operation - exact hostname match accepted
example : unsafe_cert_hostname_imp "bank.com" "bank.com" true true = true := by native_decide

-- 2) Vulnerability: hostname mismatch accepted (MITM attack succeeds)
example : unsafe_cert_hostname_imp "bank.com" "evil.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "secure.example.com" "attacker.com" true true = true := by native_decide

-- 3) Still rejects invalid/expired certs
example : unsafe_cert_hostname_imp "bank.com" "bank.com" false true = false := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "bank.com" true false = false := by native_decide

-- 4) Edge cases
example : unsafe_cert_hostname_imp "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "" "evil.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "bank.com" false false = false := by native_decide

-- Full check suite on imperative implementation
example : check unsafe_cert_hostname_imp = true := by native_decide

#eval unsafe_cert_hostname_imp "bank.com" "bank.com" true true
#eval unsafe_cert_hostname_imp "bank.com" "evil.com" true true
#eval unsafe_cert_hostname_imp "secure.example.com" "attacker.com" true true
#eval unsafe_cert_hostname_imp "bank.com" "bank.com" false true
#eval unsafe_cert_hostname_imp "bank.com" "bank.com" true false
#eval unsafe_cert_hostname_imp "bank.com" "*.evil.com" true true
#eval unsafe_cert_hostname_imp "" "evil.com" true true
#eval unsafe_cert_hostname_imp "bank.com" "bank.com" false false
#eval check unsafe_cert_hostname_imp

-- PBT checking functional-imperative equivalence (randomized + bounded)
#eval Plausible.Testable.check (∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired ==
    unsafe_cert_hostname_imp requested_host cert_san cert_valid cert_not_expired)

example : sampleHosts.all (fun h => sampleHosts.all (fun s => sampleBools.all (fun v => sampleBools.all (fun e =>
  unsafe_cert_hostname h s v e == unsafe_cert_hostname_imp h s v e)))) = true := by native_decide

/-! ## 10. Equivalence Theorem -/

theorem unsafe_cert_hostname_equiv (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) :
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname_imp requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;> rfl

end «75_unsafeCertHostname»

import Mathlib

/-!
# 75_unsafeCertHostname - unsafe certificate hostname validation

Python source (MIT 6.858 Lecture 15: Certificates; reference RFC 6125, hostname verification):

```
def unsafe_cert_hostname(requested_host: str, cert_san: str,
                         cert_valid: bool, cert_not_expired: bool) -> bool:
    return cert_valid and cert_not_expired   # Hostname never checked!
```

The modelled TLS client verifies the certificate's signature (`cert_valid`) and its
validity period (`cert_not_expired`) but **never** compares the certificate's Subject
Alternative Name (`cert_san`) with the hostname the client actually asked for
(`requested_host`).  Both string arguments are received and then ignored, so a
man-in-the-middle who owns any genuine certificate (for instance a valid certificate
for `evil.com`) is accepted while the user believes she is talking to `bank.com`.

This file formalises the program *exactly as written*: the returned decision is
`cert_valid && cert_not_expired`.  Every theorem below therefore states the real
(vulnerable) behaviour of the program - in particular that a hostname mismatch is
accepted - and never a hardened version of it.  `safeCertHostname` (the RFC 6125
compliant check) is defined only so that the divergence caused by the missing SAN/CN
check can be exhibited as a theorem.
-/

namespace «75_unsafeCertHostname»

/-! ## Functional implementation -/

set_option linter.unusedVariables false in
/-- The vulnerable validation routine: accept iff the certificate signature verifies
and the certificate has not expired.  `requestedHost` and `certSan` are accepted as
arguments but are never inspected - that omission is the vulnerability. -/
def unsafeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired

/-- The RFC 6125 compliant routine (signature, expiry *and* hostname match).
It is used only as a reference point to state that the vulnerable implementation
really does diverge from a correct one; it is not part of the Python program. -/
def safeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired && (requestedHost == certSan)

/-! ## Unit tests (transcription of the Python `check` harness) -/

-- 1) Normal operation - exact hostname match accepted
example : unsafeCertHostname "bank.com" "bank.com" true true = true := by native_decide
#eval unsafeCertHostname "bank.com" "bank.com" true true

-- 2) Vulnerability: hostname mismatch accepted (MITM attack succeeds)
example : unsafeCertHostname "bank.com" "evil.com" true true = true := by native_decide
example : unsafeCertHostname "secure.example.com" "attacker.com" true true = true := by native_decide
#eval unsafeCertHostname "bank.com" "evil.com" true true
#eval unsafeCertHostname "secure.example.com" "attacker.com" true true

-- 3) Still rejects invalid/expired certs
example : unsafeCertHostname "bank.com" "bank.com" false true = false := by native_decide
example : unsafeCertHostname "bank.com" "bank.com" true false = false := by native_decide
#eval unsafeCertHostname "bank.com" "bank.com" false true
#eval unsafeCertHostname "bank.com" "bank.com" true false

-- 4) Edge cases
example : unsafeCertHostname "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafeCertHostname "" "evil.com" true true = true := by native_decide
example : unsafeCertHostname "bank.com" "bank.com" false false = false := by native_decide
#eval unsafeCertHostname "bank.com" "*.evil.com" true true
#eval unsafeCertHostname "" "evil.com" true true
#eval unsafeCertHostname "bank.com" "bank.com" false false

-- The safe implementation, by contrast, refuses the mismatching certificate.
example : safeCertHostname "bank.com" "evil.com" true true = false := by native_decide
example : safeCertHostname "bank.com" "bank.com" true true = true := by native_decide

/-- Direct transcription of the Python `check` harness: it returns `true` exactly when
all eight assertions of the task hold for `candidate`. -/
def check (candidate : String -> String -> Bool -> Bool -> Bool) : Bool :=
  (candidate "bank.com" "bank.com" true true == true) &&
  (candidate "bank.com" "evil.com" true true == true) &&
  (candidate "secure.example.com" "attacker.com" true true == true) &&
  (candidate "bank.com" "bank.com" false true == false) &&
  (candidate "bank.com" "bank.com" true false == false) &&
  (candidate "bank.com" "*.evil.com" true true == true) &&
  (candidate "" "evil.com" true true == true) &&
  (candidate "bank.com" "bank.com" false false == false)

/-- The vulnerable implementation passes the harness of the Python program. -/
theorem check_passes_thm : check unsafeCertHostname = true := by decide

#eval check unsafeCertHostname
-- The RFC 6125 compliant implementation *fails* assertion 2 of the harness,
-- which is precisely why the harness documents the vulnerability.
example : check safeCertHostname = false := by native_decide

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- The Python routine is total: every quadruple (requested hostname, certificate SAN,
signature-valid flag, not-expired flag) is an admissible input.  No side condition is
imposed - in particular nothing requires the SAN to match the requested hostname. -/
def Pre (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  True

/-- Every input is admissible. -/
theorem pre_always_holds_thm :
    ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
      Pre requestedHost certSan certValid certNotExpired := fun _ _ _ _ => trivial

/-! ## Properties of the implementation -/

/-- Exact semantics: the decision is the conjunction of the two certificate flags. -/
def spec_prop : Prop :=
  ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired = (certValid && certNotExpired)

theorem spec_thm : spec_prop := by
  intro requestedHost certSan certValid certNotExpired
  rfl

/-- The vulnerability, stated structurally: neither the requested hostname nor the
certificate SAN has any influence on the outcome. -/
def hostname_ignored_prop : Prop :=
  ∀ (h₁ h₂ s₁ s₂ : String) (certValid certNotExpired : Bool),
    unsafeCertHostname h₁ s₁ certValid certNotExpired =
      unsafeCertHostname h₂ s₂ certValid certNotExpired

theorem hostname_ignored_thm : hostname_ignored_prop := by
  intro h₁ h₂ s₁ s₂ certValid certNotExpired
  rfl

/-- MITM attack succeeds: a certificate that is valid and unexpired is accepted even
though its SAN is a different host than the one requested. -/
def mitm_accepted_prop : Prop :=
  ∀ (requestedHost certSan : String),
    requestedHost ≠ certSan → unsafeCertHostname requestedHost certSan true true = true

theorem mitm_accepted_thm : mitm_accepted_prop := by
  intro requestedHost certSan _
  rfl

/-- Every valid, unexpired certificate is accepted, whatever the hostname and the SAN. -/
def any_valid_cert_accepted_prop : Prop :=
  ∀ (requestedHost certSan : String), unsafeCertHostname requestedHost certSan true true = true

theorem any_valid_cert_accepted_thm : any_valid_cert_accepted_prop := by
  intro requestedHost certSan
  rfl

/-- Edge case of the Python harness: the empty requested hostname is accepted. -/
def empty_hostname_accepted_prop : Prop :=
  ∀ (certSan : String), unsafeCertHostname "" certSan true true = true

theorem empty_hostname_accepted_thm : empty_hostname_accepted_prop := by
  intro certSan
  rfl

/-- Edge case of the Python harness: a wildcard SAN that does not match the requested
hostname is still accepted, because no matching is performed at all. -/
def wildcard_mismatch_accepted_prop : Prop :=
  ∀ (requestedHost certSan : String),
    unsafeCertHostname requestedHost ("*" ++ certSan) true true = true

theorem wildcard_mismatch_accepted_thm : wildcard_mismatch_accepted_prop := by
  intro requestedHost certSan
  rfl

/-- Certificates whose signature does not verify are rejected, whatever the expiry flag
and whatever the hostname. -/
def rejects_invalid_prop : Prop :=
  ∀ (requestedHost certSan : String) (certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan false certNotExpired = false

theorem rejects_invalid_thm : rejects_invalid_prop := by
  intro requestedHost certSan certNotExpired
  cases certNotExpired <;> rfl

/-- Expired certificates are rejected, whatever the signature flag and the hostname. -/
def rejects_expired_prop : Prop :=
  ∀ (requestedHost certSan : String) (certValid : Bool),
    unsafeCertHostname requestedHost certSan certValid false = false

theorem rejects_expired_thm : rejects_expired_prop := by
  intro requestedHost certSan certValid
  cases certValid <;> rfl

/-- Acceptance characterisation: the connection is accepted exactly when the signature
verifies and the certificate has not expired (no hostname condition appears). -/
def accepted_iff_prop : Prop :=
  ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    (unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
      certValid = true ∧ certNotExpired = true)

theorem accepted_iff_thm : accepted_iff_prop := by
  intro requestedHost certSan certValid certNotExpired
  cases certValid <;> cases certNotExpired <;> simp [unsafeCertHostname]

/-- The two flags enter only through `&&`, so they are interchangeable. -/
def flags_commutative_prop : Prop :=
  ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname requestedHost certSan certNotExpired certValid

theorem flags_commutative_thm : flags_commutative_prop := by
  intro requestedHost certSan certValid certNotExpired
  cases certValid <;> cases certNotExpired <;> rfl

/-- Rejection characterisation: the connection is refused exactly when at least one of
the two certificate flags is `false`. -/
def rejected_iff_prop : Prop :=
  ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    (unsafeCertHostname requestedHost certSan certValid certNotExpired = false ↔
      certValid = false ∨ certNotExpired = false)

theorem rejected_iff_thm : rejected_iff_prop := by
  intro requestedHost certSan certValid certNotExpired
  cases certValid <;> cases certNotExpired <;> simp [unsafeCertHostname]

/-- The missing SAN/CN check is observable: there are inputs on which the vulnerable
routine and the RFC 6125 compliant routine disagree. -/
def diverges_from_safe_prop : Prop :=
  ∃ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired ≠
      safeCertHostname requestedHost certSan certValid certNotExpired

theorem diverges_from_safe_thm : diverges_from_safe_prop :=
  ⟨"bank.com", "evil.com", true, true, by decide⟩

/-! ## Post-condition -/

set_option linter.unusedVariables false in
/-- Post-condition of one call: `result` is the value returned by the routine. -/
def Post_prop (requestedHost certSan : String) (certValid certNotExpired : Bool)
    (result : Bool) : Prop :=
  -- (a) the decision is exactly the conjunction of the two certificate flags
  (result = (certValid && certNotExpired)) ∧
  -- (b) it does not depend on the hostname/SAN pair at all (the vulnerability)
  (∀ (h s : String), unsafeCertHostname h s certValid certNotExpired = result) ∧
  -- (c) a valid, unexpired certificate is always accepted, whatever the hostname
  (certValid = true → certNotExpired = true → result = true) ∧
  -- (d) a certificate whose signature does not verify is always rejected
  (certValid = false → result = false) ∧
  -- (e) an expired certificate is always rejected
  (certNotExpired = false → result = false)

/-! ## Property-based tests -/

/-- Finite corpus of requested hostnames used by the bounded (exhaustive) tests. -/
def testHosts : List String :=
  ["bank.com", "evil.com", "", "*.evil.com", "*.bank.com", "secure.example.com",
   "attacker.com", "BANK.COM", "bank.com.", "www.bank.com"]

/-- Finite corpus of certificate Subject Alternative Names. -/
def testSans : List String :=
  ["bank.com", "evil.com", "", "*.evil.com", "*.bank.com", "attacker.com", "www.bank.com"]

/-- All values of the two certificate flags. -/
def testFlags : List Bool := [true, false]

/-- Exhaustive finite input space used by the bounded PBTs. -/
def allCases : List (String × String × Bool × Bool) :=
  (List.product (List.product testHosts testSans) (List.product testFlags testFlags)).map
    fun ((h, s), (v, e)) => (h, s, v, e)

/-- Executable counterpart of `Post_prop`.  Clause (b) of `Post_prop` quantifies over all
strings; here that clause is checked exhaustively over the finite corpus above. -/
def postCheck (requestedHost certSan : String) (certValid certNotExpired : Bool) : Bool :=
  let result := unsafeCertHostname requestedHost certSan certValid certNotExpired
  (result == (certValid && certNotExpired)) &&
  (testHosts.all fun h => testSans.all fun s =>
    unsafeCertHostname h s certValid certNotExpired == result) &&
  (!(certValid && certNotExpired) || (result == true)) &&
  (!(certValid == false) || (result == false)) &&
  (!(certNotExpired == false) || (result == false))

-- PBT for `spec_prop` (randomized and exhaustive)
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool), unsafeCertHostname h s v e = (v && e))
example : allCases.all (fun (h, s, v, e) => unsafeCertHostname h s v e == (v && e)) = true := by
  native_decide

-- PBT for `hostname_ignored_prop`
#eval Plausible.Testable.check
  (∀ (h₁ h₂ s₁ s₂ : String) (v e : Bool), unsafeCertHostname h₁ s₁ v e = unsafeCertHostname h₂ s₂ v e)
example : allCases.all (fun (h, s, v, e) =>
    testHosts.all fun h₂ => testSans.all fun s₂ =>
      unsafeCertHostname h s v e == unsafeCertHostname h₂ s₂ v e) = true := by native_decide

-- PBT for `mitm_accepted_prop` (the attack always succeeds).  The randomized test
-- builds a SAN that genuinely differs from the requested hostname, so no sample has to
-- be discarded; the bounded tests below run over every mismatching pair of the corpus.
#eval Plausible.Testable.check
  (∀ (h s : String), unsafeCertHostname h (h ++ s ++ ".evil.com") true true = true)
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    unsafeCertHostname h (h ++ s ++ ".evil.com") v e = (v && e))
example : (List.product testHosts testSans).all (fun (h, s) =>
    unsafeCertHostname h s true true == true) = true := by native_decide
example : ((List.product testHosts testSans).filter (fun (h, s) => h != s)).all
    (fun (h, s) => unsafeCertHostname h s true true == true) = true := by native_decide
-- the previous test is not vacuous: the corpus really contains mismatching pairs
example : ((List.product testHosts testSans).filter (fun (h, s) => h != s)).length > 0 := by
  native_decide

-- PBT for `any_valid_cert_accepted_prop`
#eval Plausible.Testable.check (∀ (h s : String), unsafeCertHostname h s true true = true)
example : (List.range 30).all (fun n =>
    unsafeCertHostname (toString n) ("evil" ++ toString n) true true = true) = true := by
  native_decide

-- PBT for `empty_hostname_accepted_prop`
#eval Plausible.Testable.check (∀ (s : String), unsafeCertHostname "" s true true = true)
example : testSans.all (fun s => unsafeCertHostname "" s true true == true) = true := by
  native_decide

-- PBT for `wildcard_mismatch_accepted_prop`
#eval Plausible.Testable.check
  (∀ (h s : String), unsafeCertHostname h ("*" ++ s) true true = true)
example : (List.product testHosts testSans).all (fun (h, s) =>
    unsafeCertHostname h ("*" ++ s) true true == true) = true := by native_decide

-- PBT for `rejects_invalid_prop`
#eval Plausible.Testable.check (∀ (h s : String) (e : Bool), unsafeCertHostname h s false e = false)
example : allCases.all (fun (h, s, _v, e) => unsafeCertHostname h s false e == false) = true := by
  native_decide

-- PBT for `rejects_expired_prop`
#eval Plausible.Testable.check (∀ (h s : String) (v : Bool), unsafeCertHostname h s v false = false)
example : allCases.all (fun (h, s, v, _e) => unsafeCertHostname h s v false == false) = true := by
  native_decide

-- PBT for `accepted_iff_prop`
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    (unsafeCertHostname h s v e = true ↔ v = true ∧ e = true))
example : allCases.all (fun (h, s, v, e) =>
    (unsafeCertHostname h s v e == true) == (v && e)) = true := by native_decide

-- PBT for `rejected_iff_prop`
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    (unsafeCertHostname h s v e = false ↔ v = false ∨ e = false))
example : allCases.all (fun (h, s, v, e) =>
    (unsafeCertHostname h s v e == false) == (!v || !e)) = true := by native_decide

-- PBT for `flags_commutative_prop`
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool), unsafeCertHostname h s v e = unsafeCertHostname h s e v)
example : allCases.all (fun (h, s, v, e) =>
    unsafeCertHostname h s v e == unsafeCertHostname h s e v) = true := by native_decide

-- PBT for `diverges_from_safe_prop` (an existential: exhibit the disagreement exhaustively)
example : allCases.any (fun (h, s, v, e) =>
    unsafeCertHostname h s v e != safeCertHostname h s v e) = true := by native_decide
example : unsafeCertHostname "bank.com" "evil.com" true true !=
    safeCertHostname "bank.com" "evil.com" true true := by native_decide

-- PBT for `check_passes_thm` (the Python harness accepts the implementation)
example : check unsafeCertHostname = true := by native_decide
#eval check unsafeCertHostname

-- PBT for `Post_prop` through its executable counterpart `postCheck`
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool), postCheck h s v e = true)
example : (List.product testHosts testSans).all (fun (h, s) =>
    testFlags.all fun v => testFlags.all fun e => postCheck h s v e) = true := by native_decide
example : allCases.all (fun (h, s, v, e) => postCheck h s v e) = true := by native_decide

/-! ## Correctness -/

/-- The implementation satisfies its post-condition on every admissible input. -/
theorem correctness_thm :
    ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
      Pre requestedHost certSan certValid certNotExpired →
      Post_prop requestedHost certSan certValid certNotExpired
        (unsafeCertHostname requestedHost certSan certValid certNotExpired) := by
  intro requestedHost certSan certValid certNotExpired _
  cases certValid <;> cases certNotExpired <;>
    refine ⟨rfl, fun _ _ => rfl, ?_, ?_, ?_⟩ <;> simp [unsafeCertHostname]

/-! ## Imperative implementation -/

set_option linter.unusedVariables false in
/-- Imperative transcription of the Python routine: a TLS client that keeps mutable
state, verifies the certificate chain, verifies the validity period, and then decides.
The step that compares `requestedHost` with the certificate's SAN/CN is absent, which
is exactly the vulnerability of the source program. -/
def unsafeCertHostnameImp (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Bool :=
  Id.run do
    let mut signatureOk : Bool := false
    let mut expiryOk : Bool := false
    let mut accepted : Bool := false
    -- step 1: the certificate chain verifies against a trusted root
    signatureOk := certValid
    -- step 2: the certificate is inside its validity period
    expiryOk := certNotExpired
    -- step 3 (RFC 6125 hostname verification) is MISSING: the comparison below is
    -- computed and then discarded, so the decision never consults the hostname/SAN pair.
    let _sanCheck : Bool := (requestedHost == certSan)
    -- step 4: the decision uses the signature and the expiry flags only
    if signatureOk && expiryOk then
      accepted := true
    return accepted

/-! ## Imperative tests -/

example : unsafeCertHostnameImp "bank.com" "bank.com" true true = true := by native_decide
example : unsafeCertHostnameImp "bank.com" "evil.com" true true = true := by native_decide
example : unsafeCertHostnameImp "secure.example.com" "attacker.com" true true = true := by
  native_decide
example : unsafeCertHostnameImp "bank.com" "bank.com" false true = false := by native_decide
example : unsafeCertHostnameImp "bank.com" "bank.com" true false = false := by native_decide
example : unsafeCertHostnameImp "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafeCertHostnameImp "" "evil.com" true true = true := by native_decide
example : unsafeCertHostnameImp "bank.com" "bank.com" false false = false := by native_decide
example : check unsafeCertHostnameImp = true := by native_decide

#eval unsafeCertHostnameImp "bank.com" "evil.com" true true
#eval unsafeCertHostnameImp "bank.com" "bank.com" false true
#eval check unsafeCertHostnameImp

-- PBT for the imperative implementation and for the equivalence statement
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool), unsafeCertHostnameImp h s v e = (v && e))
example : allCases.all (fun (h, s, v, e) =>
    unsafeCertHostnameImp h s v e == unsafeCertHostname h s v e) = true := by native_decide

/-! ## Functional / imperative equivalence -/

/-- The imperative client decides exactly like the functional specification. -/
theorem equivalence_thm :
    ∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
      unsafeCertHostname requestedHost certSan certValid certNotExpired =
        unsafeCertHostnameImp requestedHost certSan certValid certNotExpired := by
  intro requestedHost certSan certValid certNotExpired
  cases certValid <;> cases certNotExpired <;> rfl

/-- The imperative version inherits the vulnerability: it too accepts a mismatching
certificate. -/
theorem imperative_mitm_accepted_thm :
    ∀ (requestedHost certSan : String),
      requestedHost ≠ certSan → unsafeCertHostnameImp requestedHost certSan true true = true := by
  intro requestedHost certSan _
  rfl

end «75_unsafeCertHostname»

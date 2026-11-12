import Mathlib

/-!
# `75_unsafeCertHostname`: unsafe certificate hostname validation

Lean 4 formalization of the Python program `unsafe_cert_hostname`
(MIT 6.858 Lecture 15: Certificates; RFC 6125 hostname verification).

The Python function

```python
def unsafe_cert_hostname(requested_host, cert_san, cert_valid, cert_not_expired):
    return cert_valid and cert_not_expired  # Hostname never checked!
```

accepts a certificate whenever its signature is valid and it has not expired.  It never
compares the certificate's Subject Alternative Name (SAN) with the requested hostname, so a
valid certificate for `evil.com` is accepted for a connection to `bank.com`
(man-in-the-middle with a legitimately issued certificate).

Contents:
* `unsafeCertHostname` -- functional translation; the Python `check` harness as unit tests;
* `Pre` / `*_prop` / `*_thm` / `Post_prop` -- specification: the result is exactly
  `cert_valid && cert_not_expired`, it is independent of both hostname arguments, a mismatched
  SAN is still accepted (the vulnerability), and invalid or expired certificates are rejected;
* property-based tests (Plausible random tests and bounded exhaustive checks);
* `unsafeCertHostnameImp` -- imperative version with mutable state, proven equivalent.
-/

namespace «75_unsafeCertHostname»

/-! ## Functional implementation -/

set_option linter.unusedVariables false in
/-- Functional translation of `unsafe_cert_hostname`.

Returns `true` iff the certificate signature is valid and the certificate has not expired.
The hostname arguments `requestedHost` and `certSan` are accepted but never inspected:
this is the vulnerability the Python program demonstrates. -/
def unsafeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired  -- Hostname never checked!

/-- Translation of the Python `check` test harness: every assertion of `check` as one
Boolean conjunction (`candidate(...) is True` becomes `candidate ... == true`). -/
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
  (candidate "bank.com" "*.evil.com" true true == true) &&   -- Wildcard mismatch accepted
  (candidate "" "evil.com" true true == true) &&             -- Empty hostname accepted
  (candidate "bank.com" "bank.com" false false == false)

/-! ## Unit tests (the assertions of the Python `check`) -/

-- 1) Normal operation - exact hostname match accepted
example : unsafeCertHostname "bank.com" "bank.com" true true = true := by native_decide
-- 2) Vulnerability: hostname mismatch accepted (MITM attack succeeds)
example : unsafeCertHostname "bank.com" "evil.com" true true = true := by native_decide
example : unsafeCertHostname "secure.example.com" "attacker.com" true true = true := by
  native_decide
-- 3) Still rejects invalid/expired certs
example : unsafeCertHostname "bank.com" "bank.com" false true = false := by native_decide
example : unsafeCertHostname "bank.com" "bank.com" true false = false := by native_decide
-- 4) Edge cases
example : unsafeCertHostname "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafeCertHostname "" "evil.com" true true = true := by native_decide
example : unsafeCertHostname "bank.com" "bank.com" false false = false := by native_decide

-- The whole harness passes (`assert check(unsafe_cert_hostname)`).
example : check unsafeCertHostname = true := by native_decide
#eval check unsafeCertHostname                     -- true
#eval unsafeCertHostname "bank.com" "evil.com" true true   -- true (MITM accepted)

/-- The Python harness `check(unsafe_cert_hostname)` succeeds; kernel-checked by evaluation. -/
theorem check_unsafeCertHostname_thm : check unsafeCertHostname = true := by decide

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- Pre-condition: the Python function accepts arbitrary hostnames and flags; nothing is
required of the inputs. -/
def Pre (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop := True

/-! ## Properties -/

/-- The result is exactly the conjunction of signature validity and non-expiry
(`return cert_valid and cert_not_expired`). -/
def result_spec_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired = (certValid && certNotExpired)

theorem result_spec_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    result_spec_prop requestedHost certSan certValid certNotExpired := by
  unfold result_spec_prop unsafeCertHostname
  rfl

/-- Acceptance characterised as a proposition: accepted iff valid and not expired. -/
def accepted_iff_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
    (certValid = true ∧ certNotExpired = true)

theorem accepted_iff_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    accepted_iff_prop requestedHost certSan certValid certNotExpired := by
  unfold accepted_iff_prop unsafeCertHostname
  simp

/-- The hostname arguments are never inspected: replacing the requested host and the
certificate SAN by any other strings leaves the verdict unchanged. -/
def hostname_ignored_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    Prop :=
  ∀ (host' san' : String),
    unsafeCertHostname host' san' certValid certNotExpired =
      unsafeCertHostname requestedHost certSan certValid certNotExpired

theorem hostname_ignored_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    hostname_ignored_prop requestedHost certSan certValid certNotExpired := by
  intro host' san'
  rfl

/-- Normal operation: a valid, unexpired certificate whose SAN equals the requested host is
accepted. -/
def match_accepted_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    Prop :=
  requestedHost = certSan → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem match_accepted_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    match_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro _ hv he
  unfold unsafeCertHostname
  rw [hv, he]
  rfl

/-- The vulnerability: a valid, unexpired certificate whose SAN does **not** match the
requested host is accepted as well (MITM with a legitimately issued certificate). -/
def mismatch_accepted_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    Prop :=
  requestedHost ≠ certSan → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem mismatch_accepted_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    mismatch_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro _ hv he
  unfold unsafeCertHostname
  rw [hv, he]
  rfl

/-- A certificate with an invalid signature is rejected, whatever the hostnames and expiry. -/
def invalid_rejected_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    Prop :=
  certValid = false → unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem invalid_rejected_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    invalid_rejected_prop requestedHost certSan certValid certNotExpired := by
  intro hv
  unfold unsafeCertHostname
  rw [hv]
  rfl

/-- An expired certificate is rejected, whatever the hostnames and signature validity. -/
def expired_rejected_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    Prop :=
  certNotExpired = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem expired_rejected_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    expired_rejected_prop requestedHost certSan certValid certNotExpired := by
  intro he
  unfold unsafeCertHostname
  rw [he]
  exact Bool.and_false certValid

/-- Reference behaviour required by RFC 6125 (simplified to an exact SAN match, no wildcards):
accept only when the certificate is valid, unexpired **and** its SAN equals the requested host.
Used only to state precisely what the unsafe checker fails to enforce. -/
def safeCertHostname (requestedHost certSan : String) (certValid certNotExpired : Bool) : Bool :=
  certValid && certNotExpired && (requestedHost == certSan)

/-- The unsafe checker accepts everything the RFC-conforming checker accepts. -/
def accepts_all_safe_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    Prop :=
  safeCertHostname requestedHost certSan certValid certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem accepts_all_safe_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    accepts_all_safe_prop requestedHost certSan certValid certNotExpired := by
  intro hsafe
  unfold safeCertHostname at hsafe
  unfold unsafeCertHostname
  simp only [Bool.and_eq_true] at hsafe ⊢
  exact hsafe.1

/-- The unsafe checker is strictly weaker than the RFC-conforming one: the attack scenario
of the Python docstring (client requests `bank.com`, server presents a valid certificate for
`evil.com`) is accepted by the unsafe checker and rejected by the safe one. -/
def mitm_witness_prop : Prop :=
  ∃ (requestedHost certSan : String),
    requestedHost ≠ certSan ∧
    unsafeCertHostname requestedHost certSan true true = true ∧
    safeCertHostname requestedHost certSan true true = false

theorem mitm_witness_thm : mitm_witness_prop := by
  refine ⟨"bank.com", "evil.com", ?_, rfl, ?_⟩
  · decide
  · decide

/-! ## Post-condition -/

/-- Post-condition: the conjunction of all per-input properties of `unsafeCertHostname`. -/
def Post_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  result_spec_prop requestedHost certSan certValid certNotExpired ∧
  accepted_iff_prop requestedHost certSan certValid certNotExpired ∧
  hostname_ignored_prop requestedHost certSan certValid certNotExpired ∧
  match_accepted_prop requestedHost certSan certValid certNotExpired ∧
  mismatch_accepted_prop requestedHost certSan certValid certNotExpired ∧
  invalid_rejected_prop requestedHost certSan certValid certNotExpired ∧
  expired_rejected_prop requestedHost certSan certValid certNotExpired ∧
  accepts_all_safe_prop requestedHost certSan certValid certNotExpired

/-! ## Property-based tests

Randomized tests use Plausible; bounded tests enumerate a fixed set of hostnames (including
every hostname of the Python harness) against all four flag combinations. -/

/-- Hostnames used by the bounded property-based tests. -/
def sampleHosts : List String :=
  ["bank.com", "evil.com", "secure.example.com", "attacker.com", "*.evil.com", "",
   "BANK.COM", "bank.com.", "www.bank.com", "a"]

/-- Both flag values, for exhaustive enumeration. -/
def allFlags : List Bool := [true, false]

/-- Executable Boolean form of `Post_prop` on one input (quantifier over the replacement
hostnames of `hostname_ignored_prop` bounded to `sampleHosts`). -/
def postCheck (requestedHost certSan : String) (certValid certNotExpired : Bool) : Bool :=
  let r := unsafeCertHostname requestedHost certSan certValid certNotExpired
  (r == (certValid && certNotExpired)) &&                                  -- result_spec_prop
  ((r == true) == (certValid && certNotExpired)) &&                        -- accepted_iff_prop
  (sampleHosts.all fun host' => sampleHosts.all fun san' =>
      unsafeCertHostname host' san' certValid certNotExpired == r) &&      -- hostname_ignored_prop
  (!(requestedHost == certSan && certValid && certNotExpired) || r) &&     -- match_accepted_prop
  (!(requestedHost != certSan && certValid && certNotExpired) || r) &&     -- mismatch_accepted_prop
  (certValid || !r) &&                                                     -- invalid_rejected_prop
  (certNotExpired || !r) &&                                                -- expired_rejected_prop
  (!safeCertHostname requestedHost certSan certValid certNotExpired || r)  -- accepts_all_safe_prop

-- result_spec_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafeCertHostname h s v e = (v && e))
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      unsafeCertHostname h s v e == (v && e)) = true := by native_decide

-- accepted_iff_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafeCertHostname h s v e = true ↔ (v = true ∧ e = true))
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      decide (unsafeCertHostname h s v e = true ↔ (v = true ∧ e = true))) = true := by
  native_decide

-- hostname_ignored_prop
#eval Plausible.Testable.check (∀ (h s h' s' : String) (v e : Bool),
  unsafeCertHostname h' s' v e = unsafeCertHostname h s v e)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    sampleHosts.all fun h' => sampleHosts.all fun s' =>
    allFlags.all fun v => allFlags.all fun e =>
      unsafeCertHostname h' s' v e == unsafeCertHostname h s v e) = true := by native_decide

-- match_accepted_prop (Boolean implication form; random strings rarely coincide, so a second
-- random test instantiates `s := h`, and the bounded test covers the general statement)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (!(h == s && v && e) || unsafeCertHostname h s v e) = true)
#eval Plausible.Testable.check (∀ (h : String) (v e : Bool),
  (!(v && e) || unsafeCertHostname h h v e) = true)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      decide (h = s → v = true → e = true → unsafeCertHostname h s v e = true)) = true := by
  native_decide

-- mismatch_accepted_prop (Boolean implication form)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (!(h != s && v && e) || unsafeCertHostname h s v e) = true)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      decide (h ≠ s → v = true → e = true → unsafeCertHostname h s v e = true)) = true := by
  native_decide

-- invalid_rejected_prop (Boolean implication form)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (v || !unsafeCertHostname h s v e) = true)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      decide (v = false → unsafeCertHostname h s v e = false)) = true := by native_decide

-- expired_rejected_prop (Boolean implication form)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (e || !unsafeCertHostname h s v e) = true)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      decide (e = false → unsafeCertHostname h s v e = false)) = true := by native_decide

-- accepts_all_safe_prop (Boolean implication form, plus the `s := h` instance where the
-- safe checker can actually accept)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (!safeCertHostname h s v e || unsafeCertHostname h s v e) = true)
#eval Plausible.Testable.check (∀ (h : String) (v e : Bool),
  (!safeCertHostname h h v e || unsafeCertHostname h h v e) = true)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      decide (safeCertHostname h s v e = true → unsafeCertHostname h s v e = true)) = true := by
  native_decide

-- mitm_witness_prop (existential: executable form is a search over the bounded samples)
example : (sampleHosts.any fun h => sampleHosts.any fun s =>
    h != s && unsafeCertHostname h s true true && !safeCertHostname h s true true) = true := by
  native_decide
#eval sampleHosts.any fun h => sampleHosts.any fun s =>
  h != s && unsafeCertHostname h s true true && !safeCertHostname h s true true

-- Post_prop (executable form `postCheck`)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool), postCheck h s v e = true)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e => postCheck h s v e) = true := by native_decide

/-! ## Correctness -/

/-- Correctness: under the (trivial) pre-condition, every property holds. -/
theorem correctness_thm (requestedHost certSan : String) (certValid certNotExpired : Bool)
    (_hpre : Pre requestedHost certSan certValid certNotExpired) :
    Post_prop requestedHost certSan certValid certNotExpired :=
  ⟨result_spec_thm requestedHost certSan certValid certNotExpired,
   accepted_iff_thm requestedHost certSan certValid certNotExpired,
   hostname_ignored_thm requestedHost certSan certValid certNotExpired,
   match_accepted_thm requestedHost certSan certValid certNotExpired,
   mismatch_accepted_thm requestedHost certSan certValid certNotExpired,
   invalid_rejected_thm requestedHost certSan certValid certNotExpired,
   expired_rejected_thm requestedHost certSan certValid certNotExpired,
   accepts_all_safe_thm requestedHost certSan certValid certNotExpired⟩

/-! ## Imperative implementation -/

set_option linter.unusedVariables false in
/-- Imperative version of `unsafe_cert_hostname`: a step-by-step validation with a mutable
verdict.  Step 1 checks the signature, step 2 checks expiry, and the hostname comparison
(step 3 of RFC 6125) is simply missing, exactly as in the Python source. -/
def unsafeCertHostnameImp (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool := Id.run do
  let mut accepted : Bool := true
  -- Step 1: signature validity
  if !certValid then
    accepted := false
  -- Step 2: expiry
  if !certNotExpired then
    accepted := false
  -- Step 3 (missing!): `requestedHost` is never compared with `certSan`.
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
#eval check unsafeCertHostnameImp                  -- true

#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafeCertHostnameImp h s v e = unsafeCertHostname h s v e)
example : (sampleHosts.all fun h => sampleHosts.all fun s =>
    allFlags.all fun v => allFlags.all fun e =>
      unsafeCertHostnameImp h s v e == unsafeCertHostname h s v e) = true := by native_decide

/-! ## Equivalence -/

/-- The imperative and functional implementations agree on every input. -/
theorem imp_eq_functional_thm (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    unsafeCertHostnameImp requestedHost certSan certValid certNotExpired =
      unsafeCertHostname requestedHost certSan certValid certNotExpired := by
  cases certValid <;> cases certNotExpired <;> rfl

/-- Hence the imperative version also passes the Python harness. -/
theorem check_unsafeCertHostnameImp_thm : check unsafeCertHostnameImp = true := by decide

end «75_unsafeCertHostname»

import Mathlib

/-!
# Unsafe certificate hostname validation

Translation of a Python client that accepts any valid, unexpired certificate
without checking the Subject Alternative Name (SAN) or Common Name (CN)
against the requested hostname.

Vulnerability: a client connecting to `bank.com` accepts a valid certificate
for `evil.com`. Signature and expiry are checked; hostname is not. This
enables a man-in-the-middle attack even when the presented certificate is
cryptographically valid. See MIT 6.858 Lecture 15 and RFC 6125.

The functional model is exactly the Python return value
`cert_valid and cert_not_expired`. A hostname-checking variant is defined only
as a specification contrast (the check the unsafe client omits); it is not part
of the translated implementation.
-/

namespace «75_unsafeCertHostname»

set_option linter.unusedVariables false

/-- Returns true iff the certificate is valid and not expired.

Hostname (`requestedHost`, `certSan`) is intentionally never consulted.
This is the vulnerability: SAN/CN are not compared to the requested host. -/
def unsafeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired

/-- RFC 6125-style exact-match check omitted by the unsafe client.

Accepts only when the certificate is valid, unexpired, and its SAN string is
exactly the requested hostname. Wildcards and case-folding are outside the
Python tests; those tests treat names as raw strings. -/
def safeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired && (requestedHost == certSan)

/-! ## Unit tests -/

example : unsafeCertHostname "bank.com" "bank.com" true true = true := by
  native_decide

example : unsafeCertHostname "bank.com" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "secure.example.com" "attacker.com" true true = true := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" false true = false := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" true false = false := by
  native_decide

example : unsafeCertHostname "bank.com" "*.evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" false false = false := by
  native_decide

#eval unsafeCertHostname "bank.com" "bank.com" true true
#eval unsafeCertHostname "bank.com" "evil.com" true true
#eval unsafeCertHostname "secure.example.com" "attacker.com" true true
#eval unsafeCertHostname "bank.com" "bank.com" false true
#eval unsafeCertHostname "bank.com" "bank.com" true false
#eval unsafeCertHostname "bank.com" "*.evil.com" true true
#eval unsafeCertHostname "" "evil.com" true true
#eval unsafeCertHostname "bank.com" "bank.com" false false

/-! ## Pre-condition -/

/-- The Python function imposes no precondition: every string pair and every
validity/expiry flag is an admissible certificate-check query. -/
def Pre (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  requestedHost = requestedHost ∧ certSan = certSan ∧
    (certValid = true ∨ certValid = false) ∧
    (certNotExpired = true ∨ certNotExpired = false)

/-! ## Properties and theorems -/

/-- Core semantics: the result is exactly `certValid && certNotExpired`.
Hostnames do not appear in the result. -/
def returns_valid_and_unexpired_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    (certValid && certNotExpired)

theorem returns_valid_and_unexpired_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    returns_valid_and_unexpired_prop requestedHost certSan certValid certNotExpired := by
  unfold returns_valid_and_unexpired_prop unsafeCertHostname
  rfl

/-- Changing the requested host or the certificate SAN does not change the result. -/
def hostname_ignored_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  ∀ requestedHost' certSan' : String,
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname requestedHost' certSan' certValid certNotExpired

theorem hostname_ignored_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    hostname_ignored_prop requestedHost certSan certValid certNotExpired := by
  intro _ _
  unfold unsafeCertHostname
  rfl

/-- An invalid certificate is rejected, regardless of hostname and expiry. -/
def rejects_invalid_prop (requestedHost certSan : String)
    (certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan false certNotExpired = false

theorem rejects_invalid_thm (requestedHost certSan : String)
    (certNotExpired : Bool) :
    rejects_invalid_prop requestedHost certSan certNotExpired := by
  unfold rejects_invalid_prop unsafeCertHostname
  rfl

/-- An expired certificate is rejected, regardless of hostname and signature validity. -/
def rejects_expired_prop (requestedHost certSan : String)
    (certValid : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid false = false

theorem rejects_expired_thm (requestedHost certSan : String)
    (certValid : Bool) :
    rejects_expired_prop requestedHost certSan certValid := by
  unfold rejects_expired_prop unsafeCertHostname
  cases certValid <;> rfl

/-- A valid, unexpired certificate is accepted for every hostname pair.

This covers normal exact-match acceptance and the MITM mismatch case. -/
def accepts_valid_unexpired_prop (requestedHost certSan : String) : Prop :=
  unsafeCertHostname requestedHost certSan true true = true

theorem accepts_valid_unexpired_thm (requestedHost certSan : String) :
    accepts_valid_unexpired_prop requestedHost certSan := by
  unfold accepts_valid_unexpired_prop unsafeCertHostname
  rfl

/-- Vulnerability: if SAN does not match the requested host, a valid unexpired
certificate is still accepted. -/
def mismatch_accepted_prop (requestedHost certSan : String) : Prop :=
  requestedHost ≠ certSan →
    unsafeCertHostname requestedHost certSan true true = true

theorem mismatch_accepted_thm (requestedHost certSan : String) :
    mismatch_accepted_prop requestedHost certSan := by
  intro _
  unfold unsafeCertHostname
  rfl

/-- Both invalid and expired: rejected. -/
def rejects_invalid_and_expired_prop (requestedHost certSan : String) : Prop :=
  unsafeCertHostname requestedHost certSan false false = false

theorem rejects_invalid_and_expired_thm (requestedHost certSan : String) :
    rejects_invalid_and_expired_prop requestedHost certSan := by
  unfold rejects_invalid_and_expired_prop unsafeCertHostname
  rfl

/-- Acceptance holds if and only if the certificate is valid and unexpired. -/
def accepts_iff_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
    (certValid = true ∧ certNotExpired = true)

theorem accepts_iff_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    accepts_iff_prop requestedHost certSan certValid certNotExpired := by
  unfold accepts_iff_prop unsafeCertHostname
  cases certValid <;> cases certNotExpired <;> decide

/-- On an exact hostname match the unsafe client agrees with a SAN-checking client.
The bug is not "always accept"; it is "do not compare names". -/
def agrees_on_exact_match_prop (host : String) (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname host host certValid certNotExpired =
    safeCertHostname host host certValid certNotExpired

theorem agrees_on_exact_match_thm (host : String) (certValid certNotExpired : Bool) :
    agrees_on_exact_match_prop host certValid certNotExpired := by
  unfold agrees_on_exact_match_prop unsafeCertHostname safeCertHostname
  cases certValid <;> cases certNotExpired <;> simp

/-- Whenever a hostname-checking client would accept, the unsafe client accepts too. -/
def safe_implies_unsafe_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  safeCertHostname requestedHost certSan certValid certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem safe_implies_unsafe_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    safe_implies_unsafe_prop requestedHost certSan certValid certNotExpired := by
  unfold safe_implies_unsafe_prop safeCertHostname unsafeCertHostname
  intro hsafe
  cases certValid <;> cases certNotExpired <;> simp_all

/-- MITM: on a hostname mismatch a valid unexpired cert is accepted by the unsafe
client and rejected by a client that checks SAN. -/
def mitm_not_caught_prop (requestedHost certSan : String) : Prop :=
  requestedHost ≠ certSan →
    unsafeCertHostname requestedHost certSan true true = true ∧
      safeCertHostname requestedHost certSan true true = false

theorem mitm_not_caught_thm (requestedHost certSan : String) :
    mitm_not_caught_prop requestedHost certSan := by
  intro hne
  refine ⟨?_, ?_⟩
  · unfold unsafeCertHostname
    rfl
  · unfold safeCertHostname
    have hbeq : (requestedHost == certSan) = false :=
      (beq_eq_false_iff_ne).mpr hne
    simp [hbeq]

theorem exact_match_bank_thm :
    unsafeCertHostname "bank.com" "bank.com" true true = true :=
  accepts_valid_unexpired_thm "bank.com" "bank.com"

theorem mitm_bank_evil_thm :
    unsafeCertHostname "bank.com" "evil.com" true true = true :=
  accepts_valid_unexpired_thm "bank.com" "evil.com"

theorem mitm_secure_attacker_thm :
    unsafeCertHostname "secure.example.com" "attacker.com" true true = true :=
  accepts_valid_unexpired_thm "secure.example.com" "attacker.com"

theorem invalid_bank_rejected_thm :
    unsafeCertHostname "bank.com" "bank.com" false true = false :=
  rejects_invalid_thm "bank.com" "bank.com" true

theorem expired_bank_rejected_thm :
    unsafeCertHostname "bank.com" "bank.com" true false = false :=
  rejects_expired_thm "bank.com" "bank.com" true

theorem wildcard_mismatch_accepted_thm :
    unsafeCertHostname "bank.com" "*.evil.com" true true = true :=
  accepts_valid_unexpired_thm "bank.com" "*.evil.com"

theorem empty_hostname_accepted_thm :
    unsafeCertHostname "" "evil.com" true true = true :=
  accepts_valid_unexpired_thm "" "evil.com"

theorem invalid_and_expired_bank_rejected_thm :
    unsafeCertHostname "bank.com" "bank.com" false false = false :=
  rejects_invalid_and_expired_thm "bank.com" "bank.com"

/-! ## Post-condition -/

/-- Post-condition: the call implements validity-and-expiry only, so mismatches
are accepted, invalid or expired certs are rejected, and acceptance is exactly
the conjunction of those two flags. Also records that names are ignored and that
a SAN-checking client would have caught a mismatch. -/
def Post_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  returns_valid_and_unexpired_prop requestedHost certSan certValid certNotExpired ∧
    hostname_ignored_prop requestedHost certSan certValid certNotExpired ∧
    rejects_invalid_prop requestedHost certSan certNotExpired ∧
    rejects_expired_prop requestedHost certSan certValid ∧
    accepts_valid_unexpired_prop requestedHost certSan ∧
    mismatch_accepted_prop requestedHost certSan ∧
    rejects_invalid_and_expired_prop requestedHost certSan ∧
    accepts_iff_prop requestedHost certSan certValid certNotExpired ∧
    agrees_on_exact_match_prop requestedHost certValid certNotExpired ∧
    safe_implies_unsafe_prop requestedHost certSan certValid certNotExpired ∧
    mitm_not_caught_prop requestedHost certSan

/-! ## Property-based tests -/

def pbtHosts : List String :=
  ["", "bank.com", "evil.com", "secure.example.com", "attacker.com",
   "*.evil.com", "a.com", "b.com", "BANK.com", "bank.com."]

def pbtBools : List Bool := [false, true]

#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    unsafeCertHostname h s v e = (v && e))

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtBools.all fun v =>
      pbtBools.all fun e =>
        unsafeCertHostname h s v e == (v && e)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s h' s' : String) (v e : Bool),
    unsafeCertHostname h s v e = unsafeCertHostname h' s' v e)

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtHosts.all fun h' =>
      pbtHosts.all fun s' =>
        pbtBools.all fun v =>
          pbtBools.all fun e =>
            unsafeCertHostname h s v e == unsafeCertHostname h' s' v e) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String) (e : Bool),
    unsafeCertHostname h s false e = false)

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtBools.all fun e =>
      unsafeCertHostname h s false e == false) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String) (v : Bool),
    unsafeCertHostname h s v false = false)

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtBools.all fun v =>
      unsafeCertHostname h s v false == false) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String), unsafeCertHostname h s true true = true)

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    unsafeCertHostname h s true true == true) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String),
    (h == s) || (unsafeCertHostname h s true true == true))

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    decide (h ≠ s → unsafeCertHostname h s true true = true)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String), unsafeCertHostname h s false false = false)

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    unsafeCertHostname h s false false == false) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    unsafeCertHostname h s v e = true ↔ (v = true ∧ e = true))

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtBools.all fun v =>
      pbtBools.all fun e =>
        decide (unsafeCertHostname h s v e = true ↔ (v = true ∧ e = true))) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (host : String) (v e : Bool),
    unsafeCertHostname host host v e = safeCertHostname host host v e)

example : (pbtHosts.all fun host =>
  pbtBools.all fun v =>
    pbtBools.all fun e =>
      unsafeCertHostname host host v e == safeCertHostname host host v e) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    (safeCertHostname h s v e == false) || (unsafeCertHostname h s v e == true))

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtBools.all fun v =>
      pbtBools.all fun e =>
        decide (safeCertHostname h s v e = true → unsafeCertHostname h s v e = true)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s : String),
    (h == s) ||
      (unsafeCertHostname h s true true == true &&
        safeCertHostname h s true true == false))

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    decide (h ≠ s →
      unsafeCertHostname h s true true = true ∧
        safeCertHostname h s true true = false)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h s h' s' : String) (v e : Bool),
    (unsafeCertHostname h s v e == (v && e)) &&
      (unsafeCertHostname h s v e == unsafeCertHostname h' s' v e) &&
      (unsafeCertHostname h s false e == false) &&
      (unsafeCertHostname h s v false == false) &&
      (unsafeCertHostname h s true true == true) &&
      ((h == s) || (unsafeCertHostname h s true true == true)) &&
      (unsafeCertHostname h s false false == false) &&
      ((unsafeCertHostname h s v e == true) == (v && e)) &&
      (unsafeCertHostname h h v e == safeCertHostname h h v e) &&
      ((safeCertHostname h s v e == false) || (unsafeCertHostname h s v e == true)) &&
      ((h == s) ||
        (unsafeCertHostname h s true true == true &&
          safeCertHostname h s true true == false)))

example : (pbtHosts.all fun h =>
  pbtHosts.all fun s =>
    pbtBools.all fun v =>
      pbtBools.all fun e =>
        decide (
          unsafeCertHostname h s v e = (v && e) ∧
            unsafeCertHostname h s false e = false ∧
            unsafeCertHostname h s v false = false ∧
            unsafeCertHostname h s true true = true ∧
            (h ≠ s → unsafeCertHostname h s true true = true) ∧
            unsafeCertHostname h s false false = false ∧
            (unsafeCertHostname h s v e = true ↔ (v = true ∧ e = true)) ∧
            unsafeCertHostname h h v e = safeCertHostname h h v e ∧
            (safeCertHostname h s v e = true → unsafeCertHostname h s v e = true) ∧
            (h ≠ s →
              unsafeCertHostname h s true true = true ∧
                safeCertHostname h s true true = false))) = true := by
  native_decide

/-! ## Correctness -/

theorem pre_holds (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    Pre requestedHost certSan certValid certNotExpired := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases certValid <;> simp
  · cases certNotExpired <;> simp

/-- Every admissible input satisfies the post-condition. -/
theorem correctness_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    Pre requestedHost certSan certValid certNotExpired →
      Post_prop requestedHost certSan certValid certNotExpired := by
  intro _
  exact ⟨returns_valid_and_unexpired_thm requestedHost certSan certValid certNotExpired,
    hostname_ignored_thm requestedHost certSan certValid certNotExpired,
    rejects_invalid_thm requestedHost certSan certNotExpired,
    rejects_expired_thm requestedHost certSan certValid,
    accepts_valid_unexpired_thm requestedHost certSan,
    mismatch_accepted_thm requestedHost certSan,
    rejects_invalid_and_expired_thm requestedHost certSan,
    accepts_iff_thm requestedHost certSan certValid certNotExpired,
    agrees_on_exact_match_thm requestedHost certValid certNotExpired,
    safe_implies_unsafe_thm requestedHost certSan certValid certNotExpired,
    mitm_not_caught_thm requestedHost certSan⟩

/-! ## Imperative implementation -/

/-- Imperative counterpart using mutable state. Host and SAN are received and
stored, then deliberately never compared — matching the Python vulnerability. -/
def unsafeCertHostnameImp (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := false
    let _requested := requestedHost
    let _san := certSan
    if certValid && certNotExpired then
      accepted := true
    else
      accepted := false
    return accepted

/-! ## Imperative tests -/

example : unsafeCertHostnameImp "bank.com" "bank.com" true true = true := by
  native_decide

example : unsafeCertHostnameImp "bank.com" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostnameImp "secure.example.com" "attacker.com" true true = true := by
  native_decide

example : unsafeCertHostnameImp "bank.com" "bank.com" false true = false := by
  native_decide

example : unsafeCertHostnameImp "bank.com" "bank.com" true false = false := by
  native_decide

example : unsafeCertHostnameImp "bank.com" "*.evil.com" true true = true := by
  native_decide

example : unsafeCertHostnameImp "" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostnameImp "bank.com" "bank.com" false false = false := by
  native_decide

#eval unsafeCertHostnameImp "bank.com" "bank.com" true true
#eval unsafeCertHostnameImp "bank.com" "evil.com" true true
#eval unsafeCertHostnameImp "secure.example.com" "attacker.com" true true
#eval unsafeCertHostnameImp "bank.com" "bank.com" false true
#eval unsafeCertHostnameImp "bank.com" "bank.com" true false
#eval unsafeCertHostnameImp "bank.com" "*.evil.com" true true
#eval unsafeCertHostnameImp "" "evil.com" true true
#eval unsafeCertHostnameImp "bank.com" "bank.com" false false

/-! ## Equivalence -/

/-- The functional and imperative implementations agree on every input. -/
theorem equivalence_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostnameImp requestedHost certSan certValid certNotExpired := by
  cases certValid <;> cases certNotExpired <;> rfl

/-- The imperative implementation has the same validity-and-expiry semantics. -/
theorem imp_returns_valid_and_unexpired_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    unsafeCertHostnameImp requestedHost certSan certValid certNotExpired =
      (certValid && certNotExpired) := by
  rw [← equivalence_thm]
  exact returns_valid_and_unexpired_thm requestedHost certSan certValid certNotExpired

end «75_unsafeCertHostname»

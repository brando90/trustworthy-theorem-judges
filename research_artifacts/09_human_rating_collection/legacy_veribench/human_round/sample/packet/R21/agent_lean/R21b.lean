import Mathlib

/-!
# Unsafe certificate hostname validation

Lean 4 formalization of the Python program `unsafe_cert_hostname`.

The Python function returns `True` exactly when the certificate is valid and not
expired; the requested hostname and the certificate's Subject Alternative Name
are accepted as arguments but **never inspected**.  This is the vulnerability
(RFC 6125 hostname verification is skipped), so a MITM presenting a valid
certificate issued for `evil.com` is accepted by a client that asked for
`bank.com`.

The file contains:
* the functional implementation,
* unit tests mirroring the Python `check` function,
* a pre-condition (vacuous: the Python function is total),
* properties describing the true (vulnerable) semantics, each proved,
* the post-condition and the `Pre → Post` correctness theorem,
* an imperative implementation with mutable state and its equivalence proof.
-/

namespace UnsafeCertHostname

/-! ## Functional implementation -/

/-- Returns `true` if the certificate is valid and not expired.  The hostname
arguments `requestedHost` and `certSan` are ignored — this is the bug. -/
def unsafeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired

/-! ## Unit tests (mirroring the Python `check`) -/

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

#eval unsafeCertHostname "bank.com" "evil.com" true true
#eval unsafeCertHostname "bank.com" "bank.com" false true

/-- The full Python test suite as a single decidable check. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  candidate "bank.com" "bank.com" true true == true &&
  candidate "bank.com" "evil.com" true true == true &&
  candidate "secure.example.com" "attacker.com" true true == true &&
  candidate "bank.com" "bank.com" false true == false &&
  candidate "bank.com" "bank.com" true false == false &&
  candidate "bank.com" "*.evil.com" true true == true &&
  candidate "" "evil.com" true true == true &&
  candidate "bank.com" "bank.com" false false == false

example : check unsafeCertHostname = true := by native_decide

#eval check unsafeCertHostname

/-! ## Pre-condition -/

/-- The Python function is total: every combination of arguments is allowed. -/
def Pre (_requestedHost : String) (_certSan : String)
    (_certValid : Bool) (_certNotExpired : Bool) : Prop := True

/-! ## Properties -/

/-- The result is exactly the conjunction of validity and non-expiry. -/
def spec_prop (h s : String) (v e : Bool) : Prop :=
  unsafeCertHostname h s v e = (v && e)

theorem spec_thm (h s : String) (v e : Bool) : spec_prop h s v e := by
  rfl

/-- The result does not depend on either hostname argument: the certificate's
SAN is never compared against the requested host. -/
def hostnameIrrelevant_prop (h₁ s₁ h₂ s₂ : String) (v e : Bool) : Prop :=
  unsafeCertHostname h₁ s₁ v e = unsafeCertHostname h₂ s₂ v e

theorem hostnameIrrelevant_thm (h₁ s₁ h₂ s₂ : String) (v e : Bool) :
    hostnameIrrelevant_prop h₁ s₁ h₂ s₂ v e := by
  rfl

/-- **The vulnerability.**  A certificate whose SAN differs from the requested
hostname is still accepted, as long as it is valid and unexpired. -/
def mitmAccepted_prop (h s : String) : Prop :=
  h ≠ s → unsafeCertHostname h s true true = true

theorem mitmAccepted_thm (h s : String) : mitmAccepted_prop h s := by
  intro _; rfl

/-- Whenever the certificate is valid and unexpired, the request is accepted. -/
def acceptsValid_prop (h s : String) : Prop :=
  unsafeCertHostname h s true true = true

theorem acceptsValid_thm (h s : String) : acceptsValid_prop h s := by
  rfl

/-- An invalid certificate is always rejected. -/
def rejectsInvalid_prop (h s : String) (e : Bool) : Prop :=
  unsafeCertHostname h s false e = false

theorem rejectsInvalid_thm (h s : String) (e : Bool) : rejectsInvalid_prop h s e := by
  rfl

/-- An expired certificate is always rejected. -/
def rejectsExpired_prop (h s : String) (v : Bool) : Prop :=
  unsafeCertHostname h s v false = false

theorem rejectsExpired_thm (h s : String) (v : Bool) : rejectsExpired_prop h s v := by
  simp [rejectsExpired_prop, unsafeCertHostname]

/-- Acceptance happens *only* when the certificate is valid and unexpired. -/
def soundOnCertFields_prop (h s : String) (v e : Bool) : Prop :=
  unsafeCertHostname h s v e = true ↔ (v = true ∧ e = true)

theorem soundOnCertFields_thm (h s : String) (v e : Bool) :
    soundOnCertFields_prop h s v e := by
  simp [soundOnCertFields_prop, unsafeCertHostname]

/-- The secure reference behaviour required by RFC 6125: accept only when the
certificate is valid, unexpired **and** its SAN matches the requested host. -/
def safeCertHostname (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Bool :=
  certValid && certNotExpired && (requestedHost == certSan)

/-- The implementation is *not* the secure one: it differs precisely on the
inputs where a valid, unexpired certificate carries a mismatching SAN. -/
def unsafeDiffersFromSafe_prop (h s : String) (v e : Bool) : Prop :=
  (unsafeCertHostname h s v e = true ∧ safeCertHostname h s v e = false) ↔
    (v = true ∧ e = true ∧ h ≠ s)

theorem unsafeDiffersFromSafe_thm (h s : String) (v e : Bool) :
    unsafeDiffersFromSafe_prop h s v e := by
  simp [unsafeDiffersFromSafe_prop, unsafeCertHostname, safeCertHostname]
  tauto

/-- Concrete witness of the MITM attack from the Python docstring. -/
theorem mitm_witness :
    unsafeCertHostname "bank.com" "evil.com" true true = true ∧
    safeCertHostname "bank.com" "evil.com" true true = false := by
  constructor <;> native_decide

/-! ## Post-condition -/

/-- The post-condition: the conjunction of all properties above. -/
def Post_prop (h s : String) (v e : Bool) : Prop :=
  spec_prop h s v e ∧
  (∀ h₂ s₂, hostnameIrrelevant_prop h s h₂ s₂ v e) ∧
  mitmAccepted_prop h s ∧
  acceptsValid_prop h s ∧
  rejectsInvalid_prop h s e ∧
  rejectsExpired_prop h s v ∧
  soundOnCertFields_prop h s v e ∧
  unsafeDiffersFromSafe_prop h s v e

/-! ## Correctness theorem -/

theorem correctness (h s : String) (v e : Bool) :
    Pre h s v e → Post_prop h s v e := by
  intro _
  exact ⟨spec_thm h s v e,
    fun h₂ s₂ => hostnameIrrelevant_thm h s h₂ s₂ v e,
    mitmAccepted_thm h s,
    acceptsValid_thm h s,
    rejectsInvalid_thm h s e,
    rejectsExpired_thm h s v,
    soundOnCertFields_thm h s v e,
    unsafeDiffersFromSafe_thm h s v e⟩

/-! ## Imperative implementation -/

/-- Imperative rendering with mutable state: a running `accepted` flag that is
updated by the certificate checks.  The hostname check that RFC 6125 requires is
conspicuously absent, exactly as in the Python source. -/
def unsafeCertHostnameImp (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool := Id.run do
  let mut accepted : Bool := true
  if !certValid then
    accepted := false
  if !certNotExpired then
    accepted := false
  -- NOTE: `requestedHost` is never compared with `certSan`.
  let _ := requestedHost
  let _ := certSan
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

/-! ## Equivalence of the functional and imperative implementations -/

theorem funct_eq_imp (h s : String) (v e : Bool) :
    unsafeCertHostname h s v e = unsafeCertHostnameImp h s v e := by
  cases v <;> cases e <;> rfl

end UnsafeCertHostname

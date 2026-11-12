import Mathlib

/-!
# Unsafe certificate hostname validation

This file formalizes a certificate check that accepts a certificate exactly when
its signature is valid and it has not expired.  Both the requested hostname and
the certificate Subject Alternative Name are deliberately ignored, faithfully
capturing the hostname-verification vulnerability in the Python program.
-/

namespace UnsafeCertHostname75

/-! ## Functional implementation -/

def unsafeCertHostname (_requestedHost _certSan : String)
    (certValid certNotExpired : Bool) : Bool :=
  certValid && certNotExpired

/-! ## Functional unit tests -/

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

/-! ## Specification -/

/-- The Python function imposes no precondition on any of its inputs. -/
def Pre (_requestedHost _certSan : String)
    (_certValid _certNotExpired : Bool) : Prop :=
  True

/-- The result depends only on certificate validity and expiry. -/
def validityAndExpiryOnly_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    (certValid && certNotExpired)

theorem validityAndExpiryOnly_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    validityAndExpiryOnly_prop requestedHost certSan certValid certNotExpired := by
  rfl

/-- Changing either hostname cannot change the decision. -/
def hostnamesIgnored_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  ∀ otherRequestedHost otherCertSan : String,
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname otherRequestedHost otherCertSan certValid certNotExpired

theorem hostnamesIgnored_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    hostnamesIgnored_prop requestedHost certSan certValid certNotExpired := by
  intro otherRequestedHost otherCertSan
  rfl

/-- Every valid, unexpired certificate is accepted, even for a wrong hostname. -/
def validFreshAccepted_prop (requestedHost certSan : String) : Prop :=
  unsafeCertHostname requestedHost certSan true true = true

theorem validFreshAccepted_thm (requestedHost certSan : String) :
    validFreshAccepted_prop requestedHost certSan := by
  rfl

/-- A certificate with an invalid signature is rejected. -/
def invalidCertificateRejected_prop (requestedHost certSan : String)
    (certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan false certNotExpired = false

theorem invalidCertificateRejected_thm (requestedHost certSan : String)
    (certNotExpired : Bool) :
    invalidCertificateRejected_prop requestedHost certSan certNotExpired := by
  rfl

/-- An expired certificate is rejected. -/
def expiredCertificateRejected_prop (requestedHost certSan : String)
    (certValid : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid false = false

theorem expiredCertificateRejected_thm (requestedHost certSan : String)
    (certValid : Bool) :
    expiredCertificateRejected_prop requestedHost certSan certValid := by
  cases certValid <;> rfl

/-- The complete post-condition combines the decision rule and its key effects. -/
def Post_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  validityAndExpiryOnly_prop requestedHost certSan certValid certNotExpired ∧
  hostnamesIgnored_prop requestedHost certSan certValid certNotExpired ∧
  validFreshAccepted_prop requestedHost certSan ∧
  invalidCertificateRejected_prop requestedHost certSan certNotExpired ∧
  expiredCertificateRejected_prop requestedHost certSan certValid

theorem unsafeCertHostname_correct (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    Pre requestedHost certSan certValid certNotExpired →
      Post_prop requestedHost certSan certValid certNotExpired := by
  intro _hPre
  exact ⟨validityAndExpiryOnly_thm requestedHost certSan certValid certNotExpired,
    hostnamesIgnored_thm requestedHost certSan certValid certNotExpired,
    validFreshAccepted_thm requestedHost certSan,
    invalidCertificateRejected_thm requestedHost certSan certNotExpired,
    expiredCertificateRejected_thm requestedHost certSan certValid⟩

/-! ## Imperative implementation -/

def unsafeCertHostnameImperative (_requestedHost _certSan : String)
    (certValid certNotExpired : Bool) : Bool := Id.run do
  let mut accepted := certValid
  accepted := accepted && certNotExpired
  return accepted

/-! ## Imperative unit tests -/

example : unsafeCertHostnameImperative "bank.com" "bank.com" true true = true := by
  native_decide

example : unsafeCertHostnameImperative "bank.com" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostnameImperative "secure.example.com" "attacker.com" true true = true := by
  native_decide

example : unsafeCertHostnameImperative "bank.com" "bank.com" false true = false := by
  native_decide

example : unsafeCertHostnameImperative "bank.com" "bank.com" true false = false := by
  native_decide

example : unsafeCertHostnameImperative "bank.com" "*.evil.com" true true = true := by
  native_decide

example : unsafeCertHostnameImperative "" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostnameImperative "bank.com" "bank.com" false false = false := by
  native_decide

#eval unsafeCertHostnameImperative "bank.com" "bank.com" true true
#eval unsafeCertHostnameImperative "bank.com" "evil.com" true true
#eval unsafeCertHostnameImperative "secure.example.com" "attacker.com" true true
#eval unsafeCertHostnameImperative "bank.com" "bank.com" false true
#eval unsafeCertHostnameImperative "bank.com" "bank.com" true false
#eval unsafeCertHostnameImperative "bank.com" "*.evil.com" true true
#eval unsafeCertHostnameImperative "" "evil.com" true true
#eval unsafeCertHostnameImperative "bank.com" "bank.com" false false

theorem functional_eq_imperative (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostnameImperative requestedHost certSan certValid certNotExpired := by
  rfl

end UnsafeCertHostname75

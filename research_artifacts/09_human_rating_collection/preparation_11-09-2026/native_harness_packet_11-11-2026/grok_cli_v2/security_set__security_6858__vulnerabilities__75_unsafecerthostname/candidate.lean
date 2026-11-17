import Mathlib

/-!
# Unsafe certificate hostname validation

A client asks to connect to `requestedHost`. The server presents a certificate
whose Subject Alternative Name is `certSan`, together with two facts already
checked elsewhere: the signature is valid (`certValid`) and the certificate is
inside its validity window (`certNotExpired`).

The routine below returns whether the client accepts that certificate.
It returns `certValid && certNotExpired` and never compares `requestedHost`
with `certSan`. A valid, unexpired certificate for `evil.com` is therefore
accepted for `bank.com`. That is a man-in-the-middle hole even though every
certificate involved is cryptographically valid.

Reference: MIT 6.858 Lecture 15 (Certificates); RFC 6125 (hostname verification).

The Python source is

```python
def unsafe_cert_hostname(requested_host, cert_san, cert_valid, cert_not_expired):
    return cert_valid and cert_not_expired  # Hostname never checked!
```

There is no floating-point data in this program. Hostnames are `String` and the
two certificate facts are `Bool`.
-/

namespace «75_unsafeCertHostname»

/-! ## Implementation -/

set_option linter.unusedVariables false in
/-- Accept a certificate exactly when it is valid and not expired.

`requestedHost` and `certSan` are part of the Python signature and are
intentionally unused: the hostname is never checked. -/
def unsafeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired

/-- Exact string comparison of the requested host and the certificate SAN,
conjoined with validity and freshness.

This is the check `unsafeCertHostname` omits. It is the equality case of
hostname verification, not a full RFC 6125 implementation: it does not
case-fold DNS labels, expand wildcards, or interpret IDNA. A client that
fails even this check accepts certificates issued to a different name.
-/
def exactNameCheck (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired && (requestedHost == certSan)

/-! ## Unit tests

The examples mirror `check` in the Python source. `native_decide` is used only
on these closed tests, never inside a theorem proof.
-/

/-- Python `check`: the eight assertions from the source, packed as a Boolean. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  (candidate "bank.com" "bank.com" true true == true) &&
  (candidate "bank.com" "evil.com" true true == true) &&
  (candidate "secure.example.com" "attacker.com" true true == true) &&
  (candidate "bank.com" "bank.com" false true == false) &&
  (candidate "bank.com" "bank.com" true false == false) &&
  (candidate "bank.com" "*.evil.com" true true == true) &&
  (candidate "" "evil.com" true true == true) &&
  (candidate "bank.com" "bank.com" false false == false)

-- 1) Normal operation — exact hostname match accepted.
example : unsafeCertHostname "bank.com" "bank.com" true true = true := by
  native_decide

-- 2) Vulnerability — hostname mismatch accepted (MITM succeeds).
example : unsafeCertHostname "bank.com" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "secure.example.com" "attacker.com" true true = true := by
  native_decide

-- 3) Invalid or expired certificates are still rejected.
example : unsafeCertHostname "bank.com" "bank.com" false true = false := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" true false = false := by
  native_decide

-- 4) Edge cases from the Python source.
example : unsafeCertHostname "bank.com" "*.evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" false false = false := by
  native_decide

example : check unsafeCertHostname = true := by
  native_decide

-- Contrast with the omitted exact-name check (not part of the Python function).
example : exactNameCheck "bank.com" "bank.com" true true = true := by
  native_decide

example : exactNameCheck "bank.com" "evil.com" true true = false := by
  native_decide

example : exactNameCheck "bank.com" "*.evil.com" true true = false := by
  native_decide

#eval unsafeCertHostname "bank.com" "bank.com" true true
#eval unsafeCertHostname "bank.com" "evil.com" true true
#eval unsafeCertHostname "secure.example.com" "attacker.com" true true
#eval unsafeCertHostname "bank.com" "bank.com" false true
#eval unsafeCertHostname "bank.com" "bank.com" true false
#eval unsafeCertHostname "bank.com" "*.evil.com" true true
#eval unsafeCertHostname "" "evil.com" true true
#eval unsafeCertHostname "bank.com" "bank.com" false false
#eval check unsafeCertHostname
#eval exactNameCheck "bank.com" "evil.com" true true

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- Every input is admissible.

The Python function is total. Empty hostnames, wildcard SANs, and every
combination of the two flags are in the domain. There is no well-formedness
side condition to add. -/
def Pre (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  True

/-! ## Properties -/

/-- The return value is exactly the Python expression `cert_valid and cert_not_expired`. -/
def spec_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    (certValid && certNotExpired)

theorem spec_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    spec_prop requestedHost certSan certValid certNotExpired := by
  unfold spec_prop unsafeCertHostname
  rfl

/-- Docstring claim: the certificate is accepted if and only if it is valid
and not expired. The hostname does not appear in the criterion. -/
def accepts_iff_valid_unexpired_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
    certValid = true ∧ certNotExpired = true

theorem accepts_iff_valid_unexpired_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    accepts_iff_valid_unexpired_prop requestedHost certSan certValid certNotExpired := by
  unfold accepts_iff_valid_unexpired_prop unsafeCertHostname
  cases certValid <;> cases certNotExpired <;> decide

/-- An invalid certificate is rejected, whether or not it is expired and
whether or not the names match. -/
def rejects_invalid_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  certValid = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem rejects_invalid_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    rejects_invalid_prop requestedHost certSan certValid certNotExpired := by
  unfold rejects_invalid_prop unsafeCertHostname
  intro hInvalid
  simp [hInvalid]

/-- An expired certificate is rejected, whether or not the signature checked
and whether or not the names match. -/
def rejects_expired_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  certNotExpired = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem rejects_expired_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    rejects_expired_prop requestedHost certSan certValid certNotExpired := by
  unfold rejects_expired_prop unsafeCertHostname
  intro hExpired
  simp [hExpired]

/-- Normal operation from the tests: a valid, unexpired certificate whose SAN
is exactly the requested host is accepted. -/
def exact_match_accepted_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  requestedHost = certSan → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem exact_match_accepted_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    exact_match_accepted_prop requestedHost certSan certValid certNotExpired := by
  unfold exact_match_accepted_prop unsafeCertHostname
  intro _ hValid hFresh
  simp [hValid, hFresh]

/-- MITM hole: a valid, unexpired certificate is accepted even when the SAN
is a different name from the host the client requested. -/
def mitm_accepted_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  requestedHost ≠ certSan → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem mitm_accepted_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    mitm_accepted_prop requestedHost certSan certValid certNotExpired := by
  unfold mitm_accepted_prop unsafeCertHostname
  intro _ hValid hFresh
  simp [hValid, hFresh]

/-- Empty requested hostname is accepted whenever the certificate flags pass.
The Python test `candidate("", "evil.com", True, True)` is this case. -/
def empty_hostname_accepted_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  requestedHost = "" → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem empty_hostname_accepted_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    empty_hostname_accepted_prop requestedHost certSan certValid certNotExpired := by
  unfold empty_hostname_accepted_prop unsafeCertHostname
  intro _ hValid hFresh
  simp [hValid, hFresh]

/-- A wildcard SAN is not interpreted. Any pattern that begins with `*.`
(including the test value `*.evil.com`, which does not match `bank.com`) is
accepted whenever the certificate is valid and unexpired. -/
def wildcard_san_accepted_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  certSan.startsWith "*." = true → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem wildcard_san_accepted_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    wildcard_san_accepted_prop requestedHost certSan certValid certNotExpired := by
  unfold wildcard_san_accepted_prop unsafeCertHostname
  intro _ hValid hFresh
  simp [hValid, hFresh]

/-- Replacing either name leaves the decision unchanged. This is the
"hostname never checked" comment, stated for a pair of calls. -/
def hostname_irrelevant_prop (requestedHost : String) (certSan : String)
    (otherHost : String) (otherSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    unsafeCertHostname otherHost otherSan certValid certNotExpired

theorem hostname_irrelevant_thm (requestedHost : String) (certSan : String)
    (otherHost : String) (otherSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    hostname_irrelevant_prop requestedHost certSan otherHost otherSan
      certValid certNotExpired := by
  unfold hostname_irrelevant_prop unsafeCertHostname
  rfl

/-- Two calls agree whenever they are given the same certificate flags,
regardless of which hostnames either call saw. -/
def determined_by_flags_prop
    (requestedHost₁ : String) (certSan₁ : String)
    (certValid₁ : Bool) (certNotExpired₁ : Bool)
    (requestedHost₂ : String) (certSan₂ : String)
    (certValid₂ : Bool) (certNotExpired₂ : Bool) : Prop :=
  certValid₁ = certValid₂ → certNotExpired₁ = certNotExpired₂ →
    unsafeCertHostname requestedHost₁ certSan₁ certValid₁ certNotExpired₁ =
      unsafeCertHostname requestedHost₂ certSan₂ certValid₂ certNotExpired₂

theorem determined_by_flags_thm
    (requestedHost₁ : String) (certSan₁ : String)
    (certValid₁ : Bool) (certNotExpired₁ : Bool)
    (requestedHost₂ : String) (certSan₂ : String)
    (certValid₂ : Bool) (certNotExpired₂ : Bool) :
    determined_by_flags_prop requestedHost₁ certSan₁ certValid₁ certNotExpired₁
      requestedHost₂ certSan₂ certValid₂ certNotExpired₂ := by
  unfold determined_by_flags_prop unsafeCertHostname
  intro hValid hFresh
  simp [hValid, hFresh]

/-- Relative to exact SAN match: every certificate the exact check accepts is
accepted here, and every valid unexpired certificate for a different name is
accepted here and rejected by the exact check. -/
def over_accepts_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  (exactNameCheck requestedHost certSan certValid certNotExpired = true →
      unsafeCertHostname requestedHost certSan certValid certNotExpired = true) ∧
    (certValid = true → certNotExpired = true → requestedHost ≠ certSan →
      unsafeCertHostname requestedHost certSan certValid certNotExpired = true ∧
        exactNameCheck requestedHost certSan certValid certNotExpired = false)

theorem over_accepts_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    over_accepts_prop requestedHost certSan certValid certNotExpired := by
  unfold over_accepts_prop exactNameCheck unsafeCertHostname
  constructor
  · intro hAccepted
    cases certValid <;> cases certNotExpired <;> simp_all
  · intro hValid hFresh hMismatch
    subst hValid
    subst hFresh
    constructor
    · rfl
    · have hSan : (requestedHost == certSan) = false :=
        (beq_eq_false_iff_ne).mpr hMismatch
      simp [hSan]

/-- Lecture scenario: the client asked for `bank.com` and accepts a valid,
unexpired certificate whose SAN is `evil.com`. The exact-name check rejects it. -/
def bank_evil_mitm_prop : Prop :=
  unsafeCertHostname "bank.com" "evil.com" true true = true ∧
    exactNameCheck "bank.com" "evil.com" true true = false

theorem bank_evil_mitm_thm : bank_evil_mitm_prop := by
  unfold bank_evil_mitm_prop unsafeCertHostname exactNameCheck
  decide

/-- The Python harness `check(unsafe_cert_hostname)` succeeds. -/
def check_passes_prop : Prop :=
  check unsafeCertHostname = true

theorem check_passes_thm : check_passes_prop := by
  unfold check_passes_prop check unsafeCertHostname
  decide

/-! ## Post-condition -/

/-- Full contract of one call: the decision is the flag conjunction, invalid
and expired certificates are rejected, good certificates are accepted for
matching names, mismatched names, the empty host, and wildcard SANs, the
decision ignores the names, and the result strictly over-accepts exact
hostname verification. -/
def Post_prop (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  spec_prop requestedHost certSan certValid certNotExpired ∧
    accepts_iff_valid_unexpired_prop requestedHost certSan certValid certNotExpired ∧
    rejects_invalid_prop requestedHost certSan certValid certNotExpired ∧
    rejects_expired_prop requestedHost certSan certValid certNotExpired ∧
    exact_match_accepted_prop requestedHost certSan certValid certNotExpired ∧
    mitm_accepted_prop requestedHost certSan certValid certNotExpired ∧
    empty_hostname_accepted_prop requestedHost certSan certValid certNotExpired ∧
    wildcard_san_accepted_prop requestedHost certSan certValid certNotExpired ∧
    over_accepts_prop requestedHost certSan certValid certNotExpired ∧
    (∀ otherHost otherSan : String,
      hostname_irrelevant_prop requestedHost certSan otherHost otherSan
        certValid certNotExpired)

/-! ## Property-based tests

Randomized checks use Plausible on unconditional statements so every sample is
admissible. Conditional properties are also exhaustively checked on the hosts
and flag combinations below, which include every literal from the Python tests.
-/

/-- Hosts drawn from the Python tests, plus a few neighbours. -/
def hostSamples : List String :=
  [ ""
  , "bank.com"
  , "evil.com"
  , "secure.example.com"
  , "attacker.com"
  , "*.evil.com"
  , "www.bank.com"
  , "a.evil.com"
  ]

def flagSamples : List Bool := [false, true]

/-- Boolean implication, used only by executable checks. -/
def impliesB (p q : Bool) : Bool := !p || q

/-- Run `p` on every sample host pair and both certificate flags. -/
def forAllSamples (p : String → String → Bool → Bool → Bool) : Bool :=
  hostSamples.all fun requestedHost =>
    hostSamples.all fun certSan =>
      flagSamples.all fun certValid =>
        flagSamples.all fun certNotExpired =>
          p requestedHost certSan certValid certNotExpired

/-- Executable form of `Post_prop` on one input. The name-irrelevance quantifier
is checked separately across `hostSamples`. -/
def postExecutable (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  let result := unsafeCertHostname requestedHost certSan certValid certNotExpired
  let exact := exactNameCheck requestedHost certSan certValid certNotExpired
  -- spec_prop
  (result == (certValid && certNotExpired)) &&
    -- accepts_iff_valid_unexpired_prop
    ((result == true) == (certValid && certNotExpired)) &&
    -- rejects_invalid_prop
    impliesB (certValid == false) (result == false) &&
    -- rejects_expired_prop
    impliesB (certNotExpired == false) (result == false) &&
    -- exact_match_accepted_prop
    impliesB (requestedHost == certSan && certValid && certNotExpired) (result == true) &&
    -- mitm_accepted_prop
    impliesB (!(requestedHost == certSan) && certValid && certNotExpired) (result == true) &&
    -- empty_hostname_accepted_prop
    impliesB (requestedHost == "" && certValid && certNotExpired) (result == true) &&
    -- wildcard_san_accepted_prop
    impliesB (certSan.startsWith "*." && certValid && certNotExpired) (result == true) &&
    -- over_accepts_prop, first conjunct
    impliesB (exact == true) (result == true) &&
    -- over_accepts_prop, second conjunct
    impliesB (!(requestedHost == certSan) && certValid && certNotExpired)
      (result == true && exact == false)

open Plausible Plausible.Decorations

-- PBT for spec_prop
#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      (certValid && certNotExpired))

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    unsafeCertHostname requestedHost certSan certValid certNotExpired ==
      (certValid && certNotExpired)) = true := by
  native_decide

-- PBT for accepts_iff_valid_unexpired_prop
#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
      certValid = true ∧ certNotExpired = true)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    ((unsafeCertHostname requestedHost certSan certValid certNotExpired == true) ==
      (certValid && certNotExpired))) = true := by
  native_decide

-- PBT for rejects_invalid_prop
#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan false certNotExpired = false)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    impliesB (certValid == false)
      (unsafeCertHostname requestedHost certSan certValid certNotExpired == false)) = true := by
  native_decide

-- PBT for rejects_expired_prop
#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid : Bool),
    unsafeCertHostname requestedHost certSan certValid false = false)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    impliesB (certNotExpired == false)
      (unsafeCertHostname requestedHost certSan certValid certNotExpired == false)) = true := by
  native_decide

-- PBT for exact_match_accepted_prop.
-- Acceptance of a good certificate does not depend on the names being equal,
-- so the randomized check states the stronger unconditional fact.
#eval Plausible.Testable.check
  (∀ requestedHost : String,
    unsafeCertHostname requestedHost requestedHost true true = true)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    impliesB (requestedHost == certSan && certValid && certNotExpired)
      (unsafeCertHostname requestedHost certSan certValid certNotExpired == true)) = true := by
  native_decide

-- PBT for mitm_accepted_prop.
-- Every valid unexpired pair is accepted, matching names included, so a
-- mismatched SAN cannot be the reason for rejection.
#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String),
    unsafeCertHostname requestedHost certSan true true = true)

-- Strict mismatches constructed so the two names differ in length.
#eval Plausible.Testable.check
  (∀ requestedHost : String,
    unsafeCertHostname requestedHost (requestedHost ++ ".evil") true true = true ∧
      exactNameCheck requestedHost (requestedHost ++ ".evil") true true = false)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    impliesB (!(requestedHost == certSan) && certValid && certNotExpired)
      (unsafeCertHostname requestedHost certSan certValid certNotExpired == true)) = true := by
  native_decide

-- PBT for empty_hostname_accepted_prop
#eval Plausible.Testable.check
  (∀ certSan : String,
    unsafeCertHostname "" certSan true true = true)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    impliesB (requestedHost == "" && certValid && certNotExpired)
      (unsafeCertHostname requestedHost certSan certValid certNotExpired == true)) = true := by
  native_decide

-- PBT for wildcard_san_accepted_prop
#eval Plausible.Testable.check
  (∀ requestedHost : String,
    unsafeCertHostname requestedHost "*.evil.com" true true = true)

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    impliesB (certSan.startsWith "*." && certValid && certNotExpired)
      (unsafeCertHostname requestedHost certSan certValid certNotExpired == true)) = true := by
  native_decide

-- PBT for hostname_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (requestedHost certSan otherHost otherSan : String)
      (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname otherHost otherSan certValid certNotExpired)

example : (hostSamples.all fun requestedHost =>
    hostSamples.all fun certSan =>
      hostSamples.all fun otherHost =>
        hostSamples.all fun otherSan =>
          flagSamples.all fun certValid =>
            flagSamples.all fun certNotExpired =>
              unsafeCertHostname requestedHost certSan certValid certNotExpired ==
                unsafeCertHostname otherHost otherSan certValid certNotExpired) = true := by
  native_decide

-- PBT for determined_by_flags_prop.
-- When the flags differ the implication is vacuous; the randomized check
-- covers every non-vacuous case (equal flags, arbitrary names).
#eval Plausible.Testable.check
  (∀ (requestedHost₁ certSan₁ requestedHost₂ certSan₂ : String)
      (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost₁ certSan₁ certValid certNotExpired =
      unsafeCertHostname requestedHost₂ certSan₂ certValid certNotExpired)

example : (hostSamples.all fun requestedHost₁ =>
    hostSamples.all fun certSan₁ =>
      flagSamples.all fun certValid₁ =>
        flagSamples.all fun certNotExpired₁ =>
          hostSamples.all fun requestedHost₂ =>
            hostSamples.all fun certSan₂ =>
              flagSamples.all fun certValid₂ =>
                flagSamples.all fun certNotExpired₂ =>
                  impliesB (certValid₁ == certValid₂ && certNotExpired₁ == certNotExpired₂)
                    (unsafeCertHostname requestedHost₁ certSan₁ certValid₁ certNotExpired₁ ==
                      unsafeCertHostname requestedHost₂ certSan₂ certValid₂ certNotExpired₂)) =
                      true := by
  native_decide

-- PBT for over_accepts_prop
example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    let result := unsafeCertHostname requestedHost certSan certValid certNotExpired
    let exact := exactNameCheck requestedHost certSan certValid certNotExpired
    impliesB (exact == true) (result == true) &&
      impliesB (!(requestedHost == certSan) && certValid && certNotExpired)
        (result == true && exact == false)) = true := by
  native_decide

-- PBT for bank_evil_mitm_prop (closed lecture scenario, plus the family above)
example : (unsafeCertHostname "bank.com" "evil.com" true true == true &&
    exactNameCheck "bank.com" "evil.com" true true == false) = true := by
  native_decide

-- PBT for check_passes_prop
example : check unsafeCertHostname = true := by
  native_decide

-- PBT for Post_prop
#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
        (certValid && certNotExpired) ∧
      (unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
        certValid = true ∧ certNotExpired = true) ∧
      (∀ otherHost otherSan : String,
        unsafeCertHostname requestedHost certSan certValid certNotExpired =
          unsafeCertHostname otherHost otherSan certValid certNotExpired))

example : forAllSamples postExecutable = true := by
  native_decide

example : (hostSamples.all fun requestedHost =>
    hostSamples.all fun certSan =>
      flagSamples.all fun certValid =>
        flagSamples.all fun certNotExpired =>
          postExecutable requestedHost certSan certValid certNotExpired &&
            hostSamples.all fun otherHost =>
              hostSamples.all fun otherSan =>
                unsafeCertHostname requestedHost certSan certValid certNotExpired ==
                  unsafeCertHostname otherHost otherSan certValid certNotExpired) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool)
    (hPre : Pre requestedHost certSan certValid certNotExpired) :
    Post_prop requestedHost certSan certValid certNotExpired := by
  cases hPre
  unfold Post_prop
  exact ⟨spec_thm requestedHost certSan certValid certNotExpired,
    accepts_iff_valid_unexpired_thm requestedHost certSan certValid certNotExpired,
    rejects_invalid_thm requestedHost certSan certValid certNotExpired,
    rejects_expired_thm requestedHost certSan certValid certNotExpired,
    exact_match_accepted_thm requestedHost certSan certValid certNotExpired,
    mitm_accepted_thm requestedHost certSan certValid certNotExpired,
    empty_hostname_accepted_thm requestedHost certSan certValid certNotExpired,
    wildcard_san_accepted_thm requestedHost certSan certValid certNotExpired,
    over_accepts_thm requestedHost certSan certValid certNotExpired,
    fun otherHost otherSan =>
      hostname_irrelevant_thm requestedHost certSan otherHost otherSan
        certValid certNotExpired⟩

/-! ## Imperative implementation

Same decision as `unsafeCertHostname`, written with mutable flags.
The host and the SAN are copied into mutable buffers and then not consulted.
-/

def unsafeCertHostnameImp (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := false
    let mut validFlag : Bool := certValid
    let mut freshFlag : Bool := certNotExpired
    let mut hostBuf : String := requestedHost
    let mut sanBuf : String := certSan
    let _readHost := hostBuf
    let _readSan := sanBuf
    accepted := validFlag && freshFlag
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

example : check unsafeCertHostnameImp = true := by
  native_decide

example : forAllSamples (fun requestedHost certSan certValid certNotExpired =>
    unsafeCertHostname requestedHost certSan certValid certNotExpired ==
      unsafeCertHostnameImp requestedHost certSan certValid certNotExpired) = true := by
  native_decide

#eval unsafeCertHostnameImp "bank.com" "evil.com" true true
#eval unsafeCertHostnameImp "bank.com" "bank.com" false true
#eval check unsafeCertHostnameImp

/-- The imperative implementation passes the same Python harness. -/
theorem check_imp_passes_thm : check unsafeCertHostnameImp = true := by
  unfold check unsafeCertHostnameImp
  decide

/-! ## Equivalence -/

theorem functional_eq_imperative_thm (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) :
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostnameImp requestedHost certSan certValid certNotExpired := by
  rfl

end «75_unsafeCertHostname»

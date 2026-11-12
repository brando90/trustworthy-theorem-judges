import Mathlib

/-!
# Unsafe certificate hostname validation

Lean 4 translation of the Python program `unsafe_cert_hostname`.

The Python function models a *vulnerable* TLS client: it accepts a server
certificate as soon as the certificate is validly signed (`cert_valid`) and not
expired (`cert_not_expired`), but it never checks that the certificate's Subject
Alternative Name (SAN) matches the requested hostname (MIT 6.858 Lecture 15,
RFC 6125).  Consequently a client connecting to `bank.com` accepts a perfectly
valid certificate issued for `evil.com`, enabling man-in-the-middle attacks.

The functional implementation `unsafeCertHostname` returns
`certValid && certNotExpired`, ignoring both string arguments, exactly like the
Python source.  We state and prove the properties exhibited by the Python test
suite: the result is exactly the conjunction of the two Boolean flags, the
hostname/SAN are irrelevant, mismatching hostnames are accepted (the
vulnerability), and invalid or expired certificates are rejected.
-/

namespace «75_unsafeCertHostname»

/-! ## Functional implementation -/

/-- Returns `true` iff the certificate is valid and not expired.
The requested hostname and the certificate SAN are never inspected --
this is the vulnerability modelled by the Python program. -/
def unsafeCertHostname (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool :=
  certValid && certNotExpired  -- Hostname never checked!

/-! ## Unit tests (mirroring the Python `check` function) -/

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

#eval unsafeCertHostname "bank.com" "bank.com" true true      -- true
#eval unsafeCertHostname "bank.com" "evil.com" true true      -- true
#eval unsafeCertHostname "secure.example.com" "attacker.com" true true  -- true
#eval unsafeCertHostname "bank.com" "bank.com" false true     -- false
#eval unsafeCertHostname "bank.com" "bank.com" true false     -- false
#eval unsafeCertHostname "bank.com" "*.evil.com" true true    -- true
#eval unsafeCertHostname "" "evil.com" true true              -- true
#eval unsafeCertHostname "bank.com" "bank.com" false false    -- false

/-- Executable replica of the Python `check` function. -/
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
#eval check unsafeCertHostname  -- true

/-! ## Pre-condition -/

/-- Pre-condition: the Python function accepts arbitrary hostnames, SANs and
Boolean flags, so there is no restriction on the inputs. -/
def Pre (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Prop :=
  True

/-! ## Properties -/

/-- The result is exactly the conjunction of the two certificate flags. -/
def result_is_conj_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    (certValid && certNotExpired)

theorem result_is_conj_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    result_is_conj_prop requestedHost certSan certValid certNotExpired := by
  unfold result_is_conj_prop unsafeCertHostname
  rfl

/-- The certificate is accepted iff it is valid and not expired. -/
def accepts_iff_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
    (certValid = true ∧ certNotExpired = true)

theorem accepts_iff_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    accepts_iff_prop requestedHost certSan certValid certNotExpired := by
  unfold accepts_iff_prop unsafeCertHostname
  exact Iff.of_eq (Bool.and_eq_true certValid certNotExpired)

/-- The hostname is never checked: the result does not depend on the requested
hostname nor on the certificate SAN. -/
def hostname_ignored_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  ∀ (otherHost otherSan : String),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname otherHost otherSan certValid certNotExpired

theorem hostname_ignored_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    hostname_ignored_prop requestedHost certSan certValid certNotExpired := by
  intro otherHost otherSan
  rfl

/-- Vulnerability (MITM): a valid, unexpired certificate is accepted even when
its SAN does not match the requested hostname. -/
def mitm_accepted_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  requestedHost ≠ certSan → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem mitm_accepted_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    mitm_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro _ hv he
  unfold unsafeCertHostname
  rw [hv, he]
  rfl

/-- Any valid, unexpired certificate is accepted (matching or not). -/
def valid_unexpired_accepted_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem valid_unexpired_accepted_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    valid_unexpired_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro hv he
  unfold unsafeCertHostname
  rw [hv, he]
  rfl

/-- An invalid certificate (bad signature) is always rejected. -/
def invalid_rejected_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  certValid = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem invalid_rejected_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    invalid_rejected_prop requestedHost certSan certValid certNotExpired := by
  intro hv
  unfold unsafeCertHostname
  rw [hv]
  rfl

/-- An expired certificate is always rejected. -/
def expired_rejected_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  certNotExpired = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem expired_rejected_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    expired_rejected_prop requestedHost certSan certValid certNotExpired := by
  intro he
  unfold unsafeCertHostname
  rw [he]
  exact Bool.and_false certValid

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Prop :=
  result_is_conj_prop requestedHost certSan certValid certNotExpired ∧
  accepts_iff_prop requestedHost certSan certValid certNotExpired ∧
  hostname_ignored_prop requestedHost certSan certValid certNotExpired ∧
  mitm_accepted_prop requestedHost certSan certValid certNotExpired ∧
  valid_unexpired_accepted_prop requestedHost certSan certValid certNotExpired ∧
  invalid_rejected_prop requestedHost certSan certValid certNotExpired ∧
  expired_rejected_prop requestedHost certSan certValid certNotExpired

/-! ## Property-based tests -/

/-- Pool of hostnames / SANs taken from the Python tests plus a few extras. -/
def testHosts : List String :=
  ["bank.com", "evil.com", "secure.example.com", "attacker.com", "*.evil.com",
   "", "a", "localhost", "*.bank.com", "BANK.COM"]

/-- Executable Boolean form of `Post_prop` on one input, where the universally
quantified part of `hostname_ignored_prop` is checked against `testHosts`. -/
def postCheck (h s : String) (v e : Bool) : Bool :=
  let r := unsafeCertHostname h s v e
  -- result_is_conj_prop
  (r == (v && e)) &&
  -- accepts_iff_prop
  ((r == true) == (v == true && e == true)) &&
  -- hostname_ignored_prop (bounded)
  (testHosts.all fun h' => testHosts.all fun s' => r == unsafeCertHostname h' s' v e) &&
  -- mitm_accepted_prop
  (!(h != s && v && e) || r == true) &&
  -- valid_unexpired_accepted_prop
  (!(v && e) || r == true) &&
  -- invalid_rejected_prop
  (v || r == false) &&
  -- expired_rejected_prop
  (e || r == false)

-- Randomized PBTs (Plausible).

-- result_is_conj_prop
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool), unsafeCertHostname h s v e = (v && e))

-- accepts_iff_prop
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool),
    (unsafeCertHostname h s v e = true) ↔ (v = true ∧ e = true))

-- hostname_ignored_prop
#eval Plausible.Testable.check
  (∀ (h s h' s' : String) (v e : Bool),
    unsafeCertHostname h s v e = unsafeCertHostname h' s' v e)

-- mitm_accepted_prop (Bool hypotheses `v = true`, `e = true` instantiated; the
-- string hypothesis `h ≠ s → _` is written as the equivalent disjunction
-- `h = s ∨ _` so that Plausible never has to discard samples)
#eval Plausible.Testable.check
  (∀ (h s : String), h = s ∨ unsafeCertHostname h s true true = true)

-- valid_unexpired_accepted_prop (hypotheses instantiated)
#eval Plausible.Testable.check
  (∀ (h s : String), unsafeCertHostname h s true true = true)

-- invalid_rejected_prop (hypothesis `v = false` instantiated)
#eval Plausible.Testable.check
  (∀ (h s : String) (e : Bool), unsafeCertHostname h s false e = false)

-- expired_rejected_prop (hypothesis `e = false` instantiated)
#eval Plausible.Testable.check
  (∀ (h s : String) (v : Bool), unsafeCertHostname h s v false = false)

-- Post_prop (executable Boolean form `postCheck`; the universally quantified
-- hostname-independence clause is checked against the finite pool `testHosts`)
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool), postCheck h s v e = true)

-- Bounded / exhaustive PBTs over a fixed pool of hostnames and all flag values.

example :
    (testHosts.all fun h => testHosts.all fun s =>
      [true, false].all fun v => [true, false].all fun e => postCheck h s v e) = true := by
  native_decide

-- Individual bounded PBTs.
example :
    (testHosts.all fun h => testHosts.all fun s =>
      [true, false].all fun v => [true, false].all fun e =>
        unsafeCertHostname h s v e == (v && e)) = true := by
  native_decide

example :
    (testHosts.all fun h => testHosts.all fun s =>
      [true, false].all fun v => [true, false].all fun e =>
        (unsafeCertHostname h s v e == true) == (v == true && e == true)) = true := by
  native_decide

example :
    (testHosts.all fun h => testHosts.all fun s =>
      testHosts.all fun h' => testHosts.all fun s' =>
      [true, false].all fun v => [true, false].all fun e =>
        unsafeCertHostname h s v e == unsafeCertHostname h' s' v e) = true := by
  native_decide

example :
    (testHosts.all fun h => testHosts.all fun s =>
      h == s || unsafeCertHostname h s true true == true) = true := by
  native_decide

example :
    (testHosts.all fun h => testHosts.all fun s =>
      unsafeCertHostname h s true true == true) = true := by
  native_decide

example :
    (testHosts.all fun h => testHosts.all fun s =>
      [true, false].all fun e => unsafeCertHostname h s false e == false) = true := by
  native_decide

example :
    (testHosts.all fun h => testHosts.all fun s =>
      [true, false].all fun v => unsafeCertHostname h s v false == false) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    Pre requestedHost certSan certValid certNotExpired →
    Post_prop requestedHost certSan certValid certNotExpired := by
  intro _
  exact ⟨result_is_conj_thm requestedHost certSan certValid certNotExpired,
    accepts_iff_thm requestedHost certSan certValid certNotExpired,
    hostname_ignored_thm requestedHost certSan certValid certNotExpired,
    mitm_accepted_thm requestedHost certSan certValid certNotExpired,
    valid_unexpired_accepted_thm requestedHost certSan certValid certNotExpired,
    invalid_rejected_thm requestedHost certSan certValid certNotExpired,
    expired_rejected_thm requestedHost certSan certValid certNotExpired⟩

/-! ## Imperative implementation -/

/-- Imperative version with mutable state, mirroring the short-circuit
evaluation of Python's `cert_valid and cert_not_expired`.  The hostname and
SAN are (deliberately) never consulted. -/
def unsafeCertHostnameImp (requestedHost : String) (certSan : String)
    (certValid : Bool) (certNotExpired : Bool) : Bool := Id.run do
  let mut accepted : Bool := false
  -- Python: `cert_valid and cert_not_expired` (short-circuit)
  if certValid then
    if certNotExpired then
      accepted := true
  -- `requestedHost` / `certSan` are never compared: hostname never checked!
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
#eval check unsafeCertHostnameImp  -- true

-- Randomized PBT: imperative agrees with functional.
#eval Plausible.Testable.check
  (∀ (h s : String) (v e : Bool), unsafeCertHostnameImp h s v e = unsafeCertHostname h s v e)

example :
    (testHosts.all fun h => testHosts.all fun s =>
      [true, false].all fun v => [true, false].all fun e =>
        unsafeCertHostnameImp h s v e == unsafeCertHostname h s v e) = true := by
  native_decide

/-! ## Equivalence theorem -/

theorem imp_eq_fun_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    unsafeCertHostnameImp requestedHost certSan certValid certNotExpired =
      unsafeCertHostname requestedHost certSan certValid certNotExpired := by
  cases certValid <;> cases certNotExpired <;> rfl

/-- The imperative implementation therefore also satisfies the post-condition. -/
theorem imp_correctness_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    Pre requestedHost certSan certValid certNotExpired →
    unsafeCertHostnameImp requestedHost certSan certValid certNotExpired =
      (certValid && certNotExpired) := by
  intro _
  rw [imp_eq_fun_thm]
  exact result_is_conj_thm requestedHost certSan certValid certNotExpired

end «75_unsafeCertHostname»

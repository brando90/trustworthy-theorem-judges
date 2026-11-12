import Mathlib

/-!
# 75 — Unsafe Certificate Hostname Validation

Formalization of the Python program

```python
def unsafe_cert_hostname(requested_host: str, cert_san: str,
                          cert_valid: bool, cert_not_expired: bool) -> bool:
    return cert_valid and cert_not_expired  # Hostname never checked!
```

The function validates a certificate's signature and expiry but never checks
whether the certificate's Subject Alternative Name (SAN) or Common Name (CN)
matches the requested hostname (RFC 6125 hostname verification is skipped).
This enables MITM attacks: a client connecting to `bank.com` accepts a valid
certificate issued for `evil.com`.

The formalization below models the (vulnerable) behavior faithfully: the
result depends *only* on the two Boolean certificate flags and is independent
of the hostname and SAN strings.
-/

namespace «75_unsafeCertHostname»

/-- **Functional implementation** of `unsafe_cert_hostname`.

The hostname (`requested_host`) and the certificate SAN (`cert_san`) are
accepted but deliberately ignored — this is the vulnerability. -/
def unsafeCertHostname (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool :=
  cert_valid && cert_not_expired

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1) Normal operation — exact hostname match accepted
example : unsafeCertHostname "bank.com" "bank.com" true true = true := by native_decide

-- 2) Vulnerability: hostname mismatch accepted (MITM attack succeeds)
example : unsafeCertHostname "bank.com" "evil.com" true true = true := by native_decide
example : unsafeCertHostname "secure.example.com" "attacker.com" true true = true := by native_decide

-- 3) Still rejects invalid / expired certificates
example : unsafeCertHostname "bank.com" "bank.com" false true = false := by native_decide
example : unsafeCertHostname "bank.com" "bank.com" true false = false := by native_decide

-- 4) Edge cases
example : unsafeCertHostname "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafeCertHostname "" "evil.com" true true = true := by native_decide
example : unsafeCertHostname "bank.com" "bank.com" false false = false := by native_decide

#eval unsafeCertHostname "bank.com" "bank.com" true true    -- true
#eval unsafeCertHostname "bank.com" "evil.com" true true    -- true (vulnerability)
#eval unsafeCertHostname "bank.com" "bank.com" false true   -- false
#eval unsafeCertHostname "bank.com" "bank.com" true false   -- false

/-- **Pre-condition.** The Python function is total: every combination of a
requested host, a certificate SAN string and the two certificate flags is
admissible. -/
def Pre (requested_host cert_san : String) (cert_valid cert_not_expired : Bool) : Prop :=
  True

/-- **Property 1 — exact behavior.** The result equals the Boolean conjunction
of the two certificate-validity flags; hostname and SAN are never consulted. -/
def unsafeCertHostname_prop : Prop :=
  ∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
    unsafeCertHostname requested_host cert_san cert_valid cert_not_expired =
      (cert_valid && cert_not_expired)

theorem unsafeCertHostname_thm : unsafeCertHostname_prop := by
  intro requested_host cert_san cert_valid cert_not_expired
  rfl

/-- **Property 2 — the vulnerability.** A certificate is accepted whenever it
is valid and unexpired, even when the SAN does **not** match the requested
hostname (a MITM attacker with a valid cert for `evil.com` succeeds). -/
def hostnameMismatchAccepted_prop : Prop :=
  ∀ (requested_host cert_san : String),
    requested_host ≠ cert_san →
    unsafeCertHostname requested_host cert_san true true = true

theorem hostnameMismatchAccepted_thm : hostnameMismatchAccepted_prop := by
  intro requested_host cert_san _mismatch
  rfl

/-- **Property 3 — invalid/expired certs are rejected.** If the certificate
fails signature validation or is expired, the function returns `false`
(regardless of hostnames). -/
def invalidCertRejected_prop : Prop :=
  ∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
    (cert_valid = false ∨ cert_not_expired = false) →
    unsafeCertHostname requested_host cert_san cert_valid cert_not_expired = false

theorem invalidCertRejected_thm : invalidCertRejected_prop := by
  intro requested_host cert_san cert_valid cert_not_expired h
  cases cert_valid <;> cases cert_not_expired <;> simp_all [unsafeCertHostname]

/-- **Post-condition:** conjunction of all stated properties. -/
def Post_prop : Prop :=
  unsafeCertHostname_prop ∧ hostnameMismatchAccepted_prop ∧ invalidCertRejected_prop

theorem Post_thm : Post_prop :=
  ⟨unsafeCertHostname_thm, hostnameMismatchAccepted_thm, invalidCertRejected_thm⟩

/-! ## Property-based tests -/

-- PBT (bounded, exhaustive over Bool inputs) for `unsafeCertHostname_prop`.
example : [false, true].all (fun v => [false, true].all (fun e =>
    unsafeCertHostname "bank.com" "evil.com" v e == (v && e))) = true := by native_decide

-- PBT (randomized) for `unsafeCertHostname_prop` over arbitrary Bool flags,
-- with arbitrary host/SAN strings encoded from Nat samples.
#eval Plausible.Testable.check (∀ n m v e : Nat,
  unsafeCertHostname (toString n) (toString m) (v % 2 == 1) (e % 2 == 1) =
    ((v % 2 == 1) && (e % 2 == 1)))

-- PBT (bounded) for `hostnameMismatchAccepted_prop`: mismatching pairs are accepted.
example : ["bank.com", "secure.example.com", ""].all (fun h =>
    ["evil.com", "attacker.com", "*.evil.com"].all (fun s =>
      !(h == s) || (unsafeCertHostname h s true true == true))) = true := by native_decide

-- PBT (randomized) for `hostnameMismatchAccepted_prop` restricted to
-- admissible (distinct) inputs via a decidable implication.
#eval Plausible.Testable.check (∀ n m : Nat,
  toString n ≠ toString m → unsafeCertHostname (toString n) (toString m) true true = true)

-- Constructive variant of the above: the two hostnames are distinct by
-- construction, so the precondition is always fulfilled (no 'Gave up').
#eval Plausible.Testable.check (∀ n m : Nat,
  unsafeCertHostname (toString n) (toString (n + m + 1)) true true = true)

-- PBT (bounded, exhaustive) for `invalidCertRejected_prop`.
example : [false, true].all (fun v => [false, true].all (fun e =>
    !((v == false) || (e == false)) ||
      (unsafeCertHostname "bank.com" "bank.com" v e == false))) = true := by native_decide

-- PBT (bounded) for the executable form of `Post_prop`: all three properties
-- hold simultaneously on the test grid.
example : [false, true].all (fun v => [false, true].all (fun e =>
    (unsafeCertHostname "bank.com" "evil.com" v e == (v && e)) &&
    (unsafeCertHostname "bank.com" "evil.com" true true == true) &&
    (!((v == false) || (e == false)) ||
      (unsafeCertHostname "bank.com" "evil.com" v e == false)))) = true := by native_decide

/-- **Correctness theorem:** under the (trivial) pre-condition, the
post-condition — the conjunction of all properties — holds. -/
theorem correctness :
    ∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
      Pre requested_host cert_san cert_valid cert_not_expired → Post_prop := by
  intro _ _ _ _ _
  exact Post_thm

/-- **Imperative implementation** using `Id.run` with mutable state. -/
def unsafeCertHostnameImp (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Bool := Id.run do
  let mut result : Bool := cert_valid
  result := result && cert_not_expired
  return result

/-! ## Imperative tests -/

example : unsafeCertHostnameImp "bank.com" "bank.com" true true = true := by native_decide
example : unsafeCertHostnameImp "bank.com" "evil.com" true true = true := by native_decide
example : unsafeCertHostnameImp "secure.example.com" "attacker.com" true true = true := by native_decide
example : unsafeCertHostnameImp "bank.com" "bank.com" false true = false := by native_decide
example : unsafeCertHostnameImp "bank.com" "bank.com" true false = false := by native_decide
example : unsafeCertHostnameImp "bank.com" "bank.com" false false = false := by native_decide

#eval unsafeCertHostnameImp "bank.com" "evil.com" true true  -- true (vulnerability)

/-- **Equivalence theorem:** the functional and imperative implementations
agree on every input. -/
theorem functional_eq_imperative :
    ∀ (requested_host cert_san : String) (cert_valid cert_not_expired : Bool),
      unsafeCertHostname requested_host cert_san cert_valid cert_not_expired =
        unsafeCertHostnameImp requested_host cert_san cert_valid cert_not_expired := by
  intro requested_host cert_san cert_valid cert_not_expired
  rfl

end «75_unsafeCertHostname»

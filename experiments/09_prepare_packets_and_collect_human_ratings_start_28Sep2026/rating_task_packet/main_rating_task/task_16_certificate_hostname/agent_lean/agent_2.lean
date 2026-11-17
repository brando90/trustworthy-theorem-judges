import Mathlib

/-!
# Unsafe Certificate Hostname Validation (`75_unsafeCertHostname`)

This module formalizes in Lean 4 the Python function `unsafe_cert_hostname`,
which models an unsafe certificate validation routine that checks whether a
certificate has a valid signature (`cert_valid`) and is not expired
(`cert_not_expired`), while completely ignoring the requested hostname
(`requested_host`) and the certificate's Subject Alternative Name (`cert_san`).

Vulnerability modeled (MIT 6.858 Lecture 15 / RFC 6125):
A client connects to `bank.com` and the server presents a valid, non-expired
certificate issued for `evil.com`. Because `unsafe_cert_hostname` never verifies
that `requested_host` matches `cert_san`, it accepts the certificate and allows
a man-in-the-middle (MITM) attack.
-/

namespace «75_unsafeCertHostname»

/-! ## 1. Functional Implementation -/

set_option linter.unusedVariables false in
/-- Returns `true` if the certificate is valid and not expired, ignoring
`requested_host` and `cert_san` (hostname is never checked). -/
def unsafe_cert_hostname (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Bool :=
  cert_valid && cert_not_expired

/-- CamelCase alias for `unsafe_cert_hostname`. -/
abbrev unsafeCertHostname := unsafe_cert_hostname

/-- Executable test harness mirroring the Python `check(candidate)` function. -/
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

-- Full check suite
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

/-- Pre-condition for `unsafe_cert_hostname`: all `String` and `Bool` inputs are admissible. -/
def Pre (_requested_host _cert_san : String) (_cert_valid _cert_not_expired : Bool) : Prop :=
  True

/-! ## 4. Properties and Theorems -/

/-- Exact specification: the output equals `cert_valid && cert_not_expired`. -/
def exact_spec_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
    (cert_valid && cert_not_expired)

theorem exact_spec_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    exact_spec_prop requested_host cert_san cert_valid cert_not_expired := by
  rfl

/-- Logical characterization of acceptance: returns `true` iff both `cert_valid`
and `cert_not_expired` are `true`. -/
def accepts_iff_valid_and_not_expired_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true ↔
    (cert_valid = true ∧ cert_not_expired = true)

theorem accepts_iff_valid_and_not_expired_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    accepts_iff_valid_and_not_expired_prop requested_host cert_san cert_valid cert_not_expired := by
  simp [accepts_iff_valid_and_not_expired_prop, unsafe_cert_hostname]

/-- Logical characterization of rejection: returns `false` iff the certificate
is invalid or expired. -/
def rejects_iff_invalid_or_expired_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false ↔
    (cert_valid = false ∨ cert_not_expired = false)

theorem rejects_iff_invalid_or_expired_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    rejects_iff_invalid_or_expired_prop requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;>
    simp [rejects_iff_invalid_or_expired_prop, unsafe_cert_hostname]

/-- Normal operation: a valid, non-expired certificate with matching hostname is accepted. -/
def accepts_valid_matching_host_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  requested_host = cert_san →
  cert_valid = true →
  cert_not_expired = true →
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem accepts_valid_matching_host_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    accepts_valid_matching_host_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _ h_valid h_not_expired
  simp [unsafe_cert_hostname, h_valid, h_not_expired]

/-- MITM vulnerability: even when `requested_host ≠ cert_san`, a valid and
non-expired certificate is still accepted. -/
def mitm_mismatch_accepted_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  requested_host ≠ cert_san →
  cert_valid = true →
  cert_not_expired = true →
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem mitm_mismatch_accepted_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    mitm_mismatch_accepted_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _ h_valid h_not_expired
  simp [unsafe_cert_hostname, h_valid, h_not_expired]

/-- Invalid certificates are always rejected regardless of hostnames or expiry. -/
def rejects_invalid_cert_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  cert_valid = false →
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false

theorem rejects_invalid_cert_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    rejects_invalid_cert_prop requested_host cert_san cert_valid cert_not_expired := by
  intro h_invalid
  simp [unsafe_cert_hostname, h_invalid]

/-- Expired certificates are always rejected regardless of hostnames or signature validity. -/
def rejects_expired_cert_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  cert_not_expired = false →
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = false

theorem rejects_expired_cert_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    rejects_expired_cert_prop requested_host cert_san cert_valid cert_not_expired := by
  intro h_expired
  simp [unsafe_cert_hostname, h_expired]

/-- Edge case: an empty requested hostname `""` is accepted whenever the certificate
is valid and not expired. -/
def accepts_empty_hostname_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  requested_host = "" →
  cert_valid = true →
  cert_not_expired = true →
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired = true

theorem accepts_empty_hostname_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    accepts_empty_hostname_prop requested_host cert_san cert_valid cert_not_expired := by
  intro _ h_valid h_not_expired
  simp [unsafe_cert_hostname, h_valid, h_not_expired]

/-- Hostname invariance across arbitrary hostname pairs: changing `requested_host`
and `cert_san` never changes the validation result. -/
def ignores_hostnames_prop (requested_host cert_san other_host other_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
    unsafe_cert_hostname other_host other_san cert_valid cert_not_expired

theorem ignores_hostnames_thm (requested_host cert_san other_host other_san : String)
    (cert_valid cert_not_expired : Bool) :
    ignores_hostnames_prop requested_host cert_san other_host other_san cert_valid cert_not_expired := by
  rfl

/-- Hostname independence relative to empty strings: the result for any
`(requested_host, cert_san)` is identical to the result for `("", "")`. -/
def hostname_independent_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
    unsafe_cert_hostname "" "" cert_valid cert_not_expired

theorem hostname_independent_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    hostname_independent_prop requested_host cert_san cert_valid cert_not_expired := by
  rfl

/-- Swapping `requested_host` and `cert_san` does not affect the outcome. -/
def hostname_swap_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
    unsafe_cert_hostname cert_san requested_host cert_valid cert_not_expired

theorem hostname_swap_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    hostname_swap_prop requested_host cert_san cert_valid cert_not_expired := by
  rfl

/-- Commutativity in the boolean flags `cert_valid` and `cert_not_expired`. -/
def validity_comm_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
    unsafe_cert_hostname requested_host cert_san cert_not_expired cert_valid

theorem validity_comm_thm (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    validity_comm_prop requested_host cert_san cert_valid cert_not_expired := by
  unfold validity_comm_prop unsafe_cert_hostname
  exact Bool.and_comm cert_valid cert_not_expired

/-! ## 5. Post-condition -/

/-- Post-condition combining all single-call behavioral properties of `unsafe_cert_hostname`. -/
def Post_prop (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) : Prop :=
  exact_spec_prop requested_host cert_san cert_valid cert_not_expired ∧
  accepts_iff_valid_and_not_expired_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejects_iff_invalid_or_expired_prop requested_host cert_san cert_valid cert_not_expired ∧
  accepts_valid_matching_host_prop requested_host cert_san cert_valid cert_not_expired ∧
  mitm_mismatch_accepted_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejects_invalid_cert_prop requested_host cert_san cert_valid cert_not_expired ∧
  rejects_expired_cert_prop requested_host cert_san cert_valid cert_not_expired ∧
  accepts_empty_hostname_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_independent_prop requested_host cert_san cert_valid cert_not_expired ∧
  hostname_swap_prop requested_host cert_san cert_valid cert_not_expired ∧
  validity_comm_prop requested_host cert_san cert_valid cert_not_expired

/-! ## 6. Property-Based Tests (PBTs) -/

-- Randomized PBTs via Plausible for each property
-- 1. exact_spec_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafe_cert_hostname h s v e = (v && e))

-- 2. accepts_iff_valid_and_not_expired_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (unsafe_cert_hostname h s v e = true) ↔ (v = true ∧ e = true))

-- 3. rejects_iff_invalid_or_expired_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (unsafe_cert_hostname h s v e = false) ↔ (v = false ∨ e = false))

-- 4. accepts_valid_matching_host_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (!(h == s && v && e) || unsafe_cert_hostname h s v e) = true)

#eval Plausible.Testable.check (∀ (h : String),
  unsafe_cert_hostname h h true true = true)

-- 5. mitm_mismatch_accepted_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (!(h != s && v && e) || unsafe_cert_hostname h s v e) = true)

-- 6. rejects_invalid_cert_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (v || !unsafe_cert_hostname h s v e) = true)

#eval Plausible.Testable.check (∀ (h s : String) (e : Bool),
  unsafe_cert_hostname h s false e = false)

-- 7. rejects_expired_cert_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (e || !unsafe_cert_hostname h s v e) = true)

#eval Plausible.Testable.check (∀ (h s : String) (v : Bool),
  unsafe_cert_hostname h s v false = false)

-- 8. accepts_empty_hostname_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (!(h == "" && v && e) || unsafe_cert_hostname h s v e) = true)

#eval Plausible.Testable.check (∀ (s : String),
  unsafe_cert_hostname "" s true true = true)

-- 9. ignores_hostnames_prop
#eval Plausible.Testable.check (∀ (h1 s1 h2 s2 : String) (v e : Bool),
  unsafe_cert_hostname h1 s1 v e = unsafe_cert_hostname h2 s2 v e)

-- 10. hostname_independent_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafe_cert_hostname h s v e = unsafe_cert_hostname "" "" v e)

-- 11. hostname_swap_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafe_cert_hostname h s v e = unsafe_cert_hostname s h v e)

-- 12. validity_comm_prop
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  unsafe_cert_hostname h s v e = unsafe_cert_hostname h s e v)

-- 13. Post_prop (conjunction of all properties)
#eval Plausible.Testable.check (∀ (h s : String) (v e : Bool),
  (unsafe_cert_hostname h s v e == (v && e)) = true ∧
  ((unsafe_cert_hostname h s v e == true) == (v && e)) = true ∧
  ((unsafe_cert_hostname h s v e == false) == (!v || !e)) = true ∧
  (!(h == s && v && e) || unsafe_cert_hostname h s v e) = true ∧
  (!(h != s && v && e) || unsafe_cert_hostname h s v e) = true ∧
  (v || !unsafe_cert_hostname h s v e) = true ∧
  (e || !unsafe_cert_hostname h s v e) = true ∧
  (!(h == "" && v && e) || unsafe_cert_hostname h s v e) = true ∧
  (unsafe_cert_hostname h s v e == unsafe_cert_hostname "" "" v e) = true ∧
  (unsafe_cert_hostname h s v e == unsafe_cert_hostname s h v e) = true ∧
  (unsafe_cert_hostname h s v e == unsafe_cert_hostname h s e v) = true)

-- Bounded exhaustive PBTs over a corpus of hostnames and all Boolean combinations
def sampleHosts : List String :=
  ["bank.com", "evil.com", "secure.example.com", "attacker.com", "*.evil.com", "", "localhost"]

def sampleBools : List Bool := [false, true]

example : (sampleHosts.all fun h =>
  sampleHosts.all fun s =>
  sampleBools.all fun v =>
  sampleBools.all fun e =>
    (unsafe_cert_hostname h s v e == (v && e)) &&
    ((unsafe_cert_hostname h s v e == true) == (v && e)) &&
    ((unsafe_cert_hostname h s v e == false) == (!v || !e)) &&
    (!(h == s && v && e) || unsafe_cert_hostname h s v e) &&
    (!(h != s && v && e) || unsafe_cert_hostname h s v e) &&
    (v || !unsafe_cert_hostname h s v e) &&
    (e || !unsafe_cert_hostname h s v e) &&
    (!(h == "" && v && e) || unsafe_cert_hostname h s v e) &&
    (unsafe_cert_hostname h s v e == unsafe_cert_hostname "" "" v e) &&
    (unsafe_cert_hostname h s v e == unsafe_cert_hostname s h v e) &&
    (unsafe_cert_hostname h s v e == unsafe_cert_hostname h s e v)) = true := by native_decide

example : (sampleHosts.all fun h1 =>
  sampleHosts.all fun s1 =>
  sampleHosts.all fun h2 =>
  sampleHosts.all fun s2 =>
  sampleBools.all fun v =>
  sampleBools.all fun e =>
    unsafe_cert_hostname h1 s1 v e == unsafe_cert_hostname h2 s2 v e) = true := by native_decide

/-! ## 7. Correctness Theorem (`Pre → Post`) -/

/-- Full correctness theorem: under `Pre`, `unsafe_cert_hostname` satisfies `Post_prop`. -/
theorem unsafe_cert_hostname_correct (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool)
    (_h_pre : Pre requested_host cert_san cert_valid cert_not_expired) :
    Post_prop requested_host cert_san cert_valid cert_not_expired := by
  refine ⟨
    exact_spec_thm requested_host cert_san cert_valid cert_not_expired,
    accepts_iff_valid_and_not_expired_thm requested_host cert_san cert_valid cert_not_expired,
    rejects_iff_invalid_or_expired_thm requested_host cert_san cert_valid cert_not_expired,
    accepts_valid_matching_host_thm requested_host cert_san cert_valid cert_not_expired,
    mitm_mismatch_accepted_thm requested_host cert_san cert_valid cert_not_expired,
    rejects_invalid_cert_thm requested_host cert_san cert_valid cert_not_expired,
    rejects_expired_cert_thm requested_host cert_san cert_valid cert_not_expired,
    accepts_empty_hostname_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_independent_thm requested_host cert_san cert_valid cert_not_expired,
    hostname_swap_thm requested_host cert_san cert_valid cert_not_expired,
    validity_comm_thm requested_host cert_san cert_valid cert_not_expired
  ⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `unsafe_cert_hostname` using `Id.run do` and mutable state. -/
def unsafe_cert_hostname_imp (requested_host : String) (cert_san : String)
    (cert_valid : Bool) (cert_not_expired : Bool) : Bool := Id.run do
  let _ := requested_host
  let _ := cert_san
  let mut accepted : Bool := false
  if cert_valid then
    if cert_not_expired then
      accepted := true
  return accepted

/-- CamelCase alias for `unsafe_cert_hostname_imp`. -/
abbrev unsafeCertHostnameImp := unsafe_cert_hostname_imp

/-! ## 9. Imperative Tests -/

example : unsafe_cert_hostname_imp "bank.com" "bank.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "evil.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "secure.example.com" "attacker.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "bank.com" false true = false := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "bank.com" true false = false := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "*.evil.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "" "evil.com" true true = true := by native_decide
example : unsafe_cert_hostname_imp "bank.com" "bank.com" false false = false := by native_decide
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

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

/-- Pointwise equivalence between the functional and imperative implementations. -/
theorem unsafe_cert_hostname_equiv (requested_host cert_san : String)
    (cert_valid cert_not_expired : Bool) :
    unsafe_cert_hostname requested_host cert_san cert_valid cert_not_expired =
      unsafe_cert_hostname_imp requested_host cert_san cert_valid cert_not_expired := by
  cases cert_valid <;> cases cert_not_expired <;> rfl

/-- Function-level equivalence between `unsafe_cert_hostname` and `unsafe_cert_hostname_imp`. -/
theorem unsafe_cert_hostname_funext :
    unsafe_cert_hostname = unsafe_cert_hostname_imp := by
  funext requested_host cert_san cert_valid cert_not_expired
  exact unsafe_cert_hostname_equiv requested_host cert_san cert_valid cert_not_expired

end «75_unsafeCertHostname»

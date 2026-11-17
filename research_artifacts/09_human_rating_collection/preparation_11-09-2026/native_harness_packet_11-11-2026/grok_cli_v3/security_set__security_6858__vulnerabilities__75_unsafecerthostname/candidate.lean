import Mathlib

/-!
# Unsafe certificate hostname validation

Formalization of an unsafe TLS hostname check. The Python function

`unsafe_cert_hostname(requested_host, cert_san, cert_valid, cert_not_expired)`

returns `cert_valid and cert_not_expired` and never compares `requested_host`
with the certificate Subject Alternative Name (or Common Name).

A client that asks for `bank.com` therefore accepts a valid, unexpired
certificate issued to `evil.com`. That is a man-in-the-middle hole even when
the signature and expiry checks succeed. RFC 6125 requires the hostname
comparison this function omits (MIT 6.858, Lecture 15).

This file models that unsafe behavior. It does not repair it.
-/

namespace «75_unsafeCertHostname»

/-! ## Implementation -/

/-- Unsafe certificate check.

Returns `true` exactly when the certificate is valid and not expired.
`requestedHost` and `certSan` are in scope and are ignored, which is the bug. -/
def unsafeCertHostname (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Bool :=
  -- Bind both host strings so the signature matches the Python function,
  -- then drop them. The decision never reads them.
  let _ignoredHost := requestedHost
  let _ignoredSan := certSan
  certValid && certNotExpired

/-- Exact-match checker that performs the comparison the unsafe function omits.

The Python tests treat byte-for-byte equality of the requested host and the
single SAN string as a hostname match (`"bank.com"` / `"bank.com"`) and treat
every other pair, including wildcard SANs such as `"*.evil.com"`, as a
mismatch. This helper is the omitted conjunct; it is not the program under
translation. -/
def safeCertHostname (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Bool :=
  certValid && certNotExpired && (requestedHost == certSan)

/-- Python `check`: the candidate must reproduce the unsafe test suite. -/
def check (candidate : String → String → Bool → Bool → Bool) : Bool :=
  (candidate "bank.com" "bank.com" true true == true) &&
  (candidate "bank.com" "evil.com" true true == true) &&
  (candidate "secure.example.com" "attacker.com" true true == true) &&
  (candidate "bank.com" "bank.com" false true == false) &&
  (candidate "bank.com" "bank.com" true false == false) &&
  (candidate "bank.com" "*.evil.com" true true == true) &&
  (candidate "" "evil.com" true true == true) &&
  (candidate "bank.com" "bank.com" false false == false)

/-! ## Unit tests -/

-- 1) Normal operation: exact hostname match, valid and unexpired.
example : unsafeCertHostname "bank.com" "bank.com" true true = true := by
  native_decide

-- 2) Vulnerability: hostname mismatch is accepted (MITM succeeds).
example : unsafeCertHostname "bank.com" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "secure.example.com" "attacker.com" true true = true := by
  native_decide

-- 3) Invalid or expired certificates are still rejected.
example : unsafeCertHostname "bank.com" "bank.com" false true = false := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" true false = false := by
  native_decide

-- 4) Edge cases: wildcard SAN mismatch, empty host, both flags false.
example : unsafeCertHostname "bank.com" "*.evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "" "evil.com" true true = true := by
  native_decide

example : unsafeCertHostname "bank.com" "bank.com" false false = false := by
  native_decide

example : check unsafeCertHostname = true := by
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

/-! ## Pre-condition -/

/-- Every Python call is legal. Host strings are not validated, and both
certificate flags may be either Boolean. The domain is not restricted. -/
def Pre (_requestedHost _certSan : String) (_certValid _certNotExpired : Bool) : Prop :=
  True

/-- `Pre` holds for every input the Python function accepts. -/
theorem pre_total_thm (requestedHost certSan : String)
    (certValid certNotExpired : Bool) :
    Pre requestedHost certSan certValid certNotExpired := trivial

/-! ## Properties -/

/-- The decision is exactly the conjunction of the two certificate flags. -/
def result_eq_valid_and_fresh_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    (certValid && certNotExpired)

theorem result_eq_valid_and_fresh_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    result_eq_valid_and_fresh_prop requestedHost certSan certValid certNotExpired := by
  simp [result_eq_valid_and_fresh_prop, unsafeCertHostname]

/-- Changing either host string does not change the result. -/
def hostname_independent_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  ∀ requestedHost' certSan' : String,
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname requestedHost' certSan' certValid certNotExpired

theorem hostname_independent_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    hostname_independent_prop requestedHost certSan certValid certNotExpired := by
  intro _ _
  simp [unsafeCertHostname]

/-- Acceptance holds if and only if the certificate is valid and unexpired. -/
def accepts_iff_valid_and_fresh_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
    certValid = true ∧ certNotExpired = true

theorem accepts_iff_valid_and_fresh_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    accepts_iff_valid_and_fresh_prop requestedHost certSan certValid certNotExpired := by
  simp [accepts_iff_valid_and_fresh_prop, unsafeCertHostname, Bool.and_eq_true]

/-- A valid, unexpired certificate is accepted for every host pair. -/
def accepts_valid_fresh_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem accepts_valid_fresh_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    accepts_valid_fresh_prop requestedHost certSan certValid certNotExpired := by
  intro hv he
  simp [unsafeCertHostname, hv, he]

/-- An invalid certificate is rejected, whatever the hostname and expiry are. -/
def rejects_invalid_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem rejects_invalid_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    rejects_invalid_prop requestedHost certSan certValid certNotExpired := by
  intro hv
  simp [unsafeCertHostname, hv]

/-- An expired certificate is rejected, whatever the hostname and validity are. -/
def rejects_expired_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certNotExpired = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem rejects_expired_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    rejects_expired_prop requestedHost certSan certValid certNotExpired := by
  intro he
  simp [unsafeCertHostname, he]

/-- Both flags false is rejected (Python edge case). -/
def rejects_both_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = false → certNotExpired = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem rejects_both_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    rejects_both_prop requestedHost certSan certValid certNotExpired := by
  intro hv he
  simp [unsafeCertHostname, hv, he]

/-- Any failure of validity or expiry rejects the certificate. -/
def rejects_invalid_or_expired_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = false ∨ certNotExpired = false →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = false

theorem rejects_invalid_or_expired_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    rejects_invalid_or_expired_prop requestedHost certSan certValid certNotExpired := by
  intro h
  cases h with
  | inl hv => simp [unsafeCertHostname, hv]
  | inr he => simp [unsafeCertHostname, he]

/-- MITM: a SAN that differs from the requested host is still accepted when
the certificate is valid and unexpired. -/
def mismatch_accepted_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = true → certNotExpired = true → requestedHost ≠ certSan →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem mismatch_accepted_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    mismatch_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro hv he _
  simp [unsafeCertHostname, hv, he]

/-- Exact host/SAN match is accepted when the certificate is valid and fresh.
The unsafe checker does not break the matching case; it also accepts the rest. -/
def exact_match_accepted_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = true → certNotExpired = true → requestedHost = certSan →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem exact_match_accepted_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    exact_match_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro hv he _
  simp [unsafeCertHostname, hv, he]

/-- The empty requested host is accepted when the certificate is valid and fresh. -/
def empty_host_accepted_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  requestedHost = "" → certValid = true → certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem empty_host_accepted_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    empty_host_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro _ hv he
  simp [unsafeCertHostname, hv, he]

/-- A wildcard SAN is not matched. The certificate is accepted even when the
requested host fails the naive suffix check for a `*.suffix` pattern
(`"*.evil.com"` covers names ending in `".evil.com"`). `drop 1` strips the
leading `*`. -/
def wildcard_mismatch_accepted_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certSan.startsWith "*." = true →
    certValid = true →
      certNotExpired = true →
        requestedHost.endsWith (certSan.drop 1) = false →
          unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem wildcard_mismatch_accepted_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    wildcard_mismatch_accepted_prop requestedHost certSan certValid certNotExpired := by
  intro _ hv he _
  simp [unsafeCertHostname, hv, he]

/-- Whenever the exact-match checker accepts, the unsafe checker accepts too.
The unsafe checker is a weaker predicate. -/
def weaker_than_safe_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  safeCertHostname requestedHost certSan certValid certNotExpired = true →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true

theorem weaker_than_safe_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    weaker_than_safe_prop requestedHost certSan certValid certNotExpired := by
  intro hs
  cases certValid <;> cases certNotExpired <;>
    simp_all [safeCertHostname, unsafeCertHostname]

/-- On a hostname mismatch the unsafe checker accepts a valid fresh certificate
and the exact-match checker rejects it. -/
def differs_from_safe_on_mismatch_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  certValid = true → certNotExpired = true → requestedHost ≠ certSan →
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true ∧
      safeCertHostname requestedHost certSan certValid certNotExpired = false

theorem differs_from_safe_on_mismatch_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    differs_from_safe_on_mismatch_prop requestedHost certSan certValid certNotExpired := by
  intro hv he hne
  refine ⟨?_, ?_⟩
  · simp [unsafeCertHostname, hv, he]
  · have hb : (requestedHost == certSan) = false := beq_eq_false_iff_ne.mpr hne
    simp [safeCertHostname, hv, he, hb]

/-- The unsafe checker accepts an input the exact-match checker rejects
if and only if the certificate is valid and fresh and the host differs from the SAN. -/
def unsafe_accepts_extra_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  (unsafeCertHostname requestedHost certSan certValid certNotExpired = true ∧
      safeCertHostname requestedHost certSan certValid certNotExpired = false) ↔
    (certValid = true ∧ certNotExpired = true ∧ requestedHost ≠ certSan)

theorem unsafe_accepts_extra_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    unsafe_accepts_extra_prop requestedHost certSan certValid certNotExpired := by
  constructor
  · intro ⟨hu, hs⟩
    simp [unsafeCertHostname, Bool.and_eq_true] at hu
    have hv : certValid = true := hu.1
    have he : certNotExpired = true := hu.2
    simp [safeCertHostname, hv, he] at hs
    exact ⟨hv, he, hs⟩
  · intro ⟨hv, he, hne⟩
    constructor
    · simp [unsafeCertHostname, hv, he]
    · have hb : (requestedHost == certSan) = false := beq_eq_false_iff_ne.mpr hne
      simp [safeCertHostname, hv, he, hb]

/-- Concrete MITM witness from the Python tests: `bank.com` accepts `evil.com`. -/
def mitm_witness_prop : Prop :=
  ∃ requestedHost certSan : String,
    requestedHost ≠ certSan ∧
      unsafeCertHostname requestedHost certSan true true = true ∧
        safeCertHostname requestedHost certSan true true = false

theorem mitm_witness_thm : mitm_witness_prop := by
  refine ⟨"bank.com", "evil.com", ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- The original Python asserts all succeed on `unsafeCertHostname`. -/
def check_passes_prop : Prop :=
  check unsafeCertHostname = true

theorem check_passes_thm : check_passes_prop := by
  unfold check_passes_prop
  decide

/-! ## Post-condition -/

/-- The unsafe checker ignores hostnames, accepts exactly the valid unexpired
certificates, and therefore accepts MITM mismatches that an exact SAN check
would reject. Invalid and expired certificates are still rejected. -/
def Post_prop (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  result_eq_valid_and_fresh_prop requestedHost certSan certValid certNotExpired ∧
    hostname_independent_prop requestedHost certSan certValid certNotExpired ∧
      accepts_iff_valid_and_fresh_prop requestedHost certSan certValid certNotExpired ∧
        accepts_valid_fresh_prop requestedHost certSan certValid certNotExpired ∧
          rejects_invalid_prop requestedHost certSan certValid certNotExpired ∧
            rejects_expired_prop requestedHost certSan certValid certNotExpired ∧
              rejects_both_prop requestedHost certSan certValid certNotExpired ∧
                rejects_invalid_or_expired_prop requestedHost certSan certValid certNotExpired ∧
                  mismatch_accepted_prop requestedHost certSan certValid certNotExpired ∧
                    exact_match_accepted_prop requestedHost certSan certValid certNotExpired ∧
                      empty_host_accepted_prop requestedHost certSan certValid certNotExpired ∧
                        wildcard_mismatch_accepted_prop requestedHost certSan certValid certNotExpired ∧
                          weaker_than_safe_prop requestedHost certSan certValid certNotExpired ∧
                            differs_from_safe_on_mismatch_prop requestedHost certSan certValid certNotExpired ∧
                              unsafe_accepts_extra_prop requestedHost certSan certValid certNotExpired ∧
                                mitm_witness_prop ∧
                                  check_passes_prop

/-! ## Property-based tests -/

/-- Hosts drawn from the Python tests, plus wildcard and suffix variants. -/
def pbtHosts : List String :=
  [ ""
  , "bank.com"
  , "evil.com"
  , "secure.example.com"
  , "attacker.com"
  , "*.evil.com"
  , "*.bank.com"
  , "www.evil.com"
  , "www.bank.com"
  , "a"
  , "b.com"
  ]

def pbtBools : List Bool := [false, true]

/-- Exhaustive check of a Boolean property on the finite host/flag grid. -/
def forAllInputs (p : String → String → Bool → Bool → Bool) : Bool :=
  pbtHosts.all fun h =>
    pbtHosts.all fun s =>
      pbtBools.all fun v =>
        pbtBools.all fun e =>
          p h s v e

-- PBT for result_eq_valid_and_fresh_prop
example : forAllInputs (fun h s v e =>
    unsafeCertHostname h s v e == (v && e)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      (certValid && certNotExpired))
  { randomSeed := some 1 }

-- PBT for hostname_independent_prop
example : pbtHosts.all (fun h1 => pbtHosts.all (fun s1 =>
    pbtHosts.all (fun h2 => pbtHosts.all (fun s2 =>
      pbtBools.all (fun v => pbtBools.all (fun e =>
        unsafeCertHostname h1 s1 v e == unsafeCertHostname h2 s2 v e)))))) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (h1 s1 h2 s2 : String) (v e : Bool),
    unsafeCertHostname h1 s1 v e = unsafeCertHostname h2 s2 v e)
  { randomSeed := some 1 }

-- PBT for accepts_iff_valid_and_fresh_prop
example : forAllInputs (fun h s v e =>
    ((unsafeCertHostname h s v e == true) == (v && e))) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired = true ↔
      certValid = true ∧ certNotExpired = true)
  { randomSeed := some 1 }

-- PBT for accepts_valid_fresh_prop
example : forAllInputs (fun h s v e =>
    !(v && e) || unsafeCertHostname h s v e) = true := by
  native_decide

-- PBT for rejects_invalid_prop
example : forAllInputs (fun h s v e =>
    v || !(unsafeCertHostname h s v e)) = true := by
  native_decide

-- PBT for rejects_expired_prop
example : forAllInputs (fun h s v e =>
    e || !(unsafeCertHostname h s v e)) = true := by
  native_decide

-- PBT for rejects_both_prop
example : forAllInputs (fun h s v e =>
    !(v == false && e == false) || (unsafeCertHostname h s v e == false)) = true := by
  native_decide

-- PBT for rejects_invalid_or_expired_prop
example : forAllInputs (fun h s v e =>
    !((v == false) || (e == false)) || (unsafeCertHostname h s v e == false)) = true := by
  native_decide

-- PBT for mismatch_accepted_prop
example : forAllInputs (fun h s v e =>
    !(v && e && (h != s)) || unsafeCertHostname h s v e) = true := by
  native_decide

-- PBT for exact_match_accepted_prop
example : forAllInputs (fun h s v e =>
    !(v && e && (h == s)) || unsafeCertHostname h s v e) = true := by
  native_decide

-- PBT for empty_host_accepted_prop
example : forAllInputs (fun h s v e =>
    !((h == "") && v && e) || unsafeCertHostname h s v e) = true := by
  native_decide

-- PBT for wildcard_mismatch_accepted_prop
example : forAllInputs (fun h s v e =>
    !(s.startsWith "*." && v && e && !(h.endsWith (s.drop 1))) ||
      unsafeCertHostname h s v e) = true := by
  native_decide

-- PBT for weaker_than_safe_prop
example : forAllInputs (fun h s v e =>
    !(safeCertHostname h s v e) || unsafeCertHostname h s v e) = true := by
  native_decide

-- PBT for differs_from_safe_on_mismatch_prop
example : forAllInputs (fun h s v e =>
    !(v && e && (h != s)) ||
      (unsafeCertHostname h s v e && !(safeCertHostname h s v e))) = true := by
  native_decide

-- PBT for unsafe_accepts_extra_prop
example : forAllInputs (fun h s v e =>
    let gap := unsafeCertHostname h s v e && !(safeCertHostname h s v e)
    let cond := v && e && (h != s)
    gap == cond) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    ((unsafeCertHostname requestedHost certSan certValid certNotExpired = true ∧
        safeCertHostname requestedHost certSan certValid certNotExpired = false) ↔
      (certValid = true ∧ certNotExpired = true ∧ requestedHost ≠ certSan)))
  { randomSeed := some 1 }

-- PBT for mitm_witness_prop: every listed mismatch is an attack witness.
def mitmPairs : List (String × String) :=
  [ ("bank.com", "evil.com")
  , ("secure.example.com", "attacker.com")
  , ("bank.com", "*.evil.com")
  , ("", "evil.com")
  , ("www.bank.com", "*.evil.com")
  ]

example : mitmPairs.all (fun p =>
    unsafeCertHostname p.1 p.2 true true &&
      (p.1 != p.2) &&
        !(safeCertHostname p.1 p.2 true true)) = true := by
  native_decide

-- PBT for check_passes_prop
example : check unsafeCertHostname = true := by
  native_decide

/-- Executable form of `Post_prop` on one input. The global witness and the
Python suite are included, and hostname independence is checked against a
fixed second pair (the full grid is the separate independence PBT). -/
def postBool (h s : String) (v e : Bool) : Bool :=
  (unsafeCertHostname h s v e == (v && e)) &&
    (unsafeCertHostname h s v e == unsafeCertHostname "bank.com" "evil.com" v e) &&
      ((unsafeCertHostname h s v e == true) == (v && e)) &&
        (!(v && e) || unsafeCertHostname h s v e) &&
          (v || !(unsafeCertHostname h s v e)) &&
            (e || !(unsafeCertHostname h s v e)) &&
              (!(v == false && e == false) || (unsafeCertHostname h s v e == false)) &&
                (!((v == false) || (e == false)) ||
                  (unsafeCertHostname h s v e == false)) &&
                  (!(v && e && (h != s)) || unsafeCertHostname h s v e) &&
                    (!(v && e && (h == s)) || unsafeCertHostname h s v e) &&
                      (!((h == "") && v && e) || unsafeCertHostname h s v e) &&
                        (!(s.startsWith "*." && v && e && !(h.endsWith (s.drop 1))) ||
                          unsafeCertHostname h s v e) &&
                          (!(safeCertHostname h s v e) || unsafeCertHostname h s v e) &&
                            (!(v && e && (h != s)) ||
                              (unsafeCertHostname h s v e && !(safeCertHostname h s v e))) &&
                              (let gap := unsafeCertHostname h s v e && !(safeCertHostname h s v e)
                               let cond := v && e && (h != s)
                               gap == cond) &&
                                (unsafeCertHostname "bank.com" "evil.com" true true &&
                                  ("bank.com" != "evil.com") &&
                                    !(safeCertHostname "bank.com" "evil.com" true true)) &&
                                  (check unsafeCertHostname)

-- PBT for Post_prop
example : forAllInputs postBool = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      (certValid && certNotExpired) ∧
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostname "bank.com" "evil.com" certValid certNotExpired)
  { randomSeed := some 1 }

/-! ## Correctness -/

theorem correctness_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool)
    (hPre : Pre requestedHost certSan certValid certNotExpired) :
    Post_prop requestedHost certSan certValid certNotExpired := by
  have _preOk : True := hPre
  exact ⟨
    result_eq_valid_and_fresh_thm requestedHost certSan certValid certNotExpired,
    hostname_independent_thm requestedHost certSan certValid certNotExpired,
    accepts_iff_valid_and_fresh_thm requestedHost certSan certValid certNotExpired,
    accepts_valid_fresh_thm requestedHost certSan certValid certNotExpired,
    rejects_invalid_thm requestedHost certSan certValid certNotExpired,
    rejects_expired_thm requestedHost certSan certValid certNotExpired,
    rejects_both_thm requestedHost certSan certValid certNotExpired,
    rejects_invalid_or_expired_thm requestedHost certSan certValid certNotExpired,
    mismatch_accepted_thm requestedHost certSan certValid certNotExpired,
    exact_match_accepted_thm requestedHost certSan certValid certNotExpired,
    empty_host_accepted_thm requestedHost certSan certValid certNotExpired,
    wildcard_mismatch_accepted_thm requestedHost certSan certValid certNotExpired,
    weaker_than_safe_thm requestedHost certSan certValid certNotExpired,
    differs_from_safe_on_mismatch_thm requestedHost certSan certValid certNotExpired,
    unsafe_accepts_extra_thm requestedHost certSan certValid certNotExpired,
    mitm_witness_thm,
    check_passes_thm⟩

/-! ## Imperative implementation -/

/-- Imperative counterpart. A mutable flag starts false and becomes true only
when both certificate checks succeed. The host strings are read into
`_mismatch` and then ignored, matching the Python control flow. -/
def unsafeCertHostnameImp (requestedHost certSan : String)
    (certValid certNotExpired : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := false
    let _mismatch := requestedHost != certSan
    if certValid then
      if certNotExpired then
        accepted := true
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

#eval unsafeCertHostnameImp "bank.com" "bank.com" true true
#eval unsafeCertHostnameImp "bank.com" "evil.com" true true
#eval unsafeCertHostnameImp "secure.example.com" "attacker.com" true true
#eval unsafeCertHostnameImp "bank.com" "bank.com" false true
#eval unsafeCertHostnameImp "bank.com" "bank.com" true false
#eval unsafeCertHostnameImp "bank.com" "*.evil.com" true true
#eval unsafeCertHostnameImp "" "evil.com" true true
#eval unsafeCertHostnameImp "bank.com" "bank.com" false false
#eval check unsafeCertHostnameImp

/-! ## Equivalence -/

/-- Functional and imperative checkers agree on every input. -/
def functional_eq_imperative_prop
    (requestedHost certSan : String) (certValid certNotExpired : Bool) : Prop :=
  unsafeCertHostname requestedHost certSan certValid certNotExpired =
    unsafeCertHostnameImp requestedHost certSan certValid certNotExpired

theorem functional_eq_imperative_thm
    (requestedHost certSan : String) (certValid certNotExpired : Bool) :
    functional_eq_imperative_prop requestedHost certSan certValid certNotExpired := by
  cases certValid <;> cases certNotExpired <;> rfl

-- PBT for functional_eq_imperative_prop
example : forAllInputs (fun h s v e =>
    unsafeCertHostname h s v e == unsafeCertHostnameImp h s v e) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ (requestedHost certSan : String) (certValid certNotExpired : Bool),
    unsafeCertHostname requestedHost certSan certValid certNotExpired =
      unsafeCertHostnameImp requestedHost certSan certValid certNotExpired)
  { randomSeed := some 1 }

end «75_unsafeCertHostname»

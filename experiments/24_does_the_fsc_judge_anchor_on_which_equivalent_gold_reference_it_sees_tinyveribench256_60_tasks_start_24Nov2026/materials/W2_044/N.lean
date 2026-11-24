import Mathlib
namespace Agent

/-!
# Host-key authentication instead of reverse-DNS authentication

Translation of the Python `safe_rlogin_reverse_dns` program. Python integers are
modelled by unbounded `Int`; hostnames and fingerprints are `String`s. The
presented fingerprint must be nonempty and exactly equal to the trusted one.
The IP address and both hostnames are deliberately ignored for authentication.

This models the supplied fingerprint comparison, not a cryptographic protocol:
it does not assume or prove that a fingerprint cannot be forged. In particular,
the spoofing theorem assumes the attacker presents a different fingerprint.
There are no input preconditions, including no requirement that the trusted key
be nonempty. Finite executable tests supplement, but do not replace, the
universal kernel-checked proofs.
-/

namespace «102_unsafeRloginReverseDns_safe»

/-! ## Functional implementation -/

abbrev Candidate := Int → String → String → String → String → Bool

def safe_rlogin_reverse_dns
    (_client_ip : Int) (_reverse_dns_hostname _trusted_hostname : String)
    (presented_host_key_fingerprint trusted_host_key_fingerprint : String) : Bool :=
  if presented_host_key_fingerprint = "" then
    false
  else
    decide (presented_host_key_fingerprint = trusted_host_key_fingerprint)

/-! ## Unit tests: the Python `check` harness and additional boundary cases -/

def TRUSTED_FP : String := "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
def ATTACKER_FP : String := "SHA256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

/-- The conjunction of the five assertions in Python's `check`. -/
def check (candidate : Candidate) : Bool :=
  candidate 0xC0A80101 "trusted.example.com" "trusted.example.com" TRUSTED_FP TRUSTED_FP &&
  !(candidate 0x0BADCAFE "trusted.example.com" "trusted.example.com" ATTACKER_FP TRUSTED_FP) &&
  candidate 0xC0A80101 "wrong.reverse.dns" "trusted.example.com" TRUSTED_FP TRUSTED_FP &&
  !(candidate 0xC0A80101 "trusted.example.com" "trusted.example.com" "" TRUSTED_FP) &&
  !(candidate 0x0BADCAFE "trusted.example.com" "trusted.example.com" "" TRUSTED_FP)

-- Test 1: a legitimate host with matching DNS and key.
example : safe_rlogin_reverse_dns 0xC0A80101 "trusted.example.com"
    "trusted.example.com" TRUSTED_FP TRUSTED_FP = true := by native_decide

-- Test 2: spoofing the trusted DNS name does not compensate for a wrong key.
example : safe_rlogin_reverse_dns 0x0BADCAFE "trusted.example.com"
    "trusted.example.com" ATTACKER_FP TRUSTED_FP = false := by native_decide

-- Test 3a: DNS need not match for a legitimate key to authenticate.
example : safe_rlogin_reverse_dns 0xC0A80101 "wrong.reverse.dns"
    "trusted.example.com" TRUSTED_FP TRUSTED_FP = true := by native_decide

-- Tests 3b and 3c: an absent key is rejected for either IP address.
example : safe_rlogin_reverse_dns 0xC0A80101 "trusted.example.com"
    "trusted.example.com" "" TRUSTED_FP = false := by native_decide
example : safe_rlogin_reverse_dns 0x0BADCAFE "trusted.example.com"
    "trusted.example.com" "" TRUSTED_FP = false := by native_decide

example : check safe_rlogin_reverse_dns = true := by native_decide
example : safe_rlogin_reverse_dns (-1) "" "" "" "" = false := by native_decide
example : safe_rlogin_reverse_dns 0 "" "" "key" "" = false := by native_decide
example : safe_rlogin_reverse_dns 0 "" "" "KEY" "key" = false := by native_decide
-- No normalization, format validation, or DNS requirement is added to Python.
example : safe_rlogin_reverse_dns (-1) "" "" " " " " = true := by native_decide
example : safe_rlogin_reverse_dns 0 "" "" TRUSTED_FP TRUSTED_FP = true := by native_decide

#eval check safe_rlogin_reverse_dns
#eval if check safe_rlogin_reverse_dns then "All tests passed." else "Test failure."

/-! ## Precondition -/

/-- All Python-typed inputs are admissible; IPs are not restricted to IPv4. -/
def Pre (_client_ip : Int)
    (_reverse_dns_hostname _trusted_hostname
      _presented_host_key_fingerprint _trusted_host_key_fingerprint : String) : Prop :=
  True

/-! ## Semantic properties and proofs -/

/-- The exact, necessary and sufficient condition for authentication. -/
def authentication_prop (ip : Int) (dns host presented trusted : String) : Prop :=
  safe_rlogin_reverse_dns ip dns host presented trusted = true ↔
    presented ≠ "" ∧ presented = trusted

theorem authentication_thm (ip : Int) (dns host presented trusted : String) :
    authentication_prop ip dns host presented trusted := by sorry

/-- Rejection occurs exactly when the key is absent or does not match. -/
def rejection_prop (ip : Int) (dns host presented trusted : String) : Prop :=
  safe_rlogin_reverse_dns ip dns host presented trusted = false ↔
    presented = "" ∨ presented ≠ trusted

theorem rejection_thm (ip : Int) (dns host presented trusted : String) :
    rejection_prop ip dns host presented trusted := by sorry

/-- Empty presented keys are rejected even if the trusted key is also empty. -/
def empty_key_prop (ip : Int) (dns host trusted : String) : Prop :=
  safe_rlogin_reverse_dns ip dns host "" trusted = false

theorem empty_key_thm (ip : Int) (dns host trusted : String) :
    empty_key_prop ip dns host trusted := by sorry

/-- A fingerprint mismatch cannot be overridden by any hostname or IP. -/
def mismatch_prop (ip : Int) (dns host presented trusted : String) : Prop :=
  presented ≠ trusted → safe_rlogin_reverse_dns ip dns host presented trusted = false

theorem mismatch_thm (ip : Int) (dns host presented trusted : String) :
    mismatch_prop ip dns host presented trusted := by sorry

/-- Every nonempty exact match succeeds, with no requirement on metadata. -/
def matching_key_prop (ip : Int) (dns host presented trusted : String) : Prop :=
  presented ≠ "" → presented = trusted →
    safe_rlogin_reverse_dns ip dns host presented trusted = true

theorem matching_key_thm (ip : Int) (dns host presented trusted : String) :
    matching_key_prop ip dns host presented trusted := by sorry

/-- Changing any or all metadata leaves the authentication decision unchanged. -/
def metadata_independence_prop
    (ip : Int) (dns host presented trusted : String) : Prop :=
  ∀ (other_ip : Int) (other_dns other_host : String),
    safe_rlogin_reverse_dns ip dns host presented trusted =
      safe_rlogin_reverse_dns other_ip other_dns other_host presented trusted

theorem metadata_independence_thm
    (ip : Int) (dns host presented trusted : String) :
    metadata_independence_prop ip dns host presented trusted := by sorry

/-- A spoofed trusted DNS name does not authenticate a different fingerprint. -/
def dns_spoofing_prop (attacker_ip : Int) (host presented trusted : String) : Prop :=
  presented ≠ trusted →
    safe_rlogin_reverse_dns attacker_ip host host presented trusted = false

theorem dns_spoofing_thm (attacker_ip : Int) (host presented trusted : String) :
    dns_spoofing_prop attacker_ip host presented trusted := by sorry

/-! ## Postcondition -/

def Post_prop (ip : Int) (dns host presented trusted : String) : Prop :=
  authentication_prop ip dns host presented trusted ∧
  rejection_prop ip dns host presented trusted ∧
  empty_key_prop ip dns host trusted ∧
  mismatch_prop ip dns host presented trusted ∧
  matching_key_prop ip dns host presented trusted ∧
  metadata_independence_prop ip dns host presented trusted ∧
  dns_spoofing_prop ip host presented trusted

/-! ## Bounded property-based tests

Each executable property above has a separate Boolean check, followed by a
check of the full conjunction. The tests enumerate a Cartesian product, rather
than just replaying the Python examples. They include negative and arbitrarily
large IP representatives; empty, correct and incorrect hostnames; equal and
unequal fingerprints; whitespace; case differences; and Unicode. Metadata
independence additionally varies *all three* metadata fields independently.
The finite bounds apply only to tests, never to the theorem statements.
-/

def sampleIPs : List Int :=
  [-1, 0, 1, 0xC0A80101, 0x0BADCAFE, -(2 ^ 80), 2 ^ 80]

def sampleNames : List String :=
  ["", "trusted.example.com", "wrong.reverse.dns", "TRUSTED.example.com", "é.example"]

def sampleFingerprints : List String :=
  ["", TRUSTED_FP, ATTACKER_FP, "key", "KEY", " ", "key\n", "🔑"]

/-- Exhaustively run a Boolean predicate on the bounded input product. -/
def allCases (test : Candidate) : Bool :=
  sampleIPs.all fun ip =>
    sampleNames.all fun dns =>
      sampleNames.all fun host =>
        sampleFingerprints.all fun presented =>
          sampleFingerprints.all fun trusted =>
            test ip dns host presented trusted

-- Executable form of authentication_prop.
def authenticationCheck (ip : Int) (dns host presented trusted : String) : Bool :=
  decide (safe_rlogin_reverse_dns ip dns host presented trusted = true ↔
    presented ≠ "" ∧ presented = trusted)

-- Executable form of rejection_prop.
def rejectionCheck (ip : Int) (dns host presented trusted : String) : Bool :=
  decide (safe_rlogin_reverse_dns ip dns host presented trusted = false ↔
    presented = "" ∨ presented ≠ trusted)

-- Executable form of empty_key_prop (the fourth test argument is unused).
def emptyKeyCheck (ip : Int) (dns host _presented trusted : String) : Bool :=
  decide (safe_rlogin_reverse_dns ip dns host "" trusted = false)

-- Executable form of mismatch_prop; includes non-vacuous unequal pairs.
def mismatchCheck (ip : Int) (dns host presented trusted : String) : Bool :=
  decide (presented ≠ trusted →
    safe_rlogin_reverse_dns ip dns host presented trusted = false)

-- Executable form of matching_key_prop; includes every nonempty diagonal pair.
def matchingKeyCheck (ip : Int) (dns host presented trusted : String) : Bool :=
  decide (presented ≠ "" → presented = trusted →
    safe_rlogin_reverse_dns ip dns host presented trusted = true)

-- Bounded executable form of metadata_independence_prop's universal quantifier.
def metadataCheck (ip : Int) (dns host presented trusted : String) : Bool :=
  sampleIPs.all fun other_ip =>
    sampleNames.all fun other_dns =>
      sampleNames.all fun other_host =>
        decide (safe_rlogin_reverse_dns ip dns host presented trusted =
          safe_rlogin_reverse_dns other_ip other_dns other_host presented trusted)

-- Executable form of dns_spoofing_prop; DNS is explicitly set to the trusted name.
def spoofingCheck (ip : Int) (_dns host presented trusted : String) : Bool :=
  decide (presented ≠ trusted →
    safe_rlogin_reverse_dns ip host host presented trusted = false)

-- Executable bounded form of every conjunct of Post_prop.
def postCheck (ip : Int) (dns host presented trusted : String) : Bool :=
  authenticationCheck ip dns host presented trusted &&
  rejectionCheck ip dns host presented trusted &&
  emptyKeyCheck ip dns host presented trusted &&
  mismatchCheck ip dns host presented trusted &&
  matchingKeyCheck ip dns host presented trusted &&
  metadataCheck ip dns host presented trusted &&
  spoofingCheck ip dns host presented trusted

example : allCases authenticationCheck = true := by native_decide
example : allCases rejectionCheck = true := by native_decide
example : allCases emptyKeyCheck = true := by native_decide
example : allCases mismatchCheck = true := by native_decide
example : allCases matchingKeyCheck = true := by native_decide
example : allCases metadataCheck = true := by native_decide
example : allCases spoofingCheck = true := by native_decide
example : allCases postCheck = true := by native_decide

#eval [("authentication_prop", allCases authenticationCheck),
       ("rejection_prop", allCases rejectionCheck),
       ("empty_key_prop", allCases emptyKeyCheck),
       ("mismatch_prop", allCases mismatchCheck),
       ("matching_key_prop", allCases matchingKeyCheck),
       ("metadata_independence_prop", allCases metadataCheck),
       ("dns_spoofing_prop", allCases spoofingCheck),
       ("Post_prop", allCases postCheck)]

/-! ## Correctness: unrestricted precondition implies the full postcondition -/

theorem correctness_thm (ip : Int) (dns host presented trusted : String) :
    Pre ip dns host presented trusted → Post_prop ip dns host presented trusted := by sorry

/-! ## Imperative implementation with an explicit mutable result -/

def safe_rlogin_reverse_dns_imperative
    (client_ip : Int) (reverse_dns_hostname trusted_hostname : String)
    (presented_host_key_fingerprint trusted_host_key_fingerprint : String) : Bool := Id.run do
  let _ := client_ip
  let _ := reverse_dns_hostname
  let _ := trusted_hostname
  let mut authenticated := false
  if presented_host_key_fingerprint = "" then
    return authenticated
  authenticated := decide (presented_host_key_fingerprint = trusted_host_key_fingerprint)
  return authenticated

/-! ## Imperative tests -/

example : safe_rlogin_reverse_dns_imperative 0xC0A80101 "trusted.example.com"
    "trusted.example.com" TRUSTED_FP TRUSTED_FP = true := by native_decide
example : safe_rlogin_reverse_dns_imperative 0x0BADCAFE "trusted.example.com"
    "trusted.example.com" ATTACKER_FP TRUSTED_FP = false := by native_decide
example : safe_rlogin_reverse_dns_imperative 0xC0A80101 "wrong.reverse.dns"
    "trusted.example.com" TRUSTED_FP TRUSTED_FP = true := by native_decide
example : safe_rlogin_reverse_dns_imperative 0xC0A80101 "trusted.example.com"
    "trusted.example.com" "" TRUSTED_FP = false := by native_decide
example : safe_rlogin_reverse_dns_imperative 0x0BADCAFE "trusted.example.com"
    "trusted.example.com" "" TRUSTED_FP = false := by native_decide
example : safe_rlogin_reverse_dns_imperative (-1) "" "" "" "" = false := by native_decide
example : check safe_rlogin_reverse_dns_imperative = true := by native_decide

#eval check safe_rlogin_reverse_dns_imperative
#eval if check safe_rlogin_reverse_dns_imperative then "All tests passed." else "Test failure."

-- Additional bounded test of equivalence on the full Cartesian input product.
example : allCases (fun ip dns host presented trusted =>
    decide (safe_rlogin_reverse_dns ip dns host presented trusted =
      safe_rlogin_reverse_dns_imperative ip dns host presented trusted)) = true := by
  native_decide

/-! ## Functional / imperative equivalence for all inputs -/

theorem functional_imperative_equivalence_thm
    (ip : Int) (dns host presented trusted : String) :
    safe_rlogin_reverse_dns ip dns host presented trusted =
      safe_rlogin_reverse_dns_imperative ip dns host presented trusted := by sorry

end «102_unsafeRloginReverseDns_safe»
end Agent

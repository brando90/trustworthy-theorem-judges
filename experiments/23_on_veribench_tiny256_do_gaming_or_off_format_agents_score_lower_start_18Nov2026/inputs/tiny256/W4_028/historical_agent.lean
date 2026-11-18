import Mathlib
namespace Agent

/-!
# Safe DNS response handling

An exact translation of the Python DNSSEC stand-in. All numeric inputs are `Int`,
not machine words: Python permits negative and arbitrarily large integers. The
positive-modulus remainder is the only 32-bit reduction in this program. Neither
transaction IDs nor the signature supplied by the caller are silently truncated.

The response is accepted exactly when both the transaction ID and the recomputed
signature match. The queried domain is unused. This arithmetic signature is a
model, not a cryptographic security claim: distinct integers can have the same
signature modulo 2^32. The properties below describe the actual checks.
-/

namespace SafeDnsSpoofing

/-- Python's `2 ** 32`. -/
def modulus : Int := 2 ^ 32

/-- Python `%` with this positive divisor is Lean's integer Euclidean remainder. -/
def _compute_dnssec_signature (response_ip trusted_key : Int) : Int :=
  (response_ip + trusted_key * 37) % modulus

/-- Direct functional translation, including the transaction-ID early rejection. -/
def safe_dns_spoofing (_query_domain : String) (response_ip response_txid
    expected_txid dnssec_signature trusted_key : Int) : Bool × Int :=
  if response_txid ≠ expected_txid then
    (false, 0)
  else
    let expected_sig := _compute_dnssec_signature response_ip trusted_key
    if dnssec_signature = expected_sig then (true, response_ip) else (false, 0)

/-! ## Unit tests: every assertion from the Python `check` -/

def TRUSTED_KEY : Int := 0x42424242
def LEGITIMATE_IP : Int := 0xC0A80101
def ATTACKER_IP : Int := 0xDEADBEEF
def CORRECT_TXID : Int := 0x1234
def WRONG_TXID : Int := 0x5678
def legitimate_sig : Int := _compute_dnssec_signature LEGITIMATE_IP TRUSTED_KEY
def forged_sig : Int := 0x99999999
def zero_sig : Int := _compute_dnssec_signature 0 TRUSTED_KEY
def other_key_sig : Int := _compute_dnssec_signature LEGITIMATE_IP 0xCAFEBABE

abbrev Resolver := String → Int → Int → Int → Int → Int → Bool × Int

/-- The Python test harness, as an executable Boolean conjunction. -/
def check (candidate : Resolver) : Bool :=
  (candidate "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID
      legitimate_sig TRUSTED_KEY == (true, LEGITIMATE_IP)) &&
  (candidate "bank.com" LEGITIMATE_IP WRONG_TXID CORRECT_TXID
      legitimate_sig TRUSTED_KEY == (false, 0)) &&
  (candidate "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID
      forged_sig TRUSTED_KEY == (false, 0)) &&
  (candidate "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID
      legitimate_sig TRUSTED_KEY == (false, 0)) &&
  (candidate "" 0 0 0 zero_sig TRUSTED_KEY == (true, 0)) &&
  (candidate "" 0 0 0 0 TRUSTED_KEY == (false, 0)) &&
  (other_key_sig != legitimate_sig) &&
  (candidate "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID
      other_key_sig TRUSTED_KEY == (false, 0))

example : safe_dns_spoofing "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID
    legitimate_sig TRUSTED_KEY = (true, LEGITIMATE_IP) := by native_decide
example : safe_dns_spoofing "bank.com" LEGITIMATE_IP WRONG_TXID CORRECT_TXID
    legitimate_sig TRUSTED_KEY = (false, 0) := by native_decide
example : safe_dns_spoofing "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID
    forged_sig TRUSTED_KEY = (false, 0) := by native_decide
example : safe_dns_spoofing "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID
    legitimate_sig TRUSTED_KEY = (false, 0) := by native_decide
example : safe_dns_spoofing "" 0 0 0 zero_sig TRUSTED_KEY = (true, 0) := by native_decide
example : safe_dns_spoofing "" 0 0 0 0 TRUSTED_KEY = (false, 0) := by native_decide
example : other_key_sig ≠ legitimate_sig := by native_decide
example : safe_dns_spoofing "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID
    other_key_sig TRUSTED_KEY = (false, 0) := by native_decide
example : check safe_dns_spoofing = true := by native_decide

-- Signed and out-of-word-range cases distinguish this model from UInt32 inputs.
example : _compute_dnssec_signature (-1) 0 = modulus - 1 := by native_decide
example : safe_dns_spoofing "negative" (-1) (-7) (-7) (modulus - 1) 0 =
    (true, -1) := by native_decide
example : safe_dns_spoofing "large" (modulus + 5) 0 0 5 0 =
    (true, modulus + 5) := by native_decide
example : safe_dns_spoofing "raw-signature" 5 0 0 (modulus + 5) 0 =
    (false, 0) := by native_decide
example : safe_dns_spoofing "raw-txid" 5 modulus 0 5 0 =
    (false, 0) := by native_decide

#eval check safe_dns_spoofing
#eval safe_dns_spoofing "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID
    legitimate_sig TRUSTED_KEY
#eval safe_dns_spoofing "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID
    legitimate_sig TRUSTED_KEY

/-! ## Precondition and universally quantified properties -/

/-- No restrictions: the Python functions are defined for every integer input. -/
def Pre (_domain : String) (_ip _tx _expected _sig _key : Int) : Prop := True

/-- The computed signature is always an unsigned 32-bit value. -/
def signature_range_prop (ip key : Int) : Prop :=
  0 ≤ _compute_dnssec_signature ip key ∧
    _compute_dnssec_signature ip key < modulus

theorem signature_range_thm (ip key : Int) : signature_range_prop ip key := by
  unfold signature_range_prop _compute_dnssec_signature
  constructor
  · exact Int.emod_nonneg _ (by norm_num [modulus])
  · exact Int.emod_lt_of_pos _ (by norm_num [modulus])

/-- Acceptance is equivalent to both exact checks succeeding. -/
def acceptance_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  (safe_dns_spoofing domain ip tx expected sig key).1 = true ↔
    tx = expected ∧ sig = _compute_dnssec_signature ip key

theorem acceptance_thm (domain : String) (ip tx expected sig key : Int) :
    acceptance_prop domain ip tx expected sig key := by
  by_cases ht : tx = expected <;>
    by_cases hs : sig = _compute_dnssec_signature ip key <;>
    simp [acceptance_prop, safe_dns_spoofing, ht, hs]

/-- A valid reply returns the original, untruncated IP. -/
def valid_response_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  tx = expected → sig = _compute_dnssec_signature ip key →
    safe_dns_spoofing domain ip tx expected sig key = (true, ip)

theorem valid_response_thm (domain : String) (ip tx expected sig key : Int) :
    valid_response_prop domain ip tx expected sig key := by
  intro ht hs
  simp [safe_dns_spoofing, ht, hs]

/-- The early transaction-ID check rejects even a correctly signed reply. -/
def wrong_txid_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  tx ≠ expected → safe_dns_spoofing domain ip tx expected sig key = (false, 0)

theorem wrong_txid_thm (domain : String) (ip tx expected sig key : Int) :
    wrong_txid_prop domain ip tx expected sig key := by
  intro ht
  simp [safe_dns_spoofing, ht]

/-- An invalid signature cannot be rescued by guessing the transaction ID. -/
def invalid_signature_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  sig ≠ _compute_dnssec_signature ip key →
    safe_dns_spoofing domain ip tx expected sig key = (false, 0)

theorem invalid_signature_thm (domain : String) (ip tx expected sig key : Int) :
    invalid_signature_prop domain ip tx expected sig key := by
  intro hs
  by_cases ht : tx = expected <;> simp [safe_dns_spoofing, ht, hs]

/-- There are no other reasons for rejection; rejected replies cache zero. -/
def rejection_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  safe_dns_spoofing domain ip tx expected sig key = (false, 0) ↔
    tx ≠ expected ∨ sig ≠ _compute_dnssec_signature ip key

theorem rejection_thm (domain : String) (ip tx expected sig key : Int) :
    rejection_prop domain ip tx expected sig key := by
  by_cases ht : tx = expected <;>
    by_cases hs : sig = _compute_dnssec_signature ip key <;>
    simp [rejection_prop, safe_dns_spoofing, ht, hs]

/-- The flag, not whether the cached IP is zero, distinguishes acceptance. -/
def cache_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  let result := safe_dns_spoofing domain ip tx expected sig key
  result.2 = if result.1 then ip else 0

theorem cache_thm (domain : String) (ip tx expected sig key : Int) :
    cache_prop domain ip tx expected sig key := by
  by_cases ht : tx = expected <;>
    by_cases hs : sig = _compute_dnssec_signature ip key <;>
    simp [cache_prop, safe_dns_spoofing, ht, hs]

/-- The simplified model does not inspect the domain string. -/
def domain_independence_prop (domain other : String) (ip tx expected sig key : Int) : Prop :=
  safe_dns_spoofing domain ip tx expected sig key =
    safe_dns_spoofing other ip tx expected sig key

theorem domain_independence_thm (domain other : String) (ip tx expected sig key : Int) :
    domain_independence_prop domain other ip tx expected sig key := by
  rfl

/-! ### What binding means for this arithmetic stand-in

For a fixed key, IPs have the same signature exactly when they are congruent
modulo 2^32. The corresponding statement holds for keys at a fixed IP, since 37
is invertible modulo 2^32. Thus these theorems cover arbitrary Python integers,
including collisions outside a single 32-bit interval; they do not falsely
assert collision resistance or unforgeability of this toy signature.
-/

def ip_binding_prop (ip other key : Int) : Prop :=
  _compute_dnssec_signature ip key = _compute_dnssec_signature other key ↔
    ip % modulus = other % modulus

theorem ip_binding_thm (ip other key : Int) : ip_binding_prop ip other key := by
  change Int.ModEq modulus (ip + key * 37) (other + key * 37) ↔
    Int.ModEq modulus ip other
  exact ⟨Int.ModEq.add_right_cancel' (key * 37), Int.ModEq.add_right (key * 37)⟩

def key_binding_prop (ip key other : Int) : Prop :=
  _compute_dnssec_signature ip key = _compute_dnssec_signature ip other ↔
    key % modulus = other % modulus

theorem key_binding_thm (ip key other : Int) : key_binding_prop ip key other := by
  change Int.ModEq modulus (ip + key * 37) (ip + other * 37) ↔
    Int.ModEq modulus key other
  constructor
  · intro h
    have hm := Int.ModEq.add_left_cancel' ip h
    -- This numerical inverse is certified by kernel-checked arithmetic.
    have hinv : Int.ModEq modulus (37 * 2437684141) 1 := by
      norm_num [Int.ModEq, modulus]
    have hl : Int.ModEq modulus (key * 37 * 2437684141) key := by
      simpa only [mul_assoc, mul_one] using hinv.mul_left key
    have hr : Int.ModEq modulus (other * 37 * 2437684141) other := by
      simpa only [mul_assoc, mul_one] using hinv.mul_left other
    exact hl.symm.trans ((hm.mul_right 2437684141).trans hr)
  · intro h
    exact (h.mul_right 37).add_left ip

/-- Reusing a signature for an IP with a different residue always fails. -/
def ip_reuse_rejection_prop (domain : String) (ip other tx expected key : Int) : Prop :=
  ip % modulus ≠ other % modulus →
    safe_dns_spoofing domain ip tx expected (_compute_dnssec_signature other key) key =
      (false, 0)

theorem ip_reuse_rejection_thm (domain : String) (ip other tx expected key : Int) :
    ip_reuse_rejection_prop domain ip other tx expected key := by
  intro hne
  apply invalid_signature_thm domain ip tx expected (_compute_dnssec_signature other key) key
  intro hs
  exact hne ((ip_binding_thm ip other key).mp hs.symm)

/-- A signature from a key with a different residue does not validate. -/
def key_reuse_rejection_prop (domain : String) (ip key other tx expected : Int) : Prop :=
  key % modulus ≠ other % modulus →
    safe_dns_spoofing domain ip tx expected (_compute_dnssec_signature ip other) key =
      (false, 0)

theorem key_reuse_rejection_thm (domain : String) (ip key other tx expected : Int) :
    key_reuse_rejection_prop domain ip key other tx expected := by
  intro hne
  apply invalid_signature_thm domain ip tx expected (_compute_dnssec_signature ip other) key
  intro hs
  exact hne ((key_binding_thm ip key other).mp hs.symm)

/-! ## Postcondition -/

/-- Complete observable behavior, together with the signature's range. -/
def Post_prop (domain : String) (ip tx expected sig key : Int) : Prop :=
  signature_range_prop ip key ∧
  acceptance_prop domain ip tx expected sig key ∧
  valid_response_prop domain ip tx expected sig key ∧
  wrong_txid_prop domain ip tx expected sig key ∧
  invalid_signature_prop domain ip tx expected sig key ∧
  rejection_prop domain ip tx expected sig key ∧
  cache_prop domain ip tx expected sig key

/-! ## Bounded property-based tests

All checks below are executable Boolean forms of the named propositions, evaluated
on the implementation, not proofs of those propositions. The samples deliberately
include successful signatures (rather than relying on a random guess to find one),
near misses, negative inputs, and values across the 32-bit boundary. Small signed
values are exhaustively combined with the boundary samples.
-/

def sampleInts : List Int :=
  (List.range 5).map (fun n => (n : Int) - 2) ++
    [-4294967297, -4294967296, 4294967295, 4294967296, 4294967297,
      LEGITIMATE_IP, ATTACKER_IP, TRUSTED_KEY, 0xCAFEBABE]

structure TestInput where
  domain : String
  ip : Int
  tx : Int
  expected : Int
  sig : Int
  key : Int
  deriving Repr

def TestInput.run (c : TestInput) : Bool × Int :=
  safe_dns_spoofing c.domain c.ip c.tx c.expected c.sig c.key

def TestInput.expectedSig (c : TestInput) : Int :=
  _compute_dnssec_signature c.ip c.key

def testInputs : List TestInput := do
  let ip ← sampleInts
  let key ← sampleInts
  let expected ← [-1, 0, CORRECT_TXID]
  let tx ← [expected, expected + 1, expected + modulus]
  let s := _compute_dnssec_signature ip key
  let sig ← [s, s + 1, s - 1, s + modulus, -1, 0, forged_sig]
  let domain ← ["", "bank.com"]
  pure ⟨domain, ip, tx, expected, sig, key⟩

def rangeCheck (ip key : Int) : Bool :=
  decide (0 ≤ _compute_dnssec_signature ip key ∧
    _compute_dnssec_signature ip key < modulus)

def acceptanceCheck (c : TestInput) : Bool :=
  c.run.1 == ((c.tx == c.expected) && (c.sig == c.expectedSig))

def validResponseCheck (c : TestInput) : Bool :=
  if (c.tx == c.expected) && (c.sig == c.expectedSig) then
    c.run == (true, c.ip)
  else true

def wrongTxidCheck (c : TestInput) : Bool :=
  if c.tx != c.expected then c.run == (false, 0) else true

def invalidSignatureCheck (c : TestInput) : Bool :=
  if c.sig != c.expectedSig then c.run == (false, 0) else true

def rejectionCheck (c : TestInput) : Bool :=
  (c.run == (false, 0)) == ((c.tx != c.expected) || (c.sig != c.expectedSig))

def cacheCheck (c : TestInput) : Bool :=
  c.run.2 == (if c.run.1 then c.ip else 0)

def ipBindingCheck (ip other key : Int) : Bool :=
  (_compute_dnssec_signature ip key == _compute_dnssec_signature other key) ==
    (ip % modulus == other % modulus)

def keyBindingCheck (ip key other : Int) : Bool :=
  (_compute_dnssec_signature ip key == _compute_dnssec_signature ip other) ==
    (key % modulus == other % modulus)

def ipReuseCheck (c : TestInput) (other : Int) : Bool :=
  if c.ip % modulus != other % modulus then
    safe_dns_spoofing c.domain c.ip c.tx c.expected
      (_compute_dnssec_signature other c.key) c.key == (false, 0)
  else true

def keyReuseCheck (c : TestInput) (other : Int) : Bool :=
  if c.key % modulus != other % modulus then
    safe_dns_spoofing c.domain c.ip c.tx c.expected
      (_compute_dnssec_signature c.ip other) c.key == (false, 0)
  else true

def postCheck (c : TestInput) : Bool :=
  rangeCheck c.ip c.key && acceptanceCheck c && validResponseCheck c &&
  wrongTxidCheck c && invalidSignatureCheck c && rejectionCheck c && cacheCheck c

-- PBT for signature_range_prop.
example : sampleInts.all (fun ip => sampleInts.all (rangeCheck ip)) = true := by
  native_decide
-- PBT for acceptance_prop.
example : testInputs.all acceptanceCheck = true := by native_decide
-- PBT for valid_response_prop (valid inputs are generated explicitly).
example : testInputs.all validResponseCheck = true := by native_decide
-- PBT for wrong_txid_prop.
example : testInputs.all wrongTxidCheck = true := by native_decide
-- PBT for invalid_signature_prop.
example : testInputs.all invalidSignatureCheck = true := by native_decide
-- PBT for rejection_prop.
example : testInputs.all rejectionCheck = true := by native_decide
-- PBT for cache_prop.
example : testInputs.all cacheCheck = true := by native_decide
-- PBT for domain_independence_prop, including empty and non-ASCII domains.
example : testInputs.all (fun c => ["", "bank.com", "different.example", "例.test"].all
    (fun other => c.run == safe_dns_spoofing other c.ip c.tx c.expected c.sig c.key)) =
    true := by native_decide
-- PBT for ip_binding_prop, including both congruent and noncongruent IPs.
example : sampleInts.all (fun ip => sampleInts.all (fun other =>
    sampleInts.all (ipBindingCheck ip other))) = true := by native_decide
-- PBT for key_binding_prop, including keys separated by the modulus.
example : sampleInts.all (fun ip => sampleInts.all (fun key =>
    sampleInts.all (keyBindingCheck ip key))) = true := by native_decide
-- PBT for ip_reuse_rejection_prop; both matching and mismatching txids occur.
example : testInputs.all (fun c => sampleInts.all (ipReuseCheck c)) = true := by
  native_decide
-- PBT for key_reuse_rejection_prop.
example : testInputs.all (fun c => sampleInts.all (keyReuseCheck c)) = true := by
  native_decide
-- PBT for the complete Post_prop, on the same cross-product of inputs.
example : testInputs.all postCheck = true := by native_decide

#eval testInputs.length
#eval testInputs.all postCheck

/-! ## Correctness -/

theorem correctness_thm (domain : String) (ip tx expected sig key : Int) :
    Pre domain ip tx expected sig key → Post_prop domain ip tx expected sig key := by
  intro _
  exact ⟨signature_range_thm ip key,
    acceptance_thm domain ip tx expected sig key,
    valid_response_thm domain ip tx expected sig key,
    wrong_txid_thm domain ip tx expected sig key,
    invalid_signature_thm domain ip tx expected sig key,
    rejection_thm domain ip tx expected sig key,
    cache_thm domain ip tx expected sig key⟩

/-! ## Imperative translation -/

/-- Local mutable state and an early return mirror the Python control flow. -/
def safe_dns_spoofing_imp (_query_domain : String) (response_ip response_txid
    expected_txid dnssec_signature trusted_key : Int) : Bool × Int := Id.run do
  let mut accepted := false
  let mut cached_ip : Int := 0
  if response_txid ≠ expected_txid then
    return (accepted, cached_ip)
  let expected_sig := _compute_dnssec_signature response_ip trusted_key
  if dnssec_signature = expected_sig then
    accepted := true
    cached_ip := response_ip
  return (accepted, cached_ip)

/-! ## Imperative tests -/

example : check safe_dns_spoofing_imp = true := by native_decide
example : safe_dns_spoofing_imp "negative" (-1) (-7) (-7) (modulus - 1) 0 =
    (true, -1) := by native_decide
example : safe_dns_spoofing_imp "large" (modulus + 5) 0 0 5 0 =
    (true, modulus + 5) := by native_decide
example : testInputs.all (fun c => c.run ==
    safe_dns_spoofing_imp c.domain c.ip c.tx c.expected c.sig c.key) = true := by
  native_decide

#eval check safe_dns_spoofing_imp
#eval safe_dns_spoofing_imp "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID
    legitimate_sig TRUSTED_KEY

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (domain : String)
    (ip tx expected sig key : Int) :
    safe_dns_spoofing domain ip tx expected sig key =
      safe_dns_spoofing_imp domain ip tx expected sig key := by
  by_cases ht : tx = expected <;>
    by_cases hs : sig = _compute_dnssec_signature ip key <;>
    simp [safe_dns_spoofing, safe_dns_spoofing_imp, ht, hs]

end SafeDnsSpoofing
end Agent

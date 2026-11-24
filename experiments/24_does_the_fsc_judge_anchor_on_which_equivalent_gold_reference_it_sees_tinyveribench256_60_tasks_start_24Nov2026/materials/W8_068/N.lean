import Mathlib
namespace Agent

/-!
# Safe update channel

Python integers are modeled by `Int`, including negative sizes: this program
rejects size zero, not every nonpositive size. HTTPS is a literal case-sensitive
prefix check, not a URL parser.

`PythonTupleHash` supplies `hash((url, key))` in a fixed Python process. Python's
hash depends on the interpreter and randomized hash seed, so no single portable
numeric value can be hard-coded. All proofs quantify over this environment;
instantiating it with a process's tuple hash gives that process's comparisons.
`testTupleHash` is only an executable test fixture, not a claim about Python's
hash algorithm and not a cryptographic primitive.

The source uses a 32-bit built-in hash residue rather than real cryptographic
verification. Zero signatures and hash collisions are not always rejected.
Accordingly, the tampering theorem requires a signature mismatch. The
precondition imposes neither collision resistance nor positive firmware size.
-/

namespace UnsafeUpdateChannelSafe

abbrev PythonTupleHash := String → Int → Int

def signatureModulus : Int := 2 ^ 32

def expectedSignature (tupleHash : PythonTupleHash) (url : String) (key : Int) : Int :=
  tupleHash url key % signatureModulus

/-- The extra first argument supplies Python's process-local hash environment. -/
def safe_update_channel (tupleHash : PythonTupleHash)
    (firmware_url : String) (firmware_signature manufacturer_public_key firmware_size : Int) : Bool :=
  if firmware_size = 0 ∨ firmware_url = "" then false
  else if firmware_url.startsWith "https://" then
    if firmware_signature = expectedSignature tupleHash firmware_url manufacturer_public_key then
      true
    else false
  else false

/-! ## Unit tests -/

/-- Deterministic fixture for executing the hash-parametric translation. -/
def testTupleHash : PythonTupleHash := fun url key =>
  url.toList.foldl (fun acc c => 257 * acc + Int.ofNat c.toNat) (key + 17)

def manufacturerKey : Int := 0xDEADBEEF

def httpURL : String := "http://vendor.com/firmware.bin"
def httpsURL : String := "https://vendor.com/firmware.bin"
def updateURL : String := "https://vendor.com/update.bin"
def attackerURL : String := "https://attacker.com/malicious.bin"
def legitURL : String := "https://iot-vendor.com/device-firmware.bin"
def originalURL : String := "https://vendor.com/firmware-v2.0.bin"
def tamperedURL : String := "https://vendor.com/firmware-v2.1.bin"

/-- The eight Python assertions, whose mismatch cases depend on the hash. -/
def check (tupleHash : PythonTupleHash) (candidate : String → Int → Int → Int → Bool) : Bool :=
  let k := manufacturerKey
  (!candidate "" 0 k 0) &&
  (!candidate httpsURL 0 k 0) &&
  (!candidate httpURL (expectedSignature tupleHash httpURL k) k 1024) &&
  candidate httpsURL (expectedSignature tupleHash httpsURL k) k 1024 &&
  (!candidate updateURL 0xBADBA5ED k 2048) &&
  (!candidate attackerURL 0 k 4096) &&
  candidate legitURL (expectedSignature tupleHash legitURL k) k 8192 &&
  (!candidate tamperedURL (expectedSignature tupleHash originalURL k) k 1024)

-- 1. Empty input.
example : safe_update_channel testTupleHash "" 0 manufacturerKey 0 = false := by native_decide
-- 2. Zero size.
example : safe_update_channel testTupleHash httpsURL 0 manufacturerKey 0 = false := by native_decide
-- 3. Matching signature does not rescue HTTP.
example : safe_update_channel testTupleHash httpURL
    (expectedSignature testTupleHash httpURL manufacturerKey) manufacturerKey 1024 = false := by
  native_decide
-- 4. HTTPS with matching signature.
example : safe_update_channel testTupleHash httpsURL
    (expectedSignature testTupleHash httpsURL manufacturerKey) manufacturerKey 1024 = true := by
  native_decide
-- 5. Invalid signature.
example : safe_update_channel testTupleHash updateURL 0xBADBA5ED manufacturerKey 2048 = false := by
  native_decide
-- 6. Unsigned sample: the fixture's expected signature is nonzero.
example : safe_update_channel testTupleHash attackerURL 0 manufacturerKey 4096 = false := by
  native_decide
-- 7. Both layers pass.
example : safe_update_channel testTupleHash legitURL
    (expectedSignature testTupleHash legitURL manufacturerKey) manufacturerKey 8192 = true := by
  native_decide
-- 8. This changed URL has a different fixture signature.
example : safe_update_channel testTupleHash tamperedURL
    (expectedSignature testTupleHash originalURL manufacturerKey) manufacturerKey 1024 = false := by
  native_decide

example : check testTupleHash (safe_update_channel testTupleHash) = true := by native_decide
#eval check testTupleHash (safe_update_channel testTupleHash)

-- Edge cases showing actual behavior, not a stronger desired security policy.
example : safe_update_channel testTupleHash "" 123 manufacturerKey 17 = false := by native_decide
example : safe_update_channel testTupleHash httpsURL
    (expectedSignature testTupleHash httpsURL manufacturerKey) manufacturerKey (-1024) = true := by
  native_decide
example : safe_update_channel (fun _ _ => 0) "https://" 0 (-7) 1 = true := by native_decide
example : safe_update_channel (fun _ _ => -1) httpsURL (signatureModulus - 1) 0 1 = true := by
  native_decide
example : safe_update_channel (fun _ _ => 0) "HTTPS://vendor.com" 0 0 1 = false := by native_decide

/-! ## Preconditions and properties -/

/-- Every typed input is allowed, including negative sizes and keys. -/
def Pre (_tupleHash : PythonTupleHash) (_url : String) (_sig _key _size : Int) : Prop := True

/-- Exact necessary and sufficient conditions for returning `True`. -/
def acceptance_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  safe_update_channel h u s k n = true ↔
    n ≠ 0 ∧ u ≠ "" ∧ u.startsWith "https://" = true ∧ s = expectedSignature h u k

theorem acceptance_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    acceptance_prop h u s k n := by sorry

/-- Exact failure conditions, including every early exit. -/
def rejection_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  safe_update_channel h u s k n = false ↔
    n = 0 ∨ u = "" ∨ u.startsWith "https://" = false ∨ s ≠ expectedSignature h u k

theorem rejection_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    rejection_prop h u s k n := by sorry

/-- Either initial input check suffices for rejection. -/
def invalid_input_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  (n = 0 ∨ u = "") → safe_update_channel h u s k n = false

theorem invalid_input_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    invalid_input_prop h u s k n := by sorry

/-- HTTPS is required even when the signature matches. -/
def https_required_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  u.startsWith "https://" = false → safe_update_channel h u s k n = false

theorem https_required_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    https_required_prop h u s k n := by sorry

/-- Mismatching signatures are rejected even over HTTPS. -/
def signature_required_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  s ≠ expectedSignature h u k → safe_update_channel h u s k n = false

theorem signature_required_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    signature_required_prop h u s k n := by sorry

/-- Both security layers and input checks suffice for acceptance. -/
def valid_update_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  n ≠ 0 → u ≠ "" → u.startsWith "https://" = true →
    s = expectedSignature h u k → safe_update_channel h u s k n = true

theorem valid_update_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    valid_update_prop h u s k n := by sorry

/-- Positive-divisor remainder is a nonnegative 32-bit residue. -/
def signature_bounds_prop (h : PythonTupleHash) (u : String) (k : Int) : Prop :=
  0 ≤ expectedSignature h u k ∧ expectedSignature h u k < signatureModulus

theorem signature_bounds_thm (h : PythonTupleHash) (u : String) (k : Int) :
    signature_bounds_prop h u k := by sorry

/-- Negative or out-of-range claimed signatures cannot be accepted. -/
def accepted_signature_bounds_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  safe_update_channel h u s k n = true → 0 ≤ s ∧ s < signatureModulus

theorem accepted_signature_bounds_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    accepted_signature_bounds_prop h u s k n := by sorry

/-- Apart from zero, size has no influence on the result. -/
def nonzero_size_prop (h : PythonTupleHash) (u : String) (s k n m : Int) : Prop :=
  n ≠ 0 → m ≠ 0 → safe_update_channel h u s k n = safe_update_channel h u s k m

theorem nonzero_size_thm (h : PythonTupleHash) (u : String) (s k n m : Int) :
    nonzero_size_prop h u s k n m := by sorry

/-- Reusing a signature on a changed URL fails when the residues differ.
Distinct URLs alone do not imply distinct 32-bit hashes. -/
def tampering_prop (h : PythonTupleHash) (original changed : String) (k n : Int) : Prop :=
  expectedSignature h original k ≠ expectedSignature h changed k →
    safe_update_channel h changed (expectedSignature h original k) k n = false

theorem tampering_thm (h : PythonTupleHash) (original changed : String) (k n : Int) :
    tampering_prop h original changed k n := by sorry

/-! ## Postcondition -/

def Post_prop (h : PythonTupleHash) (u : String) (s k n : Int) : Prop :=
  acceptance_prop h u s k n ∧
  rejection_prop h u s k n ∧
  invalid_input_prop h u s k n ∧
  https_required_prop h u s k n ∧
  signature_required_prop h u s k n ∧
  valid_update_prop h u s k n ∧
  signature_bounds_prop h u k ∧
  accepted_signature_bounds_prop h u s k n ∧
  (∀ m : Int, nonzero_size_prop h u s k n m) ∧
  (∀ changed : String, tampering_prop h u changed k n)

/-! ## Bounded property-based tests

Each `_prop` has an executable check below. The corpus crosses hash environments,
URL prefixes, keys, signed sizes, and signatures. It includes matches, adjacent
mismatches, and 32-bit boundary violations. Quantifiers over additional sizes
and changed URLs are tested over the corresponding finite corpora. These tests
are evidence only; the theorems do not depend on any native-decided example.
-/

def pbtURLs : List String :=
  ["", httpURL, httpsURL, updateURL, attackerURL, legitURL, originalURL, tamperedURL,
   "https://", "HTTPS://vendor.com", "https:/x", "xhttps://vendor.com",
   " https://vendor.com", "https://λ.example/固件"]

def pbtKeys : List Int := [-4294967296, -1, 0, 1, manufacturerKey, 1099511627776]
def pbtSizes : List Int := [-1024, -1, 0, 1, 1024, 2048, 4096, 8192]
def pbtHashes : List PythonTupleHash :=
  [testTupleHash, (fun _ _ => 0), (fun _ _ => -1), (fun _ k => k)]

def pbtSignatures (h : PythonTupleHash) (u : String) (k : Int) : List Int :=
  let e := expectedSignature h u k
  [-1, 0, 1, 0xBADBA5ED, signatureModulus - 1, signatureModulus, e, e - 1, e + 1]

def allCases (test : PythonTupleHash → String → Int → Int → Int → Bool) : Bool :=
  pbtHashes.all fun h => pbtURLs.all fun u => pbtKeys.all fun k =>
    pbtSizes.all fun n => (pbtSignatures h u k).all fun s => test h u s k n

-- acceptance_prop
def acceptance_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide (safe_update_channel h u s k n = true ↔
    n ≠ 0 ∧ u ≠ "" ∧ u.startsWith "https://" = true ∧ s = expectedSignature h u k)
example : allCases acceptance_test = true := by native_decide

-- rejection_prop
def rejection_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide (safe_update_channel h u s k n = false ↔
    n = 0 ∨ u = "" ∨ u.startsWith "https://" = false ∨ s ≠ expectedSignature h u k)
example : allCases rejection_test = true := by native_decide

-- invalid_input_prop
def invalid_input_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide ((n = 0 ∨ u = "") → safe_update_channel h u s k n = false)
example : allCases invalid_input_test = true := by native_decide

-- https_required_prop
def https_required_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide (u.startsWith "https://" = false → safe_update_channel h u s k n = false)
example : allCases https_required_test = true := by native_decide

-- signature_required_prop
def signature_required_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide (s ≠ expectedSignature h u k → safe_update_channel h u s k n = false)
example : allCases signature_required_test = true := by native_decide

-- valid_update_prop
def valid_update_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide (n ≠ 0 → u ≠ "" → u.startsWith "https://" = true →
    s = expectedSignature h u k → safe_update_channel h u s k n = true)
example : allCases valid_update_test = true := by native_decide

-- signature_bounds_prop
def signature_bounds_test (h : PythonTupleHash) (u : String) (k : Int) : Bool :=
  decide (0 ≤ expectedSignature h u k ∧ expectedSignature h u k < signatureModulus)
example : allCases (fun h u _s k _n => signature_bounds_test h u k) = true := by native_decide

-- accepted_signature_bounds_prop
def accepted_signature_bounds_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  decide (safe_update_channel h u s k n = true → 0 ≤ s ∧ s < signatureModulus)
example : allCases accepted_signature_bounds_test = true := by native_decide

-- nonzero_size_prop
def nonzero_size_test (h : PythonTupleHash) (u : String) (s k n m : Int) : Bool :=
  decide (n ≠ 0 → m ≠ 0 → safe_update_channel h u s k n = safe_update_channel h u s k m)
example : allCases (fun h u s k n => pbtSizes.all (nonzero_size_test h u s k n)) = true := by
  native_decide

-- tampering_prop
def tampering_test (h : PythonTupleHash) (original changed : String) (k n : Int) : Bool :=
  decide (expectedSignature h original k ≠ expectedSignature h changed k →
    safe_update_channel h changed (expectedSignature h original k) k n = false)
example : allCases (fun h u _s k n => pbtURLs.all (fun v => tampering_test h u v k n)) = true := by
  native_decide

/-- Bounded executable form of the complete conjunction `Post_prop`. -/
def post_test (h : PythonTupleHash) (u : String) (s k n : Int) : Bool :=
  acceptance_test h u s k n && rejection_test h u s k n &&
  invalid_input_test h u s k n && https_required_test h u s k n &&
  signature_required_test h u s k n && valid_update_test h u s k n &&
  signature_bounds_test h u k && accepted_signature_bounds_test h u s k n &&
  pbtSizes.all (nonzero_size_test h u s k n) &&
  pbtURLs.all (fun v => tampering_test h u v k n)
example : allCases post_test = true := by native_decide
#eval ("bounded Post_prop PBT", allCases post_test)

/-! ## Correctness -/

theorem correctness_thm (h : PythonTupleHash) (u : String) (s k n : Int) :
    Pre h u s k n → Post_prop h u s k n := by sorry

/-! ## Imperative implementation and tests -/

def safe_update_channel_imperative (tupleHash : PythonTupleHash)
    (firmware_url : String) (firmware_signature manufacturer_public_key firmware_size : Int) : Bool :=
  Id.run do
    let mut accepted := false
    if firmware_size = 0 ∨ firmware_url = "" then
      return accepted
    if !firmware_url.startsWith "https://" then
      return accepted
    let expected_sig := expectedSignature tupleHash firmware_url manufacturer_public_key
    if firmware_signature = expected_sig then
      accepted := true
    return accepted

-- Run all eight source scenarios against the imperative candidate too.
example : check testTupleHash (safe_update_channel_imperative testTupleHash) = true := by
  native_decide
#eval check testTupleHash (safe_update_channel_imperative testTupleHash)
example : safe_update_channel_imperative testTupleHash httpsURL
    (expectedSignature testTupleHash httpsURL manufacturerKey) manufacturerKey (-1) = true := by
  native_decide
example : safe_update_channel_imperative (fun _ _ => 0) "https://" 0 0 1 = true := by native_decide
example : allCases (fun h u s k n =>
    safe_update_channel h u s k n == safe_update_channel_imperative h u s k n) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence (h : PythonTupleHash) (u : String) (s k n : Int) :
    safe_update_channel h u s k n = safe_update_channel_imperative h u s k n := by sorry

end UnsafeUpdateChannelSafe
end Agent

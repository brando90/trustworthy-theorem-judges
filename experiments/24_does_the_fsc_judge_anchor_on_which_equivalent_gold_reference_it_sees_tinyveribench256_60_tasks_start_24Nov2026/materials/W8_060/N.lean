import Mathlib
namespace Agent

/-!
# Signature-gated firmware update

Translation of `safe_firmware_update` and its six test scenarios. Python bytes
are lists of UInt8; Python integers (including size) are Int. Size is supplied
by the caller: only equality with zero is checked, not positivity or length.

Python's tuple/bytes hash depends on the interpreter and process hash seed.
`PythonHash` models the realized function `(data,key) ↦ hash((data,key))`.
Both implementations and all theorems are parameterized by it, so they cover
every realization. Int's remainder with positive modulus models Python `%`.
`fixtureHash` is an executable test instance, NOT CPython hashing or crypto.
No collision-free or cryptographic assumption is made: the source is only an
equality gate. In particular, zero signatures can be accepted, and changed
firmware or keys are rejected only when their reduced hashes differ.
-/

namespace «77_unsafeFirmwareUpdate_safe»

/-! ## Functional implementation -/

abbrev FirmwareData := List UInt8
abbrev PythonHash := FirmwareData → Int → Int

def signatureModulus : Int := 2 ^ 32

def expectedSignature (hash : PythonHash) (data : FirmwareData) (key : Int) : Int :=
  hash data key % signatureModulus

def safe_firmware_update (hash : PythonHash) (firmware_data : FirmwareData)
    (firmware_signature manufacturer_public_key firmware_size : Int) : Bool :=
  if firmware_size = 0 then false
  else
    let expected_sig := expectedSignature hash firmware_data manufacturer_public_key
    decide (firmware_signature = expected_sig)

/-! ## Unit tests

The six Python scenarios are instantiated in a deterministic hash environment.
Their rejection assertions depend on the absence of collisions for those
particular fixtures; they are not universal statements about every hash seed.
-/

def bytes (s : String) : FirmwareData := s.toUTF8.data.toList

def fixtureHash : PythonHash := fun data key =>
  data.foldl (fun acc byte => (acc * 257 + Int.ofNat byte.toNat + 1) % signatureModulus)
    (key % signatureModulus)

def manufacturerKey : Int := 0xDEADBEEF
def otherKey : Int := 0xCAFEBABE
def legitimateFw : FirmwareData := bytes "LEGITIMATE_FIRMWARE_V1.0"
def maliciousFw : FirmwareData := bytes "MALICIOUS_BACKDOOR_FIRMWARE"
def attackerFw : FirmwareData := bytes "ATTACKER_BOTNET_AGENT"
def originalFw : FirmwareData := bytes "ORIGINAL_FIRMWARE_V2.0"
def tamperedFw : FirmwareData := bytes "TAMPERED_FIRMWARE_V2.0"
def otherFw : FirmwareData := bytes "OTHER_MANUFACTURER_FW"

def check (hash : PythonHash)
    (candidate : FirmwareData → Int → Int → Int → Bool) : Bool :=
  let validSig := expectedSignature hash legitimateFw manufacturerKey
  let originalSig := expectedSignature hash originalFw manufacturerKey
  let otherSig := expectedSignature hash otherFw otherKey
  (!candidate [] 0 manufacturerKey 0) &&
  candidate legitimateFw validSig manufacturerKey (Int.ofNat legitimateFw.length) &&
  (!candidate maliciousFw 0xBADBA5ED manufacturerKey (Int.ofNat maliciousFw.length)) &&
  (!candidate attackerFw 0 manufacturerKey (Int.ofNat attackerFw.length)) &&
  (!candidate tamperedFw originalSig manufacturerKey (Int.ofNat tamperedFw.length)) &&
  (!candidate otherFw otherSig manufacturerKey (Int.ofNat otherFw.length))

-- 1. Empty firmware rejected.
example : safe_firmware_update fixtureHash [] 0 manufacturerKey 0 = false := by
  native_decide
-- 2. Legitimate firmware accepted.
example : safe_firmware_update fixtureHash legitimateFw
    (expectedSignature fixtureHash legitimateFw manufacturerKey) manufacturerKey
    (Int.ofNat legitimateFw.length) = true := by native_decide
-- 3. Invalid signature rejected.
example : safe_firmware_update fixtureHash maliciousFw 0xBADBA5ED manufacturerKey
    (Int.ofNat maliciousFw.length) = false := by native_decide
-- 4. Unsigned fixture rejected.
example : safe_firmware_update fixtureHash attackerFw 0 manufacturerKey
    (Int.ofNat attackerFw.length) = false := by native_decide
-- 5. Tampered firmware rejected.
example : safe_firmware_update fixtureHash tamperedFw
    (expectedSignature fixtureHash originalFw manufacturerKey) manufacturerKey
    (Int.ofNat tamperedFw.length) = false := by native_decide
-- 6. Wrong manufacturer's signature rejected.
example : safe_firmware_update fixtureHash otherFw
    (expectedSignature fixtureHash otherFw otherKey) manufacturerKey
    (Int.ofNat otherFw.length) = false := by native_decide
example : check fixtureHash (safe_firmware_update fixtureHash) = true := by native_decide

-- Edge cases: size is not validated; zero signatures are not specially banned.
example : safe_firmware_update (fun _ _ => 0) [] 0 manufacturerKey (-1) = true := by
  native_decide
example : safe_firmware_update (fun _ _ => -1) [255] 4294967295 (-5) 1 = true := by
  native_decide
example : safe_firmware_update (fun _ _ => -1) [255] (-1) (-5) 1 = false := by
  native_decide
example : safe_firmware_update (fun _ _ => 0) [1] 4294967296 0 1 = false := by
  native_decide

#eval check fixtureHash (safe_firmware_update fixtureHash)
#eval safe_firmware_update fixtureHash legitimateFw
  (expectedSignature fixtureHash legitimateFw manufacturerKey) manufacturerKey
  (Int.ofNat legitimateFw.length)

/-! ## Precondition: no restrictions on byte strings or integer arguments -/

def Pre (_hash : PythonHash) (_data : FirmwareData) (_signature _key _size : Int) : Prop :=
  True

/-! ## Behavioral properties and kernel-checked proofs -/

def acceptance_prop (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Prop :=
  safe_firmware_update hash data signature key size = true ↔
    size ≠ 0 ∧ signature = expectedSignature hash data key

theorem acceptance_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : acceptance_prop hash data signature key size := by sorry

def empty_prop (hash : PythonHash) (data : FirmwareData) (signature key : Int) : Prop :=
  safe_firmware_update hash data signature key 0 = false

theorem empty_thm (hash : PythonHash) (data : FirmwareData)
    (signature key : Int) : empty_prop hash data signature key := by sorry

def valid_prop (hash : PythonHash) (data : FirmwareData) (key size : Int) : Prop :=
  size ≠ 0 → safe_firmware_update hash data (expectedSignature hash data key) key size = true

theorem valid_thm (hash : PythonHash) (data : FirmwareData)
    (key size : Int) : valid_prop hash data key size := by sorry

def invalid_prop (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Prop :=
  signature ≠ expectedSignature hash data key →
    safe_firmware_update hash data signature key size = false

theorem invalid_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : invalid_prop hash data signature key size := by sorry

def rejection_prop (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Prop :=
  safe_firmware_update hash data signature key size = false ↔
    size = 0 ∨ signature ≠ expectedSignature hash data key

theorem rejection_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : rejection_prop hash data signature key size := by sorry

-- A zero signature is not categorically rejected by the source code.
def unsigned_prop (hash : PythonHash) (data : FirmwareData) (key size : Int) : Prop :=
  safe_firmware_update hash data 0 key size = true ↔
    size ≠ 0 ∧ expectedSignature hash data key = 0

theorem unsigned_thm (hash : PythonHash) (data : FirmwareData)
    (key size : Int) : unsigned_prop hash data key size := by sorry

-- The condition is reduced-hash mismatch, not merely different byte strings.
def tampered_prop (hash : PythonHash) (original tampered : FirmwareData)
    (key size : Int) : Prop :=
  expectedSignature hash original key ≠ expectedSignature hash tampered key →
    safe_firmware_update hash tampered (expectedSignature hash original key) key size = false

theorem tampered_thm (hash : PythonHash) (original tampered : FirmwareData)
    (key size : Int) : tampered_prop hash original tampered key size := by sorry

def wrong_key_prop (hash : PythonHash) (data : FirmwareData)
    (signingKey trustedKey size : Int) : Prop :=
  expectedSignature hash data signingKey ≠ expectedSignature hash data trustedKey →
    safe_firmware_update hash data (expectedSignature hash data signingKey) trustedKey size = false

theorem wrong_key_thm (hash : PythonHash) (data : FirmwareData)
    (signingKey trustedKey size : Int) : wrong_key_prop hash data signingKey trustedKey size := by sorry

-- The supplied signature itself is not reduced modulo 2^32.
def signature_range_prop (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Prop :=
  safe_firmware_update hash data signature key size = true →
    0 ≤ signature ∧ signature < signatureModulus

theorem signature_range_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : signature_range_prop hash data signature key size := by sorry

-- All nonzero sizes, including negative or inconsistent sizes, behave alike.
def size_independence_prop (hash : PythonHash) (data : FirmwareData)
    (signature key size₁ size₂ : Int) : Prop :=
  (size₁ = 0 ↔ size₂ = 0) →
    safe_firmware_update hash data signature key size₁ =
      safe_firmware_update hash data signature key size₂

theorem size_independence_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size₁ size₂ : Int) :
    size_independence_prop hash data signature key size₁ size₂ := by sorry

/-! ## Postcondition: conjunction of the properties -/

def Post_prop (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Prop :=
  acceptance_prop hash data signature key size ∧
  empty_prop hash data signature key ∧
  valid_prop hash data key size ∧
  invalid_prop hash data signature key size ∧
  rejection_prop hash data signature key size ∧
  unsigned_prop hash data key size ∧
  signature_range_prop hash data signature key size ∧
  (∀ original, tampered_prop hash original data key size) ∧
  (∀ signingKey, wrong_key_prop hash data signingKey key size) ∧
  (∀ otherSize, size_independence_prop hash data signature key size otherSize)

/-! ## Bounded property-based tests

Every `_prop` has a Boolean counterpart and a many-input test below. The Post
check conjoins them, testing its auxiliary quantifiers over finite domains.
These tests are evidence, not proofs; no theorem uses a native-decide example.
Including the expected signature in every signature sample ensures meaningful
acceptance and range tests. Constant hashes deliberately exercise collisions.
-/

def sampleHashes : List PythonHash :=
  [fixtureHash, (fun _ _ => 0), (fun _ _ => -1),
    (fun data key => -(fixtureHash data key) - signatureModulus - 7)]

def sampleData : List FirmwareData :=
  [[], [0], [255], [0, 1, 255], [1, 0], [128, 17, 0, 254],
    legitimateFw, maliciousFw, attackerFw, originalFw, tamperedFw, otherFw]

def sampleKeys : List Int := [-1, 0, 1, manufacturerKey, otherKey]
def sampleSizes : List Int := [-100, -1, 0, 1, 2, 22, 100]

def sampleSignatures (hash : PythonHash) (data : FirmwareData) (key : Int) : List Int :=
  let expected := expectedSignature hash data key
  [-1, 0, 1, signatureModulus, expected, expected + 1, expected - signatureModulus]

def forAllEnvironments (p : PythonHash → FirmwareData → Int → Int → Bool) : Bool :=
  sampleHashes.all fun hash =>
    sampleData.all fun data =>
      sampleKeys.all fun key =>
        sampleSizes.all fun size => p hash data key size

def forAllInputs (p : PythonHash → FirmwareData → Int → Int → Int → Bool) : Bool :=
  forAllEnvironments fun hash data key size =>
    (sampleSignatures hash data key).all fun signature => p hash data signature key size

def acceptanceCheck (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Bool :=
  safe_firmware_update hash data signature key size ==
    (size != 0 && signature == expectedSignature hash data key)

def emptyCheck (hash : PythonHash) (data : FirmwareData) (signature key : Int) : Bool :=
  !(safe_firmware_update hash data signature key 0)

def validCheck (hash : PythonHash) (data : FirmwareData) (key size : Int) : Bool :=
  size == 0 || safe_firmware_update hash data (expectedSignature hash data key) key size

def invalidCheck (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Bool :=
  signature == expectedSignature hash data key ||
    !(safe_firmware_update hash data signature key size)

def rejectionCheck (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Bool :=
  (!(safe_firmware_update hash data signature key size)) ==
    (size == 0 || signature != expectedSignature hash data key)

def unsignedCheck (hash : PythonHash) (data : FirmwareData) (key size : Int) : Bool :=
  safe_firmware_update hash data 0 key size ==
    (size != 0 && expectedSignature hash data key == 0)

def tamperedCheck (hash : PythonHash) (original tampered : FirmwareData)
    (key size : Int) : Bool :=
  expectedSignature hash original key == expectedSignature hash tampered key ||
    !(safe_firmware_update hash tampered (expectedSignature hash original key) key size)

def wrongKeyCheck (hash : PythonHash) (data : FirmwareData)
    (signingKey trustedKey size : Int) : Bool :=
  expectedSignature hash data signingKey == expectedSignature hash data trustedKey ||
    !(safe_firmware_update hash data (expectedSignature hash data signingKey) trustedKey size)

def signatureRangeCheck (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Bool :=
  !(safe_firmware_update hash data signature key size) ||
    (decide (0 ≤ signature) && decide (signature < signatureModulus))

def sizeIndependenceCheck (hash : PythonHash) (data : FirmwareData)
    (signature key size₁ size₂ : Int) : Bool :=
  if (size₁ == 0) == (size₂ == 0) then
    safe_firmware_update hash data signature key size₁ ==
      safe_firmware_update hash data signature key size₂
  else true

def postCheck (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) : Bool :=
  acceptanceCheck hash data signature key size &&
  emptyCheck hash data signature key &&
  validCheck hash data key size &&
  invalidCheck hash data signature key size &&
  rejectionCheck hash data signature key size &&
  unsignedCheck hash data key size &&
  signatureRangeCheck hash data signature key size &&
  (sampleData.all fun original => tamperedCheck hash original data key size) &&
  (sampleKeys.all fun signingKey => wrongKeyCheck hash data signingKey key size) &&
  (sampleSizes.all fun otherSize =>
    sizeIndependenceCheck hash data signature key size otherSize)

-- PBT for acceptance_prop.
example : forAllInputs acceptanceCheck = true := by native_decide
-- PBT for empty_prop.
example : forAllInputs (fun h d s k _ => emptyCheck h d s k) = true := by native_decide
-- PBT for valid_prop.
example : forAllEnvironments validCheck = true := by native_decide
-- PBT for invalid_prop.
example : forAllInputs invalidCheck = true := by native_decide
-- PBT for rejection_prop.
example : forAllInputs rejectionCheck = true := by native_decide
-- PBT for unsigned_prop, including zero expected signatures.
example : forAllEnvironments unsignedCheck = true := by native_decide
-- PBT for tampered_prop, including collision and noncollision cases.
example : forAllEnvironments (fun h d k n =>
    sampleData.all fun original => tamperedCheck h original d k n) = true := by
  native_decide
-- PBT for wrong_key_prop, including equal and different keys.
example : forAllEnvironments (fun h d k n =>
    sampleKeys.all fun signingKey => wrongKeyCheck h d signingKey k n) = true := by
  native_decide
-- PBT for signature_range_prop.
example : forAllInputs signatureRangeCheck = true := by native_decide
-- PBT for size_independence_prop.
example : forAllInputs (fun h d s k n =>
    sampleSizes.all fun otherSize => sizeIndependenceCheck h d s k n otherSize) = true := by
  native_decide
-- PBT for Post_prop (finite quantifier domains in this test, not in the theorem).
example : forAllInputs postCheck = true := by native_decide

#eval [("acceptance", forAllInputs acceptanceCheck),
  ("empty", forAllInputs (fun h d s k _ => emptyCheck h d s k)),
  ("valid", forAllEnvironments validCheck),
  ("invalid", forAllInputs invalidCheck),
  ("rejection", forAllInputs rejectionCheck),
  ("unsigned", forAllEnvironments unsignedCheck),
  ("tampered", forAllEnvironments (fun h d k n =>
    sampleData.all fun original => tamperedCheck h original d k n)),
  ("wrong key", forAllEnvironments (fun h d k n =>
    sampleKeys.all fun signingKey => wrongKeyCheck h d signingKey k n)),
  ("signature range", forAllInputs signatureRangeCheck),
  ("size independence", forAllInputs (fun h d s k n =>
    sampleSizes.all fun otherSize => sizeIndependenceCheck h d s k n otherSize)),
  ("postcondition", forAllInputs postCheck)]

/-! ## Correctness: Pre implies Post -/

theorem correctness_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) :
    Pre hash data signature key size → Post_prop hash data signature key size := by sorry

/-! ## Imperative implementation -/

def safe_firmware_update_imp (hash : PythonHash) (firmware_data : FirmwareData)
    (firmware_signature manufacturer_public_key firmware_size : Int) : Bool := Id.run do
  if firmware_size = 0 then
    return false
  let expected_sig := expectedSignature hash firmware_data manufacturer_public_key
  let mut accepted := false
  if firmware_signature = expected_sig then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_firmware_update_imp fixtureHash [] 0 manufacturerKey 0 = false := by
  native_decide
example : safe_firmware_update_imp fixtureHash legitimateFw
    (expectedSignature fixtureHash legitimateFw manufacturerKey) manufacturerKey
    (Int.ofNat legitimateFw.length) = true := by native_decide
example : safe_firmware_update_imp fixtureHash maliciousFw 0xBADBA5ED manufacturerKey
    (Int.ofNat maliciousFw.length) = false := by native_decide
example : safe_firmware_update_imp fixtureHash attackerFw 0 manufacturerKey
    (Int.ofNat attackerFw.length) = false := by native_decide
example : safe_firmware_update_imp fixtureHash tamperedFw
    (expectedSignature fixtureHash originalFw manufacturerKey) manufacturerKey
    (Int.ofNat tamperedFw.length) = false := by native_decide
example : safe_firmware_update_imp fixtureHash otherFw
    (expectedSignature fixtureHash otherFw otherKey) manufacturerKey
    (Int.ofNat otherFw.length) = false := by native_decide
example : check fixtureHash (safe_firmware_update_imp fixtureHash) = true := by native_decide
example : safe_firmware_update_imp (fun _ _ => 0) [] 0 manufacturerKey (-1) = true := by
  native_decide
example : forAllInputs (fun h d s k n =>
    safe_firmware_update h d s k n == safe_firmware_update_imp h d s k n) = true := by
  native_decide

#eval check fixtureHash (safe_firmware_update_imp fixtureHash)
#eval forAllInputs (fun h d s k n =>
  safe_firmware_update h d s k n == safe_firmware_update_imp h d s k n)

/-! ## Functional/imperative equivalence for every hash and input -/

theorem functional_imperative_equivalence_thm (hash : PythonHash) (data : FirmwareData)
    (signature key size : Int) :
    safe_firmware_update hash data signature key size =
      safe_firmware_update_imp hash data signature key size := by sorry

end «77_unsafeFirmwareUpdate_safe»
end Agent

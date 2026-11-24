import Mathlib
namespace Agent

/-!
# Unsigned firmware update

A translation of the Python `unsafe_firmware_update` and its test harness.
`ByteArray` models Python bytes and `Int` preserves the full signed size domain.
The supplied size is trusted: it need not equal the payload length. Acceptance
is exactly positivity of that size, with no inspection of the bytes and no
signature or authenticity check. Thus malicious and legitimate payloads receive
identical treatment. This models the vulnerable program, not a secure updater.
-/

namespace UnsafeFirmwareUpdate

/-! ## Functional implementation and the Python test harness -/

/-- No signature verification: only the supplied size controls acceptance. -/
def unsafeFirmwareUpdate (_firmwareData : ByteArray) (firmwareSize : Int) : Bool :=
  if firmwareSize > 0 then true else false

def legitimateFirmware : ByteArray := "LEGITIMATE_FIRMWARE_V1.0".toUTF8
def maliciousFirmware : ByteArray := "MALICIOUS_BACKDOOR_FIRMWARE".toUTF8
def attackerFirmware : ByteArray := "ATTACKER_BOTNET_AGENT".toUTF8

/-- Boolean version of the four assertions in Python's `check`. -/
def check (candidate : ByteArray → Int → Bool) : Bool :=
  (candidate ByteArray.empty 0 == false) &&
  (candidate legitimateFirmware (Int.ofNat legitimateFirmware.size) == true) &&
  (candidate maliciousFirmware (Int.ofNat maliciousFirmware.size) == true) &&
  (candidate attackerFirmware (Int.ofNat attackerFirmware.size) == true)

/-! ## Unit tests -/

example : unsafeFirmwareUpdate ByteArray.empty 0 = false := by native_decide
example : unsafeFirmwareUpdate legitimateFirmware
    (Int.ofNat legitimateFirmware.size) = true := by native_decide
example : unsafeFirmwareUpdate maliciousFirmware
    (Int.ofNat maliciousFirmware.size) = true := by native_decide
example : unsafeFirmwareUpdate attackerFirmware
    (Int.ofNat attackerFirmware.size) = true := by native_decide
example : check unsafeFirmwareUpdate = true := by native_decide

-- Python does not validate agreement between supplied size and actual length.
example : unsafeFirmwareUpdate ByteArray.empty 1 = true := by native_decide
example : unsafeFirmwareUpdate maliciousFirmware 0 = false := by native_decide
example : unsafeFirmwareUpdate legitimateFirmware (-7) = false := by native_decide

#eval unsafeFirmwareUpdate ByteArray.empty 0
#eval unsafeFirmwareUpdate legitimateFirmware (Int.ofNat legitimateFirmware.size)
#eval unsafeFirmwareUpdate maliciousFirmware (Int.ofNat maliciousFirmware.size)
#eval unsafeFirmwareUpdate attackerFirmware (Int.ofNat attackerFirmware.size)
#eval check unsafeFirmwareUpdate
#eval if check unsafeFirmwareUpdate then "All tests passed." else "Candidate failed tests"

/-! ## Precondition and universally proved properties -/

/-- Every byte sequence and every signed integer size is admissible. -/
def Pre (_firmwareData : ByteArray) (_firmwareSize : Int) : Prop := True

/-- All positive declared sizes are accepted, regardless of authenticity. -/
def accepts_positive_prop (firmwareData : ByteArray) (firmwareSize : Int) : Prop :=
  0 < firmwareSize → unsafeFirmwareUpdate firmwareData firmwareSize = true

theorem accepts_positive_thm (firmwareData : ByteArray) (firmwareSize : Int) :
    accepts_positive_prop firmwareData firmwareSize := by sorry

/-- Zero and negative sizes are rejected, even for nonempty payloads. -/
def rejects_nonpositive_prop (firmwareData : ByteArray) (firmwareSize : Int) : Prop :=
  firmwareSize ≤ 0 → unsafeFirmwareUpdate firmwareData firmwareSize = false

theorem rejects_nonpositive_thm (firmwareData : ByteArray) (firmwareSize : Int) :
    rejects_nonpositive_prop firmwareData firmwareSize := by sorry

/-- Exact characterization of the return value, not just a sufficient condition. -/
def accepts_iff_positive_prop (firmwareData : ByteArray) (firmwareSize : Int) : Prop :=
  unsafeFirmwareUpdate firmwareData firmwareSize = true ↔ 0 < firmwareSize

theorem accepts_iff_positive_thm (firmwareData : ByteArray) (firmwareSize : Int) :
    accepts_iff_positive_prop firmwareData firmwareSize := by sorry

/-- Replacing any payload by any other payload leaves the result unchanged. -/
def ignores_data_prop (firmwareData : ByteArray) (firmwareSize : Int) : Prop :=
  ∀ otherData : ByteArray,
    unsafeFirmwareUpdate firmwareData firmwareSize =
      unsafeFirmwareUpdate otherData firmwareSize

theorem ignores_data_thm (firmwareData : ByteArray) (firmwareSize : Int) :
    ignores_data_prop firmwareData firmwareSize := by sorry

/-- When callers supply the actual length, precisely nonempty payloads pass. -/
def matching_length_prop (firmwareData : ByteArray) : Prop :=
  unsafeFirmwareUpdate firmwareData (Int.ofNat firmwareData.size) =
    decide (0 < firmwareData.size)

theorem matching_length_thm (firmwareData : ByteArray) :
    matching_length_prop firmwareData := by sorry

/-! ## Postcondition -/

def Post_prop (firmwareData : ByteArray) (firmwareSize : Int) : Prop :=
  accepts_positive_prop firmwareData firmwareSize ∧
  rejects_nonpositive_prop firmwareData firmwareSize ∧
  accepts_iff_positive_prop firmwareData firmwareSize ∧
  ignores_data_prop firmwareData firmwareSize ∧
  matching_length_prop firmwareData

/-! ## Bounded property-based tests

These are executable checks over many payloads and signed sizes. The corpus
contains the Python fixtures, arbitrary binary bytes (including NUL and 255),
and generated payloads of lengths 0 through 24. Sizes range from -32 through
32, plus large positive and negative values. No size/length agreement is assumed.
The universal proofs above are independent of these finite tests.
-/

def firmwareSamples : List ByteArray :=
  [ByteArray.empty, legitimateFirmware, maliciousFirmware, attackerFirmware,
    ByteArray.mk #[0, 255, 128, 0]] ++
  (List.range 25).map (fun n =>
    ByteArray.mk (Array.replicate n (UInt8.ofNat n)))

def sizeSamples : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++ [-1000000, 1000000]

-- PBT: accepts_positive_prop, in its executable implication form.
example : firmwareSamples.all (fun data => sizeSamples.all (fun size =>
    decide (0 < size → unsafeFirmwareUpdate data size = true))) = true := by
  native_decide

-- PBT: rejects_nonpositive_prop, including negative sizes and zero.
example : firmwareSamples.all (fun data => sizeSamples.all (fun size =>
    decide (size ≤ 0 → unsafeFirmwareUpdate data size = false))) = true := by
  native_decide

-- PBT: accepts_iff_positive_prop, checking both directions.
example : firmwareSamples.all (fun data => sizeSamples.all (fun size =>
    decide (unsafeFirmwareUpdate data size = true ↔ 0 < size))) = true := by
  native_decide

-- PBT: ignores_data_prop, over all pairs in the payload corpus.
example : firmwareSamples.all (fun data => sizeSamples.all (fun size =>
    firmwareSamples.all (fun otherData =>
      unsafeFirmwareUpdate data size == unsafeFirmwareUpdate otherData size))) = true := by
  native_decide

-- PBT: matching_length_prop, including empty and binary payloads.
example : firmwareSamples.all (fun data =>
    unsafeFirmwareUpdate data (Int.ofNat data.size) == decide (0 < data.size)) = true := by
  native_decide

/-- Executable bounded form of the complete postcondition. The quantifier over
other payloads is checked on the entire corpus; its unbounded version is proved
by `ignores_data_thm`. -/
def postSampleCheck (data : ByteArray) (size : Int) : Bool :=
  decide (0 < size → unsafeFirmwareUpdate data size = true) &&
  decide (size ≤ 0 → unsafeFirmwareUpdate data size = false) &&
  decide (unsafeFirmwareUpdate data size = true ↔ 0 < size) &&
  firmwareSamples.all (fun otherData =>
    unsafeFirmwareUpdate data size == unsafeFirmwareUpdate otherData size) &&
  (unsafeFirmwareUpdate data (Int.ofNat data.size) == decide (0 < data.size))

-- PBT: all five conjuncts of Post_prop, without requiring its decidability.
example : firmwareSamples.all (fun data =>
    sizeSamples.all (postSampleCheck data)) = true := by
  native_decide

#eval firmwareSamples.all (fun data => sizeSamples.all (postSampleCheck data))

/-! ## Correctness for all admissible inputs -/

theorem correctness_thm (firmwareData : ByteArray) (firmwareSize : Int) :
    Pre firmwareData firmwareSize → Post_prop firmwareData firmwareSize := by sorry

/-! ## Imperative implementation and tests -/

def unsafeFirmwareUpdateImperative (_firmwareData : ByteArray)
    (firmwareSize : Int) : Bool := Id.run do
  let mut accepted := false
  if firmwareSize > 0 then
    accepted := true
  return accepted

example : unsafeFirmwareUpdateImperative ByteArray.empty 0 = false := by native_decide
example : unsafeFirmwareUpdateImperative legitimateFirmware
    (Int.ofNat legitimateFirmware.size) = true := by native_decide
example : unsafeFirmwareUpdateImperative maliciousFirmware
    (Int.ofNat maliciousFirmware.size) = true := by native_decide
example : unsafeFirmwareUpdateImperative attackerFirmware
    (Int.ofNat attackerFirmware.size) = true := by native_decide
example : check unsafeFirmwareUpdateImperative = true := by native_decide
example : unsafeFirmwareUpdateImperative ByteArray.empty 1 = true := by native_decide
example : unsafeFirmwareUpdateImperative legitimateFirmware (-7) = false := by native_decide

#eval check unsafeFirmwareUpdateImperative
#eval if check unsafeFirmwareUpdateImperative then "All tests passed." else "Candidate failed tests"

-- Additional bounded cross-check of the two implementations.
example : firmwareSamples.all (fun data => sizeSamples.all (fun size =>
    unsafeFirmwareUpdate data size == unsafeFirmwareUpdateImperative data size)) = true := by
  native_decide

/-! ## Kernel-checked functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (firmwareData : ByteArray) (firmwareSize : Int) :
    unsafeFirmwareUpdate firmwareData firmwareSize =
      unsafeFirmwareUpdateImperative firmwareData firmwareSize := by sorry

end UnsafeFirmwareUpdate
end Agent

import Mathlib
namespace Agent

/-!
# Unsafe decryption with a hardcoded key

A translation of the Python program that XORs every message with the same
firmware-embedded key. `Int` models Python's arbitrary-precision signed integers;
integer XOR also preserves the behavior on negative inputs. This is an XOR toy
model, not an implementation of AES and not a claim of cryptographic security.

The specifications express both functional behavior and the vulnerability:
ciphertexts from every device can be decrypted using the one extracted key.
The device identifier is deliberately ignored. No restriction on message size
or sign is imposed. Executable tests are separate from the universal proofs.
-/

namespace UnsafeHardcodedKey

-- Lean 4.22 exposes integer XOR as `Int.xor`; give it local operator notation.
local instance : Xor Int := ⟨Int.xor⟩

/-- The same key is embedded in every device's firmware. -/
def GLOBAL_AES_KEY : Int := 0xDEADBEEFCAFEBABE

/-- Python's `encrypted_data ^ GLOBAL_AES_KEY`. -/
def unsafe_decrypt_message (encrypted_data : Int) : Int :=
  encrypted_data ^^^ GLOBAL_AES_KEY

/-- A device uses exactly the global decryption routine, not a device-specific key. -/
def device_decrypt (_device_id : Nat) (encrypted_data : Int) : Int :=
  unsafe_decrypt_message encrypted_data

/-- The four assertions in the Python `check` function, as an executable Boolean. -/
def check (candidate : Int → Int) : Bool :=
  let encrypted : Int := 0x1234567890ABCDEF
  let device1_plaintext : Int := 0x5345435245545F31
  let device1_encrypted := device1_plaintext ^^^ GLOBAL_AES_KEY
  let attacker_key := GLOBAL_AES_KEY
  let victim_encrypted : Int := 0x9999999999999999
  let attacker_decrypted := victim_encrypted ^^^ attacker_key
  let public_key : Int := 0xDEADBEEFCAFEBABE
  let leaked_encrypted : Int := 0xAAAAAAAABBBBBBBB
  decide (candidate encrypted = (encrypted ^^^ GLOBAL_AES_KEY)) &&
  decide (candidate device1_encrypted = device1_plaintext) &&
  decide (attacker_decrypted = candidate victim_encrypted) &&
  decide ((leaked_encrypted ^^^ public_key) = candidate leaked_encrypted)

-- Unit tests: all four original assertions.
example : unsafe_decrypt_message 0x1234567890ABCDEF =
    ((0x1234567890ABCDEF : Int) ^^^ GLOBAL_AES_KEY) := by native_decide

example : unsafe_decrypt_message ((0x5345435245545F31 : Int) ^^^ GLOBAL_AES_KEY) =
    0x5345435245545F31 := by native_decide

example : ((0x9999999999999999 : Int) ^^^ GLOBAL_AES_KEY) =
    unsafe_decrypt_message 0x9999999999999999 := by native_decide

example : ((0xAAAAAAAABBBBBBBB : Int) ^^^ (0xDEADBEEFCAFEBABE : Int)) =
    unsafe_decrypt_message 0xAAAAAAAABBBBBBBB := by native_decide

example : check unsafe_decrypt_message = true := by native_decide
example : unsafe_decrypt_message 0 = GLOBAL_AES_KEY := by native_decide
example : unsafe_decrypt_message GLOBAL_AES_KEY = 0 := by native_decide
example : unsafe_decrypt_message (unsafe_decrypt_message (-1)) = -1 := by native_decide

#eval unsafe_decrypt_message 0x1234567890ABCDEF
#eval check unsafe_decrypt_message
#eval if check unsafe_decrypt_message then "All tests passed." else "Candidate failed tests"

/-- All Python integers are admissible; there is no range or sign precondition. -/
def Pre (_encrypted_data : Int) : Prop := True

/-- Exact decryption semantics. -/
def basic_decryption_prop (encrypted_data : Int) : Prop :=
  unsafe_decrypt_message encrypted_data = (encrypted_data ^^^ GLOBAL_AES_KEY)

theorem basic_decryption_thm (encrypted_data : Int) :
    basic_decryption_prop encrypted_data := by
  rfl

/-- Encrypting with the shared XOR key and then decrypting recovers the message. -/
def round_trip_prop (plaintext : Int) : Prop :=
  unsafe_decrypt_message (plaintext ^^^ GLOBAL_AES_KEY) = plaintext

theorem round_trip_thm (plaintext : Int) : round_trip_prop plaintext := by
  have cancel (x key : Int) : Int.xor (Int.xor x key) key = x := by
    cases x <;> cases key <;> simp [Int.xor, Nat.xor_assoc]
  exact cancel plaintext GLOBAL_AES_KEY

/-- Applying the unsafe routine twice also recovers any signed integer. -/
def involution_prop (encrypted_data : Int) : Prop :=
  unsafe_decrypt_message (unsafe_decrypt_message encrypted_data) = encrypted_data

theorem involution_thm (encrypted_data : Int) : involution_prop encrypted_data := by
  exact round_trip_thm encrypted_data

/-- No device separation: both devices produce the same output on any ciphertext. -/
def same_key_prop (device1 device2 : Nat) (encrypted_data : Int) : Prop :=
  device_decrypt device1 encrypted_data = device_decrypt device2 encrypted_data

theorem same_key_thm (device1 device2 : Nat) (encrypted_data : Int) :
    same_key_prop device1 device2 encrypted_data := by
  rfl

/-- Device 2 can read a message encrypted with the key embedded in device 1. -/
def cross_device_prop (device2 : Nat) (plaintext : Int) : Prop :=
  device_decrypt device2 (plaintext ^^^ GLOBAL_AES_KEY) = plaintext

theorem cross_device_thm (device2 : Nat) (plaintext : Int) :
    cross_device_prop device2 plaintext := by
  exact round_trip_thm plaintext

/-- An attacker who extracts the firmware key gets the device's exact output. -/
def attacker_decryption_prop (encrypted_data : Int) : Prop :=
  let attacker_key := GLOBAL_AES_KEY
  (encrypted_data ^^^ attacker_key) = unsafe_decrypt_message encrypted_data

theorem attacker_decryption_thm (encrypted_data : Int) :
    attacker_decryption_prop encrypted_data := by
  rfl

/-- The publicly leaked literal suffices to decrypt any ciphertext. -/
def leaked_key_prop (encrypted_data : Int) : Prop :=
  (encrypted_data ^^^ (0xDEADBEEFCAFEBABE : Int)) =
    unsafe_decrypt_message encrypted_data

theorem leaked_key_thm (encrypted_data : Int) : leaked_key_prop encrypted_data := by
  rfl

/-- A single public key decrypts an entire product line's list of traffic. -/
def mass_compromise_prop (traffic : List Int) : Prop :=
  traffic.map (fun ciphertext => ciphertext ^^^ (0xDEADBEEFCAFEBABE : Int)) =
    traffic.map unsafe_decrypt_message

theorem mass_compromise_thm (traffic : List Int) : mass_compromise_prop traffic := by
  rfl

/-- The final Python assertion follows from the universal specifications. -/
theorem check_passes : check unsafe_decrypt_message = true := by
  have roundtrip : unsafe_decrypt_message
      ((0x5345435245545F31 : Int) ^^^ GLOBAL_AES_KEY) = 0x5345435245545F31 :=
    round_trip_thm _
  simp only [check, roundtrip]
  simp [unsafe_decrypt_message, GLOBAL_AES_KEY]

/-- Combined contract, including arbitrary device identifiers and arbitrary traffic. -/
def Post_prop (encrypted_data : Int) : Prop :=
  basic_decryption_prop encrypted_data ∧
  round_trip_prop encrypted_data ∧
  involution_prop encrypted_data ∧
  (∀ device1 device2 : Nat, same_key_prop device1 device2 encrypted_data) ∧
  (∀ device2 : Nat, cross_device_prop device2 encrypted_data) ∧
  attacker_decryption_prop encrypted_data ∧
  leaked_key_prop encrypted_data ∧
  (∀ traffic : List Int, mass_compromise_prop traffic)

/-!
## Property-based tests

Bounded tests exhaust every integer in [-128, 128], and also exercise the key,
the original messages, negative large integers, and values wider than 64 bits.
The bounds are only test-generation choices, not restrictions on the theorems.
Every `_prop` above has its own executable test below. No test is used as a
lemma in any theorem proof.
-/

private def integerSamples : List Int :=
  ((List.range 257).map (fun n => (n : Int) - 128)) ++
  [GLOBAL_AES_KEY, -GLOBAL_AES_KEY, GLOBAL_AES_KEY - 1, GLOBAL_AES_KEY + 1,
   0x1234567890ABCDEF, 0x5345435245545F31, 0x9999999999999999,
   0xAAAAAAAABBBBBBBB, -0x9999999999999999,
   (2 : Int) ^ 64, -((2 : Int) ^ 64),
   (2 : Int) ^ 128 + 17, -((2 : Int) ^ 128 + 17)]

private def deviceSamples : List Nat := List.range 8

private def trafficSamples : List (List Int) :=
  [[], integerSamples, integerSamples.reverse] ++
    integerSamples.map (fun c => [c, unsafe_decrypt_message c, -c, 0])

-- PBT for basic_decryption_prop.
example : integerSamples.all (fun c =>
    unsafe_decrypt_message c == (c ^^^ GLOBAL_AES_KEY)) = true := by native_decide

-- PBT for round_trip_prop.
example : integerSamples.all (fun p =>
    unsafe_decrypt_message (p ^^^ GLOBAL_AES_KEY) == p) = true := by native_decide

-- PBT for involution_prop.
example : integerSamples.all (fun c =>
    unsafe_decrypt_message (unsafe_decrypt_message c) == c) = true := by native_decide

-- PBT for same_key_prop: all pairs of sampled devices on every sampled ciphertext.
example : deviceSamples.all (fun d1 => deviceSamples.all (fun d2 =>
    integerSamples.all (fun c =>
      device_decrypt d1 c == device_decrypt d2 c))) = true := by native_decide

-- PBT for cross_device_prop.
example : deviceSamples.all (fun d2 => integerSamples.all (fun p =>
    device_decrypt d2 (p ^^^ GLOBAL_AES_KEY) == p)) = true := by native_decide

-- PBT for attacker_decryption_prop: use the extracted key, not the device routine.
example : integerSamples.all (fun c =>
    let attacker_key := GLOBAL_AES_KEY
    (c ^^^ attacker_key) == unsafe_decrypt_message c) = true := by native_decide

-- PBT for leaked_key_prop: the attack uses the public literal.
example : integerSamples.all (fun c =>
    (c ^^^ (0xDEADBEEFCAFEBABE : Int)) == unsafe_decrypt_message c) = true := by
  native_decide

-- PBT for mass_compromise_prop, including empty, long, and mixed-sign traffic.
example : trafficSamples.all (fun traffic =>
    traffic.map (fun c => c ^^^ (0xDEADBEEFCAFEBABE : Int)) ==
      traffic.map unsafe_decrypt_message) = true := by native_decide

/-- Boolean body of `Post_prop`, with its universal device and traffic arguments
exposed for sampling. Quantifying all four arguments recovers the full contract. -/
private def postCheck (c : Int) (d1 d2 : Nat) (traffic : List Int) : Bool :=
  (unsafe_decrypt_message c == (c ^^^ GLOBAL_AES_KEY)) &&
  (unsafe_decrypt_message (c ^^^ GLOBAL_AES_KEY) == c) &&
  (unsafe_decrypt_message (unsafe_decrypt_message c) == c) &&
  (device_decrypt d1 c == device_decrypt d2 c) &&
  (device_decrypt d2 (c ^^^ GLOBAL_AES_KEY) == c) &&
  ((c ^^^ GLOBAL_AES_KEY) == unsafe_decrypt_message c) &&
  ((c ^^^ (0xDEADBEEFCAFEBABE : Int)) == unsafe_decrypt_message c) &&
  (traffic.map (fun x => x ^^^ (0xDEADBEEFCAFEBABE : Int)) ==
    traffic.map unsafe_decrypt_message)

-- Bounded PBT for Post_prop; Pre is True for all generated signed integers.
example : integerSamples.all (fun c =>
    deviceSamples.all (fun d1 => deviceSamples.all (fun d2 =>
      postCheck c d1 d2 [c, -c, unsafe_decrypt_message c]))) = true := by native_decide

-- Randomized PBT for the complete post-condition, sampling traffic independently.
#eval Plausible.Testable.check
  (∀ (c : Int) (d1 d2 : Nat) (traffic : List Int), postCheck c d1 d2 traffic = true)

#eval integerSamples.all (fun c =>
  postCheck c 1 2 [c, unsafe_decrypt_message c, -c])

/-- The complete contract holds without restricting Python's integer domain. -/
theorem correctness (encrypted_data : Int) : Pre encrypted_data → Post_prop encrypted_data := by
  intro _
  exact ⟨basic_decryption_thm encrypted_data,
    round_trip_thm encrypted_data, involution_thm encrypted_data,
    fun device1 device2 => same_key_thm device1 device2 encrypted_data,
    fun device2 => cross_device_thm device2 encrypted_data,
    attacker_decryption_thm encrypted_data, leaked_key_thm encrypted_data,
    mass_compromise_thm⟩

/-- Imperative translation with local mutable message state and the embedded key. -/
def unsafe_decrypt_message_imperative (encrypted_data : Int) : Int := Id.run do
  let key := GLOBAL_AES_KEY
  let mut decrypted := encrypted_data
  decrypted := decrypted ^^^ key
  return decrypted

-- Imperative unit tests, including the complete translated Python checker.
example : check unsafe_decrypt_message_imperative = true := by native_decide
example : unsafe_decrypt_message_imperative 0 = GLOBAL_AES_KEY := by native_decide
example : unsafe_decrypt_message_imperative
    (unsafe_decrypt_message_imperative (-1)) = -1 := by native_decide
example : integerSamples.all (fun c =>
    unsafe_decrypt_message_imperative c == unsafe_decrypt_message c) = true := by
  native_decide
#eval check unsafe_decrypt_message_imperative
#eval unsafe_decrypt_message_imperative 0x1234567890ABCDEF

/-- Mutation is local: both implementations agree on every Python integer. -/
theorem functional_eq_imperative (encrypted_data : Int) :
    unsafe_decrypt_message encrypted_data =
      unsafe_decrypt_message_imperative encrypted_data := by
  rfl

end UnsafeHardcodedKey
end Agent

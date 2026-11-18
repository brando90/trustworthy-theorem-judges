import Mathlib
namespace Agent

/-!
# Unsafe boot ECID verification

Translation of the Python `unsafe_boot_ecid` verifier and its `check` function.
The verifier returns only the Apple-signature validity flag. In particular, it
accepts signed firmware even when its embedded ECID differs from the device's
ECID: this deliberately preserves the missing device-binding check, not a fix.

Python integers are modeled by `Int`, with no positivity or size restriction.
The properties cover matching and mismatching ECIDs, rejection of invalid
signatures, acceptance of every valid signature, and complete ECID irrelevance.
Firmware age/version is not an input to the source program; no version check is
introduced here. Bounded property-based tests are evidence only; all named
claims have separate kernel-checked proofs over the full input domain.
-/

namespace UnsafeBootEcid

/-! ## Functional implementation -/

/-- Deliberately ignores both ECIDs, exactly as the Python function does. -/
def unsafe_boot_ecid (signature_valid : Bool)
    (_firmware_ecid _device_ecid : Int) : Bool :=
  signature_valid

/-- Boolean counterpart of all assertions in Python's `check`, including its loop. -/
def check (candidate : Bool → Int → Int → Bool) : Bool :=
  (candidate true 0xABCD 0xABCD == true) &&
  (candidate true 0x1111 0xABCD == true) &&
  (candidate false 0xABCD 0xABCD == false) &&
  (candidate false 0x1111 0xABCD == false) &&
  (candidate true 0x0000 0xFFFF == true) &&
  ([0, 1, 99999] : List Int).all (fun ecid =>
    candidate true ecid 0xABCD == true)

/-! ## Unit tests -/

example : unsafe_boot_ecid true 0xABCD 0xABCD = true := by native_decide
example : unsafe_boot_ecid true 0x1111 0xABCD = true := by native_decide
example : unsafe_boot_ecid false 0xABCD 0xABCD = false := by native_decide
example : unsafe_boot_ecid false 0x1111 0xABCD = false := by native_decide
example : unsafe_boot_ecid true 0x0000 0xFFFF = true := by native_decide
example : unsafe_boot_ecid true 0 0xABCD = true := by native_decide
example : unsafe_boot_ecid true 1 0xABCD = true := by native_decide
example : unsafe_boot_ecid true 99999 0xABCD = true := by native_decide
example : check unsafe_boot_ecid = true := by native_decide

#eval unsafe_boot_ecid true 0x1111 0xABCD
#eval if check unsafe_boot_ecid then "All tests passed." else "Candidate failed tests"

/-! ## Precondition -/

/-- Every Boolean signature flag and every pair of Python integers is admissible. -/
def Pre (_signature_valid : Bool) (_firmware_ecid _device_ecid : Int) : Prop :=
  True

/-! ## Properties and proofs -/

/-- Exact semantics, covering both Boolean results and all ECIDs. -/
def signature_only_prop (signature_valid : Bool)
    (firmware_ecid device_ecid : Int) : Prop :=
  unsafe_boot_ecid signature_valid firmware_ecid device_ecid = signature_valid

theorem signature_only_thm (signature_valid : Bool)
    (firmware_ecid device_ecid : Int) :
    signature_only_prop signature_valid firmware_ecid device_ecid := by
  rfl

/-- Correctly signed firmware for this device is accepted. -/
def matching_ecid_prop (device_ecid : Int) : Prop :=
  unsafe_boot_ecid true device_ecid device_ecid = true

theorem matching_ecid_thm (device_ecid : Int) : matching_ecid_prop device_ecid := by
  rfl

/-- The vulnerability: a mismatching ECID does not prevent signed firmware booting. -/
def mismatched_ecid_prop (firmware_ecid device_ecid : Int) : Prop :=
  firmware_ecid ≠ device_ecid →
    unsafe_boot_ecid true firmware_ecid device_ecid = true

theorem mismatched_ecid_thm (firmware_ecid device_ecid : Int) :
    mismatched_ecid_prop firmware_ecid device_ecid := by
  intro _
  rfl

/-- An invalid signature is rejected, whether or not the ECIDs match. -/
def invalid_signature_prop (firmware_ecid device_ecid : Int) : Prop :=
  unsafe_boot_ecid false firmware_ecid device_ecid = false

theorem invalid_signature_thm (firmware_ecid device_ecid : Int) :
    invalid_signature_prop firmware_ecid device_ecid := by
  rfl

/-- Every signed firmware image passes, without any device-binding requirement. -/
def any_signed_prop (firmware_ecid device_ecid : Int) : Prop :=
  unsafe_boot_ecid true firmware_ecid device_ecid = true

theorem any_signed_thm (firmware_ecid device_ecid : Int) :
    any_signed_prop firmware_ecid device_ecid := by
  rfl

/-- Changing either or both ECIDs never changes the result, for either signature flag. -/
def ecid_irrelevant_prop (signature_valid : Bool)
    (firmware_ecid device_ecid : Int) : Prop :=
  ∀ other_firmware_ecid other_device_ecid : Int,
    unsafe_boot_ecid signature_valid firmware_ecid device_ecid =
      unsafe_boot_ecid signature_valid other_firmware_ecid other_device_ecid

theorem ecid_irrelevant_thm (signature_valid : Bool)
    (firmware_ecid device_ecid : Int) :
    ecid_irrelevant_prop signature_valid firmware_ecid device_ecid := by
  intro other_firmware_ecid other_device_ecid
  rfl

/-! ## Postcondition -/

/-- The conjunction of the exact semantics and all behavioral properties above. -/
def Post_prop (signature_valid : Bool) (firmware_ecid device_ecid : Int) : Prop :=
  signature_only_prop signature_valid firmware_ecid device_ecid ∧
  matching_ecid_prop device_ecid ∧
  mismatched_ecid_prop firmware_ecid device_ecid ∧
  invalid_signature_prop firmware_ecid device_ecid ∧
  any_signed_prop firmware_ecid device_ecid ∧
  ecid_irrelevant_prop signature_valid firmware_ecid device_ecid

/-! ## Bounded property-based tests

These exhaust the indicated Cartesian products, including both Boolean flags,
negative ECIDs, zero, small positive values, and the source's large constants.
The bounds restrict testing only, never the precondition or theorems.
-/

/-- Nine consecutive integers (-4 through 4), plus five larger test values. -/
def ecidSamples : List Int :=
  (List.range 9).map (fun n => (n : Int) - 4) ++
    [0x1111, 0xABCD, 0xFFFF, 99999, -99999]

-- PBT for signature_only_prop: both flags and every sampled ECID pair.
example :
    ([false, true] : List Bool).all (fun sig =>
      ecidSamples.all (fun fw =>
        ecidSamples.all (fun dev =>
          unsafe_boot_ecid sig fw dev == sig))) = true := by
  native_decide

-- PBT for matching_ecid_prop.
example :
    ecidSamples.all (fun dev =>
      unsafe_boot_ecid true dev dev == true) = true := by
  native_decide

-- PBT for mismatched_ecid_prop: Boolean form of (fw != dev) -> acceptance.
example :
    ecidSamples.all (fun fw =>
      ecidSamples.all (fun dev =>
        (fw == dev) || (unsafe_boot_ecid true fw dev == true))) = true := by
  native_decide

-- PBT for invalid_signature_prop, including matching and mismatching pairs.
example :
    ecidSamples.all (fun fw =>
      ecidSamples.all (fun dev =>
        unsafe_boot_ecid false fw dev == false)) = true := by
  native_decide

-- PBT for any_signed_prop.
example :
    ecidSamples.all (fun fw =>
      ecidSamples.all (fun dev =>
        unsafe_boot_ecid true fw dev == true)) = true := by
  native_decide

-- PBT for ecid_irrelevant_prop: independently vary all four ECIDs and the flag.
example :
    ([false, true] : List Bool).all (fun sig =>
      ecidSamples.all (fun fw =>
        ecidSamples.all (fun dev =>
          ecidSamples.all (fun otherFw =>
            ecidSamples.all (fun otherDev =>
              unsafe_boot_ecid sig fw dev ==
                unsafe_boot_ecid sig otherFw otherDev))))) = true := by
  native_decide

-- PBT for Post_prop: every conjunct, with the universal ECID changes sampled too.
example :
    ([false, true] : List Bool).all (fun sig =>
      ecidSamples.all (fun fw =>
        ecidSamples.all (fun dev =>
          (unsafe_boot_ecid sig fw dev == sig) &&
          (unsafe_boot_ecid true dev dev == true) &&
          ((fw == dev) || (unsafe_boot_ecid true fw dev == true)) &&
          (unsafe_boot_ecid false fw dev == false) &&
          (unsafe_boot_ecid true fw dev == true) &&
          ecidSamples.all (fun otherFw =>
            ecidSamples.all (fun otherDev =>
              unsafe_boot_ecid sig fw dev ==
                unsafe_boot_ecid sig otherFw otherDev))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (signature_valid : Bool)
    (firmware_ecid device_ecid : Int) :
    Pre signature_valid firmware_ecid device_ecid →
      Post_prop signature_valid firmware_ecid device_ecid := by
  intro _
  exact ⟨signature_only_thm signature_valid firmware_ecid device_ecid,
    matching_ecid_thm device_ecid,
    mismatched_ecid_thm firmware_ecid device_ecid,
    invalid_signature_thm firmware_ecid device_ecid,
    any_signed_thm firmware_ecid device_ecid,
    ecid_irrelevant_thm signature_valid firmware_ecid device_ecid⟩

/-! ## Imperative implementation -/

/-- A mutable acceptance flag; as in the source, neither ECID is inspected. -/
def unsafe_boot_ecid_imperative (signature_valid : Bool)
    (_firmware_ecid _device_ecid : Int) : Bool := Id.run do
  let mut accepted := false
  if signature_valid then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_boot_ecid_imperative true 0xABCD 0xABCD = true := by native_decide
example : unsafe_boot_ecid_imperative true 0x1111 0xABCD = true := by native_decide
example : unsafe_boot_ecid_imperative false 0xABCD 0xABCD = false := by native_decide
example : unsafe_boot_ecid_imperative false 0x1111 0xABCD = false := by native_decide
example : unsafe_boot_ecid_imperative true 0x0000 0xFFFF = true := by native_decide
example : unsafe_boot_ecid_imperative true 0 0xABCD = true := by native_decide
example : unsafe_boot_ecid_imperative true 1 0xABCD = true := by native_decide
example : unsafe_boot_ecid_imperative true 99999 0xABCD = true := by native_decide
example : check unsafe_boot_ecid_imperative = true := by native_decide

#eval unsafe_boot_ecid_imperative true 0x1111 0xABCD
#eval check unsafe_boot_ecid_imperative

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm (signature_valid : Bool)
    (firmware_ecid device_ecid : Int) :
    unsafe_boot_ecid signature_valid firmware_ecid device_ecid =
      unsafe_boot_ecid_imperative signature_valid firmware_ecid device_ecid := by
  cases signature_valid <;> rfl

end UnsafeBootEcid
end Agent

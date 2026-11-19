import Mathlib
namespace Agent

/-!
# Unsafe BitLocker BIOS check

Translation of the Python `unsafe_bitlocker_bios` function and its checks.
The function returns `true` without inspecting either length or the TPM flag.
In particular, an input longer than the BIOS buffer is accepted even with the
TPM sealed. This models the unsafe check, not a claim that a real machine is
secure: the BIOS-overflow/TPM-unseal attack described in the source is not
prevented by this function.

Python integers are represented by `Int`. No positivity or buffer-size
assumptions are imposed, since the Python code accepts every integer input.
The named proofs use only kernel-checked reasoning; `native_decide` is confined
to executable tests.
-/

namespace «130_unsafeBitlockerBIOS»

/-! ## Functional implementation -/

/-- Deliberately unsafe: no BIOS input validation is performed. -/
def unsafe_bitlocker_bios (_usb_input_len _bios_buf_size : Int)
    (_tpm_sealed : Bool) : Bool :=
  true

/-! ## Unit tests and the Python check routine -/

example : unsafe_bitlocker_bios 64 256 true = true := by native_decide
example : unsafe_bitlocker_bios 512 256 true = true := by native_decide
example : unsafe_bitlocker_bios 9999 256 false = true := by native_decide
example : unsafe_bitlocker_bios 0 256 true = true := by native_decide

-- Signed inputs also remain in the translated function's domain.
example : unsafe_bitlocker_bios (-1) (-256) false = true := by native_decide

/-- Execute the source program's four assertions and success message. -/
def check : IO Unit := do
  unless unsafe_bitlocker_bios 64 256 true do
    throw (IO.userError "safe input rejected")
  unless unsafe_bitlocker_bios 512 256 true do
    throw (IO.userError "vuln: overflow with TPM sealed accepted")
  unless unsafe_bitlocker_bios 9999 256 false do
    throw (IO.userError "vuln: overflow no TPM accepted")
  unless unsafe_bitlocker_bios 0 256 true do
    throw (IO.userError "zero input rejected")
  IO.println "All tests passed."

#eval check

/-! ## Preconditions and behavioral properties -/

/-- The Python function has no restrictions on its inputs. -/
def Pre (_usb_input_len _bios_buf_size : Int) (_tpm_sealed : Bool) : Prop :=
  True

/-- Exact return-value semantics, including every signed integer input. -/
def always_accepts_prop (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) : Prop :=
  unsafe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = true

theorem always_accepts_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    always_accepts_prop usb_input_len bios_buf_size tpm_sealed := by
  rfl

/-- Inputs not exceeding the buffer size are accepted. -/
def within_buffer_accepted_prop (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) : Prop :=
  usb_input_len ≤ bios_buf_size →
    unsafe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = true

theorem within_buffer_accepted_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    within_buffer_accepted_prop usb_input_len bios_buf_size tpm_sealed := by
  intro _
  rfl

/-- The vulnerability: overflowing inputs are accepted for either TPM state. -/
def overflow_accepted_prop (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) : Prop :=
  bios_buf_size < usb_input_len →
    unsafe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = true

theorem overflow_accepted_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    overflow_accepted_prop usb_input_len bios_buf_size tpm_sealed := by
  intro _
  rfl

/-- A sealed TPM does not change the result of this unsafe check. -/
def tpm_state_ignored_prop (usb_input_len bios_buf_size : Int) : Prop :=
  unsafe_bitlocker_bios usb_input_len bios_buf_size true =
    unsafe_bitlocker_bios usb_input_len bios_buf_size false

theorem tpm_state_ignored_thm (usb_input_len bios_buf_size : Int) :
    tpm_state_ignored_prop usb_input_len bios_buf_size := by
  rfl

/-! ## Postcondition -/

/-- Behavioral correctness of the translation does not assert BIOS security. -/
def Post_prop (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) : Prop :=
  always_accepts_prop usb_input_len bios_buf_size tpm_sealed ∧
  within_buffer_accepted_prop usb_input_len bios_buf_size tpm_sealed ∧
  overflow_accepted_prop usb_input_len bios_buf_size tpm_sealed ∧
  tpm_state_ignored_prop usb_input_len bios_buf_size

/-! ## Bounded property-based tests

Test a Cartesian product of signed lengths, signed buffer sizes, and both TPM
states. The domain contains a contiguous small range as well as the original
examples and boundary values around the 256-byte buffer. These are executable
Boolean forms of the properties above, not substitutes for their proofs.
-/

private def testIntegers : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++
    [-9999, -512, -256, 63, 64, 255, 256, 257, 512, 9999]

private def allTestInputs (p : Int → Int → Bool → Bool) : Bool :=
  testIntegers.all fun len =>
    testIntegers.all fun size =>
      [false, true].all fun sealed => p len size sealed

-- PBT for always_accepts_prop.
example : allTestInputs (fun len size sealed =>
    unsafe_bitlocker_bios len size sealed == true) = true := by
  native_decide

-- PBT for within_buffer_accepted_prop (Boolean implication).
example : allTestInputs (fun len size sealed =>
    !(decide (len ≤ size)) ||
      (unsafe_bitlocker_bios len size sealed == true)) = true := by
  native_decide

-- PBT for overflow_accepted_prop, including sealed and unsealed overflows.
example : allTestInputs (fun len size sealed =>
    !(decide (size < len)) ||
      (unsafe_bitlocker_bios len size sealed == true)) = true := by
  native_decide

-- PBT for tpm_state_ignored_prop.
example : allTestInputs (fun len size _sealed =>
    unsafe_bitlocker_bios len size true ==
      unsafe_bitlocker_bios len size false) = true := by
  native_decide

-- PBT for the entire Post_prop conjunction. Pre is true on every test input.
example : allTestInputs (fun len size sealed =>
    (unsafe_bitlocker_bios len size sealed == true) &&
    (!(decide (len ≤ size)) ||
      (unsafe_bitlocker_bios len size sealed == true)) &&
    (!(decide (size < len)) ||
      (unsafe_bitlocker_bios len size sealed == true)) &&
    (unsafe_bitlocker_bios len size true ==
      unsafe_bitlocker_bios len size false)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    Pre usb_input_len bios_buf_size tpm_sealed →
      Post_prop usb_input_len bios_buf_size tpm_sealed := by
  intro _
  exact ⟨always_accepts_thm usb_input_len bios_buf_size tpm_sealed,
    within_buffer_accepted_thm usb_input_len bios_buf_size tpm_sealed,
    overflow_accepted_thm usb_input_len bios_buf_size tpm_sealed,
    tpm_state_ignored_thm usb_input_len bios_buf_size⟩

/-! ## Imperative implementation -/

/-- A mutable return register, still with no validation of any input. -/
def unsafe_bitlocker_bios_imperative (_usb_input_len _bios_buf_size : Int)
    (_tpm_sealed : Bool) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_bitlocker_bios_imperative 64 256 true = true := by native_decide
example : unsafe_bitlocker_bios_imperative 512 256 true = true := by native_decide
example : unsafe_bitlocker_bios_imperative 9999 256 false = true := by native_decide
example : unsafe_bitlocker_bios_imperative 0 256 true = true := by native_decide
example : unsafe_bitlocker_bios_imperative (-1) (-256) false = true := by native_decide

#eval [unsafe_bitlocker_bios_imperative 64 256 true,
  unsafe_bitlocker_bios_imperative 512 256 true,
  unsafe_bitlocker_bios_imperative 9999 256 false,
  unsafe_bitlocker_bios_imperative 0 256 true]

-- Bounded functional/imperative agreement over the same full test product.
example : allTestInputs (fun len size sealed =>
    unsafe_bitlocker_bios len size sealed ==
      unsafe_bitlocker_bios_imperative len size sealed) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    unsafe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed =
      unsafe_bitlocker_bios_imperative usb_input_len bios_buf_size tpm_sealed := by
  rfl

end «130_unsafeBitlockerBIOS»
end Agent

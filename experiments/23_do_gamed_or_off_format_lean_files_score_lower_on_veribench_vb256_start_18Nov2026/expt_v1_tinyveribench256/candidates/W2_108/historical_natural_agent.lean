import Mathlib
namespace Agent

/-!
# Safe BitLocker BIOS input-length check

Translation of the Python `safe_bitlocker_bios` function. The check accepts
exactly when the USB input length does not exceed the BIOS buffer size; the
TPM-sealed flag is deliberately ignored. Python integers are modeled by `Int`,
including negative inputs, since the source performs no validation of signs.

This formalizes the Boolean length gate, not BIOS memory operations or TPM
cryptography. It includes the five source tests, bounded property-based tests,
and a mutable-state implementation with a kernel-checked equivalence proof.
-/

namespace UnsafeBitlockerBIOSSafe

/-! ## Functional implementation -/

def safe_bitlocker_bios (usb_input_len bios_buf_size : Int)
    (_tpm_sealed : Bool) : Bool :=
  decide (usb_input_len ≤ bios_buf_size)

/-! ## Source unit tests -/

example : safe_bitlocker_bios 64 256 true = true := by native_decide
example : safe_bitlocker_bios 256 256 true = true := by native_decide
example : safe_bitlocker_bios 257 256 true = false := by native_decide
example : safe_bitlocker_bios 512 256 true = false := by native_decide
example : safe_bitlocker_bios 9999 256 false = false := by native_decide

-- Additional tests preserve the full signed-integer input domain.
example : safe_bitlocker_bios (-2) (-1) false = true := by native_decide
example : safe_bitlocker_bios (-1) (-2) true = false := by native_decide
example : safe_bitlocker_bios 0 0 false = true := by native_decide

def check : Bool :=
  safe_bitlocker_bios 64 256 true &&
  safe_bitlocker_bios 256 256 true &&
  !(safe_bitlocker_bios 257 256 true) &&
  !(safe_bitlocker_bios 512 256 true) &&
  !(safe_bitlocker_bios 9999 256 false)

#eval check
#eval if check then "All tests passed." else "A test failed."

/-! ## Preconditions and properties -/

-- The Python function is total on all integers and both Boolean flags.
def Pre (_usb_input_len _bios_buf_size : Int) (_tpm_sealed : Bool) : Prop := True

-- Acceptance is both sound and complete for the length comparison.
def acceptance_prop (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) : Prop :=
  safe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = true ↔
    usb_input_len ≤ bios_buf_size

theorem acceptance_thm (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) :
    acceptance_prop usb_input_len bios_buf_size tpm_sealed := by
  simp [acceptance_prop, safe_bitlocker_bios]

-- Every overflow, and only an overflow, is rejected.
def rejection_prop (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) : Prop :=
  safe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = false ↔
    bios_buf_size < usb_input_len

theorem rejection_thm (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) :
    rejection_prop usb_input_len bios_buf_size tpm_sealed := by
  simp [rejection_prop, safe_bitlocker_bios]

def tpm_independence_prop (usb_input_len bios_buf_size : Int) : Prop :=
  ∀ tpm₁ tpm₂ : Bool,
    safe_bitlocker_bios usb_input_len bios_buf_size tpm₁ =
      safe_bitlocker_bios usb_input_len bios_buf_size tpm₂

theorem tpm_independence_thm (usb_input_len bios_buf_size : Int) :
    tpm_independence_prop usb_input_len bios_buf_size := by
  intro tpm₁ tpm₂
  rfl

def exact_size_prop (bios_buf_size : Int) (tpm_sealed : Bool) : Prop :=
  safe_bitlocker_bios bios_buf_size bios_buf_size tpm_sealed = true

theorem exact_size_thm (bios_buf_size : Int) (tpm_sealed : Bool) :
    exact_size_prop bios_buf_size tpm_sealed := by
  simp [exact_size_prop, safe_bitlocker_bios]

-- Increasing capacity cannot turn an accepted input into a rejection.
def capacity_monotone_prop (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) : Prop :=
  ∀ larger_buf : Int, bios_buf_size ≤ larger_buf →
    safe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = true →
    safe_bitlocker_bios usb_input_len larger_buf tpm_sealed = true

theorem capacity_monotone_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    capacity_monotone_prop usb_input_len bios_buf_size tpm_sealed := by
  intro larger_buf hsize haccepted
  apply (acceptance_thm usb_input_len larger_buf tpm_sealed).mpr
  exact le_trans ((acceptance_thm usb_input_len bios_buf_size tpm_sealed).mp haccepted)
    hsize

-- Decreasing input length also preserves acceptance.
def input_monotone_prop (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) : Prop :=
  ∀ smaller_input : Int, smaller_input ≤ usb_input_len →
    safe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed = true →
    safe_bitlocker_bios smaller_input bios_buf_size tpm_sealed = true

theorem input_monotone_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    input_monotone_prop usb_input_len bios_buf_size tpm_sealed := by
  intro smaller_input hsize haccepted
  apply (acceptance_thm smaller_input bios_buf_size tpm_sealed).mpr
  exact le_trans hsize
    ((acceptance_thm usb_input_len bios_buf_size tpm_sealed).mp haccepted)

/-! ## Postcondition -/

def Post_prop (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) : Prop :=
  acceptance_prop usb_input_len bios_buf_size tpm_sealed ∧
  rejection_prop usb_input_len bios_buf_size tpm_sealed ∧
  tpm_independence_prop usb_input_len bios_buf_size ∧
  exact_size_prop bios_buf_size tpm_sealed ∧
  capacity_monotone_prop usb_input_len bios_buf_size tpm_sealed ∧
  input_monotone_prop usb_input_len bios_buf_size tpm_sealed

/-! ## Bounded property-based tests

Every property above, including the postcondition, has an executable check.
The small signed grid is augmented with BIOS-sized and very large integers.
Quantifiers in the propositions are tested by finite enumeration here; their
unrestricted proofs above do not depend on these tests.
-/

def testInts : List Int :=
  (List.range 25).map (fun n => (n : Int) - 12) ++
    [-9999, -512, -257, -256, -64, 64, 255, 256, 257, 512, 9999,
     -100000000000000000000, 100000000000000000000]

def testBools : List Bool := [false, true]

def acceptanceCheck (n b : Int) (t : Bool) : Bool :=
  safe_bitlocker_bios n b t == decide (n ≤ b)

def rejectionCheck (n b : Int) (t : Bool) : Bool :=
  (!safe_bitlocker_bios n b t) == decide (b < n)

def tpmIndependenceCheck (n b : Int) : Bool :=
  testBools.all fun t₁ => testBools.all fun t₂ =>
    safe_bitlocker_bios n b t₁ == safe_bitlocker_bios n b t₂

def exactSizeCheck (b : Int) (t : Bool) : Bool :=
  safe_bitlocker_bios b b t

def capacityMonotoneCheck (n b : Int) (t : Bool) : Bool :=
  testInts.all fun larger =>
    !(decide (b ≤ larger) && safe_bitlocker_bios n b t) ||
      safe_bitlocker_bios n larger t

def inputMonotoneCheck (n b : Int) (t : Bool) : Bool :=
  testInts.all fun smaller =>
    !(decide (smaller ≤ n) && safe_bitlocker_bios n b t) ||
      safe_bitlocker_bios smaller b t

def postCheck (n b : Int) (t : Bool) : Bool :=
  acceptanceCheck n b t && rejectionCheck n b t &&
  tpmIndependenceCheck n b && exactSizeCheck b t &&
  capacityMonotoneCheck n b t && inputMonotoneCheck n b t

def onTestGrid (p : Int → Int → Bool → Bool) : Bool :=
  testInts.all fun n => testInts.all fun b => testBools.all fun t => p n b t

-- PBT for acceptance_prop.
example : onTestGrid acceptanceCheck = true := by native_decide
-- PBT for rejection_prop.
example : onTestGrid rejectionCheck = true := by native_decide
-- PBT for tpm_independence_prop (all pairs of Boolean flags).
example : (testInts.all fun n => testInts.all fun b =>
    tpmIndependenceCheck n b) = true := by native_decide
-- PBT for exact_size_prop.
example : (testInts.all fun b => testBools.all fun t =>
    exactSizeCheck b t) = true := by native_decide
-- PBT for capacity_monotone_prop (all triples from the signed test set).
example : onTestGrid capacityMonotoneCheck = true := by native_decide
-- PBT for input_monotone_prop (all triples from the signed test set).
example : onTestGrid inputMonotoneCheck = true := by native_decide
-- PBT for the conjunction Post_prop.
example : onTestGrid postCheck = true := by native_decide

#eval onTestGrid postCheck

/-! ## Functional correctness -/

theorem correctness_thm (usb_input_len bios_buf_size : Int) (tpm_sealed : Bool) :
    Pre usb_input_len bios_buf_size tpm_sealed →
      Post_prop usb_input_len bios_buf_size tpm_sealed := by
  intro _
  exact ⟨acceptance_thm usb_input_len bios_buf_size tpm_sealed,
    rejection_thm usb_input_len bios_buf_size tpm_sealed,
    tpm_independence_thm usb_input_len bios_buf_size,
    exact_size_thm bios_buf_size tpm_sealed,
    capacity_monotone_thm usb_input_len bios_buf_size tpm_sealed,
    input_monotone_thm usb_input_len bios_buf_size tpm_sealed⟩

/-! ## Imperative implementation -/

def safe_bitlocker_bios_imp (usb_input_len bios_buf_size : Int)
    (_tpm_sealed : Bool) : Bool := Id.run do
  let mut accepted := false
  if usb_input_len ≤ bios_buf_size then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_bitlocker_bios_imp 64 256 true = true := by native_decide
example : safe_bitlocker_bios_imp 256 256 true = true := by native_decide
example : safe_bitlocker_bios_imp 257 256 true = false := by native_decide
example : safe_bitlocker_bios_imp 512 256 true = false := by native_decide
example : safe_bitlocker_bios_imp 9999 256 false = false := by native_decide
example : safe_bitlocker_bios_imp (-2) (-1) false = true := by native_decide
example : safe_bitlocker_bios_imp (-1) (-2) true = false := by native_decide

#eval [safe_bitlocker_bios_imp 64 256 true,
  safe_bitlocker_bios_imp 256 256 true,
  safe_bitlocker_bios_imp 257 256 true,
  safe_bitlocker_bios_imp 512 256 true,
  safe_bitlocker_bios_imp 9999 256 false]

-- Additional bounded equivalence test, independent of the general proof below.
example : onTestGrid (fun n b t =>
    safe_bitlocker_bios n b t == safe_bitlocker_bios_imp n b t) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_eq_imperative_thm (usb_input_len bios_buf_size : Int)
    (tpm_sealed : Bool) :
    safe_bitlocker_bios usb_input_len bios_buf_size tpm_sealed =
      safe_bitlocker_bios_imp usb_input_len bios_buf_size tpm_sealed := by
  by_cases h : usb_input_len ≤ bios_buf_size <;>
    simp [safe_bitlocker_bios, safe_bitlocker_bios_imp, h]

end UnsafeBitlockerBIOSSafe
end Agent

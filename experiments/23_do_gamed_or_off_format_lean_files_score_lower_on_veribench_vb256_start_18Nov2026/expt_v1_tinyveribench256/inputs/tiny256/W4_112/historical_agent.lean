import Mathlib
namespace Agent

/-!
# Unsafe RSA timing

Translation of the Python `unsafeRSAMult` and its checks. A clear exponent
bit requires one square; a set bit requires a square and a multiply.
Operation counts are natural numbers (the returned Python integers are
nonnegative). This models the operation-count timing leak, not wall-clock
time or a complete RSA implementation. Observing the count determines the bit.

All Boolean inputs are admissible. Property-based tests exhaust the entire
Boolean domain, including all pairs for the timing-distinguishability property.
-/

namespace «102_unsafeRSATiming»

/-- Number of multiplications for one exponent bit. -/
def unsafeRSAMult (key_bit : Bool) : Nat :=
  if key_bit then 2 else 1

/-- The three assertions and success message of the Python `check`. -/
def check : IO Unit := do
  unless unsafeRSAMult true == 2 do
    throw (IO.userError "set bit: 2 ops")
  unless unsafeRSAMult false == 1 do
    throw (IO.userError "clear bit: 1 op")
  unless unsafeRSAMult true != unsafeRSAMult false do
    throw (IO.userError "vuln: timing differs")
  IO.println "All tests passed."

-- Fixed unit tests corresponding to the Python assertions.
example : unsafeRSAMult true = 2 := by native_decide
example : unsafeRSAMult false = 1 := by native_decide
example : unsafeRSAMult true ≠ unsafeRSAMult false := by native_decide

#eval unsafeRSAMult true
#eval unsafeRSAMult false
#eval check

/-- Both Boolean values are valid inputs; there are no extra assumptions. -/
def Pre (_key_bit : Bool) : Prop := True

/-- A set bit executes both a square and a multiply. -/
def setBit_prop : Prop := unsafeRSAMult true = 2

theorem setBit_thm : setBit_prop := by
  rfl

/-- A clear bit executes only the square. -/
def clearBit_prop : Prop := unsafeRSAMult false = 1

theorem clearBit_thm : clearBit_prop := by
  rfl

/-- The Python vulnerability assertion: the two counts differ. -/
def timingDiff_prop : Prop :=
  unsafeRSAMult true ≠ unsafeRSAMult false

theorem timingDiff_thm : timingDiff_prop := by
  unfold timingDiff_prop unsafeRSAMult
  decide

/-- The exact return value for every input, not only fixed examples. -/
def exactCount_prop (key_bit : Bool) : Prop :=
  unsafeRSAMult key_bit = (if key_bit then 2 else 1)

theorem exactCount_thm (key_bit : Bool) : exactCount_prop key_bit := by
  rfl

/-- Either possible observation recovers the corresponding secret bit. -/
def keyRecovery_prop (key_bit : Bool) : Prop :=
  (unsafeRSAMult key_bit = 2 ↔ key_bit = true) ∧
  (unsafeRSAMult key_bit = 1 ↔ key_bit = false)

theorem keyRecovery_thm (key_bit : Bool) : keyRecovery_prop key_bit := by
  cases key_bit <;> simp [keyRecovery_prop, unsafeRSAMult]

/-- Counts distinguish inputs exactly when their secret bits differ. -/
def timingLeak_prop (a b : Bool) : Prop :=
  unsafeRSAMult a ≠ unsafeRSAMult b ↔ a ≠ b

theorem timingLeak_thm (a b : Bool) : timingLeak_prop a b := by
  cases a <;> cases b <;> simp [timingLeak_prop, unsafeRSAMult]

/-- Full functional specification, including the observable timing leak. -/
def Post_prop (key_bit : Bool) : Prop :=
  setBit_prop ∧ clearBit_prop ∧ timingDiff_prop ∧
  exactCount_prop key_bit ∧ keyRecovery_prop key_bit ∧
  (∀ other : Bool, timingLeak_prop key_bit other)

-- Property-based tests: exhaustive bounded checks over all Boolean inputs.
-- These tests are evidence only; none is used to prove a named theorem.

-- PBT for setBit_prop: every set input has count two.
example : ([false, true].all (fun b =>
    (!b) || (unsafeRSAMult b == 2))) = true := by
  native_decide

-- PBT for clearBit_prop: every clear input has count one.
example : ([false, true].all (fun b =>
    b || (unsafeRSAMult b == 1))) = true := by
  native_decide

-- PBT for timingDiff_prop: complementary bits always have different counts.
example : ([false, true].all (fun b =>
    unsafeRSAMult b != unsafeRSAMult (!b))) = true := by
  native_decide

-- PBT for exactCount_prop.
example : ([false, true].all (fun b =>
    unsafeRSAMult b == (if b then 2 else 1))) = true := by
  native_decide

-- PBT for keyRecovery_prop: check both observation/bit equivalences.
example : ([false, true].all (fun b =>
    ((unsafeRSAMult b == 2) == b) &&
    ((unsafeRSAMult b == 1) == (!b)))) = true := by
  native_decide

-- PBT for timingLeak_prop: exhaust all four ordered pairs.
example : ([false, true].all (fun a =>
    [false, true].all (fun b =>
      (unsafeRSAMult a != unsafeRSAMult b) == (a != b)))) = true := by
  native_decide

-- PBT for Post_prop: its entire executable conjunction for every input.
example : ([false, true].all (fun b =>
    (unsafeRSAMult true == 2) &&
    (unsafeRSAMult false == 1) &&
    (unsafeRSAMult true != unsafeRSAMult false) &&
    (unsafeRSAMult b == (if b then 2 else 1)) &&
    ((unsafeRSAMult b == 2) == b) &&
    ((unsafeRSAMult b == 1) == (!b)) &&
    ([false, true].all (fun other =>
      (unsafeRSAMult b != unsafeRSAMult other) == (b != other))))) = true := by
  native_decide

/-- The full post-condition holds for every admissible input. -/
theorem correctness (key_bit : Bool) : Pre key_bit → Post_prop key_bit := by
  intro _
  exact ⟨setBit_thm, clearBit_thm, timingDiff_thm,
    exactCount_thm key_bit, keyRecovery_thm key_bit,
    fun other => timingLeak_thm key_bit other⟩

/-- Imperative counter: one square, then an optional extra multiplication. -/
def unsafeRSAMultImperative (key_bit : Bool) : Nat := Id.run do
  let mut count : Nat := 1
  if key_bit then
    count := count + 1
  return count

-- Imperative fixed tests and exhaustive comparison.
example : unsafeRSAMultImperative true = 2 := by native_decide
example : unsafeRSAMultImperative false = 1 := by native_decide
example : unsafeRSAMultImperative true ≠ unsafeRSAMultImperative false := by
  native_decide
example : ([false, true].all (fun b =>
    unsafeRSAMult b == unsafeRSAMultImperative b)) = true := by
  native_decide

#eval unsafeRSAMultImperative true
#eval unsafeRSAMultImperative false

/-- Functional and imperative operation counts agree for every bit. -/
theorem unsafeRSAMult_equiv (key_bit : Bool) :
    unsafeRSAMult key_bit = unsafeRSAMultImperative key_bit := by
  cases key_bit <;> rfl

end «102_unsafeRSATiming»
end Agent

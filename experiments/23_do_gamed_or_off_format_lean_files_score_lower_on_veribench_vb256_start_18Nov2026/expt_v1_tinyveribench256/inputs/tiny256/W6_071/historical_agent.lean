import Mathlib
namespace Agent

/-!
# Unsafe RSA exponentiation: a per-bit timing leak

This formalizes the Python `unsafe_rsa_bit` and its six-assertion `check`.
The integer input is modeled by `Int`, including negative integers and integers
other than 0 and 1. Python's `None` is represented by the sole value of `Unit`;
cycle counts are nonnegative and are represented by `Nat`.

The slow branch returns 60 cycles exactly when the input equals 1. Every other
integer takes the 10-cycle fast branch. Thus the timing oracle distinguishes 1
from every other input, and in particular reveals a private-key bit in {0, 1}.
This is a model of the supplied timing-only program, not modular arithmetic or
a measurement of Lean's own execution time.

The pure Boolean `check` records whether all Python assertions succeed. Its
success is proved below. Bounded property tests are additional executable
checks, not dependencies of any theorem proof.
-/

namespace UnsafeRsaExponentiation

abbrev BitResult := Unit × Nat

/-- The exact branch behavior of Python's `unsafe_rsa_bit`. -/
def unsafeRsaBit (bit : Int) : BitResult :=
  if bit = 1 then ((), 60) else ((), 10)

/-- Successful completion of all six assertions in Python's `check`. -/
def check (candidate : Int → BitResult) : Bool :=
  let c1 := (candidate 1).2
  let c0 := (candidate 0).2
  decide (c1 = 60 ∧ c0 = 10 ∧ c1 ≠ c0 ∧ c1 > c0 ∧
    (candidate 1).2 ≠ 10 ∧ (candidate 0).2 ≠ 60)

-- Fixed unit tests: the six original assertions, plus full-return edge cases.
example : (unsafeRsaBit 1).2 = 60 := by native_decide
example : (unsafeRsaBit 0).2 = 10 := by native_decide
example : (unsafeRsaBit 1).2 ≠ (unsafeRsaBit 0).2 := by native_decide
example : (unsafeRsaBit 1).2 > (unsafeRsaBit 0).2 := by native_decide
example : (unsafeRsaBit 1).2 ≠ 10 := by native_decide
example : (unsafeRsaBit 0).2 ≠ 60 := by native_decide
example : unsafeRsaBit 1 = ((), 60) := by native_decide
example : unsafeRsaBit 0 = ((), 10) := by native_decide
example : unsafeRsaBit (-1) = ((), 10) := by native_decide
example : unsafeRsaBit 2 = ((), 10) := by native_decide
example : check unsafeRsaBit = true := by native_decide

#eval unsafeRsaBit 1
#eval unsafeRsaBit 0
#eval unsafeRsaBit (-1)
#eval check unsafeRsaBit
#eval if check unsafeRsaBit then "All tests passed."
      else "Candidate failed RSA timing-leak tests"

/-- No restriction to binary digits: Python accepts every integer. -/
def Pre (_bit : Int) : Prop := True

/-- Assertion 1, including the `None` component of the return value. -/
def slowPath_prop (bit : Int) : Prop :=
  bit = 1 → unsafeRsaBit bit = ((), 60)

theorem slowPath_thm (bit : Int) : slowPath_prop bit := by
  unfold slowPath_prop
  intro h
  simp [unsafeRsaBit, h]

/-- Assertion 2 at zero, generalized to the entire Python else branch. -/
def fastPath_prop (bit : Int) : Prop :=
  bit ≠ 1 → unsafeRsaBit bit = ((), 10)

theorem fastPath_thm (bit : Int) : fastPath_prop bit := by
  unfold fastPath_prop
  intro h
  simp [unsafeRsaBit, h]

/-- Assertion 3a: the slow timing is distinct from every fast-path timing. -/
def timingDistinct_prop (bit : Int) : Prop :=
  bit ≠ 1 → (unsafeRsaBit 1).2 ≠ (unsafeRsaBit bit).2

theorem timingDistinct_thm (bit : Int) : timingDistinct_prop bit := by
  unfold timingDistinct_prop
  intro h
  norm_num [unsafeRsaBit, h]

/-- Assertion 3b: the slow branch takes strictly more cycles. -/
def timingOrdered_prop (bit : Int) : Prop :=
  bit ≠ 1 → (unsafeRsaBit 1).2 > (unsafeRsaBit bit).2

theorem timingOrdered_thm (bit : Int) : timingOrdered_prop bit := by
  unfold timingOrdered_prop
  intro h
  norm_num [unsafeRsaBit, h]

/-- Assertion 4: an input equal to one cannot have the fast timing. -/
def slowNotFast_prop (bit : Int) : Prop :=
  bit = 1 → (unsafeRsaBit bit).2 ≠ 10

theorem slowNotFast_thm (bit : Int) : slowNotFast_prop bit := by
  unfold slowNotFast_prop
  intro h
  norm_num [unsafeRsaBit, h]

/-- Assertion 5: every non-one input, including zero, cannot have slow timing. -/
def fastNotSlow_prop (bit : Int) : Prop :=
  bit ≠ 1 → (unsafeRsaBit bit).2 ≠ 60

theorem fastNotSlow_thm (bit : Int) : fastNotSlow_prop bit := by
  unfold fastNotSlow_prop
  intro h
  norm_num [unsafeRsaBit, h]

/-- The timing oracle identifies the branch exactly; on binary inputs it
therefore recovers the private-key bit. No binary-input assumption is needed
for these equivalences. -/
def timingOracle_prop (bit : Int) : Prop :=
  ((unsafeRsaBit bit).2 = 60 ↔ bit = 1) ∧
  ((unsafeRsaBit bit).2 = 10 ↔ bit ≠ 1)

theorem timingOracle_thm (bit : Int) : timingOracle_prop bit := by
  unfold timingOracle_prop
  by_cases h : bit = 1 <;> simp [unsafeRsaBit, h]

/-- The original top-level assertion succeeds, proved by kernel reduction. -/
theorem check_thm : check unsafeRsaBit = true := by
  decide

/-- All branch properties and all assertions hold simultaneously. -/
def Post_prop (bit : Int) : Prop :=
  slowPath_prop bit ∧
  fastPath_prop bit ∧
  timingDistinct_prop bit ∧
  timingOrdered_prop bit ∧
  slowNotFast_prop bit ∧
  fastNotSlow_prop bit ∧
  timingOracle_prop bit ∧
  check unsafeRsaBit = true

/-! ## Property-based tests

Exhaustively sample the 65 integers from -32 through 32. This includes both
branches, zero, negative integers, and non-binary positive integers. Each test
below is the executable Boolean form of the named property. In particular,
these are not random implications whose antecedents might never be sampled.
-/

def testBits : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32)

-- PBT: slowPath_prop.
example : testBits.all (fun bit =>
    decide (bit = 1 → unsafeRsaBit bit = ((), 60))) = true := by
  native_decide

-- PBT: fastPath_prop.
example : testBits.all (fun bit =>
    decide (bit ≠ 1 → unsafeRsaBit bit = ((), 10))) = true := by
  native_decide

-- PBT: timingDistinct_prop (zero is one of the sampled fast inputs).
example : testBits.all (fun bit =>
    decide (bit ≠ 1 → (unsafeRsaBit 1).2 ≠ (unsafeRsaBit bit).2)) = true := by
  native_decide

-- PBT: timingOrdered_prop.
example : testBits.all (fun bit =>
    decide (bit ≠ 1 → (unsafeRsaBit 1).2 > (unsafeRsaBit bit).2)) = true := by
  native_decide

-- PBT: slowNotFast_prop.
example : testBits.all (fun bit =>
    decide (bit = 1 → (unsafeRsaBit bit).2 ≠ 10)) = true := by
  native_decide

-- PBT: fastNotSlow_prop.
example : testBits.all (fun bit =>
    decide (bit ≠ 1 → (unsafeRsaBit bit).2 ≠ 60)) = true := by
  native_decide

-- PBT: timingOracle_prop, checking both directions of both equivalences.
example : testBits.all (fun bit =>
    decide (((unsafeRsaBit bit).2 = 60 ↔ bit = 1) ∧
      ((unsafeRsaBit bit).2 = 10 ↔ bit ≠ 1))) = true := by
  native_decide

-- PBT: Post_prop, expanded to its executable assertions.
example : testBits.all (fun bit =>
    decide ((bit = 1 → unsafeRsaBit bit = ((), 60)) ∧
      (bit ≠ 1 → unsafeRsaBit bit = ((), 10)) ∧
      (bit ≠ 1 → (unsafeRsaBit 1).2 ≠ (unsafeRsaBit bit).2) ∧
      (bit ≠ 1 → (unsafeRsaBit 1).2 > (unsafeRsaBit bit).2) ∧
      (bit = 1 → (unsafeRsaBit bit).2 ≠ 10) ∧
      (bit ≠ 1 → (unsafeRsaBit bit).2 ≠ 60) ∧
      (((unsafeRsaBit bit).2 = 60 ↔ bit = 1) ∧
        ((unsafeRsaBit bit).2 = 10 ↔ bit ≠ 1)) ∧
      check unsafeRsaBit = true)) = true := by
  native_decide

#eval testBits.all (fun bit =>
  (unsafeRsaBit bit).2 == (if bit = 1 then 60 else 10))

/-- Correctness for the full Python integer-input domain. -/
theorem correctness_thm (bit : Int) : Pre bit → Post_prop bit := by
  intro _
  exact ⟨slowPath_thm bit, fastPath_thm bit,
    timingDistinct_thm bit, timingOrdered_thm bit,
    slowNotFast_thm bit, fastNotSlow_thm bit,
    timingOracle_thm bit, check_thm⟩

/-- Imperative timing model: a square always costs 10 cycles, and the
conditional multiply adds 50 cycles only when the integer input equals 1. -/
def unsafeRsaBitImperative (bit : Int) : BitResult := Id.run do
  let mut cycles : Nat := 10
  if bit = 1 then
    cycles := cycles + 50
  return ((), cycles)

-- Imperative tests include the original entire check and else-branch edges.
example : unsafeRsaBitImperative 1 = ((), 60) := by native_decide
example : unsafeRsaBitImperative 0 = ((), 10) := by native_decide
example : unsafeRsaBitImperative (-1) = ((), 10) := by native_decide
example : unsafeRsaBitImperative 2 = ((), 10) := by native_decide
example : check unsafeRsaBitImperative = true := by native_decide
example : testBits.all (fun bit =>
    decide (unsafeRsaBit bit = unsafeRsaBitImperative bit)) = true := by
  native_decide

#eval unsafeRsaBitImperative 1
#eval unsafeRsaBitImperative 0
#eval check unsafeRsaBitImperative

/-- Equality of the complete return values, for every integer, not only bits. -/
theorem functional_imperative_equiv (bit : Int) :
    unsafeRsaBit bit = unsafeRsaBitImperative bit := by
  by_cases h : bit = 1 <;>
    simp [unsafeRsaBit, unsafeRsaBitImperative, h]

end UnsafeRsaExponentiation
end Agent

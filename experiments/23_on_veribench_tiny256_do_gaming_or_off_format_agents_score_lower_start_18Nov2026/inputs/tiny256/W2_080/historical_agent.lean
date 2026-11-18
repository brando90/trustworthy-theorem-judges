import Mathlib
namespace Agent

/-!
# Safe file integrity

A translation of the equality-based hash check from MIT 6.858 Lab 5.
Python's unbounded integers are modeled by `Int`: all integers, including
negative values and zero, are admissible. The function accepts exactly when
the stored hash equals the client's expected hash. This specifies hash
comparison, not a claim that distinct file contents cannot have hash collisions.

The file includes the original checks, a complete specification with proofs,
bounded property-based tests, and an equivalent mutable-state implementation.
-/

namespace «112_unsafeFileIntegrity_safe»

/-- Accept the retrieved file exactly when its stored and expected hashes agree. -/
def safe_read_file (stored expected : Int) : Bool :=
  decide (stored = expected)

-- The four tests from the Python program.
example : safe_read_file 42 42 = true := by native_decide
example : safe_read_file 99 42 = false := by native_decide
example : safe_read_file 0 12345 = false := by native_decide
example : safe_read_file 0 0 = true := by native_decide

-- Int also preserves the Python behavior on negative integers.
example : safe_read_file (-42) (-42) = true := by native_decide
example : safe_read_file (-42) 42 = false := by native_decide

/-- Executable counterpart of the Python test driver. -/
def check : IO Unit := do
  unless safe_read_file 42 42 do
    throw (IO.userError "valid file rejected")
  if safe_read_file 99 42 then
    throw (IO.userError "tampered content accepted")
  if safe_read_file 0 12345 then
    throw (IO.userError "zeroed content accepted")
  unless safe_read_file 0 0 do
    throw (IO.userError "both-zero case failed")
  IO.println "All tests passed."

#eval check

/-- There are no restrictions on either integer hash. -/
def Pre (_stored _expected : Int) : Prop := True

/-- Matching hashes are always accepted. -/
def valid_file_prop (stored expected : Int) : Prop :=
  stored = expected → safe_read_file stored expected = true

theorem valid_file_thm (stored expected : Int) : valid_file_prop stored expected := by
  simp [valid_file_prop, safe_read_file]

/-- Every mismatch is rejected, including a zeroed hash that differs from expectation. -/
def tamper_detection_prop (stored expected : Int) : Prop :=
  stored ≠ expected → safe_read_file stored expected = false

theorem tamper_detection_thm (stored expected : Int) :
    tamper_detection_prop stored expected := by
  simp [tamper_detection_prop, safe_read_file]

/-- Acceptance is both sound and complete for hash equality. -/
def acceptance_iff_prop (stored expected : Int) : Prop :=
  safe_read_file stored expected = true ↔ stored = expected

theorem acceptance_iff_thm (stored expected : Int) :
    acceptance_iff_prop stored expected := by
  simp [acceptance_iff_prop, safe_read_file]

/-- Rejection is both sound and complete for hash inequality. -/
def rejection_iff_prop (stored expected : Int) : Prop :=
  safe_read_file stored expected = false ↔ stored ≠ expected

theorem rejection_iff_thm (stored expected : Int) :
    rejection_iff_prop stored expected := by
  simp [rejection_iff_prop, safe_read_file]

/-- The full contract, with both possible Boolean outcomes characterized. -/
def Post_prop (stored expected : Int) : Prop :=
  valid_file_prop stored expected ∧
  tamper_detection_prop stored expected ∧
  acceptance_iff_prop stored expected ∧
  rejection_iff_prop stored expected

/-! ## Bounded property-based tests

Each test exhausts the Cartesian square of the sample set. In addition to
all integers from -32 through 32, the set includes the original nonzero test
hashes, their negatives, and integers beyond machine-word range. Equality and
inequality cases are both exercised. These are executable counterparts of the
properties above, not replacements for their universally quantified proofs.
-/

def pbtHashes : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [42, 99, 12345, -42, -99, -12345,
     340282366920938463463374607431768211456,
     -340282366920938463463374607431768211456]

-- PBT for valid_file_prop.
example : (pbtHashes.all fun stored => pbtHashes.all fun expected =>
    decide (stored = expected → safe_read_file stored expected = true)) = true := by
  native_decide

-- PBT for tamper_detection_prop.
example : (pbtHashes.all fun stored => pbtHashes.all fun expected =>
    decide (stored ≠ expected → safe_read_file stored expected = false)) = true := by
  native_decide

-- PBT for acceptance_iff_prop.
example : (pbtHashes.all fun stored => pbtHashes.all fun expected =>
    decide (safe_read_file stored expected = true ↔ stored = expected)) = true := by
  native_decide

-- PBT for rejection_iff_prop.
example : (pbtHashes.all fun stored => pbtHashes.all fun expected =>
    decide (safe_read_file stored expected = false ↔ stored ≠ expected)) = true := by
  native_decide

-- PBT for Post_prop: all four executable properties checked together.
example : (pbtHashes.all fun stored => pbtHashes.all fun expected =>
    decide ((stored = expected → safe_read_file stored expected = true) ∧
      (stored ≠ expected → safe_read_file stored expected = false) ∧
      (safe_read_file stored expected = true ↔ stored = expected) ∧
      (safe_read_file stored expected = false ↔ stored ≠ expected))) = true := by
  native_decide

/-- Correctness on the entire admissible domain of Python integers. -/
theorem correctness_thm (stored expected : Int) :
    Pre stored expected → Post_prop stored expected := by
  intro _
  exact ⟨valid_file_thm stored expected,
    tamper_detection_thm stored expected,
    acceptance_iff_thm stored expected,
    rejection_iff_thm stored expected⟩

/-- A mutable-state implementation of the same hash comparison. -/
def safe_read_file_imperative (stored expected : Int) : Bool := Id.run do
  let mut accepted := false
  if stored = expected then
    accepted := true
  return accepted

-- Imperative counterparts of the original unit tests.
example : safe_read_file_imperative 42 42 = true := by native_decide
example : safe_read_file_imperative 99 42 = false := by native_decide
example : safe_read_file_imperative 0 12345 = false := by native_decide
example : safe_read_file_imperative 0 0 = true := by native_decide
example : safe_read_file_imperative (-42) (-42) = true := by native_decide
example : safe_read_file_imperative (-42) 42 = false := by native_decide

#eval [safe_read_file_imperative 42 42, safe_read_file_imperative 99 42,
  safe_read_file_imperative 0 12345, safe_read_file_imperative 0 0]

-- Additional bounded equivalence check, independent of the proof below.
example : (pbtHashes.all fun stored => pbtHashes.all fun expected =>
    decide (safe_read_file stored expected =
      safe_read_file_imperative stored expected)) = true := by
  native_decide

/-- Functional and imperative versions agree for every pair of integers. -/
theorem functional_imperative_equivalence_thm (stored expected : Int) :
    safe_read_file stored expected = safe_read_file_imperative stored expected := by
  by_cases h : stored = expected
  · simp [safe_read_file, safe_read_file_imperative, h]
  · simp [safe_read_file, safe_read_file_imperative, h]

end «112_unsafeFileIntegrity_safe»
end Agent

import Mathlib
namespace Agent

/-!
# Unsafe file integrity

A translation of the Python `unsafe_read_file` program from the MIT 6.858
Lab 5 setting. Python integers are modeled by `Int`, without restricting their
sign or magnitude. The reader always returns `true`: it neither compares the
stored and expected values nor checks a hash or MAC. The properties below
characterize this vulnerability, rather than asserting an integrity guarantee.
-/

namespace UnsafeFileIntegrity

/-! ## Functional implementation and the original checks -/

/-- Accept the file without inspecting either argument. -/
def unsafe_read_file (_stored _expected : Int) : Bool := true

/-- The three Python assertions, with their original failure messages. -/
def check : IO Unit := do
  unless unsafe_read_file 42 42 == true do
    throw (IO.userError "normal case failed")
  unless unsafe_read_file 99 42 == true do
    throw (IO.userError "vuln: tampered content accepted")
  unless unsafe_read_file 0 12345 == true do
    throw (IO.userError "vuln: zeroed content accepted")
  IO.println "All tests passed."

/-- The Python script's entry point. -/
def main : IO Unit := check

example : unsafe_read_file 42 42 = true := by native_decide
example : unsafe_read_file 99 42 = true := by native_decide
example : unsafe_read_file 0 12345 = true := by native_decide
example : unsafe_read_file (-99) (-42) = true := by native_decide

#eval unsafe_read_file 42 42
#eval unsafe_read_file 99 42
#eval unsafe_read_file 0 12345
#eval main

/-! ## Specification and kernel-checked properties -/

/-- The Python function has no precondition on its integer inputs. -/
def Pre (_stored _expected : Int) : Prop := True

/-- Every input is accepted, independently of its contents. -/
def always_accepts_prop (stored expected : Int) : Prop :=
  unsafe_read_file stored expected = true

theorem always_accepts_thm (stored expected : Int) :
    always_accepts_prop stored expected := by
  rfl

/-- Matching values are accepted (the normal case). -/
def matching_accepted_prop (stored expected : Int) : Prop :=
  stored = expected → unsafe_read_file stored expected = true

theorem matching_accepted_thm (stored expected : Int) :
    matching_accepted_prop stored expected := by
  intro _
  rfl

/-- Mismatching values are also accepted: tampering is not detected. -/
def tampered_accepted_prop (stored expected : Int) : Prop :=
  stored ≠ expected → unsafe_read_file stored expected = true

theorem tampered_accepted_thm (stored expected : Int) :
    tampered_accepted_prop stored expected := by
  intro _
  rfl

/-- Replacing the expected content by any stored value leaves the result unchanged. -/
def replacement_undetected_prop (stored expected : Int) : Prop :=
  unsafe_read_file stored expected = unsafe_read_file expected expected

theorem replacement_undetected_thm (stored expected : Int) :
    replacement_undetected_prop stored expected := by
  rfl

/-- The postcondition records acceptance and the absence of an integrity check. -/
def Post_prop (stored expected : Int) : Prop :=
  always_accepts_prop stored expected ∧
  matching_accepted_prop stored expected ∧
  tampered_accepted_prop stored expected ∧
  replacement_undetected_prop stored expected

/-! ## Property-based tests

Each check uses the executable expression underlying the named property,
not a custom decidability instance for the specification. These tests are
separate from the proofs above and below.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check
  (∀ stored expected : Int, unsafe_read_file stored expected = true)

-- PBT for matching_accepted_prop: generate matching pairs directly, so no
-- random samples are discarded for failing the equality premise.
#eval Plausible.Testable.check
  (∀ content : Int, unsafe_read_file content content = true)

-- PBT for tampered_accepted_prop. Boolean implication avoids discarding
-- matching samples: either the values match or the mismatching file is accepted.
#eval Plausible.Testable.check
  (∀ stored expected : Int,
    ((stored == expected) || unsafe_read_file stored expected) = true)

-- PBT for replacement_undetected_prop.
#eval Plausible.Testable.check
  (∀ stored expected : Int,
    unsafe_read_file stored expected = unsafe_read_file expected expected)

-- PBT for Post_prop, with each conjunct expanded to Boolean operations.
-- The two implications are checked as disjunctions, not sampling filters.
#eval Plausible.Testable.check
  (∀ stored expected : Int,
    ((unsafe_read_file stored expected == true) &&
     ((stored != expected) || unsafe_read_file stored expected) &&
     ((stored == expected) || unsafe_read_file stored expected) &&
     (unsafe_read_file stored expected == unsafe_read_file expected expected)) = true)

/-- Exhaustive small inputs include negative, zero, and positive integers. -/
def testInputs : List Int :=
  (List.range 31).map (fun n => (n : Int) - 15)

-- Bounded PBT for tampered_accepted_prop, including every distinct pair.
example :
    testInputs.all (fun stored => testInputs.all (fun expected =>
      (stored == expected) || unsafe_read_file stored expected)) = true := by
  native_decide

-- Bounded PBT for the entire postcondition, covering every pair in [-15, 15].
-- The middle Boolean expressions implement the two implication premises.
example :
    testInputs.all (fun stored => testInputs.all (fun expected =>
      (unsafe_read_file stored expected == true) &&
      ((stored != expected) || unsafe_read_file stored expected) &&
      ((stored == expected) || unsafe_read_file stored expected) &&
      (unsafe_read_file stored expected == unsafe_read_file expected expected)))
      = true := by native_decide

/-! ## Correctness relative to the deliberately unsafe specification -/

theorem correctness_thm (stored expected : Int) :
    Pre stored expected → Post_prop stored expected := by
  intro _
  exact ⟨always_accepts_thm stored expected,
    matching_accepted_thm stored expected,
    tampered_accepted_thm stored expected,
    replacement_undetected_thm stored expected⟩

/-! ## Imperative implementation -/

/-- A mutable return register is set to true, without any integrity check. -/
def unsafe_read_file_imperative (_stored _expected : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_read_file_imperative 42 42 = true := by native_decide
example : unsafe_read_file_imperative 99 42 = true := by native_decide
example : unsafe_read_file_imperative 0 12345 = true := by native_decide
example : unsafe_read_file_imperative (-99) (-42) = true := by native_decide

#eval unsafe_read_file_imperative 42 42
#eval unsafe_read_file_imperative 99 42
#eval unsafe_read_file_imperative 0 12345

-- A bounded comparison exercises both implementations on signed inputs.
example :
    testInputs.all (fun stored => testInputs.all (fun expected =>
      unsafe_read_file stored expected == unsafe_read_file_imperative stored expected))
      = true := by native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv (stored expected : Int) :
    unsafe_read_file stored expected = unsafe_read_file_imperative stored expected := by
  rfl

end UnsafeFileIntegrity
end Agent

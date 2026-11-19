import Mathlib
namespace Agent

/-!
# Unsafe saltless password comparison

Translation of the Python `unsafe_saltless_check` and its test harness.
Python integers are modeled by `Int`, including negative and arbitrarily large
values. The function compares the password directly with the stored integer:
there is no salt, hashing, or other transformation. Consequently equality alone
determines acceptance; this is not a secure password-storage construction.

The specifications characterize both acceptance and rejection, self-acceptance,
and symmetry. Bounded property tests are evidence only; all named theorems have
separate kernel-checked proofs over the full integer domain.
-/

namespace UnsafeSaltlessStore

/-- Exactly the Boolean result of Python's `pw == stored`. -/
def unsafe_saltless_check (pw stored : Int) : Bool :=
  decide (pw = stored)

-- Unit tests: the three assertions in the Python source.
example : unsafe_saltless_check 1234 1234 = true := by native_decide
example : unsafe_saltless_check 0 0 = true := by native_decide
example : unsafe_saltless_check 9999 1234 = false := by native_decide

-- Additional coverage for signed and arbitrary-precision integers.
example : unsafe_saltless_check (-1234) (-1234) = true := by native_decide
example : unsafe_saltless_check (-1234) 1234 = false := by native_decide
example : unsafe_saltless_check 1000000000000000000000000000000
    1000000000000000000000000000000 = true := by native_decide

/-- The Python test harness, including its failure messages and success output. -/
def check : IO Unit := do
  unless unsafe_saltless_check 1234 1234 do
    throw (IO.userError "normal case failed")
  unless unsafe_saltless_check 0 0 do
    throw (IO.userError "zero case failed")
  if unsafe_saltless_check 9999 1234 then
    throw (IO.userError "wrong pw should fail")
  IO.println "All tests passed."

#eval unsafe_saltless_check 1234 1234
#eval unsafe_saltless_check 0 0
#eval unsafe_saltless_check 9999 1234
#eval check

/-- Every pair of Python integers is admissible. -/
def Pre (_pw _stored : Int) : Prop := True

/-- A password is accepted exactly when it equals the stored integer. -/
def acceptance_prop (pw stored : Int) : Prop :=
  unsafe_saltless_check pw stored = true ↔ pw = stored

theorem acceptance_thm (pw stored : Int) : acceptance_prop pw stored := by
  simp [acceptance_prop, unsafe_saltless_check]

/-- A password is rejected exactly when it differs from the stored integer. -/
def rejection_prop (pw stored : Int) : Prop :=
  unsafe_saltless_check pw stored = false ↔ pw ≠ stored

theorem rejection_thm (pw stored : Int) : rejection_prop pw stored := by
  simp [rejection_prop, unsafe_saltless_check]

/-- With no salt or transformation, every integer matches itself. -/
def reflexivity_prop (pw : Int) : Prop :=
  unsafe_saltless_check pw pw = true

theorem reflexivity_thm (pw : Int) : reflexivity_prop pw := by
  simp [reflexivity_prop, unsafe_saltless_check]

/-- Direct equality is symmetric in the supplied and stored integers. -/
def symmetry_prop (pw stored : Int) : Prop :=
  unsafe_saltless_check pw stored = unsafe_saltless_check stored pw

theorem symmetry_thm (pw stored : Int) : symmetry_prop pw stored := by
  simp [symmetry_prop, unsafe_saltless_check, eq_comm]

/-- The complete post-condition is the conjunction of the stated properties. -/
def Post_prop (pw stored : Int) : Prop :=
  acceptance_prop pw stored ∧
  rejection_prop pw stored ∧
  reflexivity_prop pw ∧
  symmetry_prop pw stored

/-!
## Property-based tests

Exhaustively check all integers from -20 through 20 (1,681 ordered pairs).
The predicates below are executable forms of the specifications, not uses of
the proved theorems. `Pre` is always true, so no test inputs are filtered out.
-/

private def testInputs : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20)

-- PBT for acceptance_prop.
example : testInputs.all (fun pw => testInputs.all (fun stored =>
    decide (unsafe_saltless_check pw stored = true ↔ pw = stored))) = true := by
  native_decide

-- PBT for rejection_prop.
example : testInputs.all (fun pw => testInputs.all (fun stored =>
    decide (unsafe_saltless_check pw stored = false ↔ pw ≠ stored))) = true := by
  native_decide

-- PBT for reflexivity_prop.
example : testInputs.all (fun pw => unsafe_saltless_check pw pw) = true := by
  native_decide

-- PBT for symmetry_prop.
example : testInputs.all (fun pw => testInputs.all (fun stored =>
    unsafe_saltless_check pw stored == unsafe_saltless_check stored pw)) = true := by
  native_decide

-- PBT for Post_prop: check every conjunct together on each input pair.
example : testInputs.all (fun pw => testInputs.all (fun stored =>
    decide (unsafe_saltless_check pw stored = true ↔ pw = stored) &&
    decide (unsafe_saltless_check pw stored = false ↔ pw ≠ stored) &&
    unsafe_saltless_check pw pw &&
    (unsafe_saltless_check pw stored == unsafe_saltless_check stored pw))) = true := by
  native_decide

/-- Correctness holds for every admissible pair, without restricting integers. -/
theorem correctness_thm (pw stored : Int) : Pre pw stored → Post_prop pw stored := by
  intro _
  exact ⟨acceptance_thm pw stored, rejection_thm pw stored,
    reflexivity_thm pw, symmetry_thm pw stored⟩

/-- An imperative rendition using a mutable Boolean result. -/
def unsafe_saltless_check_imperative (pw stored : Int) : Bool := Id.run do
  let mut result := false
  if pw = stored then
    result := true
  return result

-- Imperative unit tests, including the original three cases.
example : unsafe_saltless_check_imperative 1234 1234 = true := by native_decide
example : unsafe_saltless_check_imperative 0 0 = true := by native_decide
example : unsafe_saltless_check_imperative 9999 1234 = false := by native_decide
example : unsafe_saltless_check_imperative (-1234) (-1234) = true := by native_decide
example : unsafe_saltless_check_imperative (-1234) 1234 = false := by native_decide

#eval unsafe_saltless_check_imperative 1234 1234
#eval unsafe_saltless_check_imperative 0 0
#eval unsafe_saltless_check_imperative 9999 1234

-- Bounded cross-implementation test, separate from the universal proof.
example : testInputs.all (fun pw => testInputs.all (fun stored =>
    unsafe_saltless_check pw stored == unsafe_saltless_check_imperative pw stored)) = true := by
  native_decide

/-- Functional and imperative implementations agree on the full input domain. -/
theorem equivalence_thm (pw stored : Int) :
    unsafe_saltless_check pw stored = unsafe_saltless_check_imperative pw stored := by
  by_cases h : pw = stored <;>
    simp [unsafe_saltless_check, unsafe_saltless_check_imperative, h]

end UnsafeSaltlessStore
end Agent

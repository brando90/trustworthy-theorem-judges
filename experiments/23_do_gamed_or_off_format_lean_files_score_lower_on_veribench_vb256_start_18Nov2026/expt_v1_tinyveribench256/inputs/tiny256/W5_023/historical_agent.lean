import Mathlib
namespace Agent

/-!
# Unsafe plaintext file access

Translation of the Python `unsafe_file_access` example from MIT 6.858 Lab 5.
Files are plaintext: the access decision is always `true`, even if the server
has the wrong key or the zero key. This file specifies the vulnerability rather
than repairing it. Python's arbitrary-precision integer keys are modeled by
`Int`, with no sign, size, or key-equality restriction.

The functional and mutable implementations have the same unconditional result.
The executable tests are evidence only; all named theorems have kernel proofs.
-/

namespace «113_unsafePlaintextFS»

-- Functional implementation: neither key participates in the decision.
def unsafe_file_access (_file_key _server_key : Int) : Bool :=
  true

-- Unit tests, including all three assertions in the Python program.
example : unsafe_file_access 100 100 = true := by native_decide
example : unsafe_file_access 100 999 = true := by native_decide
example : unsafe_file_access 42 0 = true := by native_decide
example : unsafe_file_access (-42) (-999) = true := by native_decide
example : unsafe_file_access 0 0 = true := by native_decide

-- The original executable test harness, with IO errors for failed assertions.
def check : IO Unit := do
  unless unsafe_file_access 100 100 do
    throw (IO.userError "normal case failed")
  unless unsafe_file_access 100 999 do
    throw (IO.userError "vuln: wrong key reads file")
  unless unsafe_file_access 42 0 do
    throw (IO.userError "vuln: zero key reads file")
  IO.println "All tests passed."

#eval unsafe_file_access 100 100
#eval unsafe_file_access 100 999
#eval unsafe_file_access 42 0
#eval check

-- All integer pairs are admissible; no possession of a correct key is required.
def Pre (_file_key _server_key : Int) : Prop := True

-- The result is always true, not merely true for the supplied examples.
def always_access_prop (file_key server_key : Int) : Prop :=
  unsafe_file_access file_key server_key = true

theorem always_access_thm (file_key server_key : Int) :
    always_access_prop file_key server_key := by
  rfl

-- The normal, matching-key case also succeeds.
def matching_key_prop (file_key : Int) : Prop :=
  unsafe_file_access file_key file_key = true

theorem matching_key_thm (file_key : Int) : matching_key_prop file_key := by
  rfl

-- Vulnerability: even genuinely different keys grant access.
def wrong_key_access_prop (file_key server_key : Int) : Prop :=
  file_key ≠ server_key → unsafe_file_access file_key server_key = true

theorem wrong_key_access_thm (file_key server_key : Int) :
    wrong_key_access_prop file_key server_key := by
  intro _
  rfl

-- Changing either or both keys has no effect on the result.
def key_independence_prop (file_key server_key : Int) : Prop :=
  ∀ other_file_key other_server_key : Int,
    unsafe_file_access file_key server_key =
      unsafe_file_access other_file_key other_server_key

theorem key_independence_thm (file_key server_key : Int) :
    key_independence_prop file_key server_key := by
  intro other_file_key other_server_key
  rfl

-- Postcondition records both the successful normal case and the insecurity.
def Post_prop (file_key server_key : Int) : Prop :=
  always_access_prop file_key server_key ∧
  matching_key_prop file_key ∧
  wrong_key_access_prop file_key server_key ∧
  key_independence_prop file_key server_key

/-! ## Bounded property-based tests

Each executable property above, including the postcondition, is checked on
many inputs. The sample set contains every integer from -10 through 10 and
all additional keys used by the source tests. Nested `all` checks enumerate
all tuples in this set, including all four keys for independence. Only the
tests are bounded; the properties and their proofs quantify over all `Int`.
-/

def testKeys : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10) ++ [42, 100, 999]

-- PBT for always_access_prop: 24 * 24 pairs.
example : (testKeys.all (fun file_key =>
    testKeys.all (fun server_key =>
      unsafe_file_access file_key server_key))) = true := by
  native_decide

-- PBT for matching_key_prop.
example : (testKeys.all (fun file_key =>
    unsafe_file_access file_key file_key)) = true := by
  native_decide

-- PBT for wrong_key_access_prop. The Boolean expression is the implication
-- (file_key ≠ server_key) → (result = true), without discarding any samples.
example : (testKeys.all (fun file_key =>
    testKeys.all (fun server_key =>
      (file_key == server_key) || unsafe_file_access file_key server_key))) =
    true := by
  native_decide

-- PBT for key_independence_prop: all 24^4 key quadruples.
example : (testKeys.all (fun file_key =>
    testKeys.all (fun server_key =>
      testKeys.all (fun other_file_key =>
        testKeys.all (fun other_server_key =>
          unsafe_file_access file_key server_key ==
            unsafe_file_access other_file_key other_server_key))))) = true := by
  native_decide

-- PBT for Post_prop: its conjunction, with the universal independence clause
-- exhaustively checked over the same bounded set of alternative keys.
example : (testKeys.all (fun file_key =>
    testKeys.all (fun server_key =>
      unsafe_file_access file_key server_key &&
      unsafe_file_access file_key file_key &&
      ((file_key == server_key) || unsafe_file_access file_key server_key) &&
      testKeys.all (fun other_file_key =>
        testKeys.all (fun other_server_key =>
          unsafe_file_access file_key server_key ==
            unsafe_file_access other_file_key other_server_key))))) = true := by
  native_decide

-- Correctness relative to the intentionally unsafe specification.
theorem correctness_thm (file_key server_key : Int) :
    Pre file_key server_key → Post_prop file_key server_key := by
  intro _
  exact ⟨always_access_thm file_key server_key,
    matching_key_thm file_key,
    wrong_key_access_thm file_key server_key,
    key_independence_thm file_key server_key⟩

-- Imperative implementation: initialize mutable state, then grant access
-- unconditionally. Neither key is inspected.
def unsafe_file_access_imperative (_file_key _server_key : Int) : Bool := Id.run do
  let mut granted := false
  granted := true
  return granted

-- Imperative tests.
example : unsafe_file_access_imperative 100 100 = true := by native_decide
example : unsafe_file_access_imperative 100 999 = true := by native_decide
example : unsafe_file_access_imperative 42 0 = true := by native_decide
example : unsafe_file_access_imperative (-42) (-999) = true := by native_decide
example : unsafe_file_access_imperative 0 0 = true := by native_decide

#eval unsafe_file_access_imperative 100 100
#eval unsafe_file_access_imperative 100 999
#eval unsafe_file_access_imperative 42 0

example : (testKeys.all (fun file_key =>
    testKeys.all (fun server_key =>
      unsafe_file_access file_key server_key ==
        unsafe_file_access_imperative file_key server_key))) = true := by
  native_decide

-- Kernel reduction of Id.run proves equivalence for every integer pair.
theorem functional_eq_imperative_thm (file_key server_key : Int) :
    unsafe_file_access file_key server_key =
      unsafe_file_access_imperative file_key server_key := by
  rfl

end «113_unsafePlaintextFS»
end Agent

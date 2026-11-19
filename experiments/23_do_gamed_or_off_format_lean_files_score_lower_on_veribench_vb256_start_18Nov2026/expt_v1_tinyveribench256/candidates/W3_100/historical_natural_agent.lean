import Mathlib
namespace Agent

/-!
# Safe TOFU key verification

Translation of the Python `safe_tofu_key` function. Python's arbitrary-precision
integers are represented by `Int`. The supplied stored key is already pinned:
this function checks equality, without establishing or updating that pin.
The sender identifier does not affect the result. All integer keys, including
zero and negative keys, are admissible; zero is accepted exactly when pinned.

The file includes the Python checks, specifications with kernel-checked proofs,
exhaustive bounded property tests, and an equivalent mutable implementation.
-/

namespace SafeTofuKey

/-- Accept precisely when the presented key equals the stored key. -/
def safe_tofu_key (_sender_id new_key stored_key : Int) : Bool :=
  decide (new_key = stored_key)

-- Unit tests from the Python program.
example : safe_tofu_key 1 42 42 = true := by native_decide
example : safe_tofu_key 1 99 42 = false := by native_decide
example : safe_tofu_key 1 0 42 = false := by native_decide

-- Additional integer-domain edge cases.
example : safe_tofu_key (-7) (-42) (-42) = true := by native_decide
example : safe_tofu_key (-7) (-42) 42 = false := by native_decide
example : safe_tofu_key 0 0 0 = true := by native_decide

/-- Executable translation of the Python test driver. -/
def check : IO Unit := do
  unless safe_tofu_key 1 42 42 do
    throw <| IO.userError "matching key rejected"
  if safe_tofu_key 1 99 42 then
    throw <| IO.userError "key substitution accepted"
  if safe_tofu_key 1 0 42 then
    throw <| IO.userError "zero key accepted"
  IO.println "All tests passed."

#eval safe_tofu_key 1 42 42
#eval safe_tofu_key 1 99 42
#eval safe_tofu_key 1 0 42
#eval check

/-- The Python function imposes no restrictions on its integer arguments. -/
def Pre (_sender_id _new_key _stored_key : Int) : Prop := True

/-- Exact characterization of acceptance, in both directions. -/
def key_match_prop (sender_id new_key stored_key : Int) : Prop :=
  safe_tofu_key sender_id new_key stored_key = true ↔ new_key = stored_key

theorem key_match_thm (sender_id new_key stored_key : Int) :
    key_match_prop sender_id new_key stored_key := by
  simp [key_match_prop, safe_tofu_key]

/-- Exact characterization of rejection, in both directions. -/
def rejection_prop (sender_id new_key stored_key : Int) : Prop :=
  safe_tofu_key sender_id new_key stored_key = false ↔ new_key ≠ stored_key

theorem rejection_thm (sender_id new_key stored_key : Int) :
    rejection_prop sender_id new_key stored_key := by
  simp [rejection_prop, safe_tofu_key]

/-- A matching pinned key is never rejected. -/
def pinned_key_accepted_prop (sender_id stored_key : Int) : Prop :=
  safe_tofu_key sender_id stored_key stored_key = true

theorem pinned_key_accepted_thm (sender_id stored_key : Int) :
    pinned_key_accepted_prop sender_id stored_key := by
  simp [pinned_key_accepted_prop, safe_tofu_key]

/-- Any substitution of a different key is detected by a false result. -/
def substitution_detected_prop (sender_id new_key stored_key : Int) : Prop :=
  new_key ≠ stored_key → safe_tofu_key sender_id new_key stored_key = false

theorem substitution_detected_thm (sender_id new_key stored_key : Int) :
    substitution_detected_prop sender_id new_key stored_key := by
  unfold substitution_detected_prop
  intro h
  simp [safe_tofu_key, h]

/-- The unused sender identifier cannot alter the decision. -/
def sender_independent_prop (sender_id other_sender new_key stored_key : Int) : Prop :=
  safe_tofu_key sender_id new_key stored_key =
    safe_tofu_key other_sender new_key stored_key

theorem sender_independent_thm (sender_id other_sender new_key stored_key : Int) :
    sender_independent_prop sender_id other_sender new_key stored_key := by
  rfl

/-- Zero has no special rejection rule: it is accepted exactly when pinned. -/
def zero_key_prop (sender_id stored_key : Int) : Prop :=
  safe_tofu_key sender_id 0 stored_key = true ↔ stored_key = 0

theorem zero_key_thm (sender_id stored_key : Int) :
    zero_key_prop sender_id stored_key := by
  simp [zero_key_prop, safe_tofu_key, eq_comm]

/-- The complete contract, including independence from every other sender. -/
def Post_prop (sender_id new_key stored_key : Int) : Prop :=
  key_match_prop sender_id new_key stored_key ∧
  rejection_prop sender_id new_key stored_key ∧
  pinned_key_accepted_prop sender_id stored_key ∧
  substitution_detected_prop sender_id new_key stored_key ∧
  (∀ other_sender : Int,
    sender_independent_prop sender_id other_sender new_key stored_key) ∧
  zero_key_prop sender_id stored_key

-- Property-based tests: exhaustive Boolean checks on all integers from -8 to 8.
-- These bounded tests include negative, zero, equal, and unequal inputs.
-- They provide test evidence only; the theorems cover all Int values.
private def testInts : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8)

-- PBT for key_match_prop: acceptance agrees exactly with key equality.
example :
    (testInts.all fun sender_id =>
      testInts.all fun new_key =>
        testInts.all fun stored_key =>
          safe_tofu_key sender_id new_key stored_key == (new_key == stored_key)) =
      true := by native_decide

-- PBT for rejection_prop: rejection agrees exactly with key inequality.
example :
    (testInts.all fun sender_id =>
      testInts.all fun new_key =>
        testInts.all fun stored_key =>
          (!(safe_tofu_key sender_id new_key stored_key)) ==
            (new_key != stored_key)) = true := by native_decide

-- PBT for pinned_key_accepted_prop.
example :
    (testInts.all fun sender_id =>
      testInts.all fun stored_key =>
        safe_tofu_key sender_id stored_key stored_key) = true := by native_decide

-- PBT for substitution_detected_prop: executable implication.
example :
    (testInts.all fun sender_id =>
      testInts.all fun new_key =>
        testInts.all fun stored_key =>
          (new_key == stored_key) ||
            !(safe_tofu_key sender_id new_key stored_key)) = true := by native_decide

-- PBT for sender_independent_prop, varying both sender identifiers.
example :
    (testInts.all fun sender_id =>
      testInts.all fun other_sender =>
        testInts.all fun new_key =>
          testInts.all fun stored_key =>
            safe_tofu_key sender_id new_key stored_key ==
              safe_tofu_key other_sender new_key stored_key) = true := by native_decide

-- PBT for zero_key_prop, including a pinned zero.
example :
    (testInts.all fun sender_id =>
      testInts.all fun stored_key =>
        safe_tofu_key sender_id 0 stored_key == (stored_key == 0)) =
      true := by native_decide

-- PBT for Post_prop: executable conjunction of every part of the contract.
-- The universally quantified other sender is exhaustively bounded here too.
example :
    (testInts.all fun sender_id =>
      testInts.all fun new_key =>
        testInts.all fun stored_key =>
          (safe_tofu_key sender_id new_key stored_key == (new_key == stored_key)) &&
          ((!(safe_tofu_key sender_id new_key stored_key)) ==
            (new_key != stored_key)) &&
          safe_tofu_key sender_id stored_key stored_key &&
          ((new_key == stored_key) || !(safe_tofu_key sender_id new_key stored_key)) &&
          (testInts.all fun other_sender =>
            safe_tofu_key sender_id new_key stored_key ==
              safe_tofu_key other_sender new_key stored_key) &&
          (safe_tofu_key sender_id 0 stored_key == (stored_key == 0))) =
      true := by native_decide

/-- Every admissible input satisfies the full post-condition. -/
theorem correctness_thm (sender_id new_key stored_key : Int) :
    Pre sender_id new_key stored_key → Post_prop sender_id new_key stored_key := by
  intro _
  exact ⟨key_match_thm sender_id new_key stored_key,
    rejection_thm sender_id new_key stored_key,
    pinned_key_accepted_thm sender_id stored_key,
    substitution_detected_thm sender_id new_key stored_key,
    fun other_sender => sender_independent_thm sender_id other_sender new_key stored_key,
    zero_key_thm sender_id stored_key⟩

/-- Imperative version with a mutable decision, initially rejection. -/
def safe_tofu_key_imperative (_sender_id new_key stored_key : Int) : Bool := Id.run do
  let mut accepted := false
  if new_key = stored_key then
    accepted := true
  return accepted

-- Imperative unit tests.
example : safe_tofu_key_imperative 1 42 42 = true := by native_decide
example : safe_tofu_key_imperative 1 99 42 = false := by native_decide
example : safe_tofu_key_imperative 1 0 42 = false := by native_decide
example : safe_tofu_key_imperative (-7) (-42) (-42) = true := by native_decide
example : safe_tofu_key_imperative (-7) (-42) 42 = false := by native_decide
example : safe_tofu_key_imperative 0 0 0 = true := by native_decide

#eval safe_tofu_key_imperative 1 42 42
#eval safe_tofu_key_imperative 1 99 42
#eval safe_tofu_key_imperative 1 0 42

/-- Functional and imperative implementations agree for all Python integers. -/
theorem functional_imperative_equiv_thm (sender_id new_key stored_key : Int) :
    safe_tofu_key sender_id new_key stored_key =
      safe_tofu_key_imperative sender_id new_key stored_key := by
  by_cases h : new_key = stored_key <;>
    simp [safe_tofu_key, safe_tofu_key_imperative, h]

end SafeTofuKey
end Agent

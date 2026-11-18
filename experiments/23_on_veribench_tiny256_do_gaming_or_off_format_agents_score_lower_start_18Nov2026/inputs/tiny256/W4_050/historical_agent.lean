import Mathlib
namespace Agent

/-!
# Safe key persistence

Translation of the Boolean policy checker from MIT 6.858 Lecture 09 (iOS
Security). The result is true exactly when the device is unlocked and a key
is present. Locked devices and devices without a key are rejected.

This function checks a policy; it does not mutate RAM or itself erase a key.
In particular, the cold-boot test rejects the input `locked = true,
key_present = true`, rather than claiming that this input cannot occur.
All Boolean inputs are admissible. Exhaustive property-based tests cover the
entire four-element input space, and the named proofs are kernel checked.
-/

namespace SafeKeyPersistence

/-! ## Functional implementation -/

def safe_key_persistence (device_locked key_present : Bool) : Bool :=
  (!device_locked) && key_present

/-! ## Original unit tests -/

-- Unlocked with key: accepted.
example : safe_key_persistence false true = true := by native_decide
-- Locked with key: rejected.
example : safe_key_persistence true true = false := by native_decide
-- No key present: rejected.
example : safe_key_persistence false false = false := by native_decide
-- Locked without key: rejected.
example : safe_key_persistence true false = false := by native_decide
-- Cold-boot attempt: rejected (the repeated assertion in the Python source).
example : safe_key_persistence true true = false := by native_decide

/-- Executable counterpart of the Python `check` function. -/
def check : IO Unit := do
  unless safe_key_persistence false true == true do
    throw (IO.userError "unlocked with key ok")
  unless safe_key_persistence true true == false do
    throw (IO.userError "locked: key must be gone")
  unless safe_key_persistence false false == false do
    throw (IO.userError "no key present")
  unless safe_key_persistence true false == false do
    throw (IO.userError "locked no key")
  unless safe_key_persistence true true == false do
    throw (IO.userError "cold-boot attack blocked")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- The Python checker accepts every pair of Boolean inputs. -/
def Pre (_device_locked _key_present : Bool) : Prop := True

/-! ## Semantic properties and kernel-checked proofs -/

/-- Acceptance is equivalent to being unlocked with a key present. -/
def acceptance_prop (device_locked key_present : Bool) : Prop :=
  safe_key_persistence device_locked key_present = true ↔
    device_locked = false ∧ key_present = true

theorem acceptance_thm (device_locked key_present : Bool) :
    acceptance_prop device_locked key_present := by
  cases device_locked <;> cases key_present <;>
    simp [acceptance_prop, safe_key_persistence]

/-- Rejection is equivalent to being locked or lacking a key. -/
def rejection_prop (device_locked key_present : Bool) : Prop :=
  safe_key_persistence device_locked key_present = false ↔
    device_locked = true ∨ key_present = false

theorem rejection_thm (device_locked key_present : Bool) :
    rejection_prop device_locked key_present := by
  cases device_locked <;> cases key_present <;>
    simp [rejection_prop, safe_key_persistence]

/-- Locking causes rejection regardless of whether a key remains in memory. -/
def locked_prop (device_locked key_present : Bool) : Prop :=
  device_locked = true → safe_key_persistence device_locked key_present = false

theorem locked_thm (device_locked key_present : Bool) :
    locked_prop device_locked key_present := by
  cases device_locked <;> cases key_present <;>
    simp [locked_prop, safe_key_persistence]

/-- Absence of a key always causes rejection. -/
def absent_key_prop (device_locked key_present : Bool) : Prop :=
  key_present = false → safe_key_persistence device_locked key_present = false

theorem absent_key_thm (device_locked key_present : Bool) :
    absent_key_prop device_locked key_present := by
  cases device_locked <;> cases key_present <;>
    simp [absent_key_prop, safe_key_persistence]

/-- On an unlocked device, the result is exactly the key-presence flag. -/
def unlocked_prop (device_locked key_present : Bool) : Prop :=
  device_locked = false →
    safe_key_persistence device_locked key_present = key_present

theorem unlocked_thm (device_locked key_present : Bool) :
    unlocked_prop device_locked key_present := by
  cases device_locked <;> cases key_present <;>
    simp [unlocked_prop, safe_key_persistence]

/-! ## Postcondition -/

def Post_prop (device_locked key_present : Bool) : Prop :=
  acceptance_prop device_locked key_present ∧
  rejection_prop device_locked key_present ∧
  locked_prop device_locked key_present ∧
  absent_key_prop device_locked key_present ∧
  unlocked_prop device_locked key_present

/-! ## Exhaustive property-based tests

These bounded PBTs enumerate both Boolean inputs independently: all four
possible pairs are checked, not merely a random sample. Each check uses the
Boolean form of the corresponding proposition over the implementation.
The test proofs are not used by any named theorem.
-/

def boolInputs : List Bool := [false, true]

-- PBT for acceptance_prop: equivalence of two truth conditions.
example : boolInputs.all (fun locked => boolInputs.all (fun present =>
    (safe_key_persistence locked present == true) ==
      ((locked == false) && (present == true)))) = true := by
  native_decide

-- PBT for rejection_prop.
example : boolInputs.all (fun locked => boolInputs.all (fun present =>
    (safe_key_persistence locked present == false) ==
      ((locked == true) || (present == false)))) = true := by
  native_decide

-- PBT for locked_prop: Boolean implication is not antecedent or consequent.
example : boolInputs.all (fun locked => boolInputs.all (fun present =>
    (!locked) || (safe_key_persistence locked present == false))) = true := by
  native_decide

-- PBT for absent_key_prop.
example : boolInputs.all (fun locked => boolInputs.all (fun present =>
    present || (safe_key_persistence locked present == false))) = true := by
  native_decide

-- PBT for unlocked_prop.
example : boolInputs.all (fun locked => boolInputs.all (fun present =>
    locked || (safe_key_persistence locked present == present))) = true := by
  native_decide

-- PBT for Post_prop: the conjunction of all five executable properties.
example : boolInputs.all (fun locked => boolInputs.all (fun present =>
    (((safe_key_persistence locked present == true) ==
        ((locked == false) && (present == true))) &&
     ((safe_key_persistence locked present == false) ==
        ((locked == true) || (present == false))) &&
     ((!locked) || (safe_key_persistence locked present == false)) &&
     (present || (safe_key_persistence locked present == false)) &&
     (locked || (safe_key_persistence locked present == present))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (device_locked key_present : Bool) :
    Pre device_locked key_present → Post_prop device_locked key_present := by
  intro _
  exact ⟨acceptance_thm device_locked key_present,
    rejection_thm device_locked key_present,
    locked_thm device_locked key_present,
    absent_key_thm device_locked key_present,
    unlocked_thm device_locked key_present⟩

/-! ## Imperative implementation -/

/-- A local mutable result implements the same policy without modifying inputs. -/
def safe_key_persistence_imperative (device_locked key_present : Bool) : Bool :=
  Id.run do
    let mut accepted := false
    if !device_locked then
      accepted := key_present
    return accepted

/-! ## Imperative unit tests -/

example : safe_key_persistence_imperative false true = true := by native_decide
example : safe_key_persistence_imperative true true = false := by native_decide
example : safe_key_persistence_imperative false false = false := by native_decide
example : safe_key_persistence_imperative true false = false := by native_decide
example : safe_key_persistence_imperative true true = false := by native_decide

#eval [safe_key_persistence_imperative false true,
  safe_key_persistence_imperative true true,
  safe_key_persistence_imperative false false,
  safe_key_persistence_imperative true false,
  safe_key_persistence_imperative true true]

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (device_locked key_present : Bool) :
    safe_key_persistence device_locked key_present =
      safe_key_persistence_imperative device_locked key_present := by
  cases device_locked <;> cases key_present <;> rfl

end SafeKeyPersistence
end Agent

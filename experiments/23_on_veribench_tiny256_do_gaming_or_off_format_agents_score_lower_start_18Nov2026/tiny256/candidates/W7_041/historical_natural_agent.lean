import Mathlib
namespace Agent

/-!
# Unsafe Binder IPC call: no permission mediation

This formalizes the supplied Python `unsafe_binder_call` and its test harness.
Every call returns `true`: the service ID, caller UID, and required permission
are all ignored. In particular, this describes the vulnerability rather than
repairing it or assuming that callers are authorized. Python integers are
modeled by `Int`, with no restriction on their sign or size.

The pure `check` function records whether all four Python assertions pass;
the successful harness's printed message is reproduced by an evaluation below.
The Boolean result is the source program's entire observable dispatch model:
no actual Binder service or permission database is present in the source.
-/

namespace UnsafeBinderCall

/-! ## Functional implementation and source test harness -/

def unsafe_binder_call (_service_id _caller_uid _required_permission : Int) : Bool :=
  true

/-- Executable counterpart of the four assertions in the Python harness. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 100 1000 1 &&
  candidate 100 9999 1 &&
  candidate 100 1000 999 &&
  candidate 100 0 1

/-! ## Unit tests -/

-- Normal call; the implementation still skips authorization.
example : unsafe_binder_call 100 1000 1 = true := by native_decide
-- The unauthorized caller is not blocked.
example : unsafe_binder_call 100 9999 1 = true := by native_decide
-- The wrong permission is not blocked.
example : unsafe_binder_call 100 1000 999 = true := by native_decide
-- UID zero is not blocked.
example : unsafe_binder_call 100 0 1 = true := by native_decide
-- Negative IDs and permissions are also accepted, as in the Python function.
example : unsafe_binder_call (-100) (-9999) (-1) = true := by native_decide
example : check unsafe_binder_call = true := by native_decide

#eval unsafe_binder_call 100 1000 1
#eval unsafe_binder_call 100 9999 1
#eval unsafe_binder_call 100 1000 999
#eval unsafe_binder_call 100 0 1
#eval check unsafe_binder_call
#eval if check unsafe_binder_call then IO.println "All tests passed."
      else IO.println "Test harness failed."

/-! ## Unrestricted precondition -/

/-- The source accepts all integer triples; there is no authorization premise. -/
def Pre (_service_id _caller_uid _required_permission : Int) : Prop := True

/-! ## Behavioral properties and kernel-checked proofs -/

/-- Every call succeeds, irrespective of authorization or argument validity. -/
def always_dispatches_prop (service_id caller_uid required_permission : Int) : Prop :=
  unsafe_binder_call service_id caller_uid required_permission = true

theorem always_dispatches_thm (service_id caller_uid required_permission : Int) :
    always_dispatches_prop service_id caller_uid required_permission := by
  rfl

/-- Replacing the caller UID never affects the result. -/
def caller_uid_irrelevant_prop (service_id caller_uid required_permission : Int) : Prop :=
  ∀ other_uid : Int,
    unsafe_binder_call service_id caller_uid required_permission =
      unsafe_binder_call service_id other_uid required_permission

theorem caller_uid_irrelevant_thm (service_id caller_uid required_permission : Int) :
    caller_uid_irrelevant_prop service_id caller_uid required_permission := by
  intro other_uid
  rfl

/-- Replacing the required permission never affects the result. -/
def required_permission_irrelevant_prop
    (service_id caller_uid required_permission : Int) : Prop :=
  ∀ other_permission : Int,
    unsafe_binder_call service_id caller_uid required_permission =
      unsafe_binder_call service_id caller_uid other_permission

theorem required_permission_irrelevant_thm
    (service_id caller_uid required_permission : Int) :
    required_permission_irrelevant_prop service_id caller_uid required_permission := by
  intro other_permission
  rfl

/-- Even the service ID is unused by this Boolean model of dispatch. -/
def service_id_irrelevant_prop (service_id caller_uid required_permission : Int) : Prop :=
  ∀ other_service : Int,
    unsafe_binder_call service_id caller_uid required_permission =
      unsafe_binder_call other_service caller_uid required_permission

theorem service_id_irrelevant_thm (service_id caller_uid required_permission : Int) :
    service_id_irrelevant_prop service_id caller_uid required_permission := by
  intro other_service
  rfl

/-! ## Postcondition -/

/-- The output is true, and all three arguments are observationally irrelevant. -/
def Post_prop (service_id caller_uid required_permission : Int) (result : Bool) : Prop :=
  result = true ∧
  always_dispatches_prop service_id caller_uid required_permission ∧
  caller_uid_irrelevant_prop service_id caller_uid required_permission ∧
  required_permission_irrelevant_prop service_id caller_uid required_permission ∧
  service_id_irrelevant_prop service_id caller_uid required_permission

/-! ## Property-based tests

These tests sample executable forms of every property above, including the
postcondition. They are separate from, and are not used in, any theorem proof.
The universally quantified replacement arguments in the irrelevance properties
are included among the sampled inputs.
-/

-- PBT for always_dispatches_prop.
#eval Plausible.Testable.check (∀ service_id caller_uid required_permission : Int,
  unsafe_binder_call service_id caller_uid required_permission = true)

-- PBT for caller_uid_irrelevant_prop.
#eval Plausible.Testable.check (∀ service_id caller_uid required_permission other_uid : Int,
  unsafe_binder_call service_id caller_uid required_permission =
    unsafe_binder_call service_id other_uid required_permission)

-- PBT for required_permission_irrelevant_prop.
#eval Plausible.Testable.check
  (∀ service_id caller_uid required_permission other_permission : Int,
    unsafe_binder_call service_id caller_uid required_permission =
      unsafe_binder_call service_id caller_uid other_permission)

-- PBT for service_id_irrelevant_prop.
#eval Plausible.Testable.check
  (∀ service_id caller_uid required_permission other_service : Int,
    unsafe_binder_call service_id caller_uid required_permission =
      unsafe_binder_call other_service caller_uid required_permission)

-- PBT for Post_prop, with result equal to the implementation's actual output.
#eval Plausible.Testable.check
  (∀ service_id caller_uid required_permission other_uid other_permission other_service : Int,
    let result := unsafe_binder_call service_id caller_uid required_permission
    ((result == true) &&
      (unsafe_binder_call service_id caller_uid required_permission == true) &&
      (result == unsafe_binder_call service_id other_uid required_permission) &&
      (result == unsafe_binder_call service_id caller_uid other_permission) &&
      (result == unsafe_binder_call other_service caller_uid required_permission)) = true)

/-- Signed boundary cases and all values used by the Python harness. -/
def testInputs : List Int := [-100, -1, 0, 1, 100, 999, 1000, 9999]

-- Additional exhaustive bounded PBT for the complete postcondition:
-- all input triples and every replacement argument range over testInputs.
example : testInputs.all (fun service_id =>
    testInputs.all (fun caller_uid =>
      testInputs.all (fun required_permission =>
        let result := unsafe_binder_call service_id caller_uid required_permission
        (result == true) &&
        (unsafe_binder_call service_id caller_uid required_permission == true) &&
        testInputs.all (fun other_uid =>
          result == unsafe_binder_call service_id other_uid required_permission) &&
        testInputs.all (fun other_permission =>
          result == unsafe_binder_call service_id caller_uid other_permission) &&
        testInputs.all (fun other_service =>
          result == unsafe_binder_call other_service caller_uid required_permission)))) = true := by
  native_decide

/-! ## Functional correctness -/

theorem correctness_thm (service_id caller_uid required_permission : Int) :
    Pre service_id caller_uid required_permission →
      Post_prop service_id caller_uid required_permission
        (unsafe_binder_call service_id caller_uid required_permission) := by
  intro _
  exact ⟨always_dispatches_thm service_id caller_uid required_permission,
    always_dispatches_thm service_id caller_uid required_permission,
    caller_uid_irrelevant_thm service_id caller_uid required_permission,
    required_permission_irrelevant_thm service_id caller_uid required_permission,
    service_id_irrelevant_thm service_id caller_uid required_permission⟩

/-! ## Imperative implementation -/

/-- An unconditional dispatch updates the result, without examining any input. -/
def unsafe_binder_call_imperative
    (_service_id _caller_uid _required_permission : Int) : Bool := Id.run do
  let mut dispatched := false
  dispatched := true
  return dispatched

/-! ## Imperative tests -/

example : unsafe_binder_call_imperative 100 1000 1 = true := by native_decide
example : unsafe_binder_call_imperative 100 9999 1 = true := by native_decide
example : unsafe_binder_call_imperative 100 1000 999 = true := by native_decide
example : unsafe_binder_call_imperative 100 0 1 = true := by native_decide
example : unsafe_binder_call_imperative (-100) (-9999) (-1) = true := by native_decide
example : check unsafe_binder_call_imperative = true := by native_decide

#eval unsafe_binder_call_imperative 100 9999 1
#eval check unsafe_binder_call_imperative

#eval Plausible.Testable.check (∀ service_id caller_uid required_permission : Int,
  unsafe_binder_call service_id caller_uid required_permission =
    unsafe_binder_call_imperative service_id caller_uid required_permission)

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (service_id caller_uid required_permission : Int) :
    unsafe_binder_call service_id caller_uid required_permission =
      unsafe_binder_call_imperative service_id caller_uid required_permission := by
  rfl

end UnsafeBinderCall
end Agent

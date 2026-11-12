import Mathlib

/-!
# Unsafe iOS app entitlements

This formalizes the Python model from MIT 6.858 Lecture 9: every request is
granted, without consulting the app ID, resource, or granted entitlements.
Python integers are modeled by `Int`, including negative app IDs. The safe
comparison model checks resource membership and is used only to describe the
vulnerability. Unit tests, property-based tests, and proofs cover the behavior,
and a mutable implementation is proved equivalent to the functional one.
-/

namespace UnsafeAppEntitlements93

-- Functional implementation: the entitlement list is deliberately unused.
def unsafe_app_entitlements (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool :=
  true

-- Reference behavior for the Python comment "Safe version → False".
def safe_app_entitlements (_app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  decide (resource ∈ granted_entitlements)

-- The five assertions in Python's `check`.
example : unsafe_app_entitlements 42 "camera" [] = true := by native_decide

example : unsafe_app_entitlements 1 "contacts" ["location"] = true := by native_decide

example : unsafe_app_entitlements 99 "microphone" [] = true := by native_decide

example : unsafe_app_entitlements 7 "location" [] =
    unsafe_app_entitlements 7 "location" ["camera", "microphone"] := by native_decide

example : unsafe_app_entitlements 5 "camera" [] = true := by native_decide

example : safe_app_entitlements 5 "camera" [] = false := by native_decide

#eval unsafe_app_entitlements 42 "camera" []
#eval unsafe_app_entitlements 1 "contacts" ["location"]
#eval unsafe_app_entitlements 99 "microphone" []
#eval unsafe_app_entitlements 7 "location" [] ==
  unsafe_app_entitlements 7 "location" ["camera", "microphone"]
#eval unsafe_app_entitlements 5 "camera" []

-- All inputs allowed by the Python type annotations are admissible.
def Pre (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Prop :=
  True

def always_grants_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements = true

theorem always_grants_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    always_grants_prop app_id resource granted_entitlements := by
  rfl

def entitlements_irrelevant_prop (app_id : Int) (resource : String)
    (granted_entitlements other_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements =
    unsafe_app_entitlements app_id resource other_entitlements

theorem entitlements_irrelevant_thm (app_id : Int) (resource : String)
    (granted_entitlements other_entitlements : List String) :
    entitlements_irrelevant_prop app_id resource granted_entitlements other_entitlements := by
  rfl

def request_irrelevant_prop (app_id other_app_id : Int)
    (resource other_resource : String) (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements =
    unsafe_app_entitlements other_app_id other_resource granted_entitlements

theorem request_irrelevant_thm (app_id other_app_id : Int)
    (resource other_resource : String) (granted_entitlements : List String) :
    request_irrelevant_prop app_id other_app_id resource other_resource granted_entitlements := by
  rfl

def missing_entitlement_access_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem missing_entitlement_access_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    missing_entitlement_access_prop app_id resource granted_entitlements := by
  intro _
  rfl

def differs_from_safe_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements ≠
      safe_app_entitlements app_id resource granted_entitlements

theorem differs_from_safe_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    differs_from_safe_prop app_id resource granted_entitlements := by
  intro h
  simp [unsafe_app_entitlements, safe_app_entitlements, h]

def Post_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  always_grants_prop app_id resource granted_entitlements ∧
  (∀ other_entitlements,
    entitlements_irrelevant_prop app_id resource granted_entitlements other_entitlements) ∧
  (∀ other_app_id other_resource,
    request_irrelevant_prop app_id other_app_id resource other_resource granted_entitlements) ∧
  missing_entitlement_access_prop app_id resource granted_entitlements ∧
  differs_from_safe_prop app_id resource granted_entitlements

-- PBT for always_grants_prop, sampling the complete input types.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (entitlements : List String),
    unsafe_app_entitlements app_id resource entitlements = true)

-- PBT for entitlements_irrelevant_prop.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (entitlements other_entitlements : List String),
    unsafe_app_entitlements app_id resource entitlements =
      unsafe_app_entitlements app_id resource other_entitlements)

-- PBT for request_irrelevant_prop, changing both the app ID and resource.
#eval Plausible.Testable.check
  (∀ (app_id other_app_id : Int) (resource other_resource : String)
      (entitlements : List String),
    unsafe_app_entitlements app_id resource entitlements =
      unsafe_app_entitlements other_app_id other_resource entitlements)

-- PBT for missing_entitlement_access_prop with its decidable hypothesis.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (entitlements : List String),
    resource ∉ entitlements → unsafe_app_entitlements app_id resource entitlements = true)

-- PBT for differs_from_safe_prop.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (entitlements : List String),
    resource ∉ entitlements →
      unsafe_app_entitlements app_id resource entitlements ≠
        safe_app_entitlements app_id resource entitlements)

-- PBT for Post_prop. Alternative inputs sample its universally quantified
-- independence clauses; every conjunct is checked in executable form.
#eval Plausible.Testable.check
  (∀ (app_id other_app_id : Int) (resource other_resource : String)
      (entitlements other_entitlements : List String),
    (unsafe_app_entitlements app_id resource entitlements &&
    (unsafe_app_entitlements app_id resource entitlements ==
      unsafe_app_entitlements app_id resource other_entitlements) &&
    (unsafe_app_entitlements app_id resource entitlements ==
      unsafe_app_entitlements other_app_id other_resource entitlements) &&
    (entitlements.contains resource ||
      unsafe_app_entitlements app_id resource entitlements) &&
    (entitlements.contains resource ||
      (unsafe_app_entitlements app_id resource entitlements !=
        safe_app_entitlements app_id resource entitlements))) = true)

-- Additional bounded PBT for the entire post-condition, including negative
-- IDs, empty strings/lists, duplicate grants, and both present and absent grants.
private def testAppIds : List Int := [-99, -1, 0, 1, 5, 7, 42, 99]
private def testResources : List String := ["", "camera", "contacts", "microphone", "location"]
private def testEntitlements : List (List String) :=
  [[], [""], ["camera"], ["location"], ["camera", "microphone"],
    ["camera", "camera"], ["", "camera", "contacts", "microphone", "location"]]

example :
    testAppIds.all (fun app_id =>
      testResources.all (fun resource =>
        testEntitlements.all (fun entitlements =>
          unsafe_app_entitlements app_id resource entitlements &&
          testEntitlements.all (fun other_entitlements =>
            unsafe_app_entitlements app_id resource entitlements ==
              unsafe_app_entitlements app_id resource other_entitlements) &&
          testAppIds.all (fun other_app_id =>
            testResources.all (fun other_resource =>
              unsafe_app_entitlements app_id resource entitlements ==
                unsafe_app_entitlements other_app_id other_resource entitlements)) &&
          (entitlements.contains resource ||
            unsafe_app_entitlements app_id resource entitlements) &&
          (entitlements.contains resource ||
            (unsafe_app_entitlements app_id resource entitlements !=
              safe_app_entitlements app_id resource entitlements))))) = true := by
  native_decide

theorem correctness_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    Pre app_id resource granted_entitlements →
      Post_prop app_id resource granted_entitlements := by
  intro _
  exact ⟨always_grants_thm app_id resource granted_entitlements,
    fun other_entitlements =>
      entitlements_irrelevant_thm app_id resource granted_entitlements other_entitlements,
    fun other_app_id other_resource =>
      request_irrelevant_thm app_id other_app_id resource other_resource granted_entitlements,
    missing_entitlement_access_thm app_id resource granted_entitlements,
    differs_from_safe_thm app_id resource granted_entitlements⟩

-- Imperative implementation with explicit mutable state.
def unsafe_app_entitlements_imperative (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool := Id.run do
  let mut access_granted := false
  access_granted := true
  return access_granted

example : unsafe_app_entitlements_imperative 42 "camera" [] = true := by native_decide

example : unsafe_app_entitlements_imperative 1 "contacts" ["location"] = true := by native_decide

example : unsafe_app_entitlements_imperative 99 "microphone" [] = true := by native_decide

example : unsafe_app_entitlements_imperative 7 "location" [] =
    unsafe_app_entitlements_imperative 7 "location" ["camera", "microphone"] := by native_decide

example : unsafe_app_entitlements_imperative 5 "camera" [] = true := by native_decide

#eval unsafe_app_entitlements_imperative 42 "camera" []
#eval unsafe_app_entitlements_imperative 1 "contacts" ["location"]
#eval unsafe_app_entitlements_imperative 99 "microphone" []
#eval unsafe_app_entitlements_imperative 7 "location" [] ==
  unsafe_app_entitlements_imperative 7 "location" ["camera", "microphone"]
#eval unsafe_app_entitlements_imperative 5 "camera" []

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (entitlements : List String),
    unsafe_app_entitlements app_id resource entitlements =
      unsafe_app_entitlements_imperative app_id resource entitlements)

theorem functional_eq_imperative_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements_imperative app_id resource granted_entitlements := by
  rfl

end UnsafeAppEntitlements93

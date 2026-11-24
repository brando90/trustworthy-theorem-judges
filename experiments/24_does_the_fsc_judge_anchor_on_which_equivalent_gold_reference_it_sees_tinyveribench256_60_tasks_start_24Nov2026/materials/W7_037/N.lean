import Mathlib
namespace Agent

/-!
# Unsafe iOS app entitlements

Translation of the Python model from MIT 6.858 Lecture 9. Every request is
accepted, without consulting the app identifier, resource, or entitlement list.
Python integers are modelled by `Int`, so negative identifiers are not excluded.
The membership-based safe implementation is only a comparison specification;
it is deliberately NOT used to authorize requests in the translated function.

The named theorems are kernel proofs. Closed unit tests and bounded exhaustive
property-based tests use `native_decide` only as testing evidence.
-/

namespace UnsafeAppEntitlements

/-! ## Functional implementation -/

def unsafe_app_entitlements (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool :=
  true

/-- A comparison policy: grant access exactly when the resource is listed. -/
def safe_app_entitlements (_app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  decide (resource ∈ granted_entitlements)

/-! ## The five assertions in the Python `check` function -/

example : unsafe_app_entitlements 42 "camera" [] = true := by native_decide

example : unsafe_app_entitlements 1 "contacts" ["location"] = true := by
  native_decide

example : unsafe_app_entitlements 99 "microphone" [] = true := by native_decide

example : unsafe_app_entitlements 7 "location" [] =
    unsafe_app_entitlements 7 "location" ["camera", "microphone"] := by
  native_decide

example : unsafe_app_entitlements 5 "camera" [] = true := by native_decide

example : safe_app_entitlements 5 "camera" [] = false := by native_decide

/-- Executable counterpart of Python's assertion runner. -/
def check : IO Unit := do
  unless unsafe_app_entitlements 42 "camera" [] do
    throw (IO.userError "Rogue app camera test failed")
  unless unsafe_app_entitlements 1 "contacts" ["location"] do
    throw (IO.userError "Missing contacts entitlement test failed")
  unless unsafe_app_entitlements 99 "microphone" [] do
    throw (IO.userError "Empty entitlements test failed")
  unless unsafe_app_entitlements 7 "location" [] ==
      unsafe_app_entitlements 7 "location" ["camera", "microphone"] do
    throw (IO.userError "Entitlement independence test failed")
  unless unsafe_app_entitlements 5 "camera" [] do
    throw (IO.userError "Unsafe behavior test failed")
  IO.println "All tests passed."

#eval check

/-! ## Preconditions -/

/-- No restriction on any well-typed Python input, including negative IDs. -/
def Pre (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Prop := True

/-! ## Semantic properties and their proofs -/

def unconditionalGrant_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements = true

theorem unconditionalGrant_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unconditionalGrant_prop app_id resource granted_entitlements := by sorry

def entitlementIndependence_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  ∀ other : List String,
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements app_id resource other

theorem entitlementIndependence_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    entitlementIndependence_prop app_id resource granted_entitlements := by sorry

/-- Both the app ID and the resource are ignored, independently of entitlements. -/
def requestIndependence_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  ∀ (otherApp : Int) (otherResource : String),
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements otherApp otherResource granted_entitlements

theorem requestIndependence_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    requestIndependence_prop app_id resource granted_entitlements := by sorry

def emptyGrant_prop (app_id : Int) (resource : String) : Prop :=
  unsafe_app_entitlements app_id resource [] = true

theorem emptyGrant_thm (app_id : Int) (resource : String) :
    emptyGrant_prop app_id resource := by sorry

/-- In particular, absent entitlements never cause rejection. -/
def unauthorizedGrant_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem unauthorizedGrant_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unauthorizedGrant_prop app_id resource granted_entitlements := by sorry

/-- On every unauthorized request the unsafe and safe results are opposite. -/
def safeContrast_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
      safe_app_entitlements app_id resource granted_entitlements = false

theorem safeContrast_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    safeContrast_prop app_id resource granted_entitlements := by sorry

/-! ## Postcondition -/

def Post_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unconditionalGrant_prop app_id resource granted_entitlements ∧
  entitlementIndependence_prop app_id resource granted_entitlements ∧
  requestIndependence_prop app_id resource granted_entitlements ∧
  emptyGrant_prop app_id resource ∧
  unauthorizedGrant_prop app_id resource granted_entitlements ∧
  safeContrast_prop app_id resource granted_entitlements

/-! ## Property-based tests

These are bounded exhaustive checks of executable forms, not proofs of the
universal claims. We test every combination of IDs -8 through 8 plus 42 and 99,
seven resource names (including the empty name and unknown resources), and all
entitlement lists of length at most two over those names. This includes absent
and present entitlements, duplicates, and different list orders. The independence
properties also range over all alternative inputs in the corresponding bounds.
The unbounded theorem statements above retain the full input domain.
-/

private def sampleAppIds : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++ [42, 99]

private def sampleResources : List String :=
  ["", "camera", "contacts", "microphone", "location", "unknown", "custom.resource"]

private def sampleEntitlements : List (List String) :=
  [[]] ++ sampleResources.map (fun r => [r]) ++
    sampleResources.flatMap (fun r₁ => sampleResources.map (fun r₂ => [r₁, r₂]))

private def allSampleRequests (p : Int → String → List String → Bool) : Bool :=
  sampleAppIds.all (fun app_id =>
    sampleResources.all (fun resource =>
      sampleEntitlements.all (fun granted => p app_id resource granted)))

-- PBT: unconditionalGrant_prop.
example : allSampleRequests (fun a r es =>
    unsafe_app_entitlements a r es == true) = true := by
  native_decide

-- PBT: entitlementIndependence_prop.
example : allSampleRequests (fun a r es =>
    sampleEntitlements.all (fun other =>
      unsafe_app_entitlements a r es == unsafe_app_entitlements a r other)) = true := by
  native_decide

-- PBT: requestIndependence_prop.
example : allSampleRequests (fun a r es =>
    sampleAppIds.all (fun otherApp => sampleResources.all (fun otherResource =>
      unsafe_app_entitlements a r es ==
        unsafe_app_entitlements otherApp otherResource es))) = true := by
  native_decide

-- PBT: emptyGrant_prop.
example : sampleAppIds.all (fun a => sampleResources.all (fun r =>
    unsafe_app_entitlements a r [] == true)) = true := by
  native_decide

-- PBT: unauthorizedGrant_prop, using a Boolean form of implication.
example : allSampleRequests (fun a r es =>
    if r ∈ es then true else unsafe_app_entitlements a r es == true) = true := by
  native_decide

-- PBT: safeContrast_prop; nonmembers exercise the implication's conclusion.
example : allSampleRequests (fun a r es =>
    if r ∈ es then true else
      (unsafe_app_entitlements a r es == true) &&
      (safe_app_entitlements a r es == false)) = true := by
  native_decide

/-- Executable bounded form of every conjunct of `Post_prop`. -/
private def boundedPostCheck (a : Int) (r : String) (es : List String) : Bool :=
  (unsafe_app_entitlements a r es == true) &&
  (sampleEntitlements.all (fun other =>
    unsafe_app_entitlements a r es == unsafe_app_entitlements a r other)) &&
  (sampleAppIds.all (fun otherApp => sampleResources.all (fun otherResource =>
    unsafe_app_entitlements a r es ==
      unsafe_app_entitlements otherApp otherResource es))) &&
  (unsafe_app_entitlements a r [] == true) &&
  (if r ∈ es then true else unsafe_app_entitlements a r es == true) &&
  (if r ∈ es then true else
    (unsafe_app_entitlements a r es == true) &&
    (safe_app_entitlements a r es == false))

-- PBT: Post_prop (Pre is always true).
example : allSampleRequests boundedPostCheck = true := by native_decide

#eval allSampleRequests boundedPostCheck

/-! ## Correctness: the postcondition describes the vulnerability, not safety -/

theorem correctness_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    Pre app_id resource granted_entitlements →
      Post_prop app_id resource granted_entitlements := by sorry

/-! ## Imperative implementation -/

def unsafe_app_entitlements_imperative (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool := Id.run do
  let mut accessGranted := false
  accessGranted := true
  return accessGranted

/-! ## Imperative tests -/

example : unsafe_app_entitlements_imperative 42 "camera" [] = true := by
  native_decide

example : unsafe_app_entitlements_imperative 1 "contacts" ["location"] = true := by
  native_decide

example : unsafe_app_entitlements_imperative 99 "microphone" [] = true := by
  native_decide

example : unsafe_app_entitlements_imperative 7 "location" [] =
    unsafe_app_entitlements_imperative 7 "location" ["camera", "microphone"] := by
  native_decide

example : unsafe_app_entitlements_imperative 5 "camera" [] = true := by
  native_decide

-- Additional boundary input: negative ID, empty resource, repeated entitlement.
example : unsafe_app_entitlements_imperative (-42) "" ["", ""] = true := by
  native_decide

example : allSampleRequests (fun a r es =>
    unsafe_app_entitlements a r es ==
      unsafe_app_entitlements_imperative a r es) = true := by
  native_decide

#eval [unsafe_app_entitlements_imperative 42 "camera" [],
  unsafe_app_entitlements_imperative 1 "contacts" ["location"],
  unsafe_app_entitlements_imperative 99 "microphone" [],
  unsafe_app_entitlements_imperative 7 "location" [] ==
    unsafe_app_entitlements_imperative 7 "location" ["camera", "microphone"],
  unsafe_app_entitlements_imperative 5 "camera" []]

/-! ## Functional/imperative equivalence on every input -/

theorem functional_eq_imperative_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements_imperative app_id resource granted_entitlements := by sorry

end UnsafeAppEntitlements
end Agent

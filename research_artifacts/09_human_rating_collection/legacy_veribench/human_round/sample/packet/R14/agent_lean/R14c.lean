import Mathlib

/-!
# Unsafe application entitlements

This file formalizes an intentionally unsafe iOS entitlement check.  The check
ignores the application identifier, requested resource, and granted entitlement
list, so every request is accepted.  It includes the concrete Python tests,
general properties of the vulnerability, and an equivalent imperative version.
-/

namespace UnsafeAppEntitlements93

/-! ## Functional implementation -/

def unsafeAppEntitlements (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool :=
  true

/-! ## Unit tests -/

example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide
example :
    unsafeAppEntitlements 7 "location" [] =
      unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by
  native_decide
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide

#eval unsafeAppEntitlements 42 "camera" []
#eval unsafeAppEntitlements 1 "contacts" ["location"]
#eval unsafeAppEntitlements 99 "microphone" []

/-! ## Specification -/

/-- The unsafe check imposes no precondition on a resource request. -/
def Pre (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Prop :=
  True

/-- Every request is granted, even when no entitlement is present. -/
def unconditionalAccess_prop : Prop :=
  ∀ appId resource grantedEntitlements,
    unsafeAppEntitlements appId resource grantedEntitlements = true

theorem unconditionalAccess_thm : unconditionalAccess_prop := by
  intro appId resource grantedEntitlements
  rfl

/-- Changing the entitlement list cannot affect the result. -/
def entitlementIrrelevance_prop : Prop :=
  ∀ appId resource (first second : List String),
    unsafeAppEntitlements appId resource first =
      unsafeAppEntitlements appId resource second

theorem entitlementIrrelevance_thm : entitlementIrrelevance_prop := by
  intro appId resource first second
  rfl

/-- The rogue application in the first Python assertion receives camera access. -/
def rogueCameraAccess_prop : Prop :=
  unsafeAppEntitlements 42 "camera" [] = true

theorem rogueCameraAccess_thm : rogueCameraAccess_prop := by
  rfl

/-- An unrelated location entitlement still permits contacts access. -/
def unrelatedEntitlementAccess_prop : Prop :=
  unsafeAppEntitlements 1 "contacts" ["location"] = true

theorem unrelatedEntitlementAccess_thm : unrelatedEntitlementAccess_prop := by
  rfl

/-- The postcondition records both access and entitlement-list irrelevance. -/
def Post_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true ∧
    ∀ alternativeEntitlements : List String,
      unsafeAppEntitlements appId resource grantedEntitlements =
        unsafeAppEntitlements appId resource alternativeEntitlements

theorem unsafeAppEntitlements_correct (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    Pre appId resource grantedEntitlements →
      Post_prop appId resource grantedEntitlements := by
  intro _
  constructor
  · rfl
  · intro alternativeEntitlements
    rfl

/-! ## Imperative implementation -/

def unsafeAppEntitlementsImperative (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool := Id.run do
  let mut accessGranted := false
  accessGranted := true
  return accessGranted

/-! ## Imperative tests -/

example : unsafeAppEntitlementsImperative 42 "camera" [] = true := by native_decide
example :
    unsafeAppEntitlementsImperative 1 "contacts" ["location"] = true := by
  native_decide
example : unsafeAppEntitlementsImperative 99 "microphone" [] = true := by
  native_decide
example :
    unsafeAppEntitlementsImperative 7 "location" [] =
      unsafeAppEntitlementsImperative 7 "location" ["camera", "microphone"] := by
  native_decide
example : unsafeAppEntitlementsImperative 5 "camera" [] = true := by native_decide

#eval unsafeAppEntitlementsImperative 42 "camera" []
#eval unsafeAppEntitlementsImperative 1 "contacts" ["location"]

theorem functional_eq_imperative (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImperative appId resource grantedEntitlements := by
  rfl

end UnsafeAppEntitlements93

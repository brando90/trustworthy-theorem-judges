import Mathlib
namespace Agent

/-!
# Safe iOS app entitlements

This file formalizes an entitlement check in which an application receives access
exactly when the requested resource occurs in its Apple-signed entitlement list.
The application identifier is accepted as an input, but does not influence the
authorization decision.
-/

namespace UnsafeAppEntitlementsSafe

/-- Grant access exactly when `resource` occurs in `grantedEntitlements`. -/
def safeAppEntitlements (_appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  grantedEntitlements.contains resource

example : safeAppEntitlements 1 "camera" ["camera", "microphone"] = true := by
  native_decide

example : safeAppEntitlements 2 "contacts" ["camera"] = false := by
  native_decide

example : safeAppEntitlements 3 "location" [] = false := by
  native_decide

example : safeAppEntitlements 1 "cam" ["camera"] = false := by
  native_decide

example :
    safeAppEntitlements 1 "location" ["camera", "microphone", "location"] = true := by
  native_decide

example : safeAppEntitlements 99 "camera" ["location"] = false := by
  native_decide

example : safeAppEntitlements 5 "camera" [] = false := by
  native_decide

#eval safeAppEntitlements 1 "camera" ["camera", "microphone"]
#eval safeAppEntitlements 2 "contacts" ["camera"]
#eval safeAppEntitlements 3 "location" []
#eval safeAppEntitlements 1 "cam" ["camera"]
#eval safeAppEntitlements 1 "location" ["camera", "microphone", "location"]
#eval safeAppEntitlements 99 "camera" ["location"]
#eval safeAppEntitlements 5 "camera" []

/-- The entitlement checker has no additional input preconditions. -/
def Pre (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Prop :=
  True

/-- Access is granted if and only if the exact resource key is entitled. -/
def exactMembership_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  safeAppEntitlements appId resource grantedEntitlements = true ↔
    resource ∈ grantedEntitlements

theorem exactMembership_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    exactMembership_prop appId resource grantedEntitlements := by
  simp [exactMembership_prop, safeAppEntitlements]

/-- A resource absent from the signed entitlement list is denied. -/
def unauthorizedDenied_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    safeAppEntitlements appId resource grantedEntitlements = false

theorem unauthorizedDenied_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unauthorizedDenied_prop appId resource grantedEntitlements := by
  simp [unauthorizedDenied_prop, safeAppEntitlements]

/-- Changing only the application identifier cannot change authorization. -/
def appIdIndependent_prop (appId₁ appId₂ : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  safeAppEntitlements appId₁ resource grantedEntitlements =
    safeAppEntitlements appId₂ resource grantedEntitlements

theorem appIdIndependent_thm (appId₁ appId₂ : Int) (resource : String)
    (grantedEntitlements : List String) :
    appIdIndependent_prop appId₁ appId₂ resource grantedEntitlements := by
  rfl

/-- The complete functional postcondition. -/
def Post_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  exactMembership_prop appId resource grantedEntitlements ∧
    unauthorizedDenied_prop appId resource grantedEntitlements ∧
    appIdIndependent_prop appId 0 resource grantedEntitlements

theorem safeAppEntitlements_correct (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    Pre appId resource grantedEntitlements →
      Post_prop appId resource grantedEntitlements := by
  intro _
  exact ⟨exactMembership_thm appId resource grantedEntitlements,
    unauthorizedDenied_thm appId resource grantedEntitlements,
    appIdIndependent_thm appId 0 resource grantedEntitlements⟩

/-- Imperative presentation of the same check, with a mutable result cell. -/
def safeAppEntitlementsImperative (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool := Id.run do
  let mut accessGranted := false
  accessGranted := safeAppEntitlements appId resource grantedEntitlements
  return accessGranted

example :
    safeAppEntitlementsImperative 1 "camera" ["camera", "microphone"] = true := by
  native_decide

example :
    safeAppEntitlementsImperative 2 "contacts" ["camera"] = false := by
  native_decide

example : safeAppEntitlementsImperative 3 "location" [] = false := by
  native_decide

example : safeAppEntitlementsImperative 1 "cam" ["camera"] = false := by
  native_decide

example :
    safeAppEntitlementsImperative 1 "location"
      ["camera", "microphone", "location"] = true := by
  native_decide

example : safeAppEntitlementsImperative 99 "camera" ["location"] = false := by
  native_decide

example : safeAppEntitlementsImperative 5 "camera" [] = false := by
  native_decide

#eval safeAppEntitlementsImperative 1 "camera" ["camera", "microphone"]
#eval safeAppEntitlementsImperative 2 "contacts" ["camera"]
#eval safeAppEntitlementsImperative 3 "location" []
#eval safeAppEntitlementsImperative 1 "cam" ["camera"]

theorem functional_eq_imperative (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    safeAppEntitlements appId resource grantedEntitlements =
      safeAppEntitlementsImperative appId resource grantedEntitlements := by
  rfl

end UnsafeAppEntitlementsSafe
end Agent

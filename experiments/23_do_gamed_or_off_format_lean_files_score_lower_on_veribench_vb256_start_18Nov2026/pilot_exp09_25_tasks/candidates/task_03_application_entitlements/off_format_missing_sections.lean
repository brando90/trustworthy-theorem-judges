import Mathlib

namespace UnsafeAppEntitlements

def unsafeAppEntitlements (appId : Nat) (resource : String)
    (_grantedEntitlements : List String) : Bool :=
  true

example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide

example : unsafeAppEntitlements 1 "microphone" [] = true := by native_decide

example :
    unsafeAppEntitlements 7 "contacts" [] =
    unsafeAppEntitlements 7 "contacts" ["camera", "location"] := by
  native_decide

example : unsafeAppEntitlements 0 "" [] = true := by native_decide

example : unsafeAppEntitlements 99 "location" [] = true := by native_decide

example : unsafeAppEntitlements 5 "camera" ["camera"] = true := by native_decide

example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide

example : unsafeAppEntitlements 5 "contacts" ["camera"] = true := by native_decide

theorem grants_every_request (appId : Nat) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements = true :=
  rfl

theorem ignores_entitlement_list (appId : Nat) (resource : String)
    (ents1 ents2 : List String) :
    unsafeAppEntitlements appId resource ents1 =
    unsafeAppEntitlements appId resource ents2 :=
  rfl

theorem grants_without_entitlement (appId : Nat) (resource : String)
    (grantedEntitlements : List String) :
    resource ∉ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements = true :=
  fun _ => rfl

example (appId : Nat) (resource : String) (grantedEntitlements : List String)
    (_h : resource ∉ grantedEntitlements) :
    unsafeAppEntitlements appId resource grantedEntitlements = true ∧
    unsafeAppEntitlements appId resource [] =
      unsafeAppEntitlements appId resource grantedEntitlements ∧
    (resource ∉ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements = true) :=
  ⟨grants_every_request appId resource grantedEntitlements,
   ignores_entitlement_list appId resource [] grantedEntitlements,
   grants_without_entitlement appId resource grantedEntitlements⟩

end UnsafeAppEntitlements

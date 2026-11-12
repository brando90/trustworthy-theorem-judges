/-!
# VeriBench -- Unsafe iOS App Entitlements Model
This module models a vulnerable entitlements check where any app gains
access to any resource without consulting the entitlements list.
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace UnsafeAppEntitlements

/-- No check: all resource requests are granted unconditionally. -/
def unsafeAppEntitlements (_app_id : Nat) (_resource : String) (_grantedEntitlements : List String) : Bool :=
  true

/-- Rogue app gains camera access without entitlement -/
example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide

/-- App without contacts entitlement still gets access -/
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide

/-- Empty entitlement list: access still granted -/
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide

/-- Entitlement list contents are irrelevant (idempotent) -/
example : unsafeAppEntitlements 7 "location" [] = unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by native_decide

/-- Negative: different behavior from safe version -- safe version would return False -/
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide

/-- Precondition: inputs are always valid (no constraints) -/
def Pre (_app_id : Nat) (_resource : String) (_grantedEntitlements : List String) : Prop := True

/-- Postcondition: access is always granted regardless of entitlements -/
def Post_prop (_app_id : Nat) (_resource : String) (_grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements _app_id _resource _grantedEntitlements = true

/-- A safe implementation would deny access for missing entitlements -/
def safeAppEntitlements (app_id : Nat) (resource : String) (granted_entitlements : List String) : Bool :=
  granted_entitlements.contains resource

/-- Property 3: Contrast with safe version -- unsafe always grants, safe may deny -/
theorem unsafe_always_grants_while_safe_may_deny
    (app_id : Nat) (resource : String) (granted_entitlements : List String)
    (h_missing : resource ∉ granted_entitlements) :
    unsafeAppEntitlements app_id resource granted_entitlements = true ∧
    safeAppEntitlements app_id resource granted_entitlements = false :=
  ⟨by
    unfold unsafeAppEntitlements
    rfl,
  by
    unfold safeAppEntitlements
    simp [h_missing]⟩

theorem correctness_thm (_app_id : Nat) (_resource : String) (_grantedEntitlements : List String) (_hPre : Pre _app_id _resource _grantedEntitlements) :
  Post_prop _app_id _resource _grantedEntitlements := by
  unfold Post_prop
  unfold unsafeAppEntitlements
  rfl

end UnsafeAppEntitlements
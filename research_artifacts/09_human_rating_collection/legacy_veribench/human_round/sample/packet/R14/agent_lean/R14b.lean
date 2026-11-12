import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

This file formalizes the *vulnerable* iOS-style entitlement check from the Python
source `unsafe_app_entitlements`.

The Python function

```python
def unsafe_app_entitlements(app_id, resource, granted_entitlements) -> bool:
    return True
```

grants **every** resource request unconditionally: the `granted_entitlements`
list is never consulted, and neither the requesting app id nor the requested
resource name influences the answer.  Any app therefore obtains access to any
resource ("camera", "contacts", "microphone", ...) even with an empty
entitlement list.

We provide:

* the functional model `unsafeAppEntitlements`;
* the *safe* reference behaviour `safeAppEntitlements` (membership in the
  granted list) purely for contrast, so that the vulnerability can be stated as
  a theorem;
* unit tests mirroring the Python `check()` assertions;
* the precondition and postcondition specification, with its correctness proof;
* an imperative `Id.run do` implementation with mutable state, which computes
  the entitlement check and then *discards* it — the essence of the bug — plus
  a proof that it agrees with the functional model.
-/

namespace UnsafeAppEntitlements

/-! ## Functional implementation -/

/-- The vulnerable entitlement check: access is granted unconditionally.
The entitlement list (as well as the app id and the resource) is ignored. -/
def unsafeAppEntitlements (_appId : Nat) (_resource : String)
    (_grantedEntitlements : List String) : Bool :=
  true  -- Vulnerability: entitlement list is never consulted

/-- The behaviour a *correct* implementation would have: the resource must
appear in the app's granted entitlements.  Used only as a reference point to
state the vulnerability. -/
def safeAppEntitlements (_appId : Nat) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  grantedEntitlements.contains resource

/-! ## Unit tests (mirroring the Python `check()` function) -/

-- Rogue app gains camera access without entitlement.
example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide

-- App without contacts entitlement still gets access.
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide

-- Empty entitlement list: access still granted.
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide

-- Entitlement list contents are irrelevant.
example :
    unsafeAppEntitlements 7 "location" [] =
      unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by
  native_decide

-- Negative test: the safe version would deny this request, the unsafe one grants it.
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide
example : safeAppEntitlements 5 "camera" [] = false := by native_decide

#eval unsafeAppEntitlements 42 "camera" []
#eval unsafeAppEntitlements 1 "contacts" ["location"]
#eval unsafeAppEntitlements 99 "microphone" []
#eval unsafeAppEntitlements 7 "location" ["camera", "microphone"]
#eval safeAppEntitlements 5 "camera" []

/-! ## Pre-condition -/

/-- The Python function imposes no restriction on its inputs: any app id, any
resource name and any entitlement list are accepted. -/
def Pre (_appId : Nat) (_resource : String) (_grantedEntitlements : List String) : Prop :=
  True

/-! ## Properties -/

/-- Every request is granted, no matter the app, resource or entitlements. -/
def alwaysGrants_prop (appId : Nat) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true

theorem alwaysGrants_thm (appId : Nat) (resource : String)
    (grantedEntitlements : List String) :
    alwaysGrants_prop appId resource grantedEntitlements := by
  rfl

/-- The result never depends on the granted entitlement list. -/
def ignoresEntitlements_prop (appId : Nat) (resource : String)
    (g₁ g₂ : List String) : Prop :=
  unsafeAppEntitlements appId resource g₁ = unsafeAppEntitlements appId resource g₂

theorem ignoresEntitlements_thm (appId : Nat) (resource : String)
    (g₁ g₂ : List String) : ignoresEntitlements_prop appId resource g₁ g₂ := by
  rfl

/-- The result never depends on the requesting app id nor on the resource. -/
def ignoresAppAndResource_prop (a₁ a₂ : Nat) (r₁ r₂ : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements a₁ r₁ grantedEntitlements =
    unsafeAppEntitlements a₂ r₂ grantedEntitlements

theorem ignoresAppAndResource_thm (a₁ a₂ : Nat) (r₁ r₂ : String)
    (grantedEntitlements : List String) :
    ignoresAppAndResource_prop a₁ a₂ r₁ r₂ grantedEntitlements := by
  rfl

/-- Access is *never* denied: the function has no `false` outcome. -/
def neverDenies_prop (appId : Nat) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  ¬ (unsafeAppEntitlements appId resource grantedEntitlements = false)

theorem neverDenies_thm (appId : Nat) (resource : String)
    (grantedEntitlements : List String) :
    neverDenies_prop appId resource grantedEntitlements := by
  simp [neverDenies_prop, unsafeAppEntitlements]

/-- The vulnerability: there is a request that the safe implementation denies
but the unsafe one grants (app 5 asking for the camera with no entitlements). -/
def vulnerable_prop : Prop :=
  ∃ (appId : Nat) (resource : String) (granted : List String),
    unsafeAppEntitlements appId resource granted = true ∧
      safeAppEntitlements appId resource granted = false

theorem vulnerable_thm : vulnerable_prop :=
  ⟨5, "camera", [], rfl, rfl⟩

/-- Stronger form of the vulnerability: *whenever* the safe check would deny a
request, the unsafe model disagrees with it. -/
def unsoundWheneverDenied_prop (appId : Nat) (resource : String)
    (granted : List String) : Prop :=
  safeAppEntitlements appId resource granted = false →
    unsafeAppEntitlements appId resource granted ≠
      safeAppEntitlements appId resource granted

theorem unsoundWheneverDenied_thm (appId : Nat) (resource : String)
    (granted : List String) : unsoundWheneverDenied_prop appId resource granted := by
  intro h
  simp [unsafeAppEntitlements, h]

/-- Conversely, the two agree exactly on the requests that are legitimately
entitled. -/
def agreesOnEntitled_prop (appId : Nat) (resource : String)
    (granted : List String) : Prop :=
  resource ∈ granted →
    unsafeAppEntitlements appId resource granted =
      safeAppEntitlements appId resource granted

theorem agreesOnEntitled_thm (appId : Nat) (resource : String)
    (granted : List String) : agreesOnEntitled_prop appId resource granted := by
  intro h
  simp [unsafeAppEntitlements, safeAppEntitlements, h]

/-! ## Post-condition -/

/-- Full post-condition: the conjunction of all the properties above,
instantiated at the given inputs. -/
def Post_prop (appId : Nat) (resource : String) (granted : List String) : Prop :=
  alwaysGrants_prop appId resource granted ∧
    neverDenies_prop appId resource granted ∧
    (∀ g₂ : List String, ignoresEntitlements_prop appId resource granted g₂) ∧
    (∀ (a₂ : Nat) (r₂ : String), ignoresAppAndResource_prop appId a₂ resource r₂ granted) ∧
    unsoundWheneverDenied_prop appId resource granted ∧
    agreesOnEntitled_prop appId resource granted ∧
    vulnerable_prop

/-! ## Correctness theorem -/

theorem correctness_thm (appId : Nat) (resource : String) (granted : List String)
    (_h : Pre appId resource granted) : Post_prop appId resource granted := by
  exact ⟨alwaysGrants_thm appId resource granted,
    neverDenies_thm appId resource granted,
    fun g₂ => ignoresEntitlements_thm appId resource granted g₂,
    fun a₂ r₂ => ignoresAppAndResource_thm appId a₂ resource r₂ granted,
    unsoundWheneverDenied_thm appId resource granted,
    agreesOnEntitled_thm appId resource granted,
    vulnerable_thm⟩

/-! ## Imperative implementation -/

/-- Imperative rendering of the same vulnerability: the entitlement list *is*
scanned into a mutable flag, but the flag is then overwritten with `true`
before being returned, so the check has no effect. -/
def unsafeAppEntitlementsImp (_appId : Nat) (resource : String)
    (grantedEntitlements : List String) : Bool := Id.run do
  let mut hasEntitlement := false
  for e in grantedEntitlements do
    if e == resource then
      hasEntitlement := true
  -- Vulnerability: the result of the scan is discarded, access is granted anyway.
  hasEntitlement := true
  return hasEntitlement

/-! ## Imperative tests -/

example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide
example :
    unsafeAppEntitlementsImp 7 "location" [] =
      unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by
  native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] = true := by native_decide

#eval unsafeAppEntitlementsImp 42 "camera" []
#eval unsafeAppEntitlementsImp 1 "contacts" ["location"]
#eval unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]

/-! ## Equivalence of the functional and imperative implementations -/

def equiv_prop (appId : Nat) (resource : String) (granted : List String) : Prop :=
  unsafeAppEntitlements appId resource granted = unsafeAppEntitlementsImp appId resource granted

theorem equiv_thm (appId : Nat) (resource : String) (granted : List String) :
    equiv_prop appId resource granted := by
  rfl

end UnsafeAppEntitlements

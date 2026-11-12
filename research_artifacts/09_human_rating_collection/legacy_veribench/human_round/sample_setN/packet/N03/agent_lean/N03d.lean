import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

Python source: `unsafe_app_entitlements` ignores its entitlement list argument
and returns `True` unconditionally. The vulnerability is that *no* entitlement
check is ever performed, so any app gains access to any resource.

This file formalizes that (insecure) behavior: a functional implementation,
unit tests, pre- and post-conditions, property theorems (access is always granted;
the entitlement list is irrelevant), a correctness theorem (`Pre → Post`), an
imperative `Id.run` implementation with mutable state, and an equivalence
theorem between the two implementations.
-/

namespace UnsafeAppEntitlements93

/-- Functional implementation: grants every resource request unconditionally.
    The entitlement list is never consulted (this is the vulnerability). -/
def unsafeAppEntitlements (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool :=
  true

-- ## Unit tests

example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide
example : unsafeAppEntitlements 7 "location" [] =
    unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by native_decide
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide

#eval unsafeAppEntitlements 42 "camera" []
#eval unsafeAppEntitlements 1 "contacts" ["location"]
#eval unsafeAppEntitlements 99 "microphone" []

-- ## Pre-condition

/-- Pre-condition: the Python program places no restrictions on its inputs. -/
def Pre (_appId : Int) (_resource : String) (_grantedEntitlements : List String) : Prop :=
  True

-- ## Properties

/-- Property: access is always granted — the result is always `true`. -/
def unsafeAppEntitlements_always_true_prop : Prop :=
  ∀ (appId : Int) (resource : String) (granted : List String),
    unsafeAppEntitlements appId resource granted = true

theorem unsafeAppEntitlements_always_true_thm :
    unsafeAppEntitlements_always_true_prop := by
  intro appId resource granted
  rfl

/-- Property: the entitlement list is irrelevant — the result does not depend on it. -/
def unsafeAppEntitlements_entitlements_irrelevant_prop : Prop :=
  ∀ (appId : Int) (resource : String) (granted₁ granted₂ : List String),
    unsafeAppEntitlements appId resource granted₁ =
      unsafeAppEntitlements appId resource granted₂

theorem unsafeAppEntitlements_entitlements_irrelevant_thm :
    unsafeAppEntitlements_entitlements_irrelevant_prop := by
  intro appId resource granted₁ granted₂
  rfl

-- ## Post-condition

/-- Post-condition: conjunction of the program's properties. -/
def Post_prop (appId : Int) (resource : String) (granted : List String) : Prop :=
  unsafeAppEntitlements appId resource granted = true ∧
  ∀ granted' : List String,
    unsafeAppEntitlements appId resource granted' =
      unsafeAppEntitlements appId resource granted

-- ## Property-based tests

/-- Sample entitlement lists used for bounded property-based tests. -/
def sampleEntitlements : List (List String) :=
  [[], ["camera"], ["location"], ["camera", "microphone"],
   ["location", "contacts", "photos"]]

/-- Sample resources used for bounded property-based tests. -/
def sampleResources : List String :=
  ["camera", "contacts", "microphone", "location", "photos"]

-- PBT (randomized): access is granted for every sampled app id.
#eval Plausible.Testable.check (∀ n : Nat,
  unsafeAppEntitlements (n : Int) "camera" [] = true)

-- PBT (bounded, always-true property): exhaustive over a grid of inputs.
example : (List.range 30).all (fun n =>
    sampleResources.all (fun r =>
      sampleEntitlements.all (fun l =>
        unsafeAppEntitlements (n : Int) r l))) = true := by native_decide

-- PBT (bounded, entitlements-irrelevance property): all pairs of sample lists.
example : (List.range 10).all (fun n =>
    sampleResources.all (fun r =>
      sampleEntitlements.all (fun l₁ =>
        sampleEntitlements.all (fun l₂ =>
          unsafeAppEntitlements (n : Int) r l₁ ==
            unsafeAppEntitlements (n : Int) r l₂)))) = true := by native_decide

/-- Executable Boolean form of the post-condition (used for its PBT). -/
def PostCheck (appId : Int) (resource : String) (granted : List String) : Bool :=
  unsafeAppEntitlements appId resource granted &&
  sampleEntitlements.all (fun granted' =>
    unsafeAppEntitlements appId resource granted' ==
      unsafeAppEntitlements appId resource granted)

-- PBT (bounded): post-condition over a grid of inputs.
example : (List.range 10).all (fun n =>
    sampleResources.all (fun r =>
      sampleEntitlements.all (fun l => PostCheck (n : Int) r l))) = true := by
  native_decide

-- ## Correctness theorem: Pre → Post

theorem correctness_thm :
    ∀ (appId : Int) (resource : String) (granted : List String),
      Pre appId resource granted → Post_prop appId resource granted := by
  intro appId resource granted _hpre
  constructor
  · rfl
  · intro granted'
    rfl

-- ## Imperative implementation (Id.run with mutable state)

/-- Imperative implementation: mirrors the Python body — a local result
    variable is set to `true` unconditionally and returned; the entitlement
    list is never consulted. -/
def unsafeAppEntitlementsImp (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool :=
  Id.run do
    let mut result := false
    result := true  -- Vulnerability: granted unconditionally
    return result

-- ## Imperative tests

example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide

#eval unsafeAppEntitlementsImp 42 "camera" []
#eval unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]

-- ## Equivalence theorem: functional = imperative

theorem functional_imperative_equiv_thm :
    ∀ (appId : Int) (resource : String) (granted : List String),
      unsafeAppEntitlements appId resource granted =
        unsafeAppEntitlementsImp appId resource granted := by
  intro appId resource granted
  rfl

end UnsafeAppEntitlements93

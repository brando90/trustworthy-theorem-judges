import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

This module formalizes the unsafe iOS app entitlements model from MIT 6.858 Lecture 9.
The model illustrates a missing-authorization vulnerability: no entitlement check is performed,
so any application (`appId`) requesting any `resource` is unconditionally granted access
(`true`), regardless of its `grantedEntitlements` list.
-/

namespace «93_unsafeAppEntitlements»

-- ============================================================================
-- Functional Implementation
-- ============================================================================

/-- Functional implementation of the unsafe iOS app entitlements model.
No check is performed: all resource requests are granted unconditionally. -/
def unsafeAppEntitlements (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool :=
  true

/-- Python-style snake_case alias for `unsafeAppEntitlements`. -/
abbrev unsafe_app_entitlements (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  unsafeAppEntitlements appId resource grantedEntitlements

/-- Reference safe entitlement check that verifies whether the requested `resource`
is present in `grantedEntitlements`. -/
def safeAppEntitlements (_appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  grantedEntitlements.contains resource

/-- Python-style snake_case alias for `safeAppEntitlements`. -/
abbrev safe_app_entitlements (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  safeAppEntitlements appId resource grantedEntitlements

-- ============================================================================
-- Unit Tests
-- ============================================================================

-- Rogue app gains camera access without entitlement
example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide
#eval unsafeAppEntitlements 42 "camera" []

-- App without contacts entitlement still gets access
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide
#eval unsafeAppEntitlements 1 "contacts" ["location"]

-- Empty entitlement list: access still granted
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide
#eval unsafeAppEntitlements 99 "microphone" []

-- Entitlement list contents are irrelevant
example :
    unsafeAppEntitlements 7 "location" [] =
      unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafeAppEntitlements 7 "location" [] ==
  unsafeAppEntitlements 7 "location" ["camera", "microphone"]

-- Negative: different behavior from safe version (Safe version → false)
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide
example : safeAppEntitlements 5 "camera" [] = false := by native_decide
example : unsafeAppEntitlements 5 "camera" [] ≠ safeAppEntitlements 5 "camera" [] := by
  native_decide
#eval unsafeAppEntitlements 5 "camera" []

-- ============================================================================
-- Pre-condition
-- ============================================================================

/-- Pre-condition for `unsafeAppEntitlements`: all integer app IDs, resource names,
and entitlement lists are valid inputs. -/
def Pre (_appId : Int) (_resource : String) (_grantedEntitlements : List String) : Prop :=
  True

-- ============================================================================
-- Properties and Theorems
-- ============================================================================

/-- Property 1: Unconditional grant — every resource request returns `true`. -/
def always_granted_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true

/-- Theorem 1: `unsafeAppEntitlements` unconditionally returns `true` for all inputs. -/
theorem always_granted_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    always_granted_prop appId resource grantedEntitlements := by
  rfl

/-- Property 2: Empty entitlement list — access is still granted when `grantedEntitlements = []`. -/
def empty_entitlements_granted_prop (appId : Int) (resource : String) : Prop :=
  unsafeAppEntitlements appId resource [] = true

/-- Theorem 2: `unsafeAppEntitlements` grants access when the entitlement list is empty. -/
theorem empty_entitlements_granted_thm (appId : Int) (resource : String) :
    empty_entitlements_granted_prop appId resource := by
  rfl

/-- Property 3: Unentitled access — an app lacking the requested resource in its
`grantedEntitlements` list still gains access. -/
def unentitled_access_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true

/-- Theorem 3: `unsafeAppEntitlements` grants access even when `resource ∉ grantedEntitlements`. -/
theorem unentitled_access_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unentitled_access_prop appId resource grantedEntitlements := by
  intro _
  rfl

/-- Property 4: Entitled access — an app holding the requested resource in its
`grantedEntitlements` list gains access. -/
def entitled_access_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∈ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true

/-- Theorem 4: `unsafeAppEntitlements` grants access when `resource ∈ grantedEntitlements`. -/
theorem entitled_access_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    entitled_access_prop appId resource grantedEntitlements := by
  intro _
  rfl

/-- Property 5: Entitlement list irrelevance relative to the empty list. -/
def entitlements_irrelevant_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource [] =
    unsafeAppEntitlements appId resource grantedEntitlements

/-- Theorem 5: Any entitlement list yields the same result as the empty entitlement list. -/
theorem entitlements_irrelevant_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    entitlements_irrelevant_prop appId resource grantedEntitlements := by
  rfl

/-- Property 6: Entitlement list invariance — replacing `granted1` with any `granted2`
does not change the result. -/
def entitlements_invariance_prop (appId : Int) (resource : String)
    (granted1 granted2 : List String) : Prop :=
  unsafeAppEntitlements appId resource granted1 =
    unsafeAppEntitlements appId resource granted2

/-- Theorem 6: `unsafeAppEntitlements` is invariant across any two entitlement lists. -/
theorem entitlements_invariance_thm (appId : Int) (resource : String)
    (granted1 granted2 : List String) :
    entitlements_invariance_prop appId resource granted1 granted2 := by
  rfl

/-- Property 7: Complete input invariance — `appId`, `resource`, and `grantedEntitlements`
never affect the decision. -/
def inputs_invariance_prop (appId1 appId2 : Int) (resource1 resource2 : String)
    (granted1 granted2 : List String) : Prop :=
  unsafeAppEntitlements appId1 resource1 granted1 =
    unsafeAppEntitlements appId2 resource2 granted2

/-- Theorem 7: `unsafeAppEntitlements` returns the same result for any two triples of inputs. -/
theorem inputs_invariance_thm (appId1 appId2 : Int) (resource1 resource2 : String)
    (granted1 granted2 : List String) :
    inputs_invariance_prop appId1 appId2 resource1 resource2 granted1 granted2 := by
  rfl

/-- Property 8: Vulnerability / divergence from safe model — whenever `resource` is not
in `grantedEntitlements`, `unsafeAppEntitlements` disagrees with `safeAppEntitlements`. -/
def differs_from_safe_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements ≠
      safeAppEntitlements appId resource grantedEntitlements

/-- Theorem 8: Whenever `resource ∉ grantedEntitlements`, `unsafeAppEntitlements` returns a
different decision than `safeAppEntitlements`. -/
theorem differs_from_safe_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    differs_from_safe_prop appId resource grantedEntitlements := by
  intro hNotMem
  unfold unsafeAppEntitlements safeAppEntitlements
  intro hEq
  have hContains : grantedEntitlements.contains resource = true := hEq.symm
  have hMem : resource ∈ grantedEntitlements := List.mem_of_elem_eq_true hContains
  exact hNotMem hMem

/-- Property 9: Agreement with safe model — `unsafeAppEntitlements` agrees with
`safeAppEntitlements` if and only if `resource ∈ grantedEntitlements`. -/
def agrees_with_safe_iff_entitled_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  (unsafeAppEntitlements appId resource grantedEntitlements =
    safeAppEntitlements appId resource grantedEntitlements) ↔
    resource ∈ grantedEntitlements

/-- Theorem 9: `unsafeAppEntitlements` equals `safeAppEntitlements` iff the resource is granted. -/
theorem agrees_with_safe_iff_entitled_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    agrees_with_safe_iff_entitled_prop appId resource grantedEntitlements := by
  unfold agrees_with_safe_iff_entitled_prop unsafeAppEntitlements safeAppEntitlements
  constructor
  · intro hEq
    exact List.mem_of_elem_eq_true hEq.symm
  · intro hMem
    exact (List.elem_eq_true_of_mem hMem).symm

-- ============================================================================
-- Post-condition
-- ============================================================================

/-- Post-condition conjunction of the specification properties of `unsafeAppEntitlements`. -/
def Post_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  always_granted_prop appId resource grantedEntitlements ∧
  empty_entitlements_granted_prop appId resource ∧
  unentitled_access_prop appId resource grantedEntitlements ∧
  entitled_access_prop appId resource grantedEntitlements ∧
  entitlements_irrelevant_prop appId resource grantedEntitlements ∧
  differs_from_safe_prop appId resource grantedEntitlements ∧
  agrees_with_safe_iff_entitled_prop appId resource grantedEntitlements

-- ============================================================================
-- Property-Based Tests
-- ============================================================================

-- PBT for Property 1 (`always_granted_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource grantedEntitlements = true)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone", ""] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents => unsafeAppEntitlements appId res ents == true))) = true := by
  native_decide

-- PBT for Property 2 (`empty_entitlements_granted_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String),
    unsafeAppEntitlements appId resource [] = true)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone", ""] : List String).all (fun res =>
        unsafeAppEntitlements appId res [] == true)) = true := by
  native_decide

-- PBT for Property 3 (`unentitled_access_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    (!grantedEntitlements.contains resource) →
      unsafeAppEntitlements appId resource grantedEntitlements = true)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone"] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents =>
            !(ents.contains res) → unsafeAppEntitlements appId res ents = true))) = true := by
  native_decide

-- PBT for Property 4 (`entitled_access_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource (resource :: grantedEntitlements) = true)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone"] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents =>
            ents.contains res → unsafeAppEntitlements appId res ents = true))) = true := by
  native_decide

-- PBT for Property 5 (`entitlements_irrelevant_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource [] =
      unsafeAppEntitlements appId resource grantedEntitlements)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone"] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents =>
            unsafeAppEntitlements appId res [] == unsafeAppEntitlements appId res ents))) = true := by
  native_decide

-- PBT for Property 6 (`entitlements_invariance_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (granted1 granted2 : List String),
    unsafeAppEntitlements appId resource granted1 =
      unsafeAppEntitlements appId resource granted2)

example :
    ([-1, 0, 1, 7, 42] : List Int).all (fun appId =>
      (["camera", "location"] : List String).all (fun res =>
        ([[], ["camera"], ["location", "microphone"]] : List (List String)).all (fun g1 =>
          ([[], ["contacts"], ["camera", "location"]] : List (List String)).all (fun g2 =>
            unsafeAppEntitlements appId res g1 == unsafeAppEntitlements appId res g2)))) = true := by
  native_decide

-- PBT for Property 7 (`inputs_invariance_prop`)
#eval Plausible.Testable.check
  (∀ (appId1 appId2 : Int) (resource1 resource2 : String) (granted1 granted2 : List String),
    unsafeAppEntitlements appId1 resource1 granted1 =
      unsafeAppEntitlements appId2 resource2 granted2)

example :
    ([0, 7, 42] : List Int).all (fun a1 =>
      ([1, 5, 99] : List Int).all (fun a2 =>
        (["camera", "location"] : List String).all (fun r1 =>
          (["contacts", "microphone"] : List String).all (fun r2 =>
            ([[], ["camera"]] : List (List String)).all (fun g1 =>
              ([["location"], ["camera", "microphone"]] : List (List String)).all (fun g2 =>
                unsafeAppEntitlements a1 r1 g1 == unsafeAppEntitlements a2 r2 g2)))))) = true := by
  native_decide

-- PBT for Property 8 (`differs_from_safe_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    (!grantedEntitlements.contains resource) →
      unsafeAppEntitlements appId resource grantedEntitlements ≠
        safeAppEntitlements appId resource grantedEntitlements)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone"] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents =>
            !(ents.contains res) →
              unsafeAppEntitlements appId res ents ≠ safeAppEntitlements appId res ents))) = true := by
  native_decide

-- PBT for Property 9 (`agrees_with_safe_iff_entitled_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    (unsafeAppEntitlements appId resource grantedEntitlements ==
      safeAppEntitlements appId resource grantedEntitlements) =
      grantedEntitlements.contains resource)

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone"] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents =>
            (unsafeAppEntitlements appId res ents == safeAppEntitlements appId res ents) ==
              ents.contains res))) = true := by
  native_decide

-- PBT for Post-condition (`Post_prop`)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    (unsafeAppEntitlements appId resource grantedEntitlements == true) &&
    (unsafeAppEntitlements appId resource [] == true) &&
    (!( !grantedEntitlements.contains resource ) ||
      unsafeAppEntitlements appId resource grantedEntitlements == true) &&
    (!( grantedEntitlements.contains resource ) ||
      unsafeAppEntitlements appId resource grantedEntitlements == true) &&
    (unsafeAppEntitlements appId resource [] ==
      unsafeAppEntitlements appId resource grantedEntitlements) &&
    (!( !grantedEntitlements.contains resource ) ||
      unsafeAppEntitlements appId resource grantedEntitlements !=
        safeAppEntitlements appId resource grantedEntitlements) &&
    ((unsafeAppEntitlements appId resource grantedEntitlements ==
      safeAppEntitlements appId resource grantedEntitlements) ==
        grantedEntitlements.contains resource))

example :
    ([-1, 0, 1, 5, 7, 42, 99] : List Int).all (fun appId =>
      (["camera", "contacts", "location", "microphone"] : List String).all (fun res =>
        ([[], ["camera"], ["location"], ["camera", "microphone"]] : List (List String)).all
          (fun ents =>
            (unsafeAppEntitlements appId res ents == true) &&
            (unsafeAppEntitlements appId res [] == true) &&
            (!( !ents.contains res ) || unsafeAppEntitlements appId res ents == true) &&
            (!( ents.contains res ) || unsafeAppEntitlements appId res ents == true) &&
            (unsafeAppEntitlements appId res [] == unsafeAppEntitlements appId res ents) &&
            (!( !ents.contains res ) ||
              unsafeAppEntitlements appId res ents != safeAppEntitlements appId res ents) &&
            ((unsafeAppEntitlements appId res ents == safeAppEntitlements appId res ents) ==
              ents.contains res)))) = true := by
  native_decide

-- ============================================================================
-- Correctness Theorem
-- ============================================================================

/-- Correctness theorem: Under `Pre`, `Post_prop` holds for all inputs. -/
theorem correctness_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String)
    (_hPre : Pre appId resource grantedEntitlements) :
    Post_prop appId resource grantedEntitlements := by
  refine ⟨always_granted_thm appId resource grantedEntitlements,
    empty_entitlements_granted_thm appId resource,
    unentitled_access_thm appId resource grantedEntitlements,
    entitled_access_thm appId resource grantedEntitlements,
    entitlements_irrelevant_thm appId resource grantedEntitlements,
    differs_from_safe_thm appId resource grantedEntitlements,
    agrees_with_safe_iff_entitled_thm appId resource grantedEntitlements⟩

/-- Alias for `correctness_thm`. -/
theorem correctness (appId : Int) (resource : String)
    (grantedEntitlements : List String)
    (hPre : Pre appId resource grantedEntitlements) :
    Post_prop appId resource grantedEntitlements :=
  correctness_thm appId resource grantedEntitlements hPre

-- ============================================================================
-- Imperative Implementation
-- ============================================================================

/-- Imperative implementation of `unsafeAppEntitlements` using `Id.run do` with mutable state. -/
def unsafeAppEntitlementsImp (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  Id.run do
    let mut currentApp : Int := appId
    let mut requestedResource : String := resource
    let mut entitlements : List String := grantedEntitlements
    let mut accessGranted : Bool := false
    let _ := (currentApp, requestedResource, entitlements)
    -- Vulnerability: entitlement list is never consulted; access is unconditionally granted
    accessGranted := true
    return accessGranted

/-- Python-style snake_case alias for `unsafeAppEntitlementsImp`. -/
abbrev unsafe_app_entitlements_imp (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  unsafeAppEntitlementsImp appId resource grantedEntitlements

-- ============================================================================
-- Imperative Tests
-- ============================================================================

-- Rogue app gains camera access without entitlement
example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
#eval unsafeAppEntitlementsImp 42 "camera" []

-- App without contacts entitlement still gets access
example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
#eval unsafeAppEntitlementsImp 1 "contacts" ["location"]

-- Empty entitlement list: access still granted
example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide
#eval unsafeAppEntitlementsImp 99 "microphone" []

-- Entitlement list contents are irrelevant
example :
    unsafeAppEntitlementsImp 7 "location" [] =
      unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafeAppEntitlementsImp 7 "location" [] ==
  unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]

-- Negative: different behavior from safe version
example : unsafeAppEntitlementsImp 5 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] ≠ safeAppEntitlements 5 "camera" [] := by
  native_decide
#eval unsafeAppEntitlementsImp 5 "camera" []

-- ============================================================================
-- Equivalence Theorem
-- ============================================================================

/-- Equivalence theorem: Functional and imperative implementations return identical results. -/
theorem equivalence_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements := by
  rfl

/-- Alias for `equivalence_thm`. -/
theorem equivalence (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements :=
  equivalence_thm appId resource grantedEntitlements

end «93_unsafeAppEntitlements»

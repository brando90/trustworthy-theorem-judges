import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

Lean 4 translation of a Python program modelling a *vulnerable* iOS
entitlement check.  The vulnerability: no entitlement check is performed, so
any app gains access to any resource, regardless of the entitlements it was
actually granted.

* `unsafeAppEntitlements` is the functional translation of
  `unsafe_app_entitlements`: it ignores all of its arguments and returns
  `true`.
* `safeAppEntitlements` is the reference *safe* behaviour (grant access only
  if the resource is in the granted entitlement list); it is used to state the
  "negative" property from the Python test-suite that the unsafe version
  behaves differently from the safe one.
* Properties, pre/post-conditions, a correctness theorem, property-based
  tests, an imperative implementation and a functional/imperative
  equivalence theorem follow.
-/

namespace «93_unsafeAppEntitlements»

/-! ## Functional implementation -/

/-- Unsafe entitlement check: every resource request is granted
unconditionally.  The app id, the requested resource and the list of granted
entitlements are never consulted (this is the vulnerability). -/
def unsafeAppEntitlements (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool :=
  true

/-- Reference safe behaviour: access is granted only if the requested
resource appears in the granted entitlement list.  Only used to express the
"negative" test (`Safe version → False`) of the Python program. -/
def safeAppEntitlements (_appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  decide (resource ∈ grantedEntitlements)

/-! ## Unit tests (mirroring the Python `check` function) -/

-- Rogue app gains camera access without entitlement
example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide
-- App without contacts entitlement still gets access
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide
-- Empty entitlement list: access still granted
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide
-- Entitlement list contents are irrelevant
example : unsafeAppEntitlements 7 "location" [] =
    unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by native_decide
-- Negative: different behaviour from the safe version
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide
example : safeAppEntitlements 5 "camera" [] = false := by native_decide
example : unsafeAppEntitlements 5 "camera" [] ≠ safeAppEntitlements 5 "camera" [] := by
  native_decide

#eval unsafeAppEntitlements 42 "camera" []                 -- true
#eval unsafeAppEntitlements 1 "contacts" ["location"]      -- true
#eval unsafeAppEntitlements 99 "microphone" []             -- true
#eval unsafeAppEntitlements 7 "location" [] ==
      unsafeAppEntitlements 7 "location" ["camera", "microphone"]  -- true
#eval unsafeAppEntitlements 5 "camera" []                  -- true
#eval safeAppEntitlements 5 "camera" []                    -- false

/-! ## Pre-condition -/

/-- Pre-condition: the Python function accepts any app id, any resource name
and any entitlement list, so there is no restriction on the inputs. -/
def Pre (_appId : Int) (_resource : String) (_grantedEntitlements : List String) : Prop :=
  True

/-! ## Properties -/

/-- Access is always granted, whatever the inputs. -/
def always_granted_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true

theorem always_granted_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    always_granted_prop appId resource grantedEntitlements := by
  unfold always_granted_prop unsafeAppEntitlements
  rfl

/-- The contents of the entitlement list are irrelevant: two requests by the
same app for the same resource get the same answer regardless of the
entitlement lists. -/
def entitlements_irrelevant_prop (appId : Int) (resource : String)
    (ents1 ents2 : List String) : Prop :=
  unsafeAppEntitlements appId resource ents1 = unsafeAppEntitlements appId resource ents2

theorem entitlements_irrelevant_thm (appId : Int) (resource : String)
    (ents1 ents2 : List String) :
    entitlements_irrelevant_prop appId resource ents1 ents2 := by
  unfold entitlements_irrelevant_prop unsafeAppEntitlements
  rfl

/-- Access is granted even with an empty entitlement list (no entitlement is
ever required). -/
def empty_entitlements_granted_prop (appId : Int) (resource : String) : Prop :=
  unsafeAppEntitlements appId resource [] = true

theorem empty_entitlements_granted_thm (appId : Int) (resource : String) :
    empty_entitlements_granted_prop appId resource := by
  unfold empty_entitlements_granted_prop unsafeAppEntitlements
  rfl

/-- The result does not depend on any of the inputs: the function is
constant. -/
def constant_prop (appId1 appId2 : Int) (res1 res2 : String)
    (ents1 ents2 : List String) : Prop :=
  unsafeAppEntitlements appId1 res1 ents1 = unsafeAppEntitlements appId2 res2 ents2

theorem constant_thm (appId1 appId2 : Int) (res1 res2 : String)
    (ents1 ents2 : List String) :
    constant_prop appId1 appId2 res1 res2 ents1 ents2 := by
  unfold constant_prop unsafeAppEntitlements
  rfl

/-- Negative property: whenever the requested resource is *not* among the
granted entitlements, the unsafe version disagrees with the safe version
(which would deny access). -/
def differs_from_safe_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements ≠
      safeAppEntitlements appId resource grantedEntitlements

theorem differs_from_safe_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    differs_from_safe_prop appId resource grantedEntitlements := by
  unfold differs_from_safe_prop
  intro h
  simp [unsafeAppEntitlements, safeAppEntitlements, h]

/-- The unsafe version grants at least everything the safe version grants
(it is an over-approximation of the safe policy). -/
def over_approximates_safe_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  safeAppEntitlements appId resource grantedEntitlements = true →
    unsafeAppEntitlements appId resource grantedEntitlements = true

theorem over_approximates_safe_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    over_approximates_safe_prop appId resource grantedEntitlements := by
  unfold over_approximates_safe_prop
  intro _
  rfl

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (appId : Int) (resource : String) (grantedEntitlements : List String) : Prop :=
  always_granted_prop appId resource grantedEntitlements ∧
  (∀ ents2 : List String, entitlements_irrelevant_prop appId resource grantedEntitlements ents2) ∧
  empty_entitlements_granted_prop appId resource ∧
  (∀ (appId2 : Int) (res2 : String) (ents2 : List String),
    constant_prop appId appId2 resource res2 grantedEntitlements ents2) ∧
  differs_from_safe_prop appId resource grantedEntitlements ∧
  over_approximates_safe_prop appId resource grantedEntitlements

/-! ## Property-based tests -/

-- PBT: always_granted_prop
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String) (ents : List String),
  unsafeAppEntitlements appId resource ents = true)
example : (List.range 50).all (fun n =>
    unsafeAppEntitlements (Int.ofNat n) ("res" ++ toString n)
      (List.replicate (n % 5) "camera")) = true := by
  native_decide

-- PBT: entitlements_irrelevant_prop
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String) (ents1 ents2 : List String),
  unsafeAppEntitlements appId resource ents1 = unsafeAppEntitlements appId resource ents2)
example : (List.range 50).all (fun n =>
    unsafeAppEntitlements 7 "location" [] ==
      unsafeAppEntitlements 7 "location" (List.replicate n "camera")) = true := by
  native_decide

-- PBT: empty_entitlements_granted_prop
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String),
  unsafeAppEntitlements appId resource [] = true)
example : (List.range 50).all (fun n =>
    unsafeAppEntitlements (Int.ofNat n) "microphone" []) = true := by native_decide

-- PBT: constant_prop
#eval Plausible.Testable.check (∀ (a1 a2 : Int) (r1 r2 : String) (e1 e2 : List String),
  unsafeAppEntitlements a1 r1 e1 = unsafeAppEntitlements a2 r2 e2)
example : (List.range 50).all (fun n =>
    unsafeAppEntitlements (Int.ofNat n) (toString n) (List.replicate n (toString n)) ==
      unsafeAppEntitlements 0 "" []) = true := by native_decide

-- PBT: differs_from_safe_prop
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String) (ents : List String),
  resource ∉ ents →
    unsafeAppEntitlements appId resource ents ≠ safeAppEntitlements appId resource ents)
example : (List.range 50).all (fun n =>
    unsafeAppEntitlements (Int.ofNat n) "camera" (List.replicate n "location") !=
      safeAppEntitlements (Int.ofNat n) "camera" (List.replicate n "location")) = true := by
  native_decide

-- PBT: over_approximates_safe_prop (stated in the equivalent executable Boolean
-- form `¬safe ∨ unsafe`, so that no random samples are discarded)
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String) (ents : List String),
  (!(safeAppEntitlements appId resource ents) || unsafeAppEntitlements appId resource ents) = true)
-- PBT: over_approximates_safe_prop with the pre-condition forced to hold (the
-- requested resource is put into the entitlement list)
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String) (ents : List String),
  safeAppEntitlements appId resource (resource :: ents) = true →
    unsafeAppEntitlements appId resource (resource :: ents) = true)
example : (List.range 50).all (fun n =>
    !(safeAppEntitlements (Int.ofNat n) "camera" ("camera" :: List.replicate n "location")) ||
      unsafeAppEntitlements (Int.ofNat n) "camera" ("camera" :: List.replicate n "location"))
    = true := by
  native_decide

-- PBT: Post_prop (executable Boolean form of the conjunction)
#eval Plausible.Testable.check
  (∀ (appId appId2 : Int) (resource res2 : String) (ents ents2 : List String),
    unsafeAppEntitlements appId resource ents = true ∧
    unsafeAppEntitlements appId resource ents = unsafeAppEntitlements appId resource ents2 ∧
    unsafeAppEntitlements appId resource [] = true ∧
    unsafeAppEntitlements appId resource ents = unsafeAppEntitlements appId2 res2 ents2 ∧
    (resource ∉ ents →
      unsafeAppEntitlements appId resource ents ≠ safeAppEntitlements appId resource ents) ∧
    (!(safeAppEntitlements appId resource ents) || unsafeAppEntitlements appId resource ents) = true)
example : (List.range 30).all (fun n =>
    let ents := List.replicate (n % 3) "location"
    unsafeAppEntitlements (Int.ofNat n) "camera" ents &&
    (unsafeAppEntitlements (Int.ofNat n) "camera" ents ==
      unsafeAppEntitlements (Int.ofNat n) "camera" ("camera" :: ents)) &&
    unsafeAppEntitlements (Int.ofNat n) "camera" [] &&
    (unsafeAppEntitlements (Int.ofNat n) "camera" ents == unsafeAppEntitlements 0 "" []) &&
    (unsafeAppEntitlements (Int.ofNat n) "camera" ents !=
      safeAppEntitlements (Int.ofNat n) "camera" ents) &&
    (!(safeAppEntitlements (Int.ofNat n) "camera" ents) ||
      unsafeAppEntitlements (Int.ofNat n) "camera" ents)) = true := by
  native_decide

/-! ## Correctness theorem -/

/-- Correctness: under the (trivial) pre-condition, the post-condition holds. -/
theorem correctness_thm (appId : Int) (resource : String) (grantedEntitlements : List String)
    (_hpre : Pre appId resource grantedEntitlements) :
    Post_prop appId resource grantedEntitlements := by
  refine ⟨always_granted_thm _ _ _,
    fun ents2 => entitlements_irrelevant_thm _ _ _ ents2,
    empty_entitlements_granted_thm _ _,
    fun _ _ _ => constant_thm _ _ _ _ _ _,
    differs_from_safe_thm _ _ _,
    over_approximates_safe_thm _ _ _⟩

/-! ## Imperative implementation -/

/-- Imperative version of `unsafe_app_entitlements`, written with `Id.run do`
and mutable state.  The decision variable is initialised to "denied" and then
unconditionally set to "granted" without consulting the entitlement list. -/
def unsafeAppEntitlementsImp (_appId : Int) (_resource : String)
    (_grantedEntitlements : List String) : Bool := Id.run do
  let mut granted : Bool := false
  -- Vulnerability: the entitlement list is never consulted.
  granted := true
  return granted

-- Imperative tests
example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide
example : unsafeAppEntitlementsImp 7 "location" [] =
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] ≠ safeAppEntitlements 5 "camera" [] := by
  native_decide

#eval unsafeAppEntitlementsImp 42 "camera" []             -- true
#eval unsafeAppEntitlementsImp 1 "contacts" ["location"]  -- true
#eval unsafeAppEntitlementsImp 99 "microphone" []         -- true
#eval unsafeAppEntitlementsImp 5 "camera" []              -- true

-- PBT: imperative implementation agrees with the functional one
#eval Plausible.Testable.check (∀ (appId : Int) (resource : String) (ents : List String),
  unsafeAppEntitlements appId resource ents = unsafeAppEntitlementsImp appId resource ents)

/-! ## Equivalence theorem -/

/-- The functional and imperative implementations agree on every input. -/
theorem functional_imperative_equiv_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements := by
  rfl

end «93_unsafeAppEntitlements»

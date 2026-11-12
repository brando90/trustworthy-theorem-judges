import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

Lean 4 translation of the Python program `unsafe_app_entitlements`.

The Python function models a *vulnerable* entitlement checker: it ignores the
application id, the requested resource and the list of granted entitlements and
grants every resource request unconditionally (`return True`).  The entitlement
list is never consulted.

This file provides

* the functional implementation `unsafeAppEntitlements`;
* a reference *safe* checker `safeAppEntitlements` (access only when the
  requested resource appears in the granted entitlements), used solely to state
  the "different behavior from safe version" test of the Python `check`;
* unit tests mirroring the Python `check` function;
* the precondition `Pre`, named properties (`*_prop`) with proofs (`*_thm`),
  the postcondition `Post_prop` and the correctness theorem `Pre → Post_prop`;
* randomized (Plausible) and bounded property-based tests;
* an imperative implementation `unsafeAppEntitlementsImp` written with
  `Id.run do` and mutable state, its tests, and the equivalence theorem.
-/

namespace «93_unsafeAppEntitlements»

/-! ## Functional implementation -/

set_option linter.unusedVariables false in
/-- Functional translation of `unsafe_app_entitlements`.

No check is performed: every resource request is granted.  The arguments
`appId`, `resource` and `grantedEntitlements` are never consulted
(this is the vulnerability). -/
def unsafeAppEntitlements (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  true

set_option linter.unusedVariables false in
/-- Reference *safe* checker (not part of the Python program): a request is
granted only when the requested resource is among the granted entitlements.
It is used to formalize the Python comment `# Safe version → False` in the
"negative" test. -/
def safeAppEntitlements (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  grantedEntitlements.contains resource

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

-- Negative: different behavior from safe version
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide
example : safeAppEntitlements 5 "camera" [] = false := by native_decide
example : unsafeAppEntitlements 5 "camera" [] ≠ safeAppEntitlements 5 "camera" [] := by
  native_decide

#eval unsafeAppEntitlements 42 "camera" []                      -- true
#eval unsafeAppEntitlements 1 "contacts" ["location"]           -- true
#eval unsafeAppEntitlements 99 "microphone" []                  -- true
#eval unsafeAppEntitlements 7 "location" [] ==
      unsafeAppEntitlements 7 "location" ["camera", "microphone"]  -- true
#eval unsafeAppEntitlements 5 "camera" []                       -- true
#eval safeAppEntitlements 5 "camera" []                         -- false (safe version)

/-! ## Precondition -/

set_option linter.unusedVariables false in
/-- Precondition: the Python function accepts any app id, any resource name and
any list of entitlements, so there is no restriction on the inputs. -/
def Pre (appId : Int) (resource : String) (grantedEntitlements : List String) : Prop :=
  True

/-! ## Properties and theorems -/

/-- Every resource request is granted, whatever the inputs. -/
def alwaysGranted_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true

theorem alwaysGranted_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    alwaysGranted_prop appId resource grantedEntitlements := by
  unfold alwaysGranted_prop unsafeAppEntitlements
  rfl

/-- The entitlement list is never consulted: replacing it by any other list
yields the same decision. -/
def entitlementsIrrelevant_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  ∀ other : List String,
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlements appId resource other

theorem entitlementsIrrelevant_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    entitlementsIrrelevant_prop appId resource grantedEntitlements := by
  intro other
  unfold unsafeAppEntitlements
  rfl

/-- The decision depends on none of the inputs: any app requesting any
resource with any entitlements gets the same answer. -/
def inputsIrrelevant_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  ∀ (appId' : Int) (resource' : String) (grantedEntitlements' : List String),
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlements appId' resource' grantedEntitlements'

theorem inputsIrrelevant_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    inputsIrrelevant_prop appId resource grantedEntitlements := by
  intro appId' resource' grantedEntitlements'
  unfold unsafeAppEntitlements
  rfl

/-- The vulnerability: access is granted even when the requested resource is
*not* among the granted entitlements (e.g. a rogue app with no entitlements
gets the camera). -/
def grantsWithoutEntitlement_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true

theorem grantsWithoutEntitlement_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    grantsWithoutEntitlement_prop appId resource grantedEntitlements := by
  intro _
  unfold unsafeAppEntitlements
  rfl

/-- The unsafe checker is at least as permissive as the safe one: whenever the
safe checker grants access, so does the unsafe checker. -/
def atLeastAsPermissiveAsSafe_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  safeAppEntitlements appId resource grantedEntitlements = true →
    unsafeAppEntitlements appId resource grantedEntitlements = true

theorem atLeastAsPermissiveAsSafe_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    atLeastAsPermissiveAsSafe_prop appId resource grantedEntitlements := by
  intro _
  unfold unsafeAppEntitlements
  rfl

/-- Negative property: whenever the resource is not granted, the unsafe checker
disagrees with the safe checker (the safe version denies, the unsafe version
grants). -/
def differsFromSafe_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements ≠
      safeAppEntitlements appId resource grantedEntitlements

theorem differsFromSafe_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    differsFromSafe_prop appId resource grantedEntitlements := by
  intro h
  simp [unsafeAppEntitlements, safeAppEntitlements, h]

/-- Exact characterisation of the disagreement with the safe checker: the two
checkers agree if and only if the resource is actually granted. -/
def agreesWithSafeIff_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  (unsafeAppEntitlements appId resource grantedEntitlements =
      safeAppEntitlements appId resource grantedEntitlements) ↔
    resource ∈ grantedEntitlements

theorem agreesWithSafeIff_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    agreesWithSafeIff_prop appId resource grantedEntitlements := by
  unfold agreesWithSafeIff_prop
  simp [unsafeAppEntitlements, safeAppEntitlements]

/-! ## Postcondition -/

/-- Postcondition: conjunction of all the properties above. -/
def Post_prop (appId : Int) (resource : String) (grantedEntitlements : List String) : Prop :=
  alwaysGranted_prop appId resource grantedEntitlements ∧
  entitlementsIrrelevant_prop appId resource grantedEntitlements ∧
  inputsIrrelevant_prop appId resource grantedEntitlements ∧
  grantsWithoutEntitlement_prop appId resource grantedEntitlements ∧
  atLeastAsPermissiveAsSafe_prop appId resource grantedEntitlements ∧
  differsFromSafe_prop appId resource grantedEntitlements ∧
  agreesWithSafeIff_prop appId resource grantedEntitlements

/-! ## Property-based tests

Randomized tests use Plausible; bounded tests enumerate a small pool of app
ids, resource names and *all* sublists of the resource pool as entitlement
lists (exhaustive on that pool).
-/

/-- Pool of resource names used by the bounded property-based tests. -/
def testResources : List String :=
  ["camera", "contacts", "microphone", "location", "photos"]

/-- All sublists of `testResources`: the candidate entitlement lists. -/
def testEntitlementLists : List (List String) :=
  testResources.sublists

/-- Pool of app ids used by the bounded property-based tests. -/
def testAppIds : List Int :=
  [-3, 0, 1, 5, 7, 42, 99]

#eval testEntitlementLists.length   -- 32

-- PBT: alwaysGranted_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource grantedEntitlements = true)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        unsafeAppEntitlements appId resource ge) = true := by
  native_decide

-- PBT: entitlementsIrrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements other : List String),
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlements appId resource other)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge => testEntitlementLists.all fun other =>
        unsafeAppEntitlements appId resource ge ==
          unsafeAppEntitlements appId resource other) = true := by
  native_decide

-- PBT: inputsIrrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId appId' : Int) (resource resource' : String)
      (grantedEntitlements grantedEntitlements' : List String),
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlements appId' resource' grantedEntitlements')
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        testAppIds.all fun appId' => testResources.all fun resource' =>
          testEntitlementLists.all fun ge' =>
            unsafeAppEntitlements appId resource ge ==
              unsafeAppEntitlements appId' resource' ge') = true := by
  native_decide

-- PBT: grantsWithoutEntitlement_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    resource ∉ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements = true)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        !(ge.contains resource) → unsafeAppEntitlements appId resource ge) = true := by
  native_decide

-- PBT: atLeastAsPermissiveAsSafe_prop
-- (random strings are rarely members of a random list, so Plausible may give
--  up; the bounded test below covers the precondition exhaustively on the pool)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    safeAppEntitlements appId resource grantedEntitlements = true →
      unsafeAppEntitlements appId resource grantedEntitlements = true)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        safeAppEntitlements appId resource ge → unsafeAppEntitlements appId resource ge)
      = true := by
  native_decide

-- PBT: differsFromSafe_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    resource ∉ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements ≠
        safeAppEntitlements appId resource grantedEntitlements)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        !(ge.contains resource) →
          unsafeAppEntitlements appId resource ge != safeAppEntitlements appId resource ge)
      = true := by
  native_decide

-- PBT: agreesWithSafeIff_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    (unsafeAppEntitlements appId resource grantedEntitlements =
        safeAppEntitlements appId resource grantedEntitlements) ↔
      resource ∈ grantedEntitlements)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        (unsafeAppEntitlements appId resource ge == safeAppEntitlements appId resource ge)
          == ge.contains resource) = true := by
  native_decide

/-- Executable Boolean form of `Post_prop`, with the inner universal
quantifiers of `entitlementsIrrelevant_prop` and `inputsIrrelevant_prop`
bounded to the test pools. -/
def postCheck (appId : Int) (resource : String) (ge : List String) : Bool :=
  -- alwaysGranted_prop
  unsafeAppEntitlements appId resource ge &&
  -- entitlementsIrrelevant_prop (bounded)
  (testEntitlementLists.all fun other =>
    unsafeAppEntitlements appId resource ge == unsafeAppEntitlements appId resource other) &&
  -- inputsIrrelevant_prop (bounded)
  (testAppIds.all fun appId' => testResources.all fun resource' =>
    testEntitlementLists.all fun ge' =>
      unsafeAppEntitlements appId resource ge == unsafeAppEntitlements appId' resource' ge') &&
  -- grantsWithoutEntitlement_prop
  (!(ge.contains resource) → unsafeAppEntitlements appId resource ge) &&
  -- atLeastAsPermissiveAsSafe_prop
  (safeAppEntitlements appId resource ge → unsafeAppEntitlements appId resource ge) &&
  -- differsFromSafe_prop
  (!(ge.contains resource) →
    unsafeAppEntitlements appId resource ge != safeAppEntitlements appId resource ge) &&
  -- agreesWithSafeIff_prop
  ((unsafeAppEntitlements appId resource ge == safeAppEntitlements appId resource ge)
    == ge.contains resource)

-- PBT: Post_prop (randomized, with the inner quantifiers sampled by Plausible).
-- The seven-way conjunction needs a larger instance-search budget.  Random
-- strings are rarely members of a random list, so the `safeAppEntitlements`
-- hypothesis is seldom met and Plausible may report "Gave up" (a counterexample
-- in any conjunct would still be reported); the bounded tests below cover the
-- postcondition exhaustively on the test pools.
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource grantedEntitlements = true ∧
    (∀ other : List String,
      unsafeAppEntitlements appId resource grantedEntitlements =
        unsafeAppEntitlements appId resource other) ∧
    (∀ (appId' : Int) (resource' : String) (grantedEntitlements' : List String),
      unsafeAppEntitlements appId resource grantedEntitlements =
        unsafeAppEntitlements appId' resource' grantedEntitlements') ∧
    (resource ∉ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements = true) ∧
    (safeAppEntitlements appId resource grantedEntitlements = true →
      unsafeAppEntitlements appId resource grantedEntitlements = true) ∧
    (resource ∉ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements ≠
        safeAppEntitlements appId resource grantedEntitlements) ∧
    ((unsafeAppEntitlements appId resource grantedEntitlements =
        safeAppEntitlements appId resource grantedEntitlements) ↔
      resource ∈ grantedEntitlements))
-- PBT: Post_prop (bounded, exhaustive on the test pools)
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    postCheck appId resource grantedEntitlements = true)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge => postCheck appId resource ge) = true := by
  native_decide

/-! ## Correctness theorem -/

/-- Correctness: under the (trivial) precondition, the implementation satisfies
every property of the postcondition. -/
theorem correctness_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    Pre appId resource grantedEntitlements → Post_prop appId resource grantedEntitlements := by
  intro _
  exact ⟨alwaysGranted_thm appId resource grantedEntitlements,
    entitlementsIrrelevant_thm appId resource grantedEntitlements,
    inputsIrrelevant_thm appId resource grantedEntitlements,
    grantsWithoutEntitlement_thm appId resource grantedEntitlements,
    atLeastAsPermissiveAsSafe_thm appId resource grantedEntitlements,
    differsFromSafe_thm appId resource grantedEntitlements,
    agreesWithSafeIff_thm appId resource grantedEntitlements⟩

/-! ## Imperative implementation -/

set_option linter.unusedVariables false in
/-- Imperative translation of `unsafe_app_entitlements` using `Id.run do` with
a mutable decision flag.  The flag starts as "denied" and is then set to
"granted" unconditionally: no entitlement check is ever performed, and
`appId`, `resource` and `grantedEntitlements` are never consulted. -/
def unsafeAppEntitlementsImp (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool := Id.run do
  let mut granted : Bool := false
  -- Vulnerability: grant without consulting the entitlement list.
  granted := true
  return granted

/-! ## Imperative tests -/

example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide
example : unsafeAppEntitlementsImp 7 "location" [] =
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] ≠ safeAppEntitlements 5 "camera" [] := by
  native_decide

#eval unsafeAppEntitlementsImp 42 "camera" []                   -- true
#eval unsafeAppEntitlementsImp 1 "contacts" ["location"]        -- true
#eval unsafeAppEntitlementsImp 99 "microphone" []               -- true
#eval unsafeAppEntitlementsImp 5 "camera" []                    -- true

-- PBT: functional and imperative implementations agree
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements)
example :
    (testAppIds.all fun appId => testResources.all fun resource =>
      testEntitlementLists.all fun ge =>
        unsafeAppEntitlements appId resource ge == unsafeAppEntitlementsImp appId resource ge)
      = true := by
  native_decide

/-! ## Equivalence theorem -/

/-- The functional and imperative implementations coincide on all inputs. -/
theorem unsafeAppEntitlements_imp_equiv_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements := by
  rfl

end «93_unsafeAppEntitlements»

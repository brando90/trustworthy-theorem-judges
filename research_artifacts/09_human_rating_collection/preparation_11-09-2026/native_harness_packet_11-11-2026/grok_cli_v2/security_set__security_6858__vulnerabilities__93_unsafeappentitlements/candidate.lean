import Mathlib

/-!
# Unsafe iOS App Entitlements

Translation of an unsafe entitlement check (MIT 6.858 Lecture 9).

The Python function `unsafe_app_entitlements` returns `True` for every app id,
resource name, and granted-entitlement list. The list is never consulted, so a
rogue app receives access to any resource, including when its entitlement list
is empty or names other resources.

The safe baseline contrasted in the Python tests is membership:
access is granted only when `resource` occurs in `granted_entitlements`.
On that baseline, `unsafe_app_entitlements(5, "camera", [])` is `True`
while the safe check is `False`.

There is no floating-point data in this program. App identifiers are Python
`int`s, modelled here as `Int`. Resource names and entitlements are `String`s.
-/

namespace «93_unsafeAppEntitlements»

/-- Unsafe entitlement check. Every request is granted.

The parameters are part of the Python signature and are intentionally unused:
that is the vulnerability. -/
def unsafeAppEntitlements (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  let _appId := appId
  let _resource := resource
  let _grantedEntitlements := grantedEntitlements
  true

/-- Safe baseline: grant access exactly when the resource is an entitled name.

This is the check the Python comments contrast with the unsafe function
(`Safe version → False` on an empty entitlement list). -/
def safeAppEntitlements (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  let _appId := appId
  grantedEntitlements.contains resource

/-! ## Unit tests

The assertions in the Python `check` driver, plus the safe result named by the
comment on the last assertion. -/

-- Rogue app gains camera access without an entitlement.
example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide
#eval unsafeAppEntitlements 42 "camera" []

-- App without the contacts entitlement still gets access.
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide
#eval unsafeAppEntitlements 1 "contacts" ["location"]

-- Empty entitlement list: access is still granted.
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide
#eval unsafeAppEntitlements 99 "microphone" []

-- Entitlement-list contents are irrelevant.
example : unsafeAppEntitlements 7 "location" [] =
    unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafeAppEntitlements 7 "location" [] ==
  unsafeAppEntitlements 7 "location" ["camera", "microphone"]

-- Negative case: unsafe grants access. The safe version denies it.
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide
#eval unsafeAppEntitlements 5 "camera" []

example : safeAppEntitlements 5 "camera" [] = false := by native_decide
#eval safeAppEntitlements 5 "camera" []

example : (unsafeAppEntitlements 5 "camera" [] ==
    safeAppEntitlements 5 "camera" []) = false := by native_decide

/-- Boolean form of the Python `check` driver. -/
def check : Bool :=
  unsafeAppEntitlements 42 "camera" [] == true &&
  unsafeAppEntitlements 1 "contacts" ["location"] == true &&
  unsafeAppEntitlements 99 "microphone" [] == true &&
  (unsafeAppEntitlements 7 "location" [] ==
    unsafeAppEntitlements 7 "location" ["camera", "microphone"]) &&
  unsafeAppEntitlements 5 "camera" [] == true &&
  safeAppEntitlements 5 "camera" [] == false

example : check = true := by native_decide

/-- Same success message as the Python driver. -/
def checkMessage : String :=
  if check then "All tests passed." else "Tests failed."

#eval checkMessage

/-! ## Precondition -/

/-- Every Python `int`, `str`, and `list[str]` is an admissible input.
The unsafe function validates nothing. -/
def Pre (_appId : Int) (_resource : String) (_grantedEntitlements : List String) : Prop :=
  True

/-! ## Properties -/

/-- Unconditional grant: the decision is `true`. -/
def alwaysGranted_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true

theorem alwaysGranted_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    alwaysGranted_prop appId resource grantedEntitlements := by
  rfl

/-- The entitlement list is never consulted. -/
def entitlementsIrrelevant_prop (appId : Int) (resource : String) : Prop :=
  ∀ e1 e2 : List String,
    unsafeAppEntitlements appId resource e1 = unsafeAppEntitlements appId resource e2

theorem entitlementsIrrelevant_thm (appId : Int) (resource : String) :
    entitlementsIrrelevant_prop appId resource := by
  intro e1 e2
  rfl

/-- The app id is ignored: every app gets the same decision. -/
def appIdIrrelevant_prop (resource : String) (grantedEntitlements : List String) : Prop :=
  ∀ a1 a2 : Int,
    unsafeAppEntitlements a1 resource grantedEntitlements =
      unsafeAppEntitlements a2 resource grantedEntitlements

theorem appIdIrrelevant_thm (resource : String) (grantedEntitlements : List String) :
    appIdIrrelevant_prop resource grantedEntitlements := by
  intro a1 a2
  rfl

/-- The resource name is ignored: every resource is decided the same way. -/
def resourceIrrelevant_prop (appId : Int) (grantedEntitlements : List String) : Prop :=
  ∀ r1 r2 : String,
    unsafeAppEntitlements appId r1 grantedEntitlements =
      unsafeAppEntitlements appId r2 grantedEntitlements

theorem resourceIrrelevant_thm (appId : Int) (grantedEntitlements : List String) :
    resourceIrrelevant_prop appId grantedEntitlements := by
  intro r1 r2
  rfl

/-- No argument is consulted. Any two requests receive the same decision.
This is the header claim: any app gains access to any resource. -/
def argumentsIrrelevant_prop : Prop :=
  ∀ a1 a2 : Int, ∀ r1 r2 : String, ∀ e1 e2 : List String,
    unsafeAppEntitlements a1 r1 e1 = unsafeAppEntitlements a2 r2 e2

theorem argumentsIrrelevant_thm : argumentsIrrelevant_prop := by
  intro a1 a2 r1 r2 e1 e2
  rfl

/-- Missing entitlement still grants access (the vulnerability). -/
def missingEntitlementStillGranted_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true

theorem missingEntitlementStillGranted_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    missingEntitlementStillGranted_prop appId resource grantedEntitlements := by
  intro _hMissing
  rfl

/-- An empty entitlement list still grants access. -/
def emptyListGrants_prop (appId : Int) (resource : String) : Prop :=
  unsafeAppEntitlements appId resource [] = true

theorem emptyListGrants_thm (appId : Int) (resource : String) :
    emptyListGrants_prop appId resource := by
  rfl

/-- Where the safe membership check denies access, the unsafe check grants it. -/
def differsFromSafe_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∉ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true ∧
      safeAppEntitlements appId resource grantedEntitlements = false

theorem differsFromSafe_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    differsFromSafe_prop appId resource grantedEntitlements := by
  intro hMissing
  refine ⟨rfl, ?_⟩
  unfold safeAppEntitlements
  rw [List.contains_eq_mem]
  exact decide_eq_false hMissing

/-- When the entitlement is present, both checks grant access. -/
def agreesWhenEntitled_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  resource ∈ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true ∧
      safeAppEntitlements appId resource grantedEntitlements = true

theorem agreesWhenEntitled_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    agreesWhenEntitled_prop appId resource grantedEntitlements := by
  intro hMember
  refine ⟨rfl, ?_⟩
  unfold safeAppEntitlements
  rw [List.contains_eq_mem]
  exact decide_eq_true_iff.mpr hMember

/-- The two checks disagree exactly on requests the entitlement list does not cover. -/
def differsExactlyWhenMissing_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  (unsafeAppEntitlements appId resource grantedEntitlements ≠
      safeAppEntitlements appId resource grantedEntitlements) ↔
    resource ∉ grantedEntitlements

theorem differsExactlyWhenMissing_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    differsExactlyWhenMissing_prop appId resource grantedEntitlements := by
  unfold differsExactlyWhenMissing_prop unsafeAppEntitlements safeAppEntitlements
  rw [List.contains_eq_mem]
  -- `(true ≠ decide (resource ∈ grantedEntitlements)) ↔ resource ∉ _`
  by_cases hmem : resource ∈ grantedEntitlements
  · have hdec : decide (resource ∈ grantedEntitlements) = true :=
      decide_eq_true_iff.mpr hmem
    constructor
    · intro hne
      exact False.elim (hne hdec.symm)
    · intro hnot
      exact False.elim (hnot hmem)
  · have hdec : decide (resource ∈ grantedEntitlements) = false :=
      decide_eq_false hmem
    constructor
    · intro _
      exact hmem
    · intro _ heq
      rw [hdec] at heq
      cases heq

/-- The safe baseline is exactly list membership. -/
def safeGrantsIffMember_prop (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Prop :=
  safeAppEntitlements appId resource grantedEntitlements = true ↔
    resource ∈ grantedEntitlements

theorem safeGrantsIffMember_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    safeGrantsIffMember_prop appId resource grantedEntitlements := by
  unfold safeGrantsIffMember_prop safeAppEntitlements
  rw [List.contains_eq_mem]
  exact decide_eq_true_iff

/-- Concrete Python negative test: app `5`, resource `"camera"`, empty list. -/
def vulnerabilityWitness_prop : Prop :=
  unsafeAppEntitlements 5 "camera" [] = true ∧
    safeAppEntitlements 5 "camera" [] = false

theorem vulnerabilityWitness_thm : vulnerabilityWitness_prop := by
  refine ⟨rfl, ?_⟩
  unfold safeAppEntitlements
  rw [List.contains_nil]

/-- The unsafe function is not extensionally the safe membership check. -/
def notEquivalentToSafe_prop : Prop :=
  ¬ ∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
      unsafeAppEntitlements appId resource grantedEntitlements =
        safeAppEntitlements appId resource grantedEntitlements

theorem notEquivalentToSafe_thm : notEquivalentToSafe_prop := by
  intro hall
  have hEq := hall 5 "camera" ([] : List String)
  unfold unsafeAppEntitlements safeAppEntitlements at hEq
  rw [List.contains_nil] at hEq
  cases hEq

/-! ## Postcondition -/

/-- Full postcondition: unconditional grant, ignored arguments, and disagreement
with the safe membership check precisely when the entitlement is absent. -/
def Post_prop (appId : Int) (resource : String) (grantedEntitlements : List String) : Prop :=
  alwaysGranted_prop appId resource grantedEntitlements ∧
  entitlementsIrrelevant_prop appId resource ∧
  appIdIrrelevant_prop resource grantedEntitlements ∧
  resourceIrrelevant_prop appId grantedEntitlements ∧
  argumentsIrrelevant_prop ∧
  missingEntitlementStillGranted_prop appId resource grantedEntitlements ∧
  emptyListGrants_prop appId resource ∧
  differsFromSafe_prop appId resource grantedEntitlements ∧
  agreesWhenEntitled_prop appId resource grantedEntitlements ∧
  differsExactlyWhenMissing_prop appId resource grantedEntitlements ∧
  safeGrantsIffMember_prop appId resource grantedEntitlements ∧
  vulnerabilityWitness_prop ∧
  notEquivalentToSafe_prop

/-! ## Property-based tests

Executable checks of each `_prop` and of `Post_prop`. Randomized checks use
Plausible. Bounded checks exhaust small app ids, resource names, and entitlement
lists, including branches where the resource is forced in or out of the list.
-/

def pbtAppIds : List Int := [0, 1, 5, 7, 42, 99, -1, -3, 100]

def pbtResources : List String :=
  ["camera", "contacts", "microphone", "location", "photos", ""]

def pbtEntLists : List (List String) :=
  [[], ["camera"], ["location"], ["camera", "microphone"],
   ["contacts", "location"], ["camera", "contacts", "microphone", "location"],
   ["photos", "bluetooth", ""]]

-- alwaysGranted_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource grantedEntitlements = true)

example : (List.range 30).all (fun n =>
    unsafeAppEntitlements (Int.ofNat n) "camera" [] = true &&
    unsafeAppEntitlements (-(Int.ofNat n)) "microphone" ["location"] = true) = true := by
  native_decide

-- entitlementsIrrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (e1 e2 : List String),
    unsafeAppEntitlements appId resource e1 = unsafeAppEntitlements appId resource e2)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun e1 =>
        pbtEntLists.all fun e2 =>
          unsafeAppEntitlements appId resource e1 ==
            unsafeAppEntitlements appId resource e2) = true := by
  native_decide

-- appIdIrrelevant_prop
#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements a1 resource grantedEntitlements =
      unsafeAppEntitlements a2 resource grantedEntitlements)

example : (pbtAppIds.all fun a1 =>
    pbtAppIds.all fun a2 =>
      pbtResources.all fun resource =>
        pbtEntLists.all fun ents =>
          unsafeAppEntitlements a1 resource ents ==
            unsafeAppEntitlements a2 resource ents) = true := by
  native_decide

-- resourceIrrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (r1 r2 : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId r1 grantedEntitlements =
      unsafeAppEntitlements appId r2 grantedEntitlements)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun r1 =>
      pbtResources.all fun r2 =>
        pbtEntLists.all fun ents =>
          unsafeAppEntitlements appId r1 ents ==
            unsafeAppEntitlements appId r2 ents) = true := by
  native_decide

-- argumentsIrrelevant_prop
#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (r1 r2 : String) (e1 e2 : List String),
    unsafeAppEntitlements a1 r1 e1 = unsafeAppEntitlements a2 r2 e2)

example : (pbtAppIds.all fun a1 =>
    pbtAppIds.all fun a2 =>
      pbtResources.all fun r1 =>
        pbtResources.all fun r2 =>
          pbtEntLists.all fun e1 =>
            pbtEntLists.all fun e2 =>
              unsafeAppEntitlements a1 r1 e1 ==
                unsafeAppEntitlements a2 r2 e2) = true := by
  native_decide

-- missingEntitlementStillGranted_prop
-- Boolean form of `resource ∉ ents → result = true`, so samples are never discarded.
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (ents : List String),
    (ents.contains resource ||
      unsafeAppEntitlements appId resource ents == true) = true)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun ents =>
        let stripped := ents.filter fun e => e != resource
        (stripped.contains resource == false) &&
          (unsafeAppEntitlements appId resource stripped == true)) = true := by
  native_decide

-- emptyListGrants_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String),
    unsafeAppEntitlements appId resource ([] : List String) = true)

example : (List.range 30).all (fun n =>
    unsafeAppEntitlements (Int.ofNat n) "camera" [] = true &&
    unsafeAppEntitlements (-(Int.ofNat n)) "contacts" [] = true) = true := by
  native_decide

-- differsFromSafe_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (ents : List String),
    (ents.contains resource ||
      (unsafeAppEntitlements appId resource ents == true &&
        safeAppEntitlements appId resource ents == false)) = true)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun ents =>
        let stripped := ents.filter fun e => e != resource
        (unsafeAppEntitlements appId resource stripped == true) &&
          (safeAppEntitlements appId resource stripped == false)) = true := by
  native_decide

-- agreesWhenEntitled_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (ents : List String),
    (!(ents.contains resource) ||
      (unsafeAppEntitlements appId resource ents == true &&
        safeAppEntitlements appId resource ents == true)) = true)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun ents =>
        let entitled := resource :: ents
        (unsafeAppEntitlements appId resource entitled == true) &&
          (safeAppEntitlements appId resource entitled == true)) = true := by
  native_decide

-- differsExactlyWhenMissing_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (ents : List String),
    ((unsafeAppEntitlements appId resource ents !=
        safeAppEntitlements appId resource ents) ==
      !(ents.contains resource)) = true)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun ents =>
        let u := unsafeAppEntitlements appId resource ents
        let s := safeAppEntitlements appId resource ents
        ((u != s) == !(ents.contains resource))) = true := by
  native_decide

-- safeGrantsIffMember_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (ents : List String),
    (safeAppEntitlements appId resource ents == ents.contains resource) = true)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun ents =>
        safeAppEntitlements appId resource ents == ents.contains resource) = true := by
  native_decide

-- vulnerabilityWitness_prop
example : (unsafeAppEntitlements 5 "camera" ([] : List String) == true &&
    safeAppEntitlements 5 "camera" ([] : List String) == false) = true := by
  native_decide

#eval unsafeAppEntitlements 5 "camera" ([] : List String) &&
  !safeAppEntitlements 5 "camera" ([] : List String)

-- notEquivalentToSafe_prop: search the bounded domain for a disagreement.
example : (pbtAppIds.any fun appId =>
    pbtResources.any fun resource =>
      pbtEntLists.any fun ents =>
        unsafeAppEntitlements appId resource ents == true &&
          safeAppEntitlements appId resource ents == false) = true := by
  native_decide

/-- Executable Boolean form of `Post_prop` on one request, with the universal
conjuncts bounded by `pbtAppIds`, `pbtResources`, and `pbtEntLists`. -/
def postBool (appId : Int) (resource : String) (ents : List String) : Bool :=
  let u := unsafeAppEntitlements appId resource ents
  let s := safeAppEntitlements appId resource ents
  let always := u == true
  let entIrrel := pbtEntLists.all fun e2 => u == unsafeAppEntitlements appId resource e2
  let appIrrel := pbtAppIds.all fun a2 => u == unsafeAppEntitlements a2 resource ents
  let resIrrel := pbtResources.all fun r2 => u == unsafeAppEntitlements appId r2 ents
  let argsIrrel :=
    pbtAppIds.all fun a2 =>
      pbtResources.all fun r2 =>
        pbtEntLists.all fun e2 =>
          u == unsafeAppEntitlements a2 r2 e2
  let missing := ents.contains resource || u == true
  let empty := unsafeAppEntitlements appId resource [] == true
  let differs := ents.contains resource || (u == true && s == false)
  let agrees := !(ents.contains resource) || (u == true && s == true)
  let exact := (u != s) == !(ents.contains resource)
  let safeIff := s == ents.contains resource
  let witness :=
    unsafeAppEntitlements 5 "camera" [] == true &&
      safeAppEntitlements 5 "camera" [] == false
  always && entIrrel && appIrrel && resIrrel && argsIrrel && missing && empty &&
    differs && agrees && exact && safeIff && witness

/-- One random sample of the executable Boolean form of `Post_prop`. -/
def postSample (appId a2 : Int) (resource r2 : String) (e1 e2 : List String) : Bool :=
  let u := unsafeAppEntitlements appId resource e1
  let s := safeAppEntitlements appId resource e1
  (u == true) &&
    (u == unsafeAppEntitlements appId resource e2) &&
    (u == unsafeAppEntitlements a2 resource e1) &&
    (u == unsafeAppEntitlements appId r2 e1) &&
    (u == unsafeAppEntitlements a2 r2 e2) &&
    (unsafeAppEntitlements appId resource [] == true) &&
    (e1.contains resource || (u && (s == false))) &&
    (!(e1.contains resource) || (u && s)) &&
    ((u != s) == !(e1.contains resource)) &&
    (s == e1.contains resource) &&
    (unsafeAppEntitlements 5 "camera" [] &&
      (safeAppEntitlements 5 "camera" [] == false))

-- Post_prop
#eval Plausible.Testable.check
  (∀ (appId a2 : Int) (resource r2 : String) (e1 e2 : List String),
    postSample appId a2 resource r2 e1 e2 = true)

example : (pbtAppIds.all fun appId =>
    pbtResources.all fun resource =>
      pbtEntLists.all fun ents =>
        postBool appId resource ents) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String)
    (hPre : Pre appId resource grantedEntitlements) :
    Post_prop appId resource grantedEntitlements := by
  cases hPre
  unfold Post_prop
  exact
    ⟨alwaysGranted_thm appId resource grantedEntitlements,
     entitlementsIrrelevant_thm appId resource,
     appIdIrrelevant_thm resource grantedEntitlements,
     resourceIrrelevant_thm appId grantedEntitlements,
     argumentsIrrelevant_thm,
     missingEntitlementStillGranted_thm appId resource grantedEntitlements,
     emptyListGrants_thm appId resource,
     differsFromSafe_thm appId resource grantedEntitlements,
     agreesWhenEntitled_thm appId resource grantedEntitlements,
     differsExactlyWhenMissing_thm appId resource grantedEntitlements,
     safeGrantsIffMember_thm appId resource grantedEntitlements,
     vulnerabilityWitness_thm,
     notEquivalentToSafe_thm⟩

/-! ## Imperative implementation

`Id.run do` with a mutable decision flag. The flag is forced to `true` and the
app id, resource, and entitlement list are never read. That is the same
vulnerability as `return True` in Python. -/

def unsafeAppEntitlementsImp (appId : Int) (resource : String)
    (grantedEntitlements : List String) : Bool :=
  Id.run do
    let mut granted : Bool := false
    granted := true
    let _appId := appId
    let _resource := resource
    let _grantedEntitlements := grantedEntitlements
    return granted

/-! ## Imperative tests -/

example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
#eval unsafeAppEntitlementsImp 42 "camera" []

example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
#eval unsafeAppEntitlementsImp 1 "contacts" ["location"]

example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide
#eval unsafeAppEntitlementsImp 99 "microphone" []

example : unsafeAppEntitlementsImp 7 "location" [] =
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafeAppEntitlementsImp 7 "location" [] ==
  unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]

example : unsafeAppEntitlementsImp 5 "camera" [] = true := by native_decide
#eval unsafeAppEntitlementsImp 5 "camera" []

example : (unsafeAppEntitlementsImp 5 "camera" [] ==
    safeAppEntitlements 5 "camera" []) = false := by native_decide

def checkImp : Bool :=
  unsafeAppEntitlementsImp 42 "camera" [] == true &&
  unsafeAppEntitlementsImp 1 "contacts" ["location"] == true &&
  unsafeAppEntitlementsImp 99 "microphone" [] == true &&
  (unsafeAppEntitlementsImp 7 "location" [] ==
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]) &&
  unsafeAppEntitlementsImp 5 "camera" [] == true

example : checkImp = true := by native_decide

#eval checkImp

example : unsafeAppEntitlements 42 "camera" [] =
    unsafeAppEntitlementsImp 42 "camera" [] := by native_decide
example : unsafeAppEntitlements 1 "contacts" ["location"] =
    unsafeAppEntitlementsImp 1 "contacts" ["location"] := by native_decide
example : unsafeAppEntitlements 99 "microphone" [] =
    unsafeAppEntitlementsImp 99 "microphone" [] := by native_decide
example : unsafeAppEntitlements 7 "location" ["camera", "microphone"] =
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide
example : unsafeAppEntitlements 5 "camera" [] =
    unsafeAppEntitlementsImp 5 "camera" [] := by native_decide

/-! ## Equivalence -/

theorem equivalence_thm (appId : Int) (resource : String)
    (grantedEntitlements : List String) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements := by
  rfl

end «93_unsafeAppEntitlements»

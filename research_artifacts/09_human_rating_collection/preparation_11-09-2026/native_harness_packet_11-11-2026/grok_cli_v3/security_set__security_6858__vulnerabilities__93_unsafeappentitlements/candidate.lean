import Mathlib

/-!
# Unsafe iOS App Entitlements Model

MIT 6.858 Lecture 9. Vulnerability: there is no entitlement check, so any
application is granted access to any resource. The granted-entitlement list
is never consulted.

`unsafeAppEntitlements` is the direct translation of the Python function
`unsafe_app_entitlements`, whose body is `return True`.

`safeAppEntitlements` is the membership check the lecture contrasts with the
bug. The Python test records that this safe version returns `False` on the
rogue camera request that the unsafe version accepts. It is not a second
Python function; it is the specification of that contrast.
-/

namespace «93_unsafeAppEntitlements»

/-! ## Implementation -/

/-- Application identifier. Python `int`, so negative ids are included. -/
abbrev AppId := Int

/-- Resource or entitlement name. Python `str`. -/
abbrev Resource := String

/-- Entitlements granted to an app. Python `List[str]`. -/
abbrev EntitlementList := List Resource

/--
Unsafe entitlement check: every resource request is granted.

The application id, the resource name, and the granted-entitlement list are
ignored. This is the vulnerability: the entitlement list is never consulted.
-/
def unsafeAppEntitlements
    (_appId : AppId)
    (_resource : Resource)
    (_grantedEntitlements : EntitlementList) : Bool :=
  true

/--
Safe entitlement check used for the lecture's negative contrast.

Access is granted if and only if `resource` occurs in `grantedEntitlements`.
The application id is not consulted: the granted list is passed in explicitly,
as in the Python signature.
-/
def safeAppEntitlements
    (_appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Bool :=
  grantedEntitlements.contains resource

/--
Translation of Python `check`: the five lecture assertions, plus the recorded
safe-version outcome on the rogue camera request.
-/
def check : Bool :=
  (unsafeAppEntitlements 42 "camera" [] == true) &&
    (unsafeAppEntitlements 1 "contacts" ["location"] == true) &&
    (unsafeAppEntitlements 99 "microphone" [] == true) &&
    (unsafeAppEntitlements 7 "location" [] ==
      unsafeAppEntitlements 7 "location" ["camera", "microphone"]) &&
    (unsafeAppEntitlements 5 "camera" [] == true) &&
    (safeAppEntitlements 5 "camera" [] == false)

/-! ## Unit tests -/

-- Rogue app gains camera access without an entitlement.
example : unsafeAppEntitlements 42 "camera" [] = true := by native_decide

-- App without the contacts entitlement still gets access.
example : unsafeAppEntitlements 1 "contacts" ["location"] = true := by native_decide

-- Empty entitlement list: access is still granted.
example : unsafeAppEntitlements 99 "microphone" [] = true := by native_decide

-- Entitlement-list contents are irrelevant.
example : unsafeAppEntitlements 7 "location" [] =
    unsafeAppEntitlements 7 "location" ["camera", "microphone"] := by native_decide

-- Negative contrast: the unsafe checker grants the request the safe checker denies.
example : unsafeAppEntitlements 5 "camera" [] = true := by native_decide
example : safeAppEntitlements 5 "camera" [] = false := by native_decide

-- When the resource is entitled, the safe checker agrees with the unsafe one.
example : safeAppEntitlements 1 "location" ["location"] = true := by native_decide
example : unsafeAppEntitlements 1 "location" ["location"] =
    safeAppEntitlements 1 "location" ["location"] := by native_decide

-- The Python domain is `int`, so a negative application id is accepted.
example : unsafeAppEntitlements (-1) "photos" ["camera"] = true := by native_decide

example : check = true := by native_decide

#eval unsafeAppEntitlements 42 "camera" []
#eval unsafeAppEntitlements 1 "contacts" ["location"]
#eval unsafeAppEntitlements 99 "microphone" []
#eval unsafeAppEntitlements 7 "location" [] ==
  unsafeAppEntitlements 7 "location" ["camera", "microphone"]
#eval unsafeAppEntitlements 5 "camera" []
#eval safeAppEntitlements 5 "camera" []
#eval check
#eval if check then "All tests passed." else "Tests failed."

/-! ## Pre-condition -/

/--
The Python function accepts every `int`, every `str`, and every `List[str]`.
No input is rejected, so the precondition is universally true.
-/
def Pre
    (_appId : AppId)
    (_resource : Resource)
    (_grantedEntitlements : EntitlementList) : Prop :=
  True

/-! ## Properties -/

/-- Every call returns `true`: the check never denies access. -/
def unconditional_grant_prop
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  unsafeAppEntitlements appId resource grantedEntitlements = true

theorem unconditional_grant_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    unconditional_grant_prop appId resource grantedEntitlements := by
  simp only [unconditional_grant_prop, unsafeAppEntitlements]

/-- The granted-entitlement list is never consulted. -/
def entitlement_irrelevant_prop
    (appId : AppId)
    (resource : Resource)
    (ents₁ ents₂ : EntitlementList) : Prop :=
  unsafeAppEntitlements appId resource ents₁ =
    unsafeAppEntitlements appId resource ents₂

theorem entitlement_irrelevant_thm
    (appId : AppId)
    (resource : Resource)
    (ents₁ ents₂ : EntitlementList) :
    entitlement_irrelevant_prop appId resource ents₁ ents₂ := by
  simp only [entitlement_irrelevant_prop, unsafeAppEntitlements]

/-- The resource name is never consulted. -/
def resource_irrelevant_prop
    (appId : AppId)
    (resource₁ resource₂ : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  unsafeAppEntitlements appId resource₁ grantedEntitlements =
    unsafeAppEntitlements appId resource₂ grantedEntitlements

theorem resource_irrelevant_thm
    (appId : AppId)
    (resource₁ resource₂ : Resource)
    (grantedEntitlements : EntitlementList) :
    resource_irrelevant_prop appId resource₁ resource₂ grantedEntitlements := by
  simp only [resource_irrelevant_prop, unsafeAppEntitlements]

/-- The application identifier is never consulted. -/
def app_irrelevant_prop
    (appId₁ appId₂ : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  unsafeAppEntitlements appId₁ resource grantedEntitlements =
    unsafeAppEntitlements appId₂ resource grantedEntitlements

theorem app_irrelevant_thm
    (appId₁ appId₂ : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    app_irrelevant_prop appId₁ appId₂ resource grantedEntitlements := by
  simp only [app_irrelevant_prop, unsafeAppEntitlements]

/--
Any application is granted any resource. Two calls agree even when the
application id, the resource, and the entitlement list all differ.
-/
def input_irrelevant_prop
    (appId₁ appId₂ : AppId)
    (resource₁ resource₂ : Resource)
    (ents₁ ents₂ : EntitlementList) : Prop :=
  unsafeAppEntitlements appId₁ resource₁ ents₁ =
    unsafeAppEntitlements appId₂ resource₂ ents₂

theorem input_irrelevant_thm
    (appId₁ appId₂ : AppId)
    (resource₁ resource₂ : Resource)
    (ents₁ ents₂ : EntitlementList) :
    input_irrelevant_prop appId₁ appId₂ resource₁ resource₂ ents₁ ents₂ := by
  simp only [input_irrelevant_prop, unsafeAppEntitlements]

/--
Access is granted even when the requested resource is absent from the
entitlement list. This is the missing-check vulnerability.
-/
def missing_entitlement_still_granted_prop
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  ¬ resource ∈ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true

theorem missing_entitlement_still_granted_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    missing_entitlement_still_granted_prop
      appId resource grantedEntitlements := by
  intro _
  simp only [unsafeAppEntitlements]

/-- An empty entitlement list still grants access. -/
def empty_entitlements_granted_prop
    (appId : AppId)
    (resource : Resource) : Prop :=
  unsafeAppEntitlements appId resource [] = true

theorem empty_entitlements_granted_thm
    (appId : AppId)
    (resource : Resource) :
    empty_entitlements_granted_prop appId resource := by
  simp only [empty_entitlements_granted_prop, unsafeAppEntitlements]

/--
When the resource is missing, the unsafe checker returns `true` and the safe
membership checker returns `false`.
-/
def diverges_from_safe_prop
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  ¬ resource ∈ grantedEntitlements →
    unsafeAppEntitlements appId resource grantedEntitlements = true ∧
      safeAppEntitlements appId resource grantedEntitlements = false

theorem diverges_from_safe_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    diverges_from_safe_prop appId resource grantedEntitlements := by
  intro hmiss
  refine ⟨?_, ?_⟩
  · exact unconditional_grant_thm appId resource grantedEntitlements
  · simpa only [safeAppEntitlements, List.contains_eq_mem, decide_eq_false_iff_not]
      using hmiss

/--
The unsafe checker and the safe checker agree if and only if the resource
is in the granted list. They disagree exactly on the vulnerable requests.
-/
def agrees_with_safe_iff_entitled_prop
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  (unsafeAppEntitlements appId resource grantedEntitlements =
      safeAppEntitlements appId resource grantedEntitlements) ↔
    resource ∈ grantedEntitlements

theorem agrees_with_safe_iff_entitled_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    agrees_with_safe_iff_entitled_prop appId resource grantedEntitlements := by
  unfold agrees_with_safe_iff_entitled_prop
  simp only [unsafeAppEntitlements, safeAppEntitlements, List.contains_eq_mem]
  apply Iff.intro
  · intro hEq
    exact of_decide_eq_true (Eq.symm hEq)
  · intro hMem
    exact Eq.symm (decide_eq_true hMem)

/-- The safe checker grants access exactly when the resource is entitled. -/
def safe_grants_iff_member_prop
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  safeAppEntitlements appId resource grantedEntitlements = true ↔
    resource ∈ grantedEntitlements

theorem safe_grants_iff_member_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    safe_grants_iff_member_prop appId resource grantedEntitlements := by
  simp only [safe_grants_iff_member_prop, safeAppEntitlements,
    List.contains_eq_mem, decide_eq_true_iff]

/--
There exists a rogue request: some application is granted a resource that is
not in its entitlement list. The witness is the lecture's camera example.
-/
def admits_rogue_access_prop : Prop :=
  ∃ appId : AppId, ∃ resource : Resource, ∃ grantedEntitlements : EntitlementList,
    resource ∉ grantedEntitlements ∧
      unsafeAppEntitlements appId resource grantedEntitlements = true

theorem admits_rogue_access_thm : admits_rogue_access_prop := by
  refine ⟨42, "camera", [], ?_, ?_⟩
  · exact List.not_mem_nil
  · rfl

/--
The unsafe checker is not an entitlement-membership test: it is not the case
that access is granted if and only if the resource was entitled.
-/
theorem not_membership_check_thm :
    ¬ ∀ (appId : AppId) (resource : Resource) (grantedEntitlements : EntitlementList),
        (unsafeAppEntitlements appId resource grantedEntitlements = true ↔
          resource ∈ grantedEntitlements) := by
  intro h
  exact List.not_mem_nil
    ((h 5 "camera" []).1 (unconditional_grant_thm 5 "camera" []))

/-! ## Post-condition -/

/--
Post-condition of one unsafe check.

The call grants access. That decision does not depend on the entitlement list,
the resource name, or the application id. A missing entitlement, including the
empty list, still yields a grant. The result agrees with the safe membership
check exactly when the resource is entitled, and disagrees when it is not.
-/
def Post_prop
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Prop :=
  unconditional_grant_prop appId resource grantedEntitlements ∧
    (∀ ents₂ : EntitlementList,
      entitlement_irrelevant_prop appId resource grantedEntitlements ents₂) ∧
    (∀ resource₂ : Resource,
      resource_irrelevant_prop appId resource resource₂ grantedEntitlements) ∧
    (∀ appId₂ : AppId,
      app_irrelevant_prop appId appId₂ resource grantedEntitlements) ∧
    missing_entitlement_still_granted_prop appId resource grantedEntitlements ∧
    empty_entitlements_granted_prop appId resource ∧
    diverges_from_safe_prop appId resource grantedEntitlements ∧
    agrees_with_safe_iff_entitled_prop appId resource grantedEntitlements

/-! ## Property-based tests -/

/-- Application ids used by the bounded tests, including the lecture values. -/
def benchAppIds : List Int := [0, 1, 5, 7, 42, 99, -1]

/-- Resource names used by the bounded tests, including the lecture names. -/
def benchResources : List String :=
  ["camera", "contacts", "microphone", "location", "photos", ""]

/-- Entitlement lists used by the bounded tests, including the lecture lists. -/
def benchEntLists : List (List String) :=
  [[], ["location"], ["camera", "microphone"], ["camera"],
   ["contacts", "location"], ["camera", "camera"],
   ["photos", "microphone", "location"]]

/-- Executable form of `Post_prop` on one bench triple.

The nested universals of `Post_prop` are checked on the finite bench, not on
every `String` and `List String`. The theorem statement itself stays universal.
-/
def postHoldsOnBench
    (appId : AppId)
    (resource : Resource)
    (ents : EntitlementList) : Bool :=
  (unsafeAppEntitlements appId resource ents == true) &&
    (benchEntLists.all fun ents₂ =>
      unsafeAppEntitlements appId resource ents ==
        unsafeAppEntitlements appId resource ents₂) &&
    (benchResources.all fun resource₂ =>
      unsafeAppEntitlements appId resource ents ==
        unsafeAppEntitlements appId resource₂ ents) &&
    (benchAppIds.all fun appId₂ =>
      unsafeAppEntitlements appId resource ents ==
        unsafeAppEntitlements appId₂ resource ents) &&
    (ents.contains resource || unsafeAppEntitlements appId resource ents) &&
    (unsafeAppEntitlements appId resource [] == true) &&
    (ents.contains resource ||
      (unsafeAppEntitlements appId resource ents &&
        (safeAppEntitlements appId resource ents == false))) &&
    ((unsafeAppEntitlements appId resource ents ==
        safeAppEntitlements appId resource ents) ==
      ents.contains resource)

-- PBT: unconditional_grant_prop
-- Executable form: the `_prop` wrapper is not itself a Plausible instance.
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    unsafeAppEntitlements appId resource grantedEntitlements = true)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents =>
          unsafeAppEntitlements appId resource ents = true) = true := by
  native_decide

-- PBT: entitlement_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (ents₁ ents₂ : List String),
    unsafeAppEntitlements appId resource ents₁ =
      unsafeAppEntitlements appId resource ents₂)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents₁ =>
          benchEntLists.all fun ents₂ =>
            unsafeAppEntitlements appId resource ents₁ ==
              unsafeAppEntitlements appId resource ents₂) = true := by
  native_decide

-- PBT: resource_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource₁ resource₂ : String) (ents : List String),
    unsafeAppEntitlements appId resource₁ ents =
      unsafeAppEntitlements appId resource₂ ents)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource₁ =>
        benchResources.all fun resource₂ =>
          benchEntLists.all fun ents =>
            unsafeAppEntitlements appId resource₁ ents ==
              unsafeAppEntitlements appId resource₂ ents) = true := by
  native_decide

-- PBT: app_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId₁ appId₂ : Int) (resource : String) (ents : List String),
    unsafeAppEntitlements appId₁ resource ents =
      unsafeAppEntitlements appId₂ resource ents)

example :
    (benchAppIds.all fun appId₁ =>
      benchAppIds.all fun appId₂ =>
        benchResources.all fun resource =>
          benchEntLists.all fun ents =>
            unsafeAppEntitlements appId₁ resource ents ==
              unsafeAppEntitlements appId₂ resource ents) = true := by
  native_decide

-- PBT: input_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (appId₁ appId₂ : Int) (resource₁ resource₂ : String)
      (ents₁ ents₂ : List String),
    unsafeAppEntitlements appId₁ resource₁ ents₁ =
      unsafeAppEntitlements appId₂ resource₂ ents₂)

example :
    (benchAppIds.all fun appId₁ =>
      benchAppIds.all fun appId₂ =>
        benchResources.all fun resource₁ =>
          benchResources.all fun resource₂ =>
            benchEntLists.all fun ents₁ =>
              benchEntLists.all fun ents₂ =>
                unsafeAppEntitlements appId₁ resource₁ ents₁ ==
                  unsafeAppEntitlements appId₂ resource₂ ents₂) = true := by
  native_decide

-- PBT: missing_entitlement_still_granted_prop
-- The implication is the property. The bounded check below evaluates both
-- the missing-entitlement branch and the entitled branch.
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    ¬ resource ∈ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements = true)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents =>
          ents.contains resource || unsafeAppEntitlements appId resource ents) = true := by
  native_decide

-- PBT: empty_entitlements_granted_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String),
    unsafeAppEntitlements appId resource [] = true)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        unsafeAppEntitlements appId resource [] = true) = true := by
  native_decide

-- PBT: diverges_from_safe_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    ¬ resource ∈ grantedEntitlements →
      unsafeAppEntitlements appId resource grantedEntitlements = true ∧
        safeAppEntitlements appId resource grantedEntitlements = false)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents =>
          ents.contains resource ||
            (unsafeAppEntitlements appId resource ents &&
              (safeAppEntitlements appId resource ents == false))) = true := by
  native_decide

-- PBT: agrees_with_safe_iff_entitled_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    (unsafeAppEntitlements appId resource grantedEntitlements =
        safeAppEntitlements appId resource grantedEntitlements) ↔
      resource ∈ grantedEntitlements)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents =>
          ((unsafeAppEntitlements appId resource ents ==
              safeAppEntitlements appId resource ents) ==
            ents.contains resource)) = true := by
  native_decide

-- PBT: safe_grants_iff_member_prop
#eval Plausible.Testable.check
  (∀ (appId : Int) (resource : String) (grantedEntitlements : List String),
    safeAppEntitlements appId resource grantedEntitlements = true ↔
      resource ∈ grantedEntitlements)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents =>
          ((safeAppEntitlements appId resource ents == true) ==
            ents.contains resource)) = true := by
  native_decide

-- PBT: admits_rogue_access_prop
-- Closed existential: Plausible has no sampler for `∃`. The executable check
-- is the lecture witness together with a bounded search for rogue grants.
example :
    (!(([] : List String).contains "camera") &&
      unsafeAppEntitlements 42 "camera" []) = true := by
  native_decide

example :
    (benchAppIds.any fun appId =>
      benchResources.any fun resource =>
        benchEntLists.any fun ents =>
          (!ents.contains resource) &&
            unsafeAppEntitlements appId resource ents) = true := by
  native_decide

#eval (!(([] : List String).contains "camera") && unsafeAppEntitlements 42 "camera" [])

-- PBT: Post_prop
-- Flat executable form of the post-condition. Nested `∀` inside a long
-- conjunction does not synthesize a Plausible instance, so the quantified
-- comparisons are extra sampled inputs and the membership facts are Bool tests.
-- `postHoldsOnBench` below is the exhaustive check on the lecture alphabet.
#eval Plausible.Testable.check
  (∀ (appId appId₂ : Int) (resource resource₂ : String)
      (grantedEntitlements ents₂ : List String),
    ((unsafeAppEntitlements appId resource grantedEntitlements &&
        (grantedEntitlements.contains resource ||
          unsafeAppEntitlements appId resource grantedEntitlements) &&
        (unsafeAppEntitlements appId resource [] == true) &&
        (grantedEntitlements.contains resource ||
          (unsafeAppEntitlements appId resource grantedEntitlements &&
            (safeAppEntitlements appId resource grantedEntitlements == false))) &&
        ((unsafeAppEntitlements appId resource grantedEntitlements ==
            safeAppEntitlements appId resource grantedEntitlements) ==
          grantedEntitlements.contains resource)) = true) ∧
      unsafeAppEntitlements appId resource grantedEntitlements =
        unsafeAppEntitlements appId resource ents₂ ∧
      unsafeAppEntitlements appId resource grantedEntitlements =
        unsafeAppEntitlements appId resource₂ grantedEntitlements ∧
      unsafeAppEntitlements appId resource grantedEntitlements =
        unsafeAppEntitlements appId₂ resource grantedEntitlements)

example :
    (benchAppIds.all fun appId =>
      benchResources.all fun resource =>
        benchEntLists.all fun ents =>
          postHoldsOnBench appId resource ents) = true := by
  native_decide

/-! ## Correctness -/

/-- Every input admitted by `Pre` satisfies `Post_prop`. -/
theorem correctness_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList)
    (_hPre : Pre appId resource grantedEntitlements) :
    Post_prop appId resource grantedEntitlements := by
  unfold Post_prop
  refine ⟨unconditional_grant_thm appId resource grantedEntitlements, ?_⟩
  refine ⟨?_, ?_⟩
  · intro ents₂
    exact entitlement_irrelevant_thm appId resource grantedEntitlements ents₂
  refine ⟨?_, ?_⟩
  · intro resource₂
    exact resource_irrelevant_thm appId resource resource₂ grantedEntitlements
  refine ⟨?_, ?_⟩
  · intro appId₂
    exact app_irrelevant_thm appId appId₂ resource grantedEntitlements
  refine ⟨missing_entitlement_still_granted_thm appId resource grantedEntitlements, ?_⟩
  refine ⟨empty_entitlements_granted_thm appId resource, ?_⟩
  refine ⟨diverges_from_safe_thm appId resource grantedEntitlements, ?_⟩
  exact agrees_with_safe_iff_entitled_thm appId resource grantedEntitlements

/-! ## Imperative implementation -/

/--
Imperative counterpart of `unsafeAppEntitlements`.

A mutable flag starts denied. The entitlement list is traversed and the
traversal count is discarded: no membership test updates the flag. The flag
is then forced to `true`. This is `return True` written with `Id.run` and
local mutable state, and it is the same missing check.
-/
def unsafeAppEntitlementsImp
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) : Bool :=
  Id.run do
    let mut granted : Bool := false
    let mut ignoredCount : Nat := 0
    for _ent in grantedEntitlements do
      ignoredCount := ignoredCount + 1
    let _ := (appId, resource, ignoredCount)
    granted := true
    return granted

/-- Imperative translation of Python `check`. -/
def checkImp : Bool :=
  (unsafeAppEntitlementsImp 42 "camera" [] == true) &&
    (unsafeAppEntitlementsImp 1 "contacts" ["location"] == true) &&
    (unsafeAppEntitlementsImp 99 "microphone" [] == true) &&
    (unsafeAppEntitlementsImp 7 "location" [] ==
      unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]) &&
    (unsafeAppEntitlementsImp 5 "camera" [] == true) &&
    (safeAppEntitlements 5 "camera" [] == false)

/-! ## Imperative tests -/

example : unsafeAppEntitlementsImp 42 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp 1 "contacts" ["location"] = true := by native_decide
example : unsafeAppEntitlementsImp 99 "microphone" [] = true := by native_decide
example : unsafeAppEntitlementsImp 7 "location" [] =
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide
example : unsafeAppEntitlementsImp 5 "camera" [] = true := by native_decide
example : unsafeAppEntitlementsImp (-1) "photos" ["camera"] = true := by native_decide
example : checkImp = true := by native_decide

example : unsafeAppEntitlements 42 "camera" [] =
    unsafeAppEntitlementsImp 42 "camera" [] := by native_decide
example : unsafeAppEntitlements 1 "contacts" ["location"] =
    unsafeAppEntitlementsImp 1 "contacts" ["location"] := by native_decide
example : unsafeAppEntitlements 7 "location" ["camera", "microphone"] =
    unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"] := by native_decide

#eval unsafeAppEntitlementsImp 42 "camera" []
#eval unsafeAppEntitlementsImp 1 "contacts" ["location"]
#eval unsafeAppEntitlementsImp 99 "microphone" []
#eval unsafeAppEntitlementsImp 7 "location" [] ==
  unsafeAppEntitlementsImp 7 "location" ["camera", "microphone"]
#eval unsafeAppEntitlementsImp 5 "camera" []
#eval checkImp
#eval if checkImp then "All tests passed." else "Tests failed."

/-! ## Equivalence -/

/-- The functional checker and the imperative checker agree on every input. -/
theorem equivalence_thm
    (appId : AppId)
    (resource : Resource)
    (grantedEntitlements : EntitlementList) :
    unsafeAppEntitlements appId resource grantedEntitlements =
      unsafeAppEntitlementsImp appId resource grantedEntitlements := by
  simp only [unsafeAppEntitlements, unsafeAppEntitlementsImp, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, List.foldl_add_const, Nat.one_mul, Nat.zero_add,
    Id.run_pure]

end «93_unsafeAppEntitlements»

import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

This module formalizes the Python model of an unsafe iOS app entitlements check.
Vulnerability: no entitlement check is performed — any app gains access to any resource
unconditionally, regardless of its app ID, the requested resource, or its list of
granted entitlements.
-/

namespace «93_unsafeAppEntitlements»

/-! ## Implementation (Functional Definition) -/

/-- No check: all resource requests are granted unconditionally.
    Vulnerability: the entitlement list is never consulted. -/
def unsafe_app_entitlements (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool :=
  true

/-- Reference safe entitlement check: grants access iff `resource` is in `granted_entitlements`. -/
def safe_app_entitlements (_app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  granted_entitlements.contains resource

/-! ## Unit Tests -/

-- Rogue app gains camera access without entitlement
example : unsafe_app_entitlements 42 "camera" [] = true := by native_decide
#eval unsafe_app_entitlements 42 "camera" []

-- App without contacts entitlement still gets access
example : unsafe_app_entitlements 1 "contacts" ["location"] = true := by native_decide
#eval unsafe_app_entitlements 1 "contacts" ["location"]

-- Empty entitlement list: access still granted
example : unsafe_app_entitlements 99 "microphone" [] = true := by native_decide
#eval unsafe_app_entitlements 99 "microphone" []

-- Entitlement list contents are irrelevant
example :
    unsafe_app_entitlements 7 "location" [] =
    unsafe_app_entitlements 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafe_app_entitlements 7 "location" [] ==
      unsafe_app_entitlements 7 "location" ["camera", "microphone"]

-- Negative: different behavior from safe version
example : unsafe_app_entitlements 5 "camera" [] = true := by native_decide
example : safe_app_entitlements 5 "camera" [] = false := by native_decide
example :
    unsafe_app_entitlements 5 "camera" [] ≠
    safe_app_entitlements 5 "camera" [] := by native_decide
#eval unsafe_app_entitlements 5 "camera" []

/-! ## Pre-condition Predicate -/

/-- Pre-condition: all inputs (`app_id`, `resource`, `granted_entitlements`) are admissible. -/
def Pre (_app_id : Int) (_resource : String) (_granted_entitlements : List String) : Prop :=
  True

/-! ## Property Propositions and Theorems -/

/-- Property 1: Access is unconditionally granted (`true`) for any app, resource, and entitlement list. -/
def always_granted_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements = true

theorem always_granted_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    always_granted_prop app_id resource granted_entitlements := by
  rfl

/-- Property 2: No resource request is ever denied (`false`). -/
def never_denied_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements ≠ false

theorem never_denied_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    never_denied_prop app_id resource granted_entitlements := by
  simp [never_denied_prop, unsafe_app_entitlements]

/-- Property 3: An empty entitlement list still grants access to any resource. -/
def empty_entitlements_granted_prop (app_id : Int) (resource : String) : Prop :=
  unsafe_app_entitlements app_id resource [] = true

theorem empty_entitlements_granted_thm (app_id : Int) (resource : String) :
    empty_entitlements_granted_prop app_id resource := by
  rfl

/-- Property 4: Access is granted even when the requested resource is not in `granted_entitlements`. -/
def unentitled_access_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem unentitled_access_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unentitled_access_prop app_id resource granted_entitlements := by
  intro _
  rfl

/-- Property 5: Access is granted when the requested resource is in `granted_entitlements`. -/
def entitled_access_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∈ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem entitled_access_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    entitled_access_prop app_id resource granted_entitlements := by
  intro _
  rfl

/-- Property 6: The contents of `granted_entitlements` are irrelevant to the result. -/
def entitlements_irrelevant_prop (app_id : Int) (resource : String)
    (granted_entitlements₁ granted_entitlements₂ : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements₁ =
    unsafe_app_entitlements app_id resource granted_entitlements₂

theorem entitlements_irrelevant_thm (app_id : Int) (resource : String)
    (granted_entitlements₁ granted_entitlements₂ : List String) :
    entitlements_irrelevant_prop app_id resource granted_entitlements₁ granted_entitlements₂ := by
  rfl

/-- Property 7: The `app_id` argument is irrelevant to the result. -/
def app_id_irrelevant_prop (app_id₁ app_id₂ : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id₁ resource granted_entitlements =
    unsafe_app_entitlements app_id₂ resource granted_entitlements

theorem app_id_irrelevant_thm (app_id₁ app_id₂ : Int) (resource : String)
    (granted_entitlements : List String) :
    app_id_irrelevant_prop app_id₁ app_id₂ resource granted_entitlements := by
  rfl

/-- Property 8: The `resource` argument is irrelevant to the result. -/
def resource_irrelevant_prop (app_id : Int) (resource₁ resource₂ : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource₁ granted_entitlements =
    unsafe_app_entitlements app_id resource₂ granted_entitlements

theorem resource_irrelevant_thm (app_id : Int) (resource₁ resource₂ : String)
    (granted_entitlements : List String) :
    resource_irrelevant_prop app_id resource₁ resource₂ granted_entitlements := by
  rfl

/-- Property 9: All inputs (`app_id`, `resource`, and `granted_entitlements`) are irrelevant. -/
def all_inputs_irrelevant_prop (app_id₁ : Int) (resource₁ : String) (entitlements₁ : List String)
    (app_id₂ : Int) (resource₂ : String) (entitlements₂ : List String) : Prop :=
  unsafe_app_entitlements app_id₁ resource₁ entitlements₁ =
    unsafe_app_entitlements app_id₂ resource₂ entitlements₂

theorem all_inputs_irrelevant_thm (app_id₁ : Int) (resource₁ : String) (entitlements₁ : List String)
    (app_id₂ : Int) (resource₂ : String) (entitlements₂ : List String) :
    all_inputs_irrelevant_prop app_id₁ resource₁ entitlements₁ app_id₂ resource₂ entitlements₂ := by
  rfl

/-- Property 10: Divergence from the safe version whenever the requested resource is not granted. -/
def unsafe_differs_from_safe_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements ≠
      safe_app_entitlements app_id resource granted_entitlements

theorem unsafe_differs_from_safe_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_differs_from_safe_prop app_id resource granted_entitlements := by
  intro hnot
  simp only [unsafe_app_entitlements, safe_app_entitlements, ne_eq]
  intro h
  have hmem : resource ∈ granted_entitlements :=
    List.contains_iff.mp h.symm
  exact hnot hmem

/-- Property 11: Agreement with the safe version when the requested resource is granted. -/
def unsafe_agrees_with_safe_when_entitled_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∈ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements =
      safe_app_entitlements app_id resource granted_entitlements

theorem unsafe_agrees_with_safe_when_entitled_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_agrees_with_safe_when_entitled_prop app_id resource granted_entitlements := by
  intro hmem
  simp only [unsafe_app_entitlements, safe_app_entitlements]
  exact (List.contains_iff.mpr hmem).symm

/-! ## Post-condition -/

/-- Post-condition: conjunction of the specification properties for a given request. -/
def Post_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  always_granted_prop app_id resource granted_entitlements ∧
  never_denied_prop app_id resource granted_entitlements ∧
  empty_entitlements_granted_prop app_id resource ∧
  unentitled_access_prop app_id resource granted_entitlements ∧
  entitled_access_prop app_id resource granted_entitlements ∧
  entitlements_irrelevant_prop app_id resource granted_entitlements [] ∧
  app_id_irrelevant_prop app_id 0 resource granted_entitlements ∧
  resource_irrelevant_prop app_id resource "" granted_entitlements ∧
  all_inputs_irrelevant_prop app_id resource granted_entitlements 0 "" [] ∧
  unsafe_differs_from_safe_prop app_id resource granted_entitlements ∧
  unsafe_agrees_with_safe_when_entitled_prop app_id resource granted_entitlements

/-! ## Property-Based Tests -/

-- Randomized PBTs using Plausible

-- PBT for always_granted_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  unsafe_app_entitlements app_id resource entitlements = true)

-- PBT for never_denied_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  unsafe_app_entitlements app_id resource entitlements != false)

-- PBT for empty_entitlements_granted_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String),
  unsafe_app_entitlements app_id resource [] = true)

-- PBT for unentitled_access_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  !(entitlements.contains resource) →
    unsafe_app_entitlements app_id resource entitlements = true)

-- PBT for entitled_access_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  let granted := resource :: entitlements
  granted.contains resource →
    unsafe_app_entitlements app_id resource granted = true)

-- PBT for entitlements_irrelevant_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String)
    (entitlements₁ entitlements₂ : List String),
  unsafe_app_entitlements app_id resource entitlements₁ =
    unsafe_app_entitlements app_id resource entitlements₂)

-- PBT for app_id_irrelevant_prop
#eval Plausible.Testable.check (∀ (app_id₁ app_id₂ : Int) (resource : String)
    (entitlements : List String),
  unsafe_app_entitlements app_id₁ resource entitlements =
    unsafe_app_entitlements app_id₂ resource entitlements)

-- PBT for resource_irrelevant_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource₁ resource₂ : String)
    (entitlements : List String),
  unsafe_app_entitlements app_id resource₁ entitlements =
    unsafe_app_entitlements app_id resource₂ entitlements)

-- PBT for all_inputs_irrelevant_prop
#eval Plausible.Testable.check (∀ (app_id₁ : Int) (resource₁ : String) (entitlements₁ : List String)
    (app_id₂ : Int) (resource₂ : String) (entitlements₂ : List String),
  unsafe_app_entitlements app_id₁ resource₁ entitlements₁ =
    unsafe_app_entitlements app_id₂ resource₂ entitlements₂)

-- PBT for unsafe_differs_from_safe_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  !(entitlements.contains resource) →
    unsafe_app_entitlements app_id resource entitlements !=
      safe_app_entitlements app_id resource entitlements)

-- PBT for unsafe_agrees_with_safe_when_entitled_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  let granted := resource :: entitlements
  granted.contains resource →
    unsafe_app_entitlements app_id resource granted =
      safe_app_entitlements app_id resource granted)

-- PBT for Post_prop
#eval Plausible.Testable.check (∀ (app_id : Int) (resource : String) (entitlements : List String),
  unsafe_app_entitlements app_id resource entitlements = true ∧
  (unsafe_app_entitlements app_id resource entitlements != false) ∧
  unsafe_app_entitlements app_id resource [] = true ∧
  (entitlements.contains resource ||
    unsafe_app_entitlements app_id resource entitlements == true) = true ∧
  (!(entitlements.contains resource) ||
    unsafe_app_entitlements app_id resource entitlements == true) = true ∧
  unsafe_app_entitlements app_id resource entitlements =
    unsafe_app_entitlements app_id resource [] ∧
  unsafe_app_entitlements app_id resource entitlements =
    unsafe_app_entitlements 0 resource entitlements ∧
  unsafe_app_entitlements app_id resource entitlements =
    unsafe_app_entitlements app_id "" entitlements ∧
  unsafe_app_entitlements app_id resource entitlements =
    unsafe_app_entitlements 0 "" [] ∧
  (entitlements.contains resource ||
    unsafe_app_entitlements app_id resource entitlements !=
      safe_app_entitlements app_id resource entitlements) = true ∧
  (!(entitlements.contains resource) ||
    unsafe_app_entitlements app_id resource entitlements ==
      safe_app_entitlements app_id resource entitlements) = true)

-- Bounded PBTs over finite sample domains
def sampleAppIds : List Int := [-1, 0, 1, 5, 7, 42, 99]
def sampleResources : List String := ["", "camera", "contacts", "location", "microphone", "photos"]
def sampleEntitlementLists : List (List String) :=
  [[], ["camera"], ["location"], ["camera", "microphone"], ["contacts", "location", "photos"]]

example : (sampleAppIds.all fun app_id =>
  sampleResources.all fun resource =>
    sampleEntitlementLists.all fun entitlements =>
      unsafe_app_entitlements app_id resource entitlements == true &&
      unsafe_app_entitlements app_id resource entitlements != false &&
      unsafe_app_entitlements app_id resource [] == true &&
      (if !(entitlements.contains resource) then
        unsafe_app_entitlements app_id resource entitlements == true &&
        unsafe_app_entitlements app_id resource entitlements !=
          safe_app_entitlements app_id resource entitlements
       else
        unsafe_app_entitlements app_id resource entitlements ==
          safe_app_entitlements app_id resource entitlements) &&
      unsafe_app_entitlements app_id resource entitlements ==
        unsafe_app_entitlements app_id resource [] &&
      unsafe_app_entitlements app_id resource entitlements ==
        unsafe_app_entitlements 0 resource entitlements &&
      unsafe_app_entitlements app_id resource entitlements ==
        unsafe_app_entitlements app_id "" entitlements &&
      unsafe_app_entitlements app_id resource entitlements ==
        unsafe_app_entitlements 0 "" []) = true := by native_decide

/-! ## Correctness Theorem: Pre -> Post -/

theorem unsafe_app_entitlements_correct (app_id : Int) (resource : String)
    (granted_entitlements : List String)
    (_hpre : Pre app_id resource granted_entitlements) :
    Post_prop app_id resource granted_entitlements :=
  ⟨always_granted_thm app_id resource granted_entitlements,
   never_denied_thm app_id resource granted_entitlements,
   empty_entitlements_granted_thm app_id resource,
   unentitled_access_thm app_id resource granted_entitlements,
   entitled_access_thm app_id resource granted_entitlements,
   entitlements_irrelevant_thm app_id resource granted_entitlements [],
   app_id_irrelevant_thm app_id 0 resource granted_entitlements,
   resource_irrelevant_thm app_id resource "" granted_entitlements,
   all_inputs_irrelevant_thm app_id resource granted_entitlements 0 "" [],
   unsafe_differs_from_safe_thm app_id resource granted_entitlements,
   unsafe_agrees_with_safe_when_entitled_thm app_id resource granted_entitlements⟩

/-! ## Imperative Implementation -/

/-- Imperative implementation using `Id.run do` with mutable state. -/
def unsafe_app_entitlements_imp (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool := Id.run do
  let mut access_granted : Bool := true
  return access_granted

/-! ## Imperative Tests -/

-- Rogue app gains camera access without entitlement
example : unsafe_app_entitlements_imp 42 "camera" [] = true := by native_decide
#eval unsafe_app_entitlements_imp 42 "camera" []

-- App without contacts entitlement still gets access
example : unsafe_app_entitlements_imp 1 "contacts" ["location"] = true := by native_decide
#eval unsafe_app_entitlements_imp 1 "contacts" ["location"]

-- Empty entitlement list: access still granted
example : unsafe_app_entitlements_imp 99 "microphone" [] = true := by native_decide
#eval unsafe_app_entitlements_imp 99 "microphone" []

-- Entitlement list contents are irrelevant
example :
    unsafe_app_entitlements_imp 7 "location" [] =
    unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafe_app_entitlements_imp 7 "location" [] ==
      unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"]

-- Negative: different behavior from safe version
example : unsafe_app_entitlements_imp 5 "camera" [] = true := by native_decide
#eval unsafe_app_entitlements_imp 5 "camera" []

/-! ## Equivalence Theorem: Functional = Imperative -/

theorem unsafe_app_entitlements_equiv (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements_imp app_id resource granted_entitlements := by
  rfl

end «93_unsafeAppEntitlements»

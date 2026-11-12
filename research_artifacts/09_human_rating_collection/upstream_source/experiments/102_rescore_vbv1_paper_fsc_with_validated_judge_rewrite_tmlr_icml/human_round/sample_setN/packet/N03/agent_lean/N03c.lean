import Mathlib

/-!
# Unsafe iOS app entitlements

Translation of the unsafe entitlement model from MIT 6.858, Lecture 9.
Every request succeeds: the app ID, resource, and entitlement list are ignored.
Python integers are represented by `Int`, including negative and arbitrarily
large IDs. There are no restrictions on resource strings or entitlement lists.

The membership-based safe function below is only a comparison specification;
it is not substituted for the vulnerable implementation. Bounded executable
tests provide evidence, while the named theorems prove the unrestricted claims.
-/

namespace UnsafeAppEntitlements

/-! ## Functional implementation -/

/-- Deliberately unsafe: grant access without inspecting any argument. -/
def unsafe_app_entitlements (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool :=
  true

/-- Reference policy for explaining the vulnerability, not the translation. -/
def safe_app_entitlements (_app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  decide (resource ∈ granted_entitlements)

/-! ## The five Python unit tests -/

example : unsafe_app_entitlements 42 "camera" [] = true := by native_decide

example : unsafe_app_entitlements 1 "contacts" ["location"] = true := by
  native_decide

example : unsafe_app_entitlements 99 "microphone" [] = true := by native_decide

example : unsafe_app_entitlements 7 "location" [] =
    unsafe_app_entitlements 7 "location" ["camera", "microphone"] := by
  native_decide

example : unsafe_app_entitlements 5 "camera" [] = true := by native_decide

-- The negative example really differs from the reference safe policy.
example : safe_app_entitlements 5 "camera" [] = false := by native_decide

/-- Executable counterpart of the Python check routine. -/
def check : IO Unit := do
  assert! unsafe_app_entitlements 42 "camera" []
  assert! unsafe_app_entitlements 1 "contacts" ["location"]
  assert! unsafe_app_entitlements 99 "microphone" []
  assert! (unsafe_app_entitlements 7 "location" [] ==
    unsafe_app_entitlements 7 "location" ["camera", "microphone"])
  assert! unsafe_app_entitlements 5 "camera" []
  IO.println "All tests passed."

#eval check

/-! ## Precondition and semantic properties -/

/-- Every well-typed input is admissible; in particular, IDs need not be positive. -/
def Pre (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Prop := True

def always_grants_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements = true

theorem always_grants_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    always_grants_prop app_id resource granted_entitlements := by
  rfl

def entitlements_irrelevant_prop (app_id : Int) (resource : String)
    (first second : List String) : Prop :=
  unsafe_app_entitlements app_id resource first =
    unsafe_app_entitlements app_id resource second

theorem entitlements_irrelevant_thm (app_id : Int) (resource : String)
    (first second : List String) :
    entitlements_irrelevant_prop app_id resource first second := by
  rfl

def app_id_irrelevant_prop (first second : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements first resource granted_entitlements =
    unsafe_app_entitlements second resource granted_entitlements

theorem app_id_irrelevant_thm (first second : Int) (resource : String)
    (granted_entitlements : List String) :
    app_id_irrelevant_prop first second resource granted_entitlements := by
  rfl

def resource_irrelevant_prop (app_id : Int) (first second : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id first granted_entitlements =
    unsafe_app_entitlements app_id second granted_entitlements

theorem resource_irrelevant_thm (app_id : Int) (first second : String)
    (granted_entitlements : List String) :
    resource_irrelevant_prop app_id first second granted_entitlements := by
  rfl

def empty_entitlements_prop (app_id : Int) (resource : String) : Prop :=
  unsafe_app_entitlements app_id resource [] = true

theorem empty_entitlements_thm (app_id : Int) (resource : String) :
    empty_entitlements_prop app_id resource := by
  rfl

/-- Missing authorization never prevents access, unlike the reference policy. -/
def missing_entitlement_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
    safe_app_entitlements app_id resource granted_entitlements = false

theorem missing_entitlement_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    missing_entitlement_prop app_id resource granted_entitlements := by
  intro hmissing
  constructor
  · rfl
  · simp [safe_app_entitlements, hmissing]

/-! ## Postcondition -/

/-- All claims hold for a request, including comparison with arbitrary inputs. -/
def Post_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  always_grants_prop app_id resource granted_entitlements ∧
  empty_entitlements_prop app_id resource ∧
  (∀ other : List String,
    entitlements_irrelevant_prop app_id resource granted_entitlements other) ∧
  (∀ other : Int,
    app_id_irrelevant_prop app_id other resource granted_entitlements) ∧
  (∀ other : String,
    resource_irrelevant_prop app_id resource other granted_entitlements) ∧
  missing_entitlement_prop app_id resource granted_entitlements

/-! ## Bounded property-based tests

These exhaust the Cartesian products below, not just the five unit examples.
The entitlement lists include every list of length zero, one, or two over the
sample resources, hence also duplicates, differing orders, and empty strings.
Each universal comparison in the postcondition is tested over the corresponding
sample domain. The theorem domains above remain unrestricted.
-/

def sampleAppIds : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++
    [42, 99, 1000000, -1000000]

def sampleResources : List String :=
  ["", "camera", "contacts", "microphone", "location", "network", "Camera", "📷"]

def sampleEntitlements : List (List String) :=
  [[]] ++ sampleResources.map (fun r => [r]) ++
    sampleResources.flatMap (fun r => sampleResources.map (fun s => [r, s]))

def allSampleRequests (p : Int → String → List String → Bool) : Bool :=
  sampleAppIds.all (fun app_id =>
    sampleResources.all (fun resource =>
      sampleEntitlements.all (fun granted => p app_id resource granted)))

-- PBT for always_grants_prop.
def alwaysGrantsPBT : Bool :=
  allSampleRequests (fun a r gs => unsafe_app_entitlements a r gs == true)

example : alwaysGrantsPBT = true := by native_decide
#eval alwaysGrantsPBT

-- PBT for entitlements_irrelevant_prop, including all pairs of sample lists.
def entitlementsIrrelevantPBT : Bool :=
  allSampleRequests (fun a r gs =>
    sampleEntitlements.all (fun other =>
      unsafe_app_entitlements a r gs == unsafe_app_entitlements a r other))

example : entitlementsIrrelevantPBT = true := by native_decide
#eval entitlementsIrrelevantPBT

-- PBT for app_id_irrelevant_prop, including negative IDs.
def appIdIrrelevantPBT : Bool :=
  allSampleRequests (fun a r gs =>
    sampleAppIds.all (fun other =>
      unsafe_app_entitlements a r gs == unsafe_app_entitlements other r gs))

example : appIdIrrelevantPBT = true := by native_decide
#eval appIdIrrelevantPBT

-- PBT for resource_irrelevant_prop.
def resourceIrrelevantPBT : Bool :=
  allSampleRequests (fun a r gs =>
    sampleResources.all (fun other =>
      unsafe_app_entitlements a r gs == unsafe_app_entitlements a other gs))

example : resourceIrrelevantPBT = true := by native_decide
#eval resourceIrrelevantPBT

-- PBT for empty_entitlements_prop.
def emptyEntitlementsPBT : Bool :=
  sampleAppIds.all (fun a =>
    sampleResources.all (fun r => unsafe_app_entitlements a r [] == true))

example : emptyEntitlementsPBT = true := by native_decide
#eval emptyEntitlementsPBT

-- PBT for missing_entitlement_prop: Boolean implication, not a filter.
-- Both present and absent entitlements occur in the bounded domain.
def missingEntitlementPBT : Bool :=
  allSampleRequests (fun a r gs =>
    if r ∈ gs then true else
      (unsafe_app_entitlements a r gs == true) &&
      (safe_app_entitlements a r gs == false))

example : missingEntitlementPBT = true := by native_decide
#eval missingEntitlementPBT

-- PBT for the whole Post_prop on each request, with bounded comparisons.
def postPBT : Bool :=
  allSampleRequests (fun a r gs =>
    (unsafe_app_entitlements a r gs == true) &&
    (unsafe_app_entitlements a r [] == true) &&
    sampleEntitlements.all (fun other =>
      unsafe_app_entitlements a r gs == unsafe_app_entitlements a r other) &&
    sampleAppIds.all (fun other =>
      unsafe_app_entitlements a r gs == unsafe_app_entitlements other r gs) &&
    sampleResources.all (fun other =>
      unsafe_app_entitlements a r gs == unsafe_app_entitlements a other gs) &&
    (if r ∈ gs then true else
      (unsafe_app_entitlements a r gs == true) &&
      (safe_app_entitlements a r gs == false)))

example : postPBT = true := by native_decide
#eval postPBT

/-! ## Correctness -/

theorem correctness_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    Pre app_id resource granted_entitlements →
      Post_prop app_id resource granted_entitlements := by
  intro _
  exact ⟨always_grants_thm app_id resource granted_entitlements,
    empty_entitlements_thm app_id resource,
    fun other => entitlements_irrelevant_thm app_id resource granted_entitlements other,
    fun other => app_id_irrelevant_thm app_id other resource granted_entitlements,
    fun other => resource_irrelevant_thm app_id resource other granted_entitlements,
    missing_entitlement_thm app_id resource granted_entitlements⟩

/-! ## Imperative implementation and tests -/

/-- Mutable state is set to true unconditionally; no input is consulted. -/
def unsafe_app_entitlements_imperative (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool := Id.run do
  let mut accessGranted := false
  accessGranted := true
  return accessGranted

example : unsafe_app_entitlements_imperative 42 "camera" [] = true := by
  native_decide

example : unsafe_app_entitlements_imperative 1 "contacts" ["location"] = true := by
  native_decide

example : unsafe_app_entitlements_imperative 99 "microphone" [] = true := by
  native_decide

example : unsafe_app_entitlements_imperative 7 "location" [] =
    unsafe_app_entitlements_imperative 7 "location" ["camera", "microphone"] := by
  native_decide

example : unsafe_app_entitlements_imperative 5 "camera" [] = true := by
  native_decide

#eval unsafe_app_entitlements_imperative 42 "camera" []
#eval unsafe_app_entitlements_imperative 1 "contacts" ["location"]
#eval unsafe_app_entitlements_imperative 99 "microphone" []
#eval unsafe_app_entitlements_imperative 7 "location" ["camera", "microphone"]
#eval unsafe_app_entitlements_imperative 5 "camera" []

-- Additional bounded functional/imperative comparison.
example : allSampleRequests (fun a r gs =>
    unsafe_app_entitlements a r gs ==
      unsafe_app_entitlements_imperative a r gs) = true := by
  native_decide

/-! ## Unrestricted functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements_imperative app_id resource granted_entitlements := by
  rfl

end UnsafeAppEntitlements

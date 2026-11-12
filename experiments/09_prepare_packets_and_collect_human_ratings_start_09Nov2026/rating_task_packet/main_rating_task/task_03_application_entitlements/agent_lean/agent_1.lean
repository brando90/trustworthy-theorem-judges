import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

Translation of a deliberately unsafe entitlement check. The Python function
`unsafe_app_entitlements` returns `True` for every app, resource, and granted
entitlement list: the list is never consulted. That is the vulnerability —
any app gains access to any resource, including when the entitlement list is
empty or names unrelated resources.

A safe counterpart is formalized only as a specification contrast (the Python
comments state that the safe version returns `False` when the resource is not
entitled). The safe check grants access if and only if `resource` occurs in
`granted_entitlements`.

Numeric / data model:
- Python `int` app identifiers are modeled as `Int` (unbounded, possibly negative).
- Resource names and entitlement strings are `String`.
- The granted-entitlement collection is `List String`, matching Python `List[str]`.
- The Boolean decision is Lean `Bool`.
-/

namespace «93_unsafeAppEntitlements»

/-! ## Implementation -/

/-- Unsafe entitlement check.

No check is performed: every resource request is granted unconditionally.
The vulnerability is that `granted_entitlements` (and likewise `app_id` and
`resource`) is never consulted. -/
def unsafe_app_entitlements (_app_id : Int) (_resource : String)
    (_granted_entitlements : List String) : Bool :=
  true

/-- Safe entitlement check used as the behavioural contrast in the Python
comments (`Safe version → False` when the resource is not entitled).

Access is granted if and only if `resource` is a member of
`granted_entitlements`. The numeric app id is not part of the membership
test, matching a profile-style entitlement list attached to the caller. -/
def safe_app_entitlements (_app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  granted_entitlements.contains resource

/-- Bundle of the concrete assertions from the Python `check` function. -/
def check : Bool :=
  unsafe_app_entitlements 42 "camera" [] == true &&
  unsafe_app_entitlements 1 "contacts" ["location"] == true &&
  unsafe_app_entitlements 99 "microphone" [] == true &&
  (unsafe_app_entitlements 7 "location" [] ==
    unsafe_app_entitlements 7 "location" ["camera", "microphone"]) &&
  unsafe_app_entitlements 5 "camera" [] == true &&
  safe_app_entitlements 5 "camera" [] == false

/-! ## Unit tests -/

/-- Rogue app gains camera access without an entitlement. -/
example : unsafe_app_entitlements 42 "camera" [] = true := by native_decide

#eval unsafe_app_entitlements 42 "camera" []

/-- App without a contacts entitlement still gets access. -/
example : unsafe_app_entitlements 1 "contacts" ["location"] = true := by native_decide

#eval unsafe_app_entitlements 1 "contacts" ["location"]

/-- Empty entitlement list: access is still granted. -/
example : unsafe_app_entitlements 99 "microphone" [] = true := by native_decide

#eval unsafe_app_entitlements 99 "microphone" []

/-- Entitlement-list contents are irrelevant. -/
example : unsafe_app_entitlements 7 "location" [] =
    unsafe_app_entitlements 7 "location" ["camera", "microphone"] := by native_decide

#eval unsafe_app_entitlements 7 "location" [] ==
  unsafe_app_entitlements 7 "location" ["camera", "microphone"]

/-- Negative: the unsafe model grants camera access with an empty list,
whereas the safe version returns false. -/
example : unsafe_app_entitlements 5 "camera" [] = true := by native_decide

example : safe_app_entitlements 5 "camera" [] = false := by native_decide

example : unsafe_app_entitlements 5 "camera" [] ≠
    safe_app_entitlements 5 "camera" [] := by native_decide

#eval unsafe_app_entitlements 5 "camera" []

#eval safe_app_entitlements 5 "camera" []

example : check = true := by native_decide

#eval check

#eval if check then "All tests passed." else "Tests failed."

/-! ## Pre-condition -/

/-- The unsafe model imposes no restriction on its inputs: any integer app id,
any resource name, and any entitlement list (including the empty list) are
admissible. -/
def Pre (_app_id : Int) (_resource : String) (_granted_entitlements : List String) : Prop :=
  True

/-! ## Property propositions and theorems -/

/-- **Unconditional grant.** Every request is approved. -/
def unconditional_grant_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements = true

theorem unconditional_grant_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unconditional_grant_prop app_id resource granted_entitlements := by
  unfold unconditional_grant_prop unsafe_app_entitlements
  rfl

/-- **Entitlement irrelevance.** The granted-entitlement list is never
consulted: replacing it cannot change the decision. -/
def entitlement_irrelevance_prop (app_id : Int) (resource : String)
    (e1 e2 : List String) : Prop :=
  unsafe_app_entitlements app_id resource e1 =
    unsafe_app_entitlements app_id resource e2

theorem entitlement_irrelevance_thm (app_id : Int) (resource : String)
    (e1 e2 : List String) :
    entitlement_irrelevance_prop app_id resource e1 e2 := by
  unfold entitlement_irrelevance_prop unsafe_app_entitlements
  rfl

/-- **App-id irrelevance.** The numeric app identifier does not affect the
decision. -/
def app_id_irrelevance_prop (a1 a2 : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements a1 resource granted_entitlements =
    unsafe_app_entitlements a2 resource granted_entitlements

theorem app_id_irrelevance_thm (a1 a2 : Int) (resource : String)
    (granted_entitlements : List String) :
    app_id_irrelevance_prop a1 a2 resource granted_entitlements := by
  unfold app_id_irrelevance_prop unsafe_app_entitlements
  rfl

/-- **Resource irrelevance.** The requested resource name does not affect the
decision. -/
def resource_irrelevance_prop (app_id : Int) (r1 r2 : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id r1 granted_entitlements =
    unsafe_app_entitlements app_id r2 granted_entitlements

theorem resource_irrelevance_thm (app_id : Int) (r1 r2 : String)
    (granted_entitlements : List String) :
    resource_irrelevance_prop app_id r1 r2 granted_entitlements := by
  unfold resource_irrelevance_prop unsafe_app_entitlements
  rfl

/-- **Constant decision.** Any two requests receive the same answer. -/
def constant_decision_prop (a1 a2 : Int) (r1 r2 : String) (e1 e2 : List String) : Prop :=
  unsafe_app_entitlements a1 r1 e1 = unsafe_app_entitlements a2 r2 e2

theorem constant_decision_thm (a1 a2 : Int) (r1 r2 : String) (e1 e2 : List String) :
    constant_decision_prop a1 a2 r1 r2 e1 e2 := by
  unfold constant_decision_prop unsafe_app_entitlements
  rfl

/-- The implementation is the constant-true function. -/
def constant_true_fn_prop : Prop :=
  unsafe_app_entitlements = (fun _ _ _ => true)

theorem constant_true_fn_thm : constant_true_fn_prop := by
  unfold constant_true_fn_prop
  funext app_id resource granted_entitlements
  rfl

/-- **Empty list still grants.** Access is approved even with no entitlements. -/
def empty_list_grants_prop (app_id : Int) (resource : String) : Prop :=
  unsafe_app_entitlements app_id resource [] = true

theorem empty_list_grants_thm (app_id : Int) (resource : String) :
    empty_list_grants_prop app_id resource := by
  unfold empty_list_grants_prop
  exact unconditional_grant_thm app_id resource []

/-- **Grant without entitlement.** If the resource is absent, the unsafe model
still returns true. This is the vulnerability. -/
def grants_without_entitlement_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem grants_without_entitlement_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    grants_without_entitlement_prop app_id resource granted_entitlements := by
  intro _hmiss
  exact unconditional_grant_thm app_id resource granted_entitlements

/-- The safe check returns true exactly when the resource is entitled. -/
def safe_grants_iff_mem_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  safe_app_entitlements app_id resource granted_entitlements = true ↔
    resource ∈ granted_entitlements

theorem safe_grants_iff_mem_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    safe_grants_iff_mem_prop app_id resource granted_entitlements := by
  unfold safe_grants_iff_mem_prop safe_app_entitlements
  simp [List.contains_eq_mem]

/-- **Differs from the safe version when the entitlement is missing.**
The Python negative test records that the safe version returns false for
`(5, "camera", [])` while the unsafe version returns true. In general, absence
of the resource yields unsafe `true` and safe `false`. -/
def differs_from_safe_when_missing_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∉ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
    safe_app_entitlements app_id resource granted_entitlements = false

theorem differs_from_safe_when_missing_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    differs_from_safe_when_missing_prop app_id resource granted_entitlements := by
  intro hmiss
  refine ⟨unconditional_grant_thm app_id resource granted_entitlements, ?_⟩
  have hnot : safe_app_entitlements app_id resource granted_entitlements ≠ true := by
    intro htrue
    exact hmiss ((safe_grants_iff_mem_thm app_id resource granted_entitlements).mp htrue)
  cases hbool : safe_app_entitlements app_id resource granted_entitlements
  · rfl
  · exact absurd hbool hnot

/-- **No false deny relative to the safe check.** Whenever the safe model
grants access, the unsafe model grants it as well. The bug is over-granting,
not under-granting. -/
def unsafe_supersets_safe_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  safe_app_entitlements app_id resource granted_entitlements = true →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem unsafe_supersets_safe_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_supersets_safe_prop app_id resource granted_entitlements := by
  intro _hsafe
  exact unconditional_grant_thm app_id resource granted_entitlements

/-- **Disagreement characterizes the missing entitlement.** The unsafe and safe
models return different Booleans if and only if the resource is not in the
granted list. -/
def disagreement_iff_missing_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  (unsafe_app_entitlements app_id resource granted_entitlements ≠
      safe_app_entitlements app_id resource granted_entitlements) ↔
    resource ∉ granted_entitlements

theorem disagreement_iff_missing_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    disagreement_iff_missing_prop app_id resource granted_entitlements := by
  unfold disagreement_iff_missing_prop
  constructor
  · intro hne hmem
    have hsafe : safe_app_entitlements app_id resource granted_entitlements = true :=
      (safe_grants_iff_mem_thm app_id resource granted_entitlements).mpr hmem
    have hunsafe :
        unsafe_app_entitlements app_id resource granted_entitlements = true :=
      unconditional_grant_thm app_id resource granted_entitlements
    exact hne (hunsafe.trans hsafe.symm)
  · intro hmiss heq
    have hdiff :=
      differs_from_safe_when_missing_thm app_id resource granted_entitlements hmiss
    have : true = false := by
      calc
        true = unsafe_app_entitlements app_id resource granted_entitlements :=
          (hdiff.1).symm
        _ = safe_app_entitlements app_id resource granted_entitlements := heq
        _ = false := hdiff.2
    exact Bool.noConfusion this

/-- When the resource is entitled, both models grant access. -/
def agrees_when_entitled_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  resource ∈ granted_entitlements →
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
    safe_app_entitlements app_id resource granted_entitlements = true

theorem agrees_when_entitled_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    agrees_when_entitled_prop app_id resource granted_entitlements := by
  intro hmem
  refine ⟨unconditional_grant_thm app_id resource granted_entitlements, ?_⟩
  exact (safe_grants_iff_mem_thm app_id resource granted_entitlements).mpr hmem

/-! ## Post-condition -/

/-- Post-condition of one unsafe call: the request is granted, the decision
does not depend on the app id, the resource, or the entitlement list, access
is still granted when the list is empty or does not contain the resource, and
the result differs from the safe membership check exactly in that missing case. -/
def Post_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unconditional_grant_prop app_id resource granted_entitlements ∧
  (∀ e2 : List String,
    entitlement_irrelevance_prop app_id resource granted_entitlements e2) ∧
  (∀ a2 : Int,
    app_id_irrelevance_prop app_id a2 resource granted_entitlements) ∧
  (∀ r2 : String,
    resource_irrelevance_prop app_id resource r2 granted_entitlements) ∧
  (∀ a2 : Int, ∀ r2 : String, ∀ e2 : List String,
    constant_decision_prop app_id a2 resource r2 granted_entitlements e2) ∧
  empty_list_grants_prop app_id resource ∧
  grants_without_entitlement_prop app_id resource granted_entitlements ∧
  differs_from_safe_when_missing_prop app_id resource granted_entitlements ∧
  unsafe_supersets_safe_prop app_id resource granted_entitlements ∧
  disagreement_iff_missing_prop app_id resource granted_entitlements ∧
  agrees_when_entitled_prop app_id resource granted_entitlements ∧
  safe_grants_iff_mem_prop app_id resource granted_entitlements

/-! ## Property-based tests

Executable Boolean forms of each `_prop` and of `Post_prop`. Randomized checks
use Plausible; bounded checks exhaust small app ids and the power set of a
fixed resource universe so properties with rare membership guards are still
exercised. -/

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    unsafe_app_entitlements app_id resource granted_entitlements = true)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (e1 e2 : List String),
    unsafe_app_entitlements app_id resource e1 =
      unsafe_app_entitlements app_id resource e2)

#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (resource : String) (granted_entitlements : List String),
    unsafe_app_entitlements a1 resource granted_entitlements =
      unsafe_app_entitlements a2 resource granted_entitlements)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (r1 r2 : String) (granted_entitlements : List String),
    unsafe_app_entitlements app_id r1 granted_entitlements =
      unsafe_app_entitlements app_id r2 granted_entitlements)

#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (r1 r2 : String) (e1 e2 : List String),
    unsafe_app_entitlements a1 r1 e1 = unsafe_app_entitlements a2 r2 e2)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String),
    unsafe_app_entitlements app_id resource [] = true)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    granted_entitlements.contains resource = false →
      unsafe_app_entitlements app_id resource granted_entitlements = true)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    (safe_app_entitlements app_id resource granted_entitlements = true) =
      granted_entitlements.contains resource)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    granted_entitlements.contains resource = false →
      unsafe_app_entitlements app_id resource granted_entitlements = true ∧
        safe_app_entitlements app_id resource granted_entitlements = false)

-- Executable form of unsafe_supersets_safe_prop without a rare membership guard:
-- unsafe always returns true, so it grants whenever the safe check does.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    unsafe_app_entitlements app_id resource granted_entitlements = true ∨
      safe_app_entitlements app_id resource granted_entitlements = false)

#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    (unsafe_app_entitlements app_id resource granted_entitlements !=
        safe_app_entitlements app_id resource granted_entitlements) =
      !granted_entitlements.contains resource)

-- Executable form of agrees_when_entitled_prop: both models match the
-- membership bit, and the unsafe bit is constantly true.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
      safe_app_entitlements app_id resource granted_entitlements =
        granted_entitlements.contains resource)

-- Executable form of Post_prop. Boolean equalities replace implication
-- guards so Plausible does not discard samples. constant_true_fn_prop is the
-- pointwise constant-true function; its executable check is the unconditional
-- grant / constant-decision tests above.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
    (∀ e2 : List String,
      unsafe_app_entitlements app_id resource granted_entitlements =
        unsafe_app_entitlements app_id resource e2) ∧
    (∀ a2 : Int,
      unsafe_app_entitlements app_id resource granted_entitlements =
        unsafe_app_entitlements a2 resource granted_entitlements) ∧
    (∀ r2 : String,
      unsafe_app_entitlements app_id resource granted_entitlements =
        unsafe_app_entitlements app_id r2 granted_entitlements) ∧
    (∀ a2 : Int, ∀ r2 : String, ∀ e2 : List String,
      unsafe_app_entitlements app_id resource granted_entitlements =
        unsafe_app_entitlements a2 r2 e2) ∧
    unsafe_app_entitlements app_id resource [] = true ∧
    safe_app_entitlements app_id resource granted_entitlements =
      granted_entitlements.contains resource ∧
    ((unsafe_app_entitlements app_id resource granted_entitlements !=
        safe_app_entitlements app_id resource granted_entitlements) =
      !granted_entitlements.contains resource))

def pbtResources : List String :=
  ["camera", "contacts", "microphone", "location"]

def subsetsOf : List String → List (List String)
  | [] => [[]]
  | x :: xs =>
    let rest := subsetsOf xs
    rest ++ rest.map (fun s => x :: s)

example : (List.range 8).all (fun n =>
    let app := Int.ofNat n
    pbtResources.all (fun r =>
      (subsetsOf pbtResources).all (fun es =>
        unsafe_app_entitlements app r es == true &&
        unsafe_app_entitlements app r [] == true &&
        unsafe_app_entitlements app r es == unsafe_app_entitlements (app + 1) r es &&
        unsafe_app_entitlements app r es == unsafe_app_entitlements app "other" es &&
        unsafe_app_entitlements app r es == unsafe_app_entitlements app r (r :: es) &&
        (safe_app_entitlements app r es == es.contains r) &&
        ((unsafe_app_entitlements app r es != safe_app_entitlements app r es) ==
          !es.contains r)))) = true := by
  native_decide

example : (List.range 30).all (fun n =>
    unsafe_app_entitlements (Int.ofNat n) "camera" [] = true &&
    unsafe_app_entitlements (-(Int.ofNat n)) "microphone" ["location"] = true) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    Pre app_id resource granted_entitlements →
      Post_prop app_id resource granted_entitlements := by
  intro _hPre
  unfold Post_prop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact unconditional_grant_thm app_id resource granted_entitlements
  · intro e2
    exact entitlement_irrelevance_thm app_id resource granted_entitlements e2
  · intro a2
    exact app_id_irrelevance_thm app_id a2 resource granted_entitlements
  · intro r2
    exact resource_irrelevance_thm app_id resource r2 granted_entitlements
  · intro a2 r2 e2
    exact constant_decision_thm app_id a2 resource r2 granted_entitlements e2
  · exact empty_list_grants_thm app_id resource
  · exact grants_without_entitlement_thm app_id resource granted_entitlements
  · exact differs_from_safe_when_missing_thm app_id resource granted_entitlements
  · exact unsafe_supersets_safe_thm app_id resource granted_entitlements
  · exact disagreement_iff_missing_thm app_id resource granted_entitlements
  · exact agrees_when_entitled_thm app_id resource granted_entitlements
  · exact safe_grants_iff_mem_thm app_id resource granted_entitlements

/-! ## Imperative implementation -/

/-- Imperative rendering of the same vulnerability.

A mutable decision flag is forced to `true`. The entitlement list, app id, and
resource are bound only so the signature matches the functional version; none
of them is allowed to flip the flag to `false`. -/
def unsafe_app_entitlements_imp (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  Id.run do
    let mut decision : Bool := true
    let mut ignored : Nat := 0
    -- Observe the list length and then discard it: contents are never tested.
    ignored := granted_entitlements.length - granted_entitlements.length
    let _ := app_id
    let _ := resource
    -- `ignored = 0` is always true; both branches grant access.
    if ignored == 0 then
      decision := true
    else
      decision := true
    return decision

/-! ## Imperative tests -/

example : unsafe_app_entitlements_imp 42 "camera" [] = true := by native_decide

#eval unsafe_app_entitlements_imp 42 "camera" []

example : unsafe_app_entitlements_imp 1 "contacts" ["location"] = true := by native_decide

#eval unsafe_app_entitlements_imp 1 "contacts" ["location"]

example : unsafe_app_entitlements_imp 99 "microphone" [] = true := by native_decide

#eval unsafe_app_entitlements_imp 99 "microphone" []

example : unsafe_app_entitlements_imp 7 "location" [] =
    unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"] := by native_decide

#eval unsafe_app_entitlements_imp 7 "location" [] ==
  unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"]

example : unsafe_app_entitlements_imp 5 "camera" [] = true := by native_decide

#eval unsafe_app_entitlements_imp 5 "camera" []

example : unsafe_app_entitlements_imp 5 "camera" [] ≠
    safe_app_entitlements 5 "camera" [] := by native_decide

/-! ## Equivalence theorem -/

/-- The functional and imperative implementations agree on every input. -/
theorem equivalence_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements app_id resource granted_entitlements =
      unsafe_app_entitlements_imp app_id resource granted_entitlements := by
  simp [unsafe_app_entitlements, unsafe_app_entitlements_imp]

/-- The imperative implementation also grants every request. -/
theorem unsafe_app_entitlements_imp_grants_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements_imp app_id resource granted_entitlements = true := by
  simp [unsafe_app_entitlements_imp]

end «93_unsafeAppEntitlements»

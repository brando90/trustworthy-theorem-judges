import Mathlib

/-!
# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)

VeriBench task `93_unsafeAppEntitlements`: a Lean 4 formalisation of the Python
program

    def unsafe_app_entitlements(app_id: int, resource: str,
                                granted_entitlements: List[str]) -> bool:
        """No check: all resource requests are granted unconditionally."""
        return True  # Vulnerability: entitlement list is never consulted

The function receives the identifier of the requesting application, the name of
the protected resource being requested, and the list of entitlements that were
actually granted to that application; it returns `True` unconditionally.  The
granted-entitlement list is never consulted, so *any* application gains access
to *any* resource: this is the missing-entitlement-check vulnerability the model
demonstrates.

The Python `check()` routine asserts

1. `unsafe_app_entitlements(42, "camera", []) is True` - a rogue app gains camera
   access without holding any entitlement;
2. `unsafe_app_entitlements(1, "contacts", ["location"]) is True` - an app
   without the contacts entitlement still gets access;
3. `unsafe_app_entitlements(99, "microphone", []) is True` - an empty entitlement
   list still yields access;
4. `unsafe_app_entitlements(7, "location", []) ==
   unsafe_app_entitlements(7, "location", ["camera", "microphone"])` - the
   contents of the entitlement list are irrelevant;
5. `unsafe_app_entitlements(5, "camera", []) is True`, whereas the *safe* version
   returns `False` - the behaviour differs from a correct implementation.

This file formalises all of that: the functional definition, the safe reference
implementation needed for obligation (5), unit tests for every assertion, a
pre-condition predicate, executable property propositions together with proved
theorems, the post-condition, property-based tests (randomised with Plausible
and bounded/exhaustive ones), the correctness theorem `Pre -> Post`, an
imperative implementation written with `Id.run do` and mutable state, imperative
tests, and the functional/imperative equivalence theorem.

A Lean namespace identifier may not begin with a digit, so the namespace of the
file `93_unsafeAppEntitlements.lean` is called `UnsafeAppEntitlements`.
-/

set_option linter.unusedVariables false

namespace UnsafeAppEntitlements

/-! ## Functional implementation -/

/-- `unsafe_app_entitlements app_id resource granted_entitlements` decides whether
the application `app_id` may access the protected resource `resource`.

Mirroring the Python source exactly, the answer is `true` unconditionally: the
list `granted_entitlements` of entitlements actually granted to the application
is never consulted.  That is the vulnerability. -/
def unsafe_app_entitlements (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  true

/-- The *safe* implementation referred to by the Python comment
`# Safe version -> False`: access is granted exactly when the requested resource
occurs in the list of granted entitlements.  It is used only to state obligation
(5), namely that the unsafe version behaves differently. -/
def safe_app_entitlements (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  granted_entitlements.contains resource

/-! ## Unit tests: the assertions of the Python `check()` routine -/

/-- Executable mirror of the whole Python `check()` routine: the conjunction of
all five assertions it makes. -/
def check_assertions : Bool :=
  (unsafe_app_entitlements 42 "camera" [] == true) &&
    (unsafe_app_entitlements 1 "contacts" ["location"] == true) &&
    (unsafe_app_entitlements 99 "microphone" [] == true) &&
    (unsafe_app_entitlements 7 "location" [] ==
      unsafe_app_entitlements 7 "location" ["camera", "microphone"]) &&
    (unsafe_app_entitlements 5 "camera" [] == true)

-- (1) Rogue app gains camera access without entitlement.
example : unsafe_app_entitlements 42 "camera" [] = true := by native_decide
#eval unsafe_app_entitlements 42 "camera" [] == true

-- (2) App without the contacts entitlement still gets access.
example : unsafe_app_entitlements 1 "contacts" ["location"] = true := by native_decide
#eval unsafe_app_entitlements 1 "contacts" ["location"] == true

-- (3) Empty entitlement list: access is still granted.
example : unsafe_app_entitlements 99 "microphone" [] = true := by native_decide
#eval unsafe_app_entitlements 99 "microphone" [] == true

-- (4) Entitlement list contents are irrelevant.
example : unsafe_app_entitlements 7 "location" [] =
    unsafe_app_entitlements 7 "location" ["camera", "microphone"] := by native_decide
#eval unsafe_app_entitlements 7 "location" [] ==
  unsafe_app_entitlements 7 "location" ["camera", "microphone"]

-- (5) Negative: different behavior from the safe version (safe version -> false).
example : unsafe_app_entitlements 5 "camera" [] = true := by native_decide
example : safe_app_entitlements 5 "camera" [] = false := by native_decide
example : ¬ (unsafe_app_entitlements 5 "camera" [] = safe_app_entitlements 5 "camera" []) := by
  native_decide
#eval (unsafe_app_entitlements 5 "camera" [] == true) &&
  (safe_app_entitlements 5 "camera" [] == false)

-- Every assertion of the Python `check()` routine holds, so it prints
-- "All tests passed."
example : check_assertions = true := by native_decide
#eval if check_assertions = true then "All tests passed." else "assertion failure"

/-! ## Pre-condition -/

/-- The Python function is total and performs no validation: every application
id, every resource name and every entitlement list is an admissible input, so the
pre-condition holds for all arguments. -/
def Pre (app_id : Int) (resource : String) (granted_entitlements : List String) : Prop :=
  True

/-! ## Properties of the implementation -/

/-- Property 1 (Python obligations 1, 2, 3 and 5): access is granted
unconditionally, whatever the application, the resource and the entitlements. -/
def always_granted_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id resource granted_entitlements = true

theorem always_granted_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    always_granted_prop app_id resource granted_entitlements :=
  rfl

/-- Property 2 (Python obligation 4): the granted-entitlement list is never
consulted, hence two requests differing only in their entitlement lists receive
the same answer. -/
def entitlements_ignored_prop (app_id : Int) (resource : String)
    (l1 l2 : List String) : Prop :=
  unsafe_app_entitlements app_id resource l1 = unsafe_app_entitlements app_id resource l2

theorem entitlements_ignored_thm (app_id : Int) (resource : String) (l1 l2 : List String) :
    entitlements_ignored_prop app_id resource l1 l2 :=
  rfl

/-- Property 3: the requested resource name is irrelevant too - every resource is
handed out. -/
def resource_ignored_prop (app_id : Int) (r1 r2 : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements app_id r1 granted_entitlements =
    unsafe_app_entitlements app_id r2 granted_entitlements

theorem resource_ignored_thm (app_id : Int) (r1 r2 : String)
    (granted_entitlements : List String) :
    resource_ignored_prop app_id r1 r2 granted_entitlements :=
  rfl

/-- Property 4: the identity of the requesting application is irrelevant too -
any app, rogue or not, is served. -/
def app_id_ignored_prop (a1 a2 : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  unsafe_app_entitlements a1 resource granted_entitlements =
    unsafe_app_entitlements a2 resource granted_entitlements

theorem app_id_ignored_thm (a1 a2 : Int) (resource : String)
    (granted_entitlements : List String) :
    app_id_ignored_prop a1 a2 resource granted_entitlements :=
  rfl

/-- Property 5 (the vulnerability itself): an application that does *not* hold
the entitlement for `resource` is nevertheless granted access. -/
def unentitled_access_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  granted_entitlements.contains resource = false →
    unsafe_app_entitlements app_id resource granted_entitlements = true

theorem unentitled_access_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unentitled_access_prop app_id resource granted_entitlements :=
  fun _ => rfl

/-- Property 6 (Python obligation 5): on a request that is not entitled, the
unsafe check grants access while the safe check denies it - the two
implementations behave differently. -/
def differs_from_safe_prop (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Prop :=
  granted_entitlements.contains resource = false →
    unsafe_app_entitlements app_id resource granted_entitlements = true ∧
      safe_app_entitlements app_id resource granted_entitlements = false

theorem differs_from_safe_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    differs_from_safe_prop app_id resource granted_entitlements :=
  fun h => ⟨rfl, h⟩

/-- Property 7: the vulnerability is realisable - there is an admissible request
from an application that does not hold the requested entitlement, and that
request is nevertheless granted. -/
def vulnerability_witness_prop : Prop :=
  ∃ (app_id : Int) (resource : String) (granted_entitlements : List String),
    granted_entitlements.contains resource = false ∧
      unsafe_app_entitlements app_id resource granted_entitlements = true

theorem vulnerability_witness_thm : vulnerability_witness_prop :=
  ⟨42, "camera", [], rfl, rfl⟩

/-- Property 8 (Python obligation 5, general form): the unsafe check is *not*
equivalent to the safe one - the two implementations disagree on the requests
that are not entitled. -/
def not_equivalent_to_safe_prop : Prop :=
  ¬ (∀ (app_id : Int) (resource : String) (granted_entitlements : List String),
      unsafe_app_entitlements app_id resource granted_entitlements =
        safe_app_entitlements app_id resource granted_entitlements)

theorem not_equivalent_to_safe_thm : not_equivalent_to_safe_prop := by
  intro h
  have h1 : (true : Bool) = false := h 5 "camera" []
  cases h1

/-! ## Post-condition -/

/-- Executable Boolean mirror of `Post_prop`, used by the property-based tests. -/
def Post_bool (app_id : Int) (resource : String) (granted_entitlements : List String)
    (result : Bool) : Bool :=
  (unsafe_app_entitlements app_id resource granted_entitlements == true) &&
    (result == unsafe_app_entitlements app_id resource granted_entitlements) &&
    (unsafe_app_entitlements app_id resource granted_entitlements ==
      unsafe_app_entitlements app_id resource []) &&
    (granted_entitlements.contains resource ||
      ((unsafe_app_entitlements app_id resource granted_entitlements == true) &&
        (safe_app_entitlements app_id resource granted_entitlements == false)))

/-- Post-condition of an entitlement check: access is granted unconditionally,
`result` is the value produced by the implementation, the entitlement list has no
influence on the answer, and an unentitled request is granted even though the
safe implementation would deny it. -/
def Post_prop (app_id : Int) (resource : String) (granted_entitlements : List String)
    (result : Bool) : Prop :=
  always_granted_prop app_id resource granted_entitlements ∧
  result = unsafe_app_entitlements app_id resource granted_entitlements ∧
  entitlements_ignored_prop app_id resource granted_entitlements [] ∧
  differs_from_safe_prop app_id resource granted_entitlements

/-- The executable mirror of the post-condition is sound: whenever the Boolean
check succeeds for the value returned by the implementation, `Post_prop` holds. -/
theorem Post_bool_sound (app_id : Int) (resource : String)
    (granted_entitlements : List String)
    (h : Post_bool app_id resource granted_entitlements
        (unsafe_app_entitlements app_id resource granted_entitlements) = true) :
    Post_prop app_id resource granted_entitlements
      (unsafe_app_entitlements app_id resource granted_entitlements) :=
  ⟨rfl, rfl, rfl, fun hf => ⟨rfl, hf⟩⟩

/-! ## Property-based tests -/

-- PBT (randomised, Plausible) for `always_granted_prop`: every request, from any
-- app, for any resource, with any entitlement list, is granted.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted : List String),
    unsafe_app_entitlements app_id resource granted = true)

-- PBT (randomised, Plausible) for `entitlements_ignored_prop`: the entitlement
-- list is never consulted.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (l1 l2 : List String),
    unsafe_app_entitlements app_id resource l1 = unsafe_app_entitlements app_id resource l2)

-- PBT (randomised, Plausible) for `resource_ignored_prop` and `app_id_ignored_prop`.
#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (r1 r2 : String) (granted : List String),
    unsafe_app_entitlements a1 r1 granted = unsafe_app_entitlements a2 r2 granted)

-- PBT (randomised, Plausible) for `unentitled_access_prop` and
-- `differs_from_safe_prop`, restricted to the admissible unentitled requests by a
-- decidable implication.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted : List String),
    granted.contains resource = false →
      unsafe_app_entitlements app_id resource granted = true ∧
        safe_app_entitlements app_id resource granted = false)

-- PBT (randomised, Plausible) for the post-condition `Post_prop`, in its
-- executable Boolean form `Post_bool`.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted : List String),
    Post_bool app_id resource granted (unsafe_app_entitlements app_id resource granted) = true)

/-! ### Bounded property-based tests (exhaustive over small domains) -/

/-- Small exhaustive domains used by the bounded property-based tests. -/
def testAppIds : List Int := [0, 1, 5, 7, 42, 99, -3]

def testResources : List String :=
  ["camera", "contacts", "microphone", "location", "files", ""]

def testEntitlements : List (List String) :=
  [[], ["camera"], ["location"], ["camera", "microphone"], ["contacts", "location"],
    ["files", ""]]

-- PBT (bounded) for `always_granted_prop`.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g =>
    unsafe_app_entitlements a r g == true) = true := by native_decide

-- PBT (bounded) for `entitlements_ignored_prop`.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g1 =>
    testEntitlements.all fun g2 =>
      unsafe_app_entitlements a r g1 == unsafe_app_entitlements a r g2) = true := by native_decide

-- PBT (bounded) for `app_id_ignored_prop` and `resource_ignored_prop`.
example : (testAppIds.all fun a1 => testAppIds.all fun a2 => testResources.all fun r1 =>
    testResources.all fun r2 => testEntitlements.all fun g =>
      unsafe_app_entitlements a1 r1 g == unsafe_app_entitlements a2 r2 g) = true := by native_decide

-- PBT (bounded) for `unentitled_access_prop` and `differs_from_safe_prop`: on every
-- unentitled request the unsafe check grants access and the safe check denies it.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g =>
    (g.contains r ||
      ((unsafe_app_entitlements a r g == true) && (safe_app_entitlements a r g == false)))) =
    true := by native_decide

-- PBT (bounded): the unsafe check agrees with the safe check exactly on the
-- entitled requests, and differs from it on every unentitled one.
example : (testResources.all fun r => testEntitlements.all fun g =>
    ((unsafe_app_entitlements 7 r g == safe_app_entitlements 7 r g) == g.contains r)) =
    true := by native_decide

-- PBT (bounded) for the post-condition, in its executable form `Post_bool`.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g =>
    Post_bool a r g (unsafe_app_entitlements a r g)) = true := by native_decide

-- PBT (bounded) over a range of application ids.
example : ((List.range 30).all fun n =>
    unsafe_app_entitlements (Int.ofNat n) "camera" [] == true) = true := by native_decide

-- PBT (bounded) for `vulnerability_witness_prop` and `not_equivalent_to_safe_prop`:
-- the unsafe and the safe check agree exactly on the entitled requests, hence they
-- disagree on every unentitled request, each of which the unsafe check grants.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g =>
    ((unsafe_app_entitlements a r g == safe_app_entitlements a r g) == g.contains r)) =
    true := by native_decide

/-! ## Correctness -/

/-- Correctness of the unsafe entitlement check: for every admissible input the
value it returns satisfies the post-condition. -/
theorem unsafe_app_entitlements_correct (app_id : Int) (resource : String)
    (granted_entitlements : List String)
    (h : Pre app_id resource granted_entitlements) :
    Post_prop app_id resource granted_entitlements
      (unsafe_app_entitlements app_id resource granted_entitlements) :=
  ⟨rfl, rfl, rfl, fun hf => ⟨rfl, hf⟩⟩

/-! ## Imperative implementation -/

/-- Imperative counterpart of `unsafe_app_entitlements`, written with mutable
state inside `Id.run do`.

A correct implementation would scan `granted_entitlements` and grant access only
when the requested resource shows up in it.  This one performs the scan - it
counts the inspected entitlements in `scanned` and records a hit in `found` - and
then *discards* the outcome, setting `access` to `true` unconditionally, exactly
like the Python program does. -/
def unsafe_app_entitlements_imp (app_id : Int) (resource : String)
    (granted_entitlements : List String) : Bool :=
  Id.run do
    let mut access : Bool := false
    let mut found : Bool := false
    let mut scanned : Nat := 0
    for e in granted_entitlements do
      scanned := scanned + 1
      if e == resource then
        found := true
    -- Vulnerability: the result `found` of the entitlement scan never gates the
    -- decision; access is granted unconditionally.
    access := true
    return access

/-! ### Imperative tests -/

example : unsafe_app_entitlements_imp 42 "camera" [] = true := by native_decide
example : unsafe_app_entitlements_imp 1 "contacts" ["location"] = true := by native_decide
example : unsafe_app_entitlements_imp 99 "microphone" [] = true := by native_decide
example : unsafe_app_entitlements_imp 7 "location" [] =
    unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"] := by native_decide
example : unsafe_app_entitlements_imp 5 "camera" [] = true := by native_decide
example : safe_app_entitlements 5 "camera" [] = false := by native_decide
example : ¬ (unsafe_app_entitlements_imp 5 "camera" [] = safe_app_entitlements 5 "camera" []) := by
  native_decide
example : (unsafe_app_entitlements_imp 42 "camera" [] == true) &&
    (unsafe_app_entitlements_imp 1 "contacts" ["location"] == true) &&
    (unsafe_app_entitlements_imp 99 "microphone" [] == true) &&
    (unsafe_app_entitlements_imp 7 "location" [] ==
      unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"]) &&
    (unsafe_app_entitlements_imp 5 "camera" [] == true) = true := by native_decide

#eval unsafe_app_entitlements_imp 42 "camera" []
#eval unsafe_app_entitlements_imp 1 "contacts" ["location"]
#eval unsafe_app_entitlements_imp 7 "location" ["camera", "microphone"]
#eval (unsafe_app_entitlements_imp 5 "camera" [] == true) &&
  (safe_app_entitlements 5 "camera" [] == false)

/-- The imperative implementation also grants every request. -/
theorem imp_always_granted_thm (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements_imp app_id resource granted_entitlements = true :=
  rfl

/-- The imperative implementation satisfies the same post-condition. -/
theorem imp_correct (app_id : Int) (resource : String) (granted_entitlements : List String)
    (h : Pre app_id resource granted_entitlements) :
    Post_prop app_id resource granted_entitlements
      (unsafe_app_entitlements_imp app_id resource granted_entitlements) :=
  ⟨rfl, rfl, rfl, fun hf => ⟨rfl, hf⟩⟩

-- PBT (randomised, Plausible) for the imperative implementation.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted : List String),
    unsafe_app_entitlements_imp app_id resource granted = true)

-- PBT (bounded) for the imperative implementation.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g =>
    unsafe_app_entitlements_imp a r g == true) = true := by native_decide

-- PBT (bounded) for the functional/imperative equivalence.
example : (testAppIds.all fun a => testResources.all fun r => testEntitlements.all fun g =>
    unsafe_app_entitlements_imp a r g == unsafe_app_entitlements a r g) = true := by native_decide

/-! ## Functional / imperative equivalence -/

/-- The imperative implementation computes exactly the same answer as the
functional one: both grant access unconditionally. -/
theorem functional_imperative_equiv (app_id : Int) (resource : String)
    (granted_entitlements : List String) :
    unsafe_app_entitlements_imp app_id resource granted_entitlements =
      unsafe_app_entitlements app_id resource granted_entitlements :=
  rfl

-- PBT (randomised, Plausible) for `functional_imperative_equiv`.
#eval Plausible.Testable.check
  (∀ (app_id : Int) (resource : String) (granted : List String),
    unsafe_app_entitlements_imp app_id resource granted =
      unsafe_app_entitlements app_id resource granted)

end UnsafeAppEntitlements

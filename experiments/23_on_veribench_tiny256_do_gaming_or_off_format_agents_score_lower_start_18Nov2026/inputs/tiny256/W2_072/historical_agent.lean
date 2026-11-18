import Mathlib
namespace Agent

/-!
# Safe CA name constraints

Translation of `safe_ca_name_constraint` and its Python assertion suite.
Python integers are modelled by `Int`, including negative values. A request is
accepted exactly when the issuer belongs to the trusted list and its pre-approved
domain equals the requested domain. In particular, trusting an issuer never
allows it to certify a different domain. Trust lists may be empty or contain
duplicates; there are no additional preconditions.

The functional implementation uses Boolean conjunction. The imperative version
uses mutable state and nested conditionals to preserve short-circuit behavior.
All named theorems have kernel-checked proofs. Native evaluation is used only for
tests, including exhaustive bounded property tests, not for theorem proofs.
-/

namespace «108_unsafeAnyRootCaScope_safe»

/-- The CA must be trusted and restricted to exactly the requested domain. -/
def safe_ca_name_constraint
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Bool :=
  decide (caId ∈ trustedCaIds) && decide (allowedDomain = requestedDomain)

/-! ## Unit tests: the seven assertions from the Python source -/

/-- Executable counterpart of the Python `check` assertion suite. -/
def check (candidate : Int → Int → Int → List Int → Bool) : Bool :=
  (candidate 1 99 2 [99] == false) &&
  (candidate 1 99 1 [99] == true) &&
  (candidate 1 99 1 [1, 2] == false) &&
  (candidate 100 5 100 [5] == true) &&
  (candidate 100 5 200 [5] == false) &&
  (candidate 0 0 0 [0] == true) &&
  (candidate 0 0 0 [] == false)

example : safe_ca_name_constraint 1 99 2 [99] = false := by native_decide
example : safe_ca_name_constraint 1 99 1 [99] = true := by native_decide
example : safe_ca_name_constraint 1 99 1 [1, 2] = false := by native_decide
example : safe_ca_name_constraint 100 5 100 [5] = true := by native_decide
example : safe_ca_name_constraint 100 5 200 [5] = false := by native_decide
example : safe_ca_name_constraint 0 0 0 [0] = true := by native_decide
example : safe_ca_name_constraint 0 0 0 [] = false := by native_decide
example : check safe_ca_name_constraint = true := by native_decide

-- Extra integer/list edge cases, beyond the Python unit suite.
example : safe_ca_name_constraint (-2) (-1) (-2) [-1, -1] = true := by native_decide
example : safe_ca_name_constraint (-2) (-1) 2 [-1, -1] = false := by native_decide

#eval check safe_ca_name_constraint
#eval if check safe_ca_name_constraint then "All tests passed." else "Tests failed."

/-! ## Preconditions and mathematical properties -/

/-- Every integer triple and every finite list of integer CA identifiers is valid. -/
def Pre (_requestedDomain _caId _allowedDomain : Int) (_trustedCaIds : List Int) : Prop :=
  True

/-- Exact acceptance semantics: both conditions are necessary and sufficient. -/
def acceptance_prop
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Prop :=
  safe_ca_name_constraint requestedDomain caId allowedDomain trustedCaIds = true ↔
    caId ∈ trustedCaIds ∧ allowedDomain = requestedDomain

theorem acceptance_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    acceptance_prop requestedDomain caId allowedDomain trustedCaIds := by
  simp [acceptance_prop, safe_ca_name_constraint]

/-- A request is rejected exactly when trust or the name constraint fails. -/
def rejection_prop
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Prop :=
  safe_ca_name_constraint requestedDomain caId allowedDomain trustedCaIds = false ↔
    caId ∉ trustedCaIds ∨ allowedDomain ≠ requestedDomain

theorem rejection_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    rejection_prop requestedDomain caId allowedDomain trustedCaIds := by
  by_cases trusted : caId ∈ trustedCaIds <;>
    simp [rejection_prop, safe_ca_name_constraint, trusted]

/-- No untrusted CA can obtain acceptance, regardless of domain equality. -/
def trusted_ca_prop
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Prop :=
  safe_ca_name_constraint requestedDomain caId allowedDomain trustedCaIds = true →
    caId ∈ trustedCaIds

theorem trusted_ca_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    trusted_ca_prop requestedDomain caId allowedDomain trustedCaIds := by
  intro accepted
  exact ((acceptance_thm requestedDomain caId allowedDomain trustedCaIds).mp accepted).1

/-- Even a trusted (possibly compromised) CA cannot certify outside its scope. -/
def name_constraint_prop
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Prop :=
  safe_ca_name_constraint requestedDomain caId allowedDomain trustedCaIds = true →
    allowedDomain = requestedDomain

theorem name_constraint_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    name_constraint_prop requestedDomain caId allowedDomain trustedCaIds := by
  intro accepted
  exact ((acceptance_thm requestedDomain caId allowedDomain trustedCaIds).mp accepted).2

/-- Valid requests are accepted; the implementation does not reject everything. -/
def completeness_prop
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Prop :=
  caId ∈ trustedCaIds → allowedDomain = requestedDomain →
    safe_ca_name_constraint requestedDomain caId allowedDomain trustedCaIds = true

theorem completeness_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    completeness_prop requestedDomain caId allowedDomain trustedCaIds := by
  intro trusted matching
  exact (acceptance_thm requestedDomain caId allowedDomain trustedCaIds).mpr
    ⟨trusted, matching⟩

/-- The postcondition packages the full specification and its security consequences. -/
def Post_prop
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Prop :=
  acceptance_prop requestedDomain caId allowedDomain trustedCaIds ∧
  rejection_prop requestedDomain caId allowedDomain trustedCaIds ∧
  trusted_ca_prop requestedDomain caId allowedDomain trustedCaIds ∧
  name_constraint_prop requestedDomain caId allowedDomain trustedCaIds ∧
  completeness_prop requestedDomain caId allowedDomain trustedCaIds

/-! ## Property-based tests

Each executable proposition above, including `Post_prop`, has its own bounded
PBT below. These tests exhaust all triples from nine representative integers
and all trust lists of length zero, one, or two over those integers: 66,339
inputs per property. They include negative and zero identifiers, duplicate
entries, absent/present issuers, and matching/mismatching domains. The bounds
apply only to testing: none of the theorem statements restricts the inputs.
-/

private def pbtIntegers : List Int := [-2, -1, 0, 1, 2, 5, 99, 100, 200]

private def pbtTrustLists : List (List Int) :=
  [[]] ++ pbtIntegers.map (fun a => [a]) ++
    pbtIntegers.flatMap (fun a => pbtIntegers.map (fun b => [a, b]))

private def checkBounded (test : Int → Int → Int → List Int → Bool) : Bool :=
  pbtIntegers.all fun requestedDomain =>
    pbtIntegers.all fun caId =>
      pbtIntegers.all fun allowedDomain =>
        pbtTrustLists.all fun trustedCaIds =>
          test requestedDomain caId allowedDomain trustedCaIds

-- Boolean equivalence represents the acceptance iff.
private def acceptanceCheck (r ca a : Int) (ts : List Int) : Bool :=
  safe_ca_name_constraint r ca a ts == decide (ca ∈ ts ∧ a = r)

-- Boolean equivalence represents the rejection iff.
private def rejectionCheck (r ca a : Int) (ts : List Int) : Bool :=
  (safe_ca_name_constraint r ca a ts == false) == decide (ca ∉ ts ∨ a ≠ r)

-- Boolean implications: not antecedent or consequent.
private def trustedCaCheck (r ca a : Int) (ts : List Int) : Bool :=
  !(safe_ca_name_constraint r ca a ts) || decide (ca ∈ ts)

private def nameConstraintCheck (r ca a : Int) (ts : List Int) : Bool :=
  !(safe_ca_name_constraint r ca a ts) || decide (a = r)

private def completenessCheck (r ca a : Int) (ts : List Int) : Bool :=
  !(decide (ca ∈ ts ∧ a = r)) || safe_ca_name_constraint r ca a ts

private def postCheck (r ca a : Int) (ts : List Int) : Bool :=
  acceptanceCheck r ca a ts && rejectionCheck r ca a ts &&
  trustedCaCheck r ca a ts && nameConstraintCheck r ca a ts &&
  completenessCheck r ca a ts

-- PBT for acceptance_prop.
example : checkBounded acceptanceCheck = true := by native_decide
-- PBT for rejection_prop.
example : checkBounded rejectionCheck = true := by native_decide
-- PBT for trusted_ca_prop.
example : checkBounded trustedCaCheck = true := by native_decide
-- PBT for name_constraint_prop.
example : checkBounded nameConstraintCheck = true := by native_decide
-- PBT for completeness_prop.
example : checkBounded completenessCheck = true := by native_decide
-- PBT for Post_prop (Pre imposes no restrictions).
example : checkBounded postCheck = true := by native_decide

#eval [("acceptance_prop", checkBounded acceptanceCheck),
       ("rejection_prop", checkBounded rejectionCheck),
       ("trusted_ca_prop", checkBounded trustedCaCheck),
       ("name_constraint_prop", checkBounded nameConstraintCheck),
       ("completeness_prop", checkBounded completenessCheck),
       ("Post_prop", checkBounded postCheck)]

/-! ## Correctness for every admissible input -/

theorem correctness_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    Pre requestedDomain caId allowedDomain trustedCaIds →
      Post_prop requestedDomain caId allowedDomain trustedCaIds := by
  intro _
  exact ⟨acceptance_thm requestedDomain caId allowedDomain trustedCaIds,
    rejection_thm requestedDomain caId allowedDomain trustedCaIds,
    trusted_ca_thm requestedDomain caId allowedDomain trustedCaIds,
    name_constraint_thm requestedDomain caId allowedDomain trustedCaIds,
    completeness_thm requestedDomain caId allowedDomain trustedCaIds⟩

/-! ## Imperative implementation and tests -/

/-- Nested conditionals perform the same short-circuit check using mutable state. -/
def safe_ca_name_constraint_imperative
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) : Bool :=
  Id.run do
    let mut accepted := false
    if caId ∈ trustedCaIds then
      if allowedDomain = requestedDomain then
        accepted := true
    return accepted

example : safe_ca_name_constraint_imperative 1 99 2 [99] = false := by native_decide
example : safe_ca_name_constraint_imperative 1 99 1 [99] = true := by native_decide
example : safe_ca_name_constraint_imperative 1 99 1 [1, 2] = false := by native_decide
example : safe_ca_name_constraint_imperative 100 5 100 [5] = true := by native_decide
example : safe_ca_name_constraint_imperative 100 5 200 [5] = false := by native_decide
example : safe_ca_name_constraint_imperative 0 0 0 [0] = true := by native_decide
example : safe_ca_name_constraint_imperative 0 0 0 [] = false := by native_decide
example : check safe_ca_name_constraint_imperative = true := by native_decide

#eval check safe_ca_name_constraint_imperative
#eval if check safe_ca_name_constraint_imperative then "All tests passed." else "Tests failed."

/-! ## Functional/imperative equivalence on all inputs -/

theorem equivalence_thm
    (requestedDomain caId allowedDomain : Int) (trustedCaIds : List Int) :
    safe_ca_name_constraint requestedDomain caId allowedDomain trustedCaIds =
      safe_ca_name_constraint_imperative requestedDomain caId allowedDomain trustedCaIds := by
  by_cases trusted : caId ∈ trustedCaIds <;>
    by_cases matching : allowedDomain = requestedDomain <;>
    simp [safe_ca_name_constraint, safe_ca_name_constraint_imperative, trusted, matching]

end «108_unsafeAnyRootCaScope_safe»
end Agent
